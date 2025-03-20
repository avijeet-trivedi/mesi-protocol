module cache
import types::*;
#(
    parameter ID
)
(
    input   logic           clk,
    input   logic           rst,

    // From CPU
    input   logic                                   cpu_req,
    input   logic                                   cpu_we,
    input   logic       [XLEN-1:0]                  cpu_addr,
    input   logic       [CACHELINE_SIZE-1:0]        cpu_wdata,

    // To CPU
    output  logic                                   cpu_ready,
    output  logic                                   cpu_resp,
    output  logic       [CACHELINE_SIZE-1:0]        cpu_rdata,

    // From Snoop Bus
    input   bus_msg_t                               bus_msg,

    // To Snoop Bus
    output  logic       [XLEN-1:0]                  bus_addr,
    output  bus_tx_t                                bus_tx,

    // To Arbiter
    output  logic                                   arbiter_req,
    output  logic                                   arbiter_busy,
    // From Arbiter
    input   logic                                   arbiter_gnt,

    // To Xbar
    output  xbar_msg_t                              xbar_out,

    // From Xbar
    input   xbar_msg_t                              xbar_in[NUM_CPUS]
);

    // ---------------------------------------------------------------------
    // Variable Declarations
    // ---------------------------------------------------------------------

    cacheline_t cacheline[NUM_SETS];
    cacheline_t cacheline_next[NUM_SETS];

    logic [INDEX_WIDTH-1:0] bus_msg_index, cpu_req_index;
    logic [TAG_WIDTH-1:0] bus_msg_tag, cpu_req_tag;
    logic xbar_vld;
    logic [$clog2(NUM_CPUS)-1:0] xbar_idx;
    logic [CACHELINE_SIZE-1:0] xbar_data_resp;
    logic xbar_data_resp_mem;

    logic load, store;
    logic hit, miss;
    logic load_hit, store_hit, replacement;
    
    logic ownGetS, ownGetM, ownPutM;
    logic otrGetS, otrGetM, otrPutM;

    logic [XLEN-1:0] bus_addr_next;
    bus_tx_t bus_tx_next;
    logic arbiter_req_next;

    // ---------------------------------------------------------------------
    // Data Bus Events
    // ---------------------------------------------------------------------

    always_comb begin
        xbar_vld = '0;
        xbar_idx = '0;
        for (int i = 0; i < NUM_CPUS; i++) begin
            if (!xbar_vld && xbar_in[i].valid && xbar_in[i].destination == $clog2(NUM_CPUS)'(ID)) begin 
                xbar_vld  = '1;
                xbar_idx  = ($clog2(NUM_CPUS))'(i);
            end
        end
        xbar_data_resp = xbar_vld ? xbar_in[xbar_idx].data : '0;
        xbar_data_resp_mem = xbar_vld ? (xbar_idx == $clog2(NUM_CPUS)'(NUM_CPUS - 1)) : '0;
    end

    // ---------------------------------------------------------------------
    // Message Bus Events
    // ---------------------------------------------------------------------

    assign bus_msg_index = bus_msg.addr[$clog2(NUM_SETS)-1:0];
    assign bus_msg_tag = bus_msg.addr[XLEN-1:INDEX_WIDTH];

    assign ownGetS = bus_msg.valid && (bus_msg.source == $clog2(NUM_CPUS)'(ID)) && (bus_msg.bus_tx == BusGetS) && cpu_addr == bus_msg.addr; // OwnGetS and aribiter gnt should go high together
    assign ownGetM = bus_msg.valid && (bus_msg.source == $clog2(NUM_CPUS)'(ID)) && (bus_msg.bus_tx == BusGetM) && cpu_addr == bus_msg.addr; // OwnGetM and aribiter gnt should go high together
    assign ownPutM = bus_msg.valid && (bus_msg.source == $clog2(NUM_CPUS)'(ID)) && (bus_msg.bus_tx == BusPutM) && cpu_req && {cacheline[cpu_req_index].tag, cpu_req_index} == bus_msg.addr; // OwnPutM and aribiter gnt should go high together
    assign otrGetS = bus_msg.valid && (bus_msg.source != $clog2(NUM_CPUS)'(ID)) && (bus_msg.bus_tx == BusGetS) && cacheline[bus_msg_index].tag == bus_msg_tag;
    assign otrGetM = bus_msg.valid && (bus_msg.source != $clog2(NUM_CPUS)'(ID)) && (bus_msg.bus_tx == BusGetM) && cacheline[bus_msg_index].tag == bus_msg_tag;
    assign otrPutM = bus_msg.valid && (bus_msg.source != $clog2(NUM_CPUS)'(ID)) && (bus_msg.bus_tx == BusPutM) && cacheline[bus_msg_index].tag == bus_msg_tag;

    // ---------------------------------------------------------------------
    // CPU Events
    // ---------------------------------------------------------------------

    assign cpu_req_index = cpu_addr[$clog2(NUM_SETS)-1:0];
    assign cpu_req_tag = cpu_addr[XLEN-1:INDEX_WIDTH];

    assign load  = cpu_req && !cpu_we;
    assign store = cpu_req &&  cpu_we;

    assign hit   = cpu_req &&  cacheline[cpu_req_index].tag == cpu_req_tag;
    assign miss  = cpu_req &&  cacheline[cpu_req_index].tag != cpu_req_tag;

    assign load_hit = load && hit;
    assign store_hit = store && hit;
    assign replacement = (load || store) && miss;

    // ---------------------------------------------------------------------
    // Controller Logic
    // ---------------------------------------------------------------------
    
    always_comb begin

        // CPU Rsp
        cpu_resp        = '0;
        cpu_rdata       = '0;

        // Bus Req
        arbiter_busy    = '0;
        arbiter_req_next = arbiter_req;
        bus_tx_next = bus_tx;
        bus_addr_next = bus_addr; 

        // Data Rsp
        xbar_out        = '0;

        // Cacheline next state
        cacheline_next  = cacheline;

        // Request on bus (overides CPU request)
        if (bus_msg.valid) begin
            case (cacheline[bus_msg_index].state)             
        
                M: begin
                    if (otrGetS) begin
                        // Send Data to Req and Mem
                        xbar_out = '{
                            valid: '1,
                            destination: bus_msg.source,
                            addr: bus_msg.addr,
                            data: cacheline[bus_msg_index].data,
                            writeback: '1
                        };  
                        // Move to S                      
                        cacheline_next[bus_msg_index].state = S;
                    end else if (otrGetM) begin
                        // Send Data to Req
                        xbar_out = '{
                            valid: '1,
                            destination: bus_msg.source,
                            addr: bus_msg.addr,
                            data: cacheline[bus_msg_index].data,
                            writeback: '0
                        };        
                        // Move to I                
                        cacheline_next[bus_msg_index].state = I;
                    end

                end

                E: begin
                    if (otrGetS) begin
                        // Send Data to Req
                        xbar_out = '{
                            valid: '1,
                            destination: bus_msg.source,
                            addr: bus_msg.addr,
                            data: cacheline[bus_msg_index].data,
                            writeback: '0
                        };  
                        // Move to S                      
                        cacheline_next[bus_msg_index].state = S;
                    end else if (otrGetM) begin
                        // Send Data to Req
                        xbar_out = '{
                            valid: '1,
                            destination: bus_msg.source,
                            addr: bus_msg.addr,
                            data: cacheline[bus_msg_index].data,
                            writeback: '0
                        };        
                        // Move to I                
                        cacheline_next[bus_msg_index].state = I;
                    end

                end

                S: begin
                    if (otrGetM) begin
                        cacheline_next[bus_msg_index].state = I;
                    end                    
                end

                MI: begin
                    if (ownPutM) begin
                        // De-assert request
                        arbiter_req_next = '0;
                        bus_tx_next = BusIdle;
                        bus_addr_next = '0; 
                        // Send Data to Mem
                        xbar_out = '{
                            valid: '1,
                            destination: '0,
                            addr: bus_msg.addr,
                            data: cacheline[bus_msg_index].data,
                            writeback: '1
                        };
                        // Move to I
                        cacheline_next[bus_msg_index].state = I;
                    end else if (otrGetS) begin
                        // Send Data to Req and Mem
                        xbar_out = '{
                            valid: '1,
                            destination: bus_msg.source,
                            addr: bus_msg.addr,
                            data: cacheline[bus_msg_index].data,
                            writeback: '1
                        };
                        cacheline_next[bus_msg_index].state = MI;
                    end else if (otrGetM) begin
                        // Send Data to Req
                        xbar_out = '{
                            valid: '1,
                            destination: bus_msg.source,
                            addr: bus_msg.addr,
                            data: cacheline[bus_msg_index].data,
                            writeback: '0
                        };
                        cacheline_next[bus_msg_index].state = MI;
                    end
                end

                IS: begin
                    if (ownGetS && xbar_vld) begin // xbar_vld should always be high with ownGetS - TODO
                        // De-assert request
                        arbiter_req_next = '0;
                        bus_tx_next = BusIdle;
                        bus_addr_next = '0;                         
                        // Since memory is responding with data, we move to E state
                        if (xbar_data_resp_mem) begin 
                            cacheline_next[bus_msg_index].data = xbar_data_resp;
                            cacheline_next[bus_msg_index].tag = cpu_req_tag;
                            cacheline_next[bus_msg_index].state = E;
                        // If another cache is responding with data, we move to S state
                        end else begin
                            cacheline_next[bus_msg_index].data = xbar_data_resp;
                            cacheline_next[bus_msg_index].tag = cpu_req_tag;                        
                            cacheline_next[bus_msg_index].state = S;
                        end
                    end
                end

                IM: begin
                    if (ownGetM && xbar_vld) begin // xbar_vld should always be high with ownGetM - TODO
                        // De-assert request
                        arbiter_req_next = '0;
                        bus_tx_next = BusIdle;
                        bus_addr_next = '0;                         
                        // Update CL with DataResp
                        cacheline_next[bus_msg_index].data = xbar_data_resp;
                        cacheline_next[bus_msg_index].tag = cpu_req_tag;
                        // Move to M
                        cacheline_next[bus_msg_index].state = M;
                    end
                end   

                SM: begin
                    if (ownGetM && xbar_vld) begin
                        // De-assert request
                        arbiter_req_next = '0;
                        bus_tx_next = BusIdle;
                        bus_addr_next = '0;                          
                        // Update CL with DataResp
                        cacheline_next[bus_msg_index].data = xbar_data_resp;
                        cacheline_next[bus_msg_index].tag = cpu_req_tag;
                        // Move to M
                        cacheline_next[bus_msg_index].state = M;
                    end else if (otrGetM) begin
                        // Move to IM
                        cacheline_next[bus_msg_index].state = IM;
                    end                    
                end 
            endcase
        end

        // CPU request 
        else if (cpu_req) begin
            case (cacheline[cpu_req_index].state)
            
                M: begin
                    if (load_hit) begin
                        // Read
                        cpu_resp = 1'b1;
                        cpu_rdata = cacheline[cpu_req_index].data;
                    end else if (store_hit) begin
                        // Write
                        cpu_resp = 1'b1;
                        cacheline_next[cpu_req_index].data = cpu_wdata;
                    end else if (replacement) begin
                        // Issue PutM
                        arbiter_req_next = '1;
                        bus_tx_next = BusPutM;
                        bus_addr_next = {cacheline[cpu_req_index].tag, cpu_req_index}; 
                        // Move to MI                         
                        cacheline_next[cpu_req_index].state = MI;
                        
                    end                   
                end

                E: begin
                    if (load_hit) begin
                        // Read
                        cpu_resp = 1'b1;
                        cpu_rdata = cacheline[cpu_req_index].data;
                    end else if (store_hit) begin
                        // Write and Move to M
                        cpu_resp = 1'b1;
                        cacheline_next[cpu_req_index].data = cpu_wdata;
                        cacheline_next[cpu_req_index].state = M;
                    end else if (replacement) begin
                        // Move to I
                        cacheline_next[cpu_req_index].state = I;
                    end   
                end
                
                S: begin
                    if (load_hit) begin
                        // Read
                        cpu_resp = 1'b1;
                        cpu_rdata = cacheline[cpu_req_index].data;
                    end else if (store_hit) begin
                        // Issue GetM
                        arbiter_req_next = '1;
                        bus_tx_next = BusGetM;
                        bus_addr_next = cpu_addr;                         
                        // Move to SM
                        cacheline_next[cpu_req_index].state = SM;
                    end else if (replacement) begin
                        // Move to I 
                        cacheline_next[cpu_req_index].state = I;
                    end  
                end

                I: begin
                    if (load) begin
                        // Issue GetS
                        arbiter_req_next = '1;
                        bus_tx_next = BusGetS;
                        bus_addr_next = cpu_addr;                        
                        // Move to IS
                        cacheline_next[cpu_req_index].state = IS;
                    end else if (store) begin
                        // Issue GetM
                        arbiter_req_next = '1;
                        bus_tx_next = BusGetM;
                        bus_addr_next = cpu_addr;                          
                        // Move to IM
                        cacheline_next[cpu_req_index].state = IM;
                    end
                end

            endcase
        end

    end

    // ---------------------------------------------------------------------
    // Cache logic
    // ---------------------------------------------------------------------
    
    always_ff @(posedge clk) begin
        if (rst) begin

            for (int i = 0; i < NUM_SETS; i++) begin
                cacheline[i] <= '{
                    state: I,
                    data: 0,
                    tag: 0
                };
            end

            cpu_ready <= '1;

            arbiter_req <= '0;
            bus_addr    <= '0;
            bus_tx      <= BusIdle;

        end else begin
            for (int i = 0; i < NUM_SETS; i++) begin
                cacheline[i] <= cacheline_next[i];
            end

            if (cpu_req) begin
                cpu_ready <= '0;
            end
            if (cpu_resp) begin
                cpu_ready <= '1;
            end

            arbiter_req <= arbiter_req_next;
            bus_addr    <= bus_addr_next;
            bus_tx      <= bus_tx_next;

        end
    end

    // To bypass lint 
    logic arbiter_gnt_NC = arbiter_gnt;

    // ---------------------------------------------------------------------
    // Properties
    // ---------------------------------------------------------------------
    
    // Invalid State
    property p_state_i_exclusive_read(int i);
        @(posedge clk) 
        (cacheline[i].state == I && load_hit) ##1 (cacheline[i].state == IS) ##[0:(NUM_CPUS-1)] (cacheline[i].state == IS && ownGetS && xbar_data_resp_mem) ##1 (cacheline[i].state == E);
    endproperty

    property p_state_i_shared_read(int i);
        @(posedge clk) 
        (cacheline[i].state == I && load_hit) ##1 (cacheline[i].state == IS) ##[0:(NUM_CPUS-1)] (cacheline[i].state == IS && ownGetS && !xbar_data_resp_mem) ##1 (cacheline[i].state == S);
    endproperty

    property p_state_i_write(int i);
        @(posedge clk) 
        (cacheline[i].state == I && store_hit) ##1 (cacheline[i].state == IM) ##[0:(NUM_CPUS-1)] (cacheline[i].state == IM && ownGetM) ##1 (cacheline[i].state == M);
    endproperty

    // Shared state
    property p_state_s_read(int i);
        @(posedge clk) 
        (cacheline[i].state == S && load_hit);
    endproperty

    property p_state_s_write_with_othergetm_seen_first(int i);
        @(posedge clk) 
        (cacheline[i].state == S && store_hit) ##1 (cacheline[i].state == SM) ##[0:(NUM_CPUS-1)] (cacheline[i].state == SM && otrGetM) ##1 (cacheline[i].state == IM) ##[0:(NUM_CPUS-2)] (cacheline[i].state == IM && ownGetM) ##1 (cacheline[i].state == M);
    endproperty

    property p_state_s_write_with_owngetm_seen_first(int i);
        @(posedge clk) 
        (cacheline[i].state == S && store_hit) ##1 (cacheline[i].state == SM) ##[0:(NUM_CPUS-1)] (cacheline[i].state == SM && ownGetM) ##1 (cacheline[i].state == M);
    endproperty

    property p_state_s_replacement(int i);
        @(posedge clk) 
        (cacheline[i].state == S && replacement) ##1 (cacheline[i].state == I);
    endproperty

    property p_state_s_othergetm(int i);
        @(posedge clk) 
        (cacheline[i].state == S && otrGetM) ##1 (cacheline[i].state == I);
    endproperty

    // Exclusive state
    property p_state_e_read(int i);
        @(posedge clk) 
        (cacheline[i].state == E) && (load_hit) && cpu_resp;
    endproperty

    property p_state_e_write(int i);
        @(posedge clk) 
        (cacheline[i].state == E && cpu_resp) ##1 (cacheline[i].state == M);  // We resp and initiate write in E state and then move to M
    endproperty

    property p_state_e_othergets(int i);
        @(posedge clk) 
        (cacheline[i].state == E && otrGetS) ##1 (cacheline[i].state == S);
    endproperty

    property p_state_e_replacement(int i);
        @(posedge clk) 
        (cacheline[i].state == E && replacement) ##1 (cacheline[i].state == I);
    endproperty

    property p_state_e_othergetm(int i);
        @(posedge clk) 
        (cacheline[i].state == E && otrGetM) ##1 (cacheline[i].state == I);
    endproperty

    // Modify State
    property p_state_m_read(int i);
        @(posedge clk) 
        (cacheline[i].state == M) && (load_hit) && cpu_resp;
    endproperty

    property p_state_m_write(int i);
        @(posedge clk) 
        (cacheline[i].state == M) && (store_hit) && cpu_resp;
    endproperty

    property p_state_m_replacement_with_othergets_seen_first(int i);
        @(posedge clk) 
        ((cacheline[i].state == M && replacement) ##1 (cacheline[i].state == MI)) ##[0:(NUM_CPUS-1)] (cacheline[i].state == MI && otrGetS) ##1 (cacheline[i].state == MI);
    endproperty

    property p_state_m_replacement_with_othergetm_seen_first(int i);
        @(posedge clk) 
        ((cacheline[i].state == M && replacement) ##1 (cacheline[i].state == MI)) ##[0:(NUM_CPUS-1)] (cacheline[i].state == MI && otrGetM) ##1 (cacheline[i].state == MI);
    endproperty

    property p_state_m_replacement_with_ownputm_seen_first(int i);
        @(posedge clk) 
        ((cacheline[i].state == M && replacement) ##1 (cacheline[i].state == MI)) ##[0:(NUM_CPUS-1)] (cacheline[i].state == MI && ownPutM) ##1 (cacheline[i].state == I);
    endproperty

    // ---------------------------------------------------------------------
    // Covers
    // ---------------------------------------------------------------------

    for (genvar i = 0; i < NUM_SETS; i++) begin: state_transition
        // Invalid State
        cp_state_i_exclusive_read: cover property (p_state_i_exclusive_read(i));
        cp_state_i_shared_read: cover property (p_state_i_shared_read(i));
        cp_state_i_write: cover property (p_state_i_write(i));

        // Shared State
        cp_state_s_read: cover property (p_state_s_read(i));
        cp_state_s_write_with_othergetm_seen_first: cover property (p_state_s_write_with_othergetm_seen_first(i));
        cp_state_s_write_with_owngetm_seen_first: cover property (p_state_s_write_with_owngetm_seen_first(i));
        cp_state_s_replacement: cover property (p_state_s_replacement(i));
        cp_state_s_othergetm: cover property (p_state_s_othergetm(i));

        // Exclusive State
        cp_state_e_read: cover property (p_state_e_read(i));
        cp_state_e_write_hit: cover property (p_state_e_write(i));
        cp_state_e_othergets: cover property (p_state_e_othergets(i));
        cp_state_e_replacement: cover property (p_state_e_replacement(i));
        cp_state_e_othergetm: cover property (p_state_e_othergetm(i));

        // Modify State
        cp_state_m_read: cover property (p_state_m_read(i));
        cp_state_m_write: cover property (p_state_m_write(i));
        cp_state_m_replacement_with_othergets_seen_first: cover property (p_state_m_replacement_with_othergets_seen_first(i));
        cp_state_m_replacement_with_othergetm_seen_first: cover property (p_state_m_replacement_with_othergetm_seen_first(i));
        cp_state_m_replacement_with_ownputm_seen_first: cover property (p_state_m_replacement_with_ownputm_seen_first(i));

    end

    for (genvar i = 0; i < NUM_SETS; i++) begin: state_reach
        cp_state_m : cover property (@(posedge clk) cacheline[i].state == M);
        cp_state_e : cover property (@(posedge clk) cacheline[i].state == E);
        cp_state_s : cover property (@(posedge clk) cacheline[i].state == S);
        cp_state_i : cover property (@(posedge clk) cacheline[i].state == I);
        cp_state_is: cover property (@(posedge clk) cacheline[i].state == IS);
        cp_state_im: cover property (@(posedge clk) cacheline[i].state == IM);
        cp_state_sm: cover property (@(posedge clk) cacheline[i].state == SM);
        cp_state_mi: cover property (@(posedge clk) cacheline[i].state == MI);        
    end

    // ---------------------------------------------------------------------
    // Assertions
    // ---------------------------------------------------------------------

    i_owngetm_implies_xbar_i_vld: assert property (@(posedge clk) ownGetM |-> xbar_vld);
    i_owngets_implied_xbar_i_vld: assert property (@(posedge clk) ownGetS |-> xbar_vld);
    i_ownputm_implied_xbar_o_vld: assert property (@(posedge clk) ownPutM |-> (xbar_out.valid && xbar_out.writeback));

    for (genvar i = 0; i < NUM_SETS; i++) begin: illegal_state_transition_check 
        ap_transition_m  : assert property (@(posedge clk) ((cacheline[i].state == M)  |=> cacheline[i].state inside {M,MI,S,I}));
        ap_transition_e  : assert property (@(posedge clk) ((cacheline[i].state == E)  |=> cacheline[i].state inside {M,E,S,I}));
        ap_transition_s  : assert property (@(posedge clk) ((cacheline[i].state == S)  |=> cacheline[i].state inside {S,I,SM}));
        ap_transition_i  : assert property (@(posedge clk) ((cacheline[i].state == I)  |=> cacheline[i].state inside {I,IS,IM}));
        ap_transition_is : assert property (@(posedge clk) ((cacheline[i].state == IS) |=> cacheline[i].state inside {IS,E,S}));
        ap_transition_im : assert property (@(posedge clk) ((cacheline[i].state == IM) |=> cacheline[i].state inside {IM,M}));
        ap_transition_sm : assert property (@(posedge clk) ((cacheline[i].state == SM) |=> cacheline[i].state inside {SM,IM,M}));
        ap_transition_mi : assert property (@(posedge clk) ((cacheline[i].state == MI) |=> cacheline[i].state inside {MI,I}));
    end

    for (genvar i = 0; i < NUM_SETS; i++) begin: illegal_bus_req 
        ap_m  : assert property (@(posedge clk) ((cacheline[i].state ==  M && bus_msg_index == INDEX_WIDTH'(i)) |-> (not (ownGetS || ownGetM || ownPutM))));
        ap_e  : assert property (@(posedge clk) ((cacheline[i].state ==  E && bus_msg_index == INDEX_WIDTH'(i)) |-> (not (ownGetS || ownGetM || ownPutM))));
        ap_s  : assert property (@(posedge clk) ((cacheline[i].state ==  S && bus_msg_index == INDEX_WIDTH'(i)) |-> (not (ownGetS || ownGetM || ownPutM))));
        ap_i  : assert property (@(posedge clk) ((cacheline[i].state ==  I && bus_msg_index == INDEX_WIDTH'(i)) |-> (not (ownGetS || ownGetM || ownPutM))));
        ap_is : assert property (@(posedge clk) ((cacheline[i].state == IS && bus_msg_index == INDEX_WIDTH'(i)) |-> (not (ownGetM || ownPutM))));
        ap_im : assert property (@(posedge clk) ((cacheline[i].state == IM && bus_msg_index == INDEX_WIDTH'(i)) |-> (not (ownGetS || ownPutM))));
        ap_sm : assert property (@(posedge clk) ((cacheline[i].state == SM && bus_msg_index == INDEX_WIDTH'(i)) |-> (not (ownGetS || ownPutM))));
        ap_mi : assert property (@(posedge clk) ((cacheline[i].state == MI && bus_msg_index == INDEX_WIDTH'(i)) |-> (not (ownGetS || ownGetM))));
    end

    ap_gnt_implies_bus_access : assert property (@(posedge clk) ((arbiter_gnt == 1'b1) |-> ((ownGetS || ownGetM || ownPutM))));

endmodule 