import types::*;
module cache
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

    cacheline_t cacheline[NUM_SETS];
    cacheline_t cacheline_next[NUM_SETS];

    logic [INDEX_WIDTH-1:0] bus_msg_index;
    logic [TAG_WIDTH-1:0] bus_msg_tag;
    logic xbar_msg_valid;
    logic [$clog2(NUM_CPUS)-1:0] xbar_idx;

    // Xbar input logic
    always_comb begin
        xbar_msg_valid  = '0;
        xbar_idx        = '0;
        for (int i = 0; i < NUM_CPUS; i++) begin
            if (xbar_in[i].valid && xbar_in[i].destination == ID) begin 
                xbar_msg_valid  = '1;
                xbar_idx        = ($clog2(NUM_CPUS))'(i);
            end
        end
    end
    
    // bus output logic
    always_comb begin
        arbiter_req     = '0;
        bus_addr        = '0;
        bus_tx          = Bus_Idle;

        
    end


    
    // bus input logic
    always_comb begin
        cacheline_next = cacheline;
        cpu_resp        = '0;
        cpu_rdata       = '0;
        arbiter_busy    = '0;

        bus_msg_index = bus_msg.addr[$clog2(NUM_SETS)-1:0];
        bus_msg_tag = bus_msg.addr[XLEN-1:INDEX_WIDTH];

        
        // Feel free to change the logic here as needed
        if (bus_msg.valid && bus_msg.source == ID) begin
            unique case (cacheline[bus_msg_index].state)
                default: begin
                    
                end
            endcase
        end
    end

    // Xbar output logic
    always_ff @(posedge clk) begin
        if (rst) begin
            xbar_out <= '{
                valid: 0,
                destination: 0,
                addr: 0,
                data: 0
            };
        end else begin
            xbar_out <= '{
                valid: 0,
                destination: 0,
                addr: 0,
                data: 0
            };
        end
    end


    // Cache logic
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
        end
    end


endmodule