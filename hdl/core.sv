module core
import types::*;
#(
    parameter ID
)
(
    input   logic                                   clk,
    input   logic                                   rst,

    // From Cache
    input   logic                                   cpu_ready,
    input   logic                                   cpu_resp,
    input   logic       [CACHELINE_SIZE-1:0]        cpu_rdata,

    // To Cache
    output  logic                                   cpu_req,
    output  logic                                   cpu_we,
    output  logic       [XLEN-1:0]                  cpu_addr,
    output  logic       [CACHELINE_SIZE-1:0]        cpu_wdata
);

    
    cpu_state_t cpu_state, cpu_state_next, test_state;
    logic [XLEN-1:0] addr_reg, addr_file;
    logic [CACHELINE_SIZE-1:0] wdata_reg, wdata_file;
    int fd;


    initial begin
        fd = $fopen ($sformatf("inputs_%0d.txt", ID), "r");

        if (fd == 0) begin
            $error("Failed to open test vector file");
            $finish;
        end
    end

    
    always_comb begin
        cpu_req             = '0;
        cpu_we              = '0;
        cpu_addr            = '0;
        cpu_wdata           = '0;
        
        unique case (cpu_state)
            CPU_IDLE: begin
                cpu_state_next  = test_state;
            end

            CPU_READ: begin
                cpu_req         = '1;
                cpu_addr        = addr_reg;

                if (cpu_resp) begin
                    cpu_state_next  = CPU_IDLE;
                end else begin
                    cpu_state_next  = CPU_READ;
                end
            end

            CPU_WRITE: begin
                cpu_req         = '1;
                cpu_we          = '1;
                cpu_addr        = addr_reg;
                cpu_wdata       = wdata_reg;
                
                if (cpu_resp) begin
                    cpu_state_next  = CPU_IDLE;
                end else begin
                    cpu_state_next  = CPU_WRITE;
                end
            end

            default: begin
                cpu_state_next  = CPU_IDLE;
            end
        endcase
    end


    always_ff @(posedge clk) begin
        if (rst) begin
            cpu_state   <= CPU_IDLE;
            addr_reg    <= '0;
            wdata_reg   <= '0;
        end else begin
            if (cpu_state == CPU_IDLE && cpu_ready) begin
                if ($fscanf(fd, "%d %d %d", test_state, addr_file, wdata_file) != 3) begin
                    $display("===========================================================");
                    $display("Core %0d: End of test vector", ID);
                    $display("===========================================================");
                    $finish;
                end else begin
                    if (test_state != CPU_IDLE) begin
                        $display("Time: %0t, Core %0d: State: %0s, addr: %0d, wdata: %0d", $time, ID, test_state.name(), addr_file, wdata_file);
                    end else begin
                        // $display("Skipping invalid entry");
                    end
                end
                cpu_state <= test_state;
            end else begin
                cpu_state <= cpu_state_next;
            end

            addr_reg    <= addr_file;
            wdata_reg   <= wdata_file;
        end
    end

    /***** SVA *****/

    // // Check that wdata is 0 when not writing
    // property p_wdata_zero;
    //     @(posedge clk) disable iff (rst)
    //     (cpu_state == CPU_READ || cpu_state == CPU_IDLE) |-> (wdata == 0);
    // endproperty
    // assert property (p_wdata_zero) else $error("wdata is 0 when not writing");

    // // Check that read or write state is followed by IDLE state when resp is received
    // property p_read_write_idle;
    //     @(posedge clk) disable iff (rst)
    //     (cpu_state == CPU_READ || cpu_state == CPU_WRITE) |-> s_eventually (resp && (cpu_state == CPU_IDLE));
    // endproperty
    // assert property (p_read_write_idle) else $error("Read or write state not followed by IDLE state");

    logic [CACHELINE_SIZE-1:0] cpu_rdata_NC = cpu_rdata;

endmodule


