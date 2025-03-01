import types::*;
module memory
(
    input   logic           clk,
    input   logic           rst,

    input   xbar_msg_t      xbar_in[NUM_CPUS],
    output  xbar_msg_t      xbar_out,
    input   bus_msg_t       bus_msg
);


    logic [2**XLEN-1:0][CACHELINE_SIZE-1:0] mem;

    always_ff @(posedge clk) begin
        if (rst) begin
            for (int i = 0; i < 2**XLEN; i++) begin
                mem[i] <= CACHELINE_SIZE'(i);
            end
        end else begin
            xbar_out <= '0;

            // Feel free to change the logic here as needed
            if (bus_msg.valid) begin
                unique case (bus_msg.bus_tx) 
                    Bus_Rd: begin
                        // Read from memory
                        xbar_out.valid <= 1;
                        xbar_out.addr <= bus_msg.addr;
                        xbar_out.data <= mem[bus_msg.addr];
                        xbar_out.destination <= bus_msg.source;
                    end
                
                    // Do we need to handle other bus transactions?

                    default: begin
                        
                    end
                endcase
            end
        end
    end

endmodule