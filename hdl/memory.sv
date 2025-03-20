module memory
import types::*;
(
    input   logic           clk,
    input   logic           rst,

    input   xbar_msg_t      xbar_in[NUM_CPUS],
    output  xbar_msg_t      xbar_out,
    input   bus_msg_t       bus_msg
);

    logic [2**XLEN-1:0][CACHELINE_SIZE-1:0] mem;

    logic wb_vld;
    logic [$clog2(NUM_CPUS)-1:0] wb_idx;
    logic [CACHELINE_SIZE-1:0] wb_data;
    logic [XLEN-1:0] wb_addr;

    always_comb begin
        wb_vld = '0;
        wb_idx = '0;
        for (int i = 0; i < NUM_CPUS; i++) begin
            if (xbar_in[i].valid && xbar_in[i].writeback == '1) begin 
                wb_vld  = '1;
                wb_idx  = ($clog2(NUM_CPUS))'(i);
            end
        end
        wb_data = wb_vld ? xbar_in[wb_idx].data : '0;
        wb_addr = wb_vld ? xbar_in[wb_idx].addr : '0;
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            for (int i = 0; i < 2**XLEN; i++) begin
                mem[i] <= CACHELINE_SIZE'(i);
            end
        end else begin

            if (wb_vld) begin
                mem[wb_addr] <= wb_data;
            end
        end
    end

    // Read data from memory and send it to the crossbar
    always_comb begin
        if (bus_msg.valid && (bus_msg.bus_tx == BusGetS || bus_msg.bus_tx == BusGetM)) begin
            xbar_out.valid = '1;
            xbar_out.addr = bus_msg.addr;
            xbar_out.data = mem[bus_msg.addr];
            xbar_out.destination = bus_msg.source;
            xbar_out.writeback = '0;
        end else begin
            xbar_out.valid = '0;
            xbar_out.addr = '0;
            xbar_out.data = '0;
            xbar_out.destination = '0;
            xbar_out.writeback = '0;
        end
    end

endmodule