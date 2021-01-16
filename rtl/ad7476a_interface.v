`default_nettype none

module ad7476a_interface #(
    parameter CLK_FREQ_HZ,
    parameter SCLK_FREQ_HZ = 20000000
) (
    input wire clk_i,
    input wire rst_i,

    // FPGA interface
    input  wire request_i,
    output wire [11:0] data_o,
    output wire data_valid_o

    // SPI interface
    output wire sclk_o,
    output wire cs_n_o,
    input  wire sdata_i
);
    // Try to force an elaboration failure if invalid parameters were specified
    generate if (SCLK_FREQ_HZ > 20000000)
        invalid_verilog_parameter SCLK_FREQ_HZ_can_be_no_greater_than_20MHz ();
    endgenerate
    generate if (SCLK_FREQ_HZ > CLK_FREQ_HZ)
        invalid_verilog_parameter CLK_FREQ_HZ_must_be_larger_than_SCLK_FREQ_HZ ();
    endgenerate


    // The number of system clocks per SPI clock
    localparam CLK_DIV = CLK_FREQ_HZ / SCLK_FREQ_HZ;
    // The minimum number of system clocks it takes to satisfy t2 from the datasheet
    localparam T2 = $ceil(CLK_FREQ_HZ * 10e-9);
    // The minimum number of system clocks it takes to satisfy t8+tquiet from the datasheet
    localparam T8_PLUS_TQUIET = $ceil(CLK_FREQ_HZ * 86e-9);


    /*
     * Create a timer for handling SPI timings
     */
    localparam TIMER_WIDTH = $clog2(T8_PLUS_TQUIET);
    reg start_timer;
    reg timer_done;
    reg [TIMER_WIDTH-1:0] timer_count;
    timer #(
        WIDTH = TIMER_WIDTH
    ) spi_timer (
        .clk_i(clk_i),
        .rst_i(rst_i),
        .start_i(start_timer),
        .count_i(timer_count),
        .done_o(timer_done)
    );


    /*
     * Create a shift register for reading in SPI data and converting it to parallel
     */
    localparam SPI_DATA_BITS = 16;
    reg [SPI_DATA_BITS-1:0] spi_parallel_out;
    shift_register #(
        WIDTH = SPI_DATA_BITS
    ) spi_serial_in_parallel_out (
        .clk_i(clk_i),
        .rst_i(rst_i),
        .advance_i(),
        .bit_i(),
        .value_o()
    );

    /*
     * Sampling state machine
     */
    localparam
        WAIT          = 3'h0,
        CHIP_SELECT   = 3'h1,
        READ_SAMPLE   = 3'h2,
        BE_QUIET      = 3'h3,
        SAMPLE_STROBE = 3'h4;
    reg [2:0] state, next_state;

    // State register
    initial state = WAIT;
    always @(posedge clk_i)
        if (rst_i)
            state <= WAIT;
        else
            state <= next_state;

    // State transition logic
    always @(*) begin
        next_state = state;
        /* verilator lint_off CASEINCOMPLETE */
        case (state)
            WAIT:
                if (request_i)
                    next_state = CHIP_SELECT;
            CHIP_SELECT:

            READ_SAMPLE:
            BE_QUIET:
            SAMPLE_STROBE:
        endcase
        /* verilator lint_on CASEINCOMPLETE */
    end

    // State outputs
    always @(*) begin
        /* verilator lint_off CASEINCOMPLETE */
        case (state)
            WAIT:
            CHIP_SELECT:
            READ_SAMPLE:
            BE_QUIET:
            SAMPLE_STROBE:
        endcase
        /* verilator lint_on CASEINCOMPLETE */
    end


`ifdef FORMAL
    // Keep track of whether or not $past() is valid
    reg f_past_valid = 0;
    always @(posedge clk_i)
        f_past_valid <= 1;
`endif

endmodule

`default_nettype wire
