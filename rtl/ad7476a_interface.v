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
    output reg  cs_n_o,
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
     * Create a clock divider module for generating sclk_o
     */
    reg enable_sclk;
    clkdiv #(
        DIV = CLK_DIV,
        IDLE_HIGH = 1
    ) sclk_generator (
        .clk_i(clk_i),
        .enable_i(enable_sclk),
        .clk_o(sclk_o)
    );

    /*
     * Detect rising and falling edges of sclk_o
     */
    reg last_sclk = 1;
    always @(posedge clk_i)
        last_sclk <= sclk_o
    wire sclk_rising_edge  = sclk_o && !last_sclk;
    wire sclk_falling_edge = !sclk_o && last_sclk;

    /*
     * Count 16 sclk_o falling edges
     */
    reg [2:0] sclk_falling_edge_counter = 0;
    reg got_16_sclk_falling_edges = 0;
    always @(posedge clk_i)
        if (rst_i)
            {got_16_sclk_falling_edges, num_sclk_falling_edges} <= 0;
        else
            {got_16_sclk_falling_edges, num_sclk_falling_edges} <= num_sclk_falling_edges + sclk_falling_edge;

    /*
     * Create a shift register for reading in SPI data and converting it to parallel
     */
    localparam SPI_DATA_BITS = 16;
    wire [SPI_DATA_BITS-1:0] spi_parallel_out;
    shift_register #(
        WIDTH = SPI_DATA_BITS
    ) spi_serial_in_parallel_out (
        .clk_i(clk_i),
        .rst_i(rst_i),
        .advance_i(sclk_rising_edge),
        .bit_i(sdata_i),
        .value_o(spi_parallel_out)
    );

    /*
     * Sampling state machine
     */
    localparam
        WAIT          = 5'b00001,
        CHIP_SELECT   = 5'b00010,
        READ_SAMPLE   = 5'b00100,
        BE_QUIET      = 5'b01000,
        SAMPLE_STROBE = 5'b10000;
    reg [4:0] state, next_state;

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
                if (timer_done)
                    next_state = READ_SAMPLE;
            READ_SAMPLE:
                if (got_16_sclk_falling_edges)
                    next_state = BE_QUIET;
            BE_QUIET:
                if (timer_done)
                    next_state = SAMPLE_STROBE;
            SAMPLE_STROBE:
                if (request_i)
                    next_state = CHIP_SELECT;
                else
                    next_state = WAIT;
        endcase
        /* verilator lint_on CASEINCOMPLETE */
    end

    // State outputs
    always @(*) begin
        cs_n_o = 1;
        enable_sclk = 0;
        start_timer = 0;
        timer_count = T2;
        /* verilator lint_off CASEINCOMPLETE */
        case (state)
            WAIT:
                start_timer = request_i; // TODO: finish this
            CHIP_SELECT:
                cs_n_o = 0;
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
