`default_nettype none

module ad7476a_interface #(
    parameter CLK_FREQ_HZ = 100000000,
    parameter SCLK_FREQ_HZ = 20000000,
    parameter NUM_DEVICES = 1,
    parameter COVER = 0,
    localparam SAMPLE_WIDTH = 12
) (
    input wire clk_i,
    input wire rst_i,

    // FPGA interface
    input  wire request_i,
    output wire [SAMPLE_WIDTH*NUM_DEVICES-1:0] data_o,
    output reg  data_valid_o,

    // SPI interface
    output wire sclk_o,
    output reg  cs_n_o,
    input  wire [NUM_DEVICES-1:0] sdata_i
);
    // Try to force an elaboration failure if invalid parameters were specified
    generate if (SCLK_FREQ_HZ > 20000000)
        invalid_verilog_parameter SCLK_FREQ_HZ_can_be_no_greater_than_20MHz ();
    endgenerate
    generate if (SCLK_FREQ_HZ > CLK_FREQ_HZ)
        invalid_verilog_parameter CLK_FREQ_HZ_must_be_larger_than_SCLK_FREQ_HZ ();
    endgenerate
    generate if (NUM_DEVICES <= 0)
        invalid_verilog_parameter NUM_DEVICES_must_be_a_positive_integer ();
    endgenerate


    // The number of system clocks per SPI clock
    localparam CLK_DIV = CLK_FREQ_HZ / SCLK_FREQ_HZ;
    // The minimum number of system clocks it takes to satisfy t2 from the datasheet
    localparam T2 = $rtoi($ceil(CLK_FREQ_HZ * 10e-9));
    // The minimum number of system clocks it takes to satisfy t8+tquiet from the datasheet
    localparam T8_PLUS_TQUIET = $rtoi($ceil(CLK_FREQ_HZ * 86e-9));


    /*
     * Create a timer for handling SPI timings
     */
    localparam TIMER_WIDTH = $clog2(T8_PLUS_TQUIET);
    reg start_timer;
    reg timer_done;
    reg [TIMER_WIDTH-1:0] timer_count;
    timer #(
        .WIDTH(TIMER_WIDTH)
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
        .DIV(CLK_DIV),
        .IDLE_HIGH(1)
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
        last_sclk <= sclk_o;
    wire sclk_rising_edge  = sclk_o && !last_sclk;
    wire sclk_falling_edge = !sclk_o && last_sclk;

    /*
     * Count 16 sclk_o falling edges
     */
    reg [3:0] num_sclk_falling_edges = 0;
    reg got_16_sclk_falling_edges = 0;
    always @(posedge clk_i)
        if (rst_i)
            {got_16_sclk_falling_edges, num_sclk_falling_edges} <= 0;
        else
            {got_16_sclk_falling_edges, num_sclk_falling_edges} <= {1'b0,num_sclk_falling_edges} + {3'b0,sclk_falling_edge};

    /*
     * Create a shift register for each device for reading in SPI data and converting it to parallel
     */
    localparam SHIFT_REGISTER_WIDTH = SAMPLE_WIDTH + 1; // add one to account for sclk_o's return to idle
    genvar i;
    generate for (i = 0; i < NUM_DEVICES; i = i+1) begin
        wire [SHIFT_REGISTER_WIDTH-1:0] spi_parallel_out;
        shift_register #(
            .WIDTH(SHIFT_REGISTER_WIDTH)
        ) spi_serial_in_parallel_out (
            .clk_i(clk_i),
            .rst_i(rst_i),
            .advance_i(sclk_rising_edge),
            .bit_i(sdata_i[i]),
            .value_o(spi_parallel_out)
        );
        assign data_o[SAMPLE_WIDTH*i +: SAMPLE_WIDTH] = spi_parallel_out[1 +: SAMPLE_WIDTH];
    end endgenerate

    /*
     * Sampling state machine
     */
    localparam
        WAIT          = 3'h0,
        CHIP_SELECT   = 3'h1,
        READ_SAMPLE   = 3'h2,
        BE_QUIET      = 3'h3,
        SAMPLE_STROBE = 3'h4,
        RESET         = 3'h5;
    reg [2:0] state, next_state;

    // State register
    initial state = RESET;
    always @(posedge clk_i)
        if (rst_i)
            state <= RESET;
        else
            state <= next_state;

    // State transition logic
    always @(*) begin
        next_state = state;
        /* verilator lint_off CASEINCOMPLETE */
        case (state)
            RESET:
                if (sclk_o)
                    next_state = WAIT;
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
        data_valid_o = 0;
        enable_sclk = 0;
        start_timer = 0;
        timer_count = T2[TIMER_WIDTH-1:0];
        /* verilator lint_off CASEINCOMPLETE */
        case (state)
            RESET: begin
                // all outputs are the default
            end
            WAIT: begin
                start_timer = request_i; // TODO: finish this
            end
            CHIP_SELECT: begin
                cs_n_o = 0;
                enable_sclk = timer_done;
            end
            READ_SAMPLE: begin
                timer_count = T8_PLUS_TQUIET[TIMER_WIDTH-1:0];
                start_timer = got_16_sclk_falling_edges;
                cs_n_o = 0;
                enable_sclk = 1;
            end
            BE_QUIET: begin
                // all outputs are the default
            end
            SAMPLE_STROBE: begin
                data_valid_o = 1;
                start_timer = request_i;
            end
        endcase
        /* verilator lint_on CASEINCOMPLETE */
    end


`ifdef FORMAL
    genvar f;

    // Keep track of whether or not $past() is valid
    reg f_past_valid = 0;
    always @(posedge clk_i)
        f_past_valid <= 1;

    // Start BMC and cover with a reset
    always @(posedge clk_i)
        if (!f_past_valid)
            assume(rst_i);

    // Count the number of falling edges, resetting on data_valid_o or a reset
    integer f_falling_edge_counter = 0;
    always @(posedge clk_i)
        if (rst_i || data_valid_o)
            f_falling_edge_counter <= 0;
        else if (f_past_valid && $fell(sclk_o))
            f_falling_edge_counter <= f_falling_edge_counter + 1;
        else
            f_falling_edge_counter <= f_falling_edge_counter;

    // Keep track of the last 13 data bits read clocked in on sdata_i
    reg [SAMPLE_WIDTH:0] f_last_data_word [0:NUM_DEVICES];
    generate for (f = 0; f < NUM_DEVICES; f = f+1) begin
        always @(posedge clk_i)
            if (f_past_valid && $rose(sclk_o))
                f_last_data_word[f] <= {f_last_data_word[f][SAMPLE_WIDTH-1:0], sdata_i[f]};
    end endgenerate

    // Assume that the data input is synchronous to the clock output and only changes on the falling edge
    always @(posedge clk_i)
        if (f_past_valid && $changed(sdata_i))
            assume($fell(sclk_o));

    // Verify that we're always in a valid state
    always @(*)
        assert(
            state == RESET ||
            state == WAIT ||
            state == CHIP_SELECT ||
            state == READ_SAMPLE ||
            state == BE_QUIET ||
            state == SAMPLE_STROBE
        );

    // Verify that data_valid_o is only strobed if 16 falling edges happened. The first falling edge is the clock
    // leaving the idle state, and then the next 3 are dummy bits that the device sends out while making the conversion.
    // The last 12 are the actual sample
    always @(*)
        if (data_valid_o)
            assert(f_falling_edge_counter == SAMPLE_WIDTH+4);

    // Verify that data_o matches the data bits received on sdata_i when data_valid_o is strobed
    generate for (f = 0; f < NUM_DEVICES; f = f+1)
        always @(*)
            if (data_valid_o)
                assert(f_last_data_word[f][SAMPLE_WIDTH:1] == data_o[SAMPLE_WIDTH*f +: SAMPLE_WIDTH]);
    endgenerate

    // Generate a simple test bench that does one read and gets 0xba5 back on each device
    generate if (COVER==1) begin
        always @(*)
            cover(data_valid_o && data_o=={NUM_DEVICES{12'hba5}});
    end endgenerate

`endif

endmodule

`default_nettype wire
