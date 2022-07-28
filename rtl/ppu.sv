// Copyright (c) 2012-2013 Ludvig Strigeus
// This program is GPL Licensed. See COPYING for the full license.

// altera message_off 10935
// altera message_off 10027

// Disable this for more dainty FPGAs
`define EXTRA_SPRITES

import regs_savestates::*;

// H = Horizontal
// V = Vertical
// EQ = Equals
// GT/LT = Greater-than Less-than
// R = "and rendering"
enum {
	H_EQ_256,
	H_EQ_270,
	H_EQ_279,
	H_EQ_65R,
	H_EQ_0_7_OR_256_263,
	IN_VISIBLE_FRAME,
	H_EQ_339R,
	H_EQ_63R,
	H_EQ_255R,
	H_LT_64R,
	H_EQ_256_TO_319R,
	H_EQ_279_TO_303,
	H_EQ_270_TO_327,
	IN_VISIBLE_FRAME_R,
	H_MOD8_0_OR_1R,
	H_MOD8_6_OR_7R,
	H_MOD8_4_OR_5R,
	H_EQ_320_TO_335R,
	H_LT_256R,
	H_MOD8_2_OR_3R,
	H_EQ_328,
	H_EQ_304,
	H_EQ_323,
	H_EQ_308,
	V_EQ_247,
	V_EQ_244,
	V_EQ_261,
	V_EQ_261_I,
	V_EQ_241,
	V_EQ_0,
	V_EQ_240,
	V_EQ_255
} timing_signals;

// Generates the current scanline / cycle counters
module ClockGen(
	input  logic       clk,
	input  logic       ce,
	input  logic       ce2,
	input  logic       reset,
	input  logic [1:0] sys_type,
	input  logic       nes_reset,
	input  logic       h_eq_339r,
	input  logic       v_eq_261,
	input  logic       v_eq_255,
	output logic       held_reset,
	output logic [8:0] scanline,
	output logic [8:0] cycle,
	output logic       end_of_line,
	output logic       entering_vblank,
	output logic       short_frame,
	output logic       pclk0,        // Phase clock 0
	output logic       pclk1         // Phase clock 1
);

// State
logic even_frame_toggle = 0; // 1 indicates even frame.
logic [8:0] cycle_next, scanline_next;
logic [8:0] cycle_latch, scanline_latch;

// Ephmeral state
logic reset_reg;

// Nonvolatile State
logic [8:0] vblank_start_sl;
logic [8:0] vblank_end_sl;
logic skip_en;
logic v261_last = 0;

// Continuous Intermediates
logic skip_dot;

assign pclk0 = ce;
assign pclk1 = ce2;

// For NTSC only, the *last* cycle of odd frames is skipped. This signal is for de-jitter.
assign short_frame = skip_dot && pclk0;

assign skip_dot = v_eq_261 && h_eq_339r && ~even_frame_toggle && skip_en;
assign held_reset = reset | (nes_reset & reset_reg);

assign cycle = pclk0 ? cycle_next : cycle_latch;
assign scanline = pclk0 && end_of_line ? scanline_next : scanline_latch;
assign entering_vblank = cycle == 1 && scanline == vblank_start_sl;

always @(posedge clk) if (reset) begin
	cycle_latch <= 9'd0;
	scanline_latch <= 9'd0;
	even_frame_toggle <= 0;
	end_of_line <= 0;
	reset_reg <= 1;
	cycle_next <= 0;
	scanline_next <= 0;

	case (sys_type)
		2'b00,2'b11: begin // NTSC/Vs.
			vblank_start_sl <= 9'd241;
			vblank_end_sl   <= 9'd260;
			skip_en         <= 1'b1;
		end

		2'b01: begin       // PAL
			vblank_start_sl <= 9'd241;
			vblank_end_sl   <= 9'd310;
			skip_en         <= 1'b0;
		end

		2'b10: begin       // Dendy
			vblank_start_sl <= 9'd291;
			vblank_end_sl   <= 9'd310;
			skip_en         <= 1'b0;
		end
	endcase
end else begin
	if (pclk1) begin // The determinaton to advance to the next line is made at pclk1
		end_of_line <= 0;
		v261_last <= v_eq_261;
		if (v261_last)
			reset_reg <= 0;

		cycle_next <= cycle_next + 1'd1;
		if (skip_dot || cycle == 340) begin
			end_of_line <= 1;
			cycle_next <= 0;
			scanline_next <= scanline_latch == vblank_end_sl ? 9'd511 : v_eq_261 ? 9'd0 : scanline_latch + 1'd1;
		end
	end

	// Once the scanline counter reaches end of 260, it gets reset to -1.

	if (pclk0) begin
		cycle_latch <= cycle_next;

		if (end_of_line) begin
			scanline_latch <= scanline_next;



			if (v_eq_255)
				even_frame_toggle <= ~even_frame_toggle;
		end
	end
end

endmodule // ClockGen

module VramGen (
	input  logic        clk,
	input  logic        reset,
	input  logic        pclk0,
	input  logic        pclk1,
	input  logic        read_ce,
	input  logic        write_ce,
	input  logic        is_rendering,
	input  logic        rendering_enabled,
	input  logic  [2:0] ain,           // input address from CPU
	input  logic  [7:0] din,           // data input
	input  logic        read,          // read
	input  logic        write,         // write
	input  logic        v_eq_261, // Is this the pre-render scanline
	input  logic        ppu_incr,
	input  logic        HVTog,
	input  logic        h_eq_255r,
	input  logic        h_mod8_6_or_7r,
	input  logic        h_lt_256r,
	input  logic        h_eq_320_to_335r,
	input  logic        h_eq_279_to_303,
	input  logic        hpos_0,
	input  logic        w2000,
	input  logic        w2005a,
	input  logic        w2005b,
	input  logic        w2006a,
	input  logic        w2006b,
	input  logic        w2007,
	input  logic        r2007,

	output logic [14:0] vram_addr,
	output logic  [2:0] fine_x_scroll  // Current fine_x_scroll value
);

// Temporary VRAM address register
logic [14:0] vram_t;

// All cycle timing signals are delayed by 1 pclk1 and 1 pclk0
logic [1:0] load_vscroll_next;
logic [2:0] copy_hscroll;
logic [1:0] load_hscroll_next;
logic [1:0] copy_vscroll;

// Write signal handling
logic trigger_2007;
logic write_2006;
logic w2006b_reg = 0;
logic w2006b_pipe = 0;

// Other intermediates
logic [14:0] vram_t_mask, vram_t_reg;
logic [14:0] vram_v;

assign load_hscroll_next[0] = ((h_mod8_6_or_7r && hpos_0) && (h_lt_256r || h_eq_320_to_335r));
assign load_vscroll_next[0] = h_eq_255r;


assign vram_t[14] = w2005b ? din[2]: w2006a ? 1'b0 : vram_t_reg[14];
assign vram_t[13:12] = w2005b ? din[1:0]: w2006a ? din[5:4] : vram_t_reg[13:12];
assign vram_t[11:10] = w2000 ? din[1:0]: w2006a ? din[3:2] : vram_t_reg[11:10];
assign vram_t[9:8] = w2005b ? din[7:6]: w2006a ? din[1:0] : vram_t_reg[9:8];
assign vram_t[7:5] = w2005b ? din[5:3]: w2006b ? din[7:5] : vram_t_reg[7:5];
assign vram_t[4:0] = w2005a ? din[7:3]: w2006b ? din[4:0] : vram_t_reg[4:0];

// VRAM_v reference:
// [14 13 12] [11 10] [9 8 7 6 5] [4 3 2 1 0]
//  Fine Y     NT Sel  Coarse Y    Coarse X
// Fine X is its own seperate register.

// Performs the glitchy vram_scroll used by Burai Fighter and some others
assign trigger_2007 = w2007 | r2007;

// Mask used to simulate glitchy behavior caused by a 2006 delayed write landing on the same cycle
// as natural copy from t->v
assign {vram_t_mask[10], vram_t_mask[4:0]} = (write_2006 || copy_hscroll[0]) ? {vram_t[10], vram_t[4:0]} : 6'b11_1111;
assign {vram_t_mask[14:11], vram_t_mask[9:5]} = (write_2006 || copy_vscroll[0]) ? {vram_t[14:11], vram_t[9:5]} : 9'b1_1111_1111;

// assign load_vscroll_next[0] = h_eq_255r;
// assign load_hscroll_next[0] = ((h_mod8_6_or_7r && hpos_0) && (h_lt_256r || h_eq_320_to_335r));

assign vram_addr = vram_v; // gated by pclk0, but shouldn't matter

always @(posedge clk) if (reset) begin
	vram_t_reg <= 0;
	fine_x_scroll <= 0;
	vram_v <= 15'd0;
	fine_x_scroll <= 3'd0;
	write_2006 <= 0;
	w2006b_pipe <= 0;
	w2006b_reg <= 0;

end else begin

	if (pclk0) begin
		write_2006 <= w2006b_pipe;
		copy_vscroll[0] <= h_eq_279_to_303 && v_eq_261 && rendering_enabled;
		copy_vscroll[1] <= copy_vscroll[0];
	end

	// Copies from T to V are delayed by 1 pclk1 and then 1 pclk0 cycle after the second 2006 write
	if (pclk1) begin
		w2006b_pipe <= (!w2006b && w2006b_reg);
		if (write_2006) begin
			w2006b_reg <= 0;
			w2006b_pipe <= 0;
		end

		copy_hscroll <= {copy_hscroll[1:0], h_eq_255r};

		// Horizontal copy at cycle 257 and rendering OR if delayed 2006 write
		if (copy_hscroll[0] || write_2006)
			{vram_v[10], vram_v[4:0]} <= {vram_t[10], vram_t[4:0]};

		// Vertical copy at Cycles 280 to 304 and rendering OR delayed 2006 write
		if (copy_vscroll[0] || write_2006)
			{vram_v[14:11], vram_v[9:5]} <= {vram_t[14:11], vram_t[9:5]};

		// Increment course X scroll from (cycle 0-255 or 320-335) and cycle[2:0] == 7
		if (load_hscroll_next[0] || (trigger_2007 && is_rendering)) begin
			vram_v[4:0] <= (vram_v[4:0] + 1'd1) & vram_t_mask[4:0];
			vram_v[10] <= (vram_v[10] ^ &vram_v[4:0]) & vram_t_mask[10];
		end

		// Vertical Increment at 256 and rendering
		if (load_vscroll_next[0] || (trigger_2007 && is_rendering)) begin
			vram_v[14:12] <= (vram_v[14:12] + 1'd1) & vram_t_mask[14:12];
			vram_v[9:5] <= vram_v[9:5] & vram_t_mask[9:5];
			vram_v[11] <= vram_v[11] & vram_t_mask[11];
			if (vram_v[14:12] == 7) begin
				if (vram_v[9:5] == 29) begin
					vram_v[9:5] <= 0;
					vram_v[11] <= ~vram_v[11] & vram_t_mask[11];
				end else begin
					vram_v[9:5] <= (vram_v[9:5] + 1'd1) & vram_t_mask[9:5];
				end
			end
		end

		if (~is_rendering && trigger_2007)
			vram_v <= vram_v + (ppu_incr ? 15'd32 : 15'd1);
	end

	if (w2000) begin
		vram_t_reg[10] <= din[0];
		vram_t_reg[11] <= din[1];
	end else if (w2005a) begin
		vram_t_reg[4:0] <= din[7:3];
		fine_x_scroll <= din[2:0];
	end else if (w2005b) begin
		vram_t_reg[9:5] <= din[7:3];
		vram_t_reg[14:12] <= din[2:0];
	end else if (w2006a) begin
		vram_t_reg[13:8] <= din[5:0];
		vram_t_reg[14] <= 0;
	end else if (w2006b) begin
		vram_t_reg[7:0] <= din;
		// 2006_write trigger should occur on the next pckl0 after the first pclk1 that occurs after the
		// w2006b signal goes high.
		w2006b_reg <= w2006b;
	end
end

endmodule

// 8 of these exist, they are used to output sprites.
module Sprite(
	input clk,
	input ce,
	input enable,
	input [3:0] load,
	input [26:0] load_in,
	output [26:0] load_out,
	output [4:0] bits // Low 4 bits = pixel, high bit = prio
);

reg [1:0] upper_color; // Upper 2 bits of color
reg [7:0] x_coord;     // X coordinate where we want things
reg [7:0] pix1, pix2;  // Shift registers, output when x_coord == 0
reg aprio;             // Current prio
wire active = (x_coord == 0);

always @(posedge clk) if (ce) begin
	if (enable) begin
		if (!active) begin
			// Decrease until x_coord is zero.
			x_coord <= x_coord - 8'h01;
		end else begin
			pix1 <= pix1 >> 1;
			pix2 <= pix2 >> 1;
		end
	end
	if (load[3]) pix1 <= load_in[26:19];
	if (load[2]) pix2 <= load_in[18:11];
	if (load[1]) x_coord <= load_in[10:3];
	if (load[0]) {upper_color, aprio} <= load_in[2:0];
end
assign bits = {aprio, upper_color, active && pix2[0], active && pix1[0]};
assign load_out = {pix1, pix2, x_coord, upper_color, aprio};

endmodule  // SpriteGen

// This contains all sprites. Will return the pixel value of the highest prioritized sprite.
// When load is set, and clocked, load_in is loaded into sprite 15 and all others are shifted down.
// Sprite 0 has highest prio.
module SpriteSet(
	input clk,
	input ce,               // Input clock
	input enable,           // Enable pixel generation
	input [3:0] load,       // Which parts of the state to load/shift.
	input [3:0] load_ex,    // Which parts of the state to load/shift for extra sprites.
	input [26:0] load_in,   // State to load with
	input [26:0] load_in_ex,// Extra spirtes
	output [4:0] bits,      // Output bits
	output is_sprite0,       // Set to true if sprite #0 was output
	input extra_sprites
);

wire [26:0] load_out7, load_out6, load_out5, load_out4, load_out3, load_out2, load_out1, load_out0,
	load_out15, load_out14, load_out13, load_out12, load_out11, load_out10, load_out9, load_out8;
wire [4:0] bits7, bits6, bits5, bits4, bits3, bits2, bits1, bits0,
	bits15, bits14, bits13, bits12, bits11, bits10, bits9, bits8;

`ifdef EXTRA_SPRITES
// Extra sprites
Sprite sprite15(clk, ce, enable, load_ex, load_in_ex, load_out15, bits15);
Sprite sprite14(clk, ce, enable, load_ex, load_out15, load_out14, bits14);
Sprite sprite13(clk, ce, enable, load_ex, load_out14, load_out13, bits13);
Sprite sprite12(clk, ce, enable, load_ex, load_out13, load_out12, bits12);
Sprite sprite11(clk, ce, enable, load_ex, load_out12, load_out11, bits11);
Sprite sprite10(clk, ce, enable, load_ex, load_out11, load_out10, bits10);
Sprite sprite9( clk, ce, enable, load_ex, load_out10, load_out9,  bits9);
Sprite sprite8( clk, ce, enable, load_ex, load_out9,  load_out8,  bits8);
`endif

// Basic Sprites
Sprite sprite7( clk, ce, enable, load, load_in,    load_out7,  bits7);
Sprite sprite6( clk, ce, enable, load, load_out7,  load_out6,  bits6);
Sprite sprite5( clk, ce, enable, load, load_out6,  load_out5,  bits5);
Sprite sprite4( clk, ce, enable, load, load_out5,  load_out4,  bits4);
Sprite sprite3( clk, ce, enable, load, load_out4,  load_out3,  bits3);
Sprite sprite2( clk, ce, enable, load, load_out3,  load_out2,  bits2);
Sprite sprite1( clk, ce, enable, load, load_out2,  load_out1,  bits1);
Sprite sprite0( clk, ce, enable, load, load_out1,  load_out0,  bits0);

// Determine which sprite is visible on this pixel.
assign bits = enable ? bits_orig : 5'd0;
wire [4:0] bits_orig =
	bits0[1:0]  != 0 ? bits0 :
	bits1[1:0]  != 0 ? bits1 :
	bits2[1:0]  != 0 ? bits2 :
	bits3[1:0]  != 0 ? bits3 :
	bits4[1:0]  != 0 ? bits4 :
	bits5[1:0]  != 0 ? bits5 :
	bits6[1:0]  != 0 ? bits6 :
	bits7[1:0]  != 0 || ~extra_sprites ? bits7 :
`ifdef EXTRA_SPRITES
	bits_ex;

wire [4:0] bits_ex =
	bits8[1:0]  != 0 ? bits8 :
	bits9[1:0]  != 0 ? bits9 :
	bits10[1:0] != 0 ? bits10 :
	bits11[1:0] != 0 ? bits11 :
	bits12[1:0] != 0 ? bits12 :
	bits13[1:0] != 0 ? bits13 :
	bits14[1:0] != 0 ? bits14 :
	bits15;
`else
	bits7;
`endif

assign is_sprite0 = enable && bits0[1:0] != 0;

endmodule  // SpriteSet


// module SpriteRam(
// 	input logic clk,
// 	input logic rendering,
// 	input logic in_visible_frame_r,
// 	input logic write_cycle,
// 	input logic [7:0] spr_addr,
// 	input logic [4:0] spr_ptr,
// 	output logic [4:0] row_part,
// 	output logic [2:0] col_part
// );

// // dpram #(.widthad_a(8), .width_a(8)) OAM_ram2 //256 * 8 bits
// // (
// // 	.clock_a   (clk),
// // 	.address_a (oam_addr_adj),
// // 	.data_a    (oam_data_adj), // byte 3 has no bits 2-4
// // 	.wren_a    ((oam_data_write_sr[2] && ~rendering) || ram_corruption_write),
// // 	.q_a       (oamd),

// // 	.clock_b   (clk),
// // 	.address_b (oam_addr_ex),
// // 	.wren_b    (0),
// // 	.q_b       (oamxd)
// // );

// wire spr_addr_load_next_value = ((delayed_write_2004) || (in_visible_frame_r && hpos_0 && ~h_lt_64r)) && pclk0;
// wire end_of_oam_or_secondary_oam_overflow = h_lt_64r || ~(oam_addr[8] && spr_addr_load_next_value);

// wire spr_eval_copy_sprite = sprite_in_range && ~h_lt_64r && in_visible_frame_r && ~end_of_oam_or_secondary_oam_overflow;
// wire spr_addr_clear_low_bump_high = rendering && ~spr_eval_copy_sprite;

// wire col_8 = ~rendering || (in_visible_frame_r && write_cycle);
// wire [7:0] oam_addr = {col_8 ? spr_ptr : spr_addr[7:3], spr_addr[2:0]};

// wire [7:0] spr2_mask = oam_addr[2] ? 8'b11_11_00_00 : 8'b00_00_11_11;
// wire [7:0] spr1_mask = oam_addr[1] ? 8'b11_00_11_00 : 8'b00_11_00_11;
// wire [7:0] spr0_mask = oam_addr[0] ? 8'b01_01_01_01 : 8'b10_10_10_10;

// wire [7:0] columns = (col_8 ? 8'h00 : (spr0_mask & spr1_mask & spr2_mask));

// wire spr7_mask = oam_addr[7] ? 32'b0101_0101_0101_0101_0101_0101_0101_0101 : 32'b1010_1010_1010_1010_1010_1010_1010_1010;
// wire spr6_mask = oam_addr[6] ? 32'b0011_0011_0011_0011_0011_0011_0011_0011 : 32'b1100_1100_1100_1100_1100_1100_1100_1100;
// wire spr5_mask = oam_addr[5] ? 32'b0000_1111_0000_1111_0000_1111_0000_1111 : 32'b1111_0000_1111_0000_1111_0000_1111_0000;
// wire spr4_mask = oam_addr[4] ? 32'b0000_0000_1111_1111_0000_0000_1111_1111 : 32'b1111_1111_0000_0000_1111_1111_0000_0000;
// wire spr3_mask = oam_addr[3] ? 32'b0000_0000_0000_0000_1111_1111_1111_1111 : 32'b1111_1111_1111_1111_0000_0000_0000_0000;

// // Row is always unselected during pclk0
// wire [31:0] rows = (spr7_mask & spr6_mask & spr5_mask & spr4_mask & spr3_mask);

// generate
// 	genvar xi;

// 	always_comb begin : addrgen
// 		col_part = 0;
// 		row_part = 0;
// 		for (xi = 0; xi < 32; xi++)
// 			if (rows[xi[4:0]]) row_part = xi[4:0];
// 		for (xi = 0; xi < 7; xi++)
// 			if (columns[xi[2:0]]) col_part = xi[2:0];
// 	end
// endgenerate

// endmodule


// module OAMram (
// 	input clk,
// 	input reset,
// 	input pclk0,
// 	input pclk1,
// 	input sprite_addr,
// 	input sprite_ptr
	
// );

// endmodule OAMram

// module OAMEval2 (
// 	input  logic        clk,
// 	input  logic        reset,
// 	input  logic        pclk0,
// 	input  logic        pclk1,
// 	input  logic        h_lt_64r,
// 	input  logic        h_eq_65r,
// 	input  logic        h_lt_256r,
// 	input  logic        h_eq_256_to_319r,
// 	input  logic        h_eq_63_255_or_339_r,
// 	input  logic        in_visible_frame_r,
// 	input  logic        hpos_0,
// 	input  logic        rendering,
// 	input  logic        v_eq_261,        // Is the pre-render scanline
// 	input  logic        spr_size,
// 	input  logic  [8:0] vpos
// 	input  logic        w2003,       // Load oam with specified value, when writing to NES $2003.
// 	input  logic        w2004,       // Load oam_ptr with specified value, when writing to NES $2004.
// 	input  logic  [7:0] din,              // New value for oam or oam_ptr
// 	output logic        spr_overflow,         // Set to true if we had more than 8 objects on a scan line.
// 	output logic  [7:0] oam_bus,              // Current value on the OAM bus, returned to NES through $2004.
// 	output logic [3:0][7:0] oam_bus_ex,           // Load out for extra sprites
// 	output logic        masked_sprites,       // If the game is trying to mask extra sprites
// );

// logic [8:0] sprite_addr; // Pointer to OAM columns 0-7
// logic [5:0] sprite_ptr;  // Pointer to OAM column 8, aka "temp"



// endmodule OAMEval2


module OAMEval(
	input  logic        clk,
	input  logic        pclk0,
	input  logic        pclk1,
	input  logic        h_lt_64r,
	input  logic        h_eq_65r,
	input  logic        h_lt_256r,
	input  logic        h_eq_256_to_319r,
	input  logic        h_eq_63_255_or_339_r,
	input  logic        in_visible_frame_r,
	input  logic        hpos_0,
	input  logic        reset,
	input  logic        rendering,            // Set to 1 if evaluations are enabled
	input  logic        obj_size,             // Set to 1 if objects are 16 pixels.
	input  logic  [8:0] scanline,             // Current scan line (compared against Y)
	input  logic  [8:0] hpos,                 // Current cycle.
	input  logic        oam_addr_write,       // Load oam with specified value, when writing to NES $2003.
	input  logic        oam_data_write,       // Load oam_ptr with specified value, when writing to NES $2004.
	input  logic        oam_data_read,        // read
	input  logic  [7:0] oam_din,              // New value for oam or oam_ptr
	input  logic        v_eq_261,        // Is the pre-render scanline
	input  logic        end_of_line,          // Last pixel of the line
	input  logic        PAL,
	output logic        spr_overflow,         // Set to true if we had more than 8 objects on a scan line.
	output logic        sprite0,              // True if sprite#0 is included on the scan line currently being painted.
	output logic  [7:0] oam_bus,              // Current value on the OAM bus, returned to NES through $2004.
	output logic  [7:0] oam_read_bus,
	output logic [3:0][7:0] oam_bus_ex,           // Load out for extra sprites
	output logic        masked_sprites,       // If the game is trying to mask extra sprites
	output logic        sprite_load
);

// https://wiki.nesdev.com/w/index.php/PPU_sprite_evaluation

logic oam_wr;
logic [7:0] oamd;
logic [7:0] oamxd;
assign sprite_load = (oam_state == STATE_FETCH);
assign oam_bus = rendering ? oam_data : 8'hFF;

enum logic [2:0] {
	STATE_CLEAR   = 3'd1,
	STATE_EVAL    = 3'd2,
	STATE_FETCH   = 3'd3,
	STATE_REFRESH = 3'd4
} oam_state;

reg [7:0] oam_addr;        // OAM Address Register 2003
reg [2:0] oam_temp_slot;   // Pointer to oam_temp;
reg [7:0] oam_data;        // OAM Data Register 2004
reg oam_temp_wren;         // Write enable for OAM temp, disabled if full
logic [7:0] oam_addr_ex;     // OAM pointer for use with extra sprites
logic [3:0] oam_temp_slot_ex;

// Extra Registers
`ifdef EXTRA_SPRITES
reg [1:0] m_ex;
reg [7:0] oam_ex_data;
reg [2:0] spr_counter;     // Count sprites
`endif

reg [6:0] feed_cnt;

reg sprite0_curr;
logic [4:0] repeat_count;

logic [7:0] oam_addr_adj;
logic ram_corruption_phase;
logic ram_corruption_write;
logic [7:0] oam_data_adj;
logic [7:0] oamtd, oamxtd;
logic [7:0] ram_corruption_data;
logic [7:0] oam_addr_next;

logic [7:0] sprite_data_ex[4] = '{8'hFF, 8'hFF, 8'hFF, 8'hFF};
logic [7:0] sprite_compare[4] = '{8'hFF, 8'hFF, 8'hFF, 8'hFF};

assign oam_addr_next = oam_addr + 1'd1;
assign oam_read_bus = oam_data;
// If OAMADDR is not less than eight when rendering starts, the eight bytes starting at OAMADDR &
// 0xF8 are copied to the first eight bytes of OAM

wire [8:0] vpos = scanline;
wire [8:0] vpos_minus_spr = vpos - oam_data;
wire sprite_in_range = (vpos[7] || ~oam_data[7]) && ~|vpos_minus_spr[7:4] && (~vpos[3] || obj_size);
// wire spr_addr_load_next_value = ((delayed_write_2004) || (in_visible_frame_r && hpos_0 && ~h_lt_64r)) && pclk0;
// //wire end_of_oam_or_secondary_oam_overflow = h_lt_64r || ~(oam_addr[8] && spr_addr_load_next_value);
wire spr_eval_copy_sprite = sprite_in_range && ~h_lt_64r && in_visible_frame_r && ~overflow;//end_of_oam_or_secondary_oam_overflow;

assign ram_corruption_phase = ~|hpos[8:4] && v_eq_261 && rendering && oam_addr > 8 && ~PAL;

assign oam_addr_adj = ram_corruption_phase ? (~write_cycle ? {oam_addr[7:3], hpos[3:1]} : {5'd0, hpos[3:1]}) : oam_addr;
assign ram_corruption_write = ram_corruption_phase && write_cycle;
assign oam_data_adj = ram_corruption_phase ? ram_corruption_data : (oam_addr[1:0] == 2'b10) ? {oam_data_latch[7:5], 3'b000, oam_din[1:0]} : oam_data_latch;

dpram #(.widthad_a(8), .width_a(8)) OAM_ram //256 * 8 bits
(
	.clock_a   (clk),
	.address_a (oam_addr_adj),
	.data_a    (oam_data_adj), // byte 3 has no bits 2-4
	.wren_a    ((oam_data_write_sr[2] && ~rendering) || ram_corruption_write),
	.q_a       (oamd),

	.clock_b   (clk),
	.address_b (oam_addr_ex),
	.wren_b    (0),
	.q_b       (oamxd)
);

logic [6:0] oam_temp_full_addr;
logic [6:0] oam_temp_ex_full_addr;
logic [7:0] oam_ex_db;

logic oam_temp_wren_adj, oam_temp_ex_wren;
reg n_ovr, ex_ovr;
logic write_cycle;
assign write_cycle = hpos[0];

// wire [7:0] spr2_mask = oam_addr[2] ? 8'b11_11_00_00 : 8'b00_00_11_11;
// wire [7:0] spr1_mask = oam_addr[1] ? 8'b11_00_11_00 : 8'b00_11_00_11;
// wire [7:0] spr0_mask = oam_addr[0] ? 8'b01_01_01_01 : 8'b10_10_10_10;

// wire col_8 = ~rendering || (in_visible_frame_r && ~write_cycle);
// wire [7:0] columns = (col_8 ? 8'h00 : (spr0_mask & spr1_mask & spr2_mask));

// wire spr7_mask = oam_addr[7] ? 32'b0101_0101_0101_0101_0101_0101_0101_0101 : 32'b1010_1010_1010_1010_1010_1010_1010_1010;
// wire spr6_mask = oam_addr[6] ? 32'b0011_0011_0011_0011_0011_0011_0011_0011 : 32'b1100_1100_1100_1100_1100_1100_1100_1100;
// wire spr5_mask = oam_addr[5] ? 32'b0000_1111_0000_1111_0000_1111_0000_1111 : 32'b1111_0000_1111_0000_1111_0000_1111_0000;
// wire spr4_mask = oam_addr[4] ? 32'b0000_0000_1111_1111_0000_0000_1111_1111 : 32'b1111_1111_0000_0000_1111_1111_0000_0000;
// wire spr3_mask = oam_addr[3] ? 32'b0000_0000_0000_0000_1111_1111_1111_1111 : 32'b1111_1111_1111_1111_0000_0000_0000_0000;

// // Row is always unselected during pclk0
// wire [31:0] rows = (spr7_mask & spr6_mask & spr5_mask & spr4_mask & spr3_mask);

// wire inc_temp_ptr = ((h_lt_64r || spr_eval_copy_sprite) && ~hpos[0]) || (h_eq_256_to_319r && ~hpos[2]);


always_comb begin
	if (h_lt_64r)
		oam_state = STATE_CLEAR;   // 64 cycles
	else if (h_lt_256r)
		oam_state = STATE_EVAL;    // 192 cycles
	else if (h_eq_256_to_319r)
		oam_state = STATE_FETCH;   // 64 cycles
	else
		oam_state = STATE_REFRESH; // 19+1 cycles

	oam_temp_full_addr = 6'd0;
	oam_temp_ex_full_addr = 6'b100000;
	oam_db = rendering ? oamtd : oamd;
	oam_ex_db = rendering ? oamxtd : oamxd;
	oam_temp_wren_adj = 0;
	oam_temp_ex_wren = 0;

	case (oam_state)
		STATE_CLEAR: begin
			oam_temp_full_addr = {1'b0, hpos[5:1]};
			oam_temp_ex_full_addr = {1'b1, hpos[5:1]};
			if (in_visible_frame_r) begin
				oam_db = 8'hFF;
				oam_ex_db = 8'hFF;
				oam_temp_wren_adj = write_cycle;
				oam_temp_ex_wren = write_cycle;
			end
		end

		STATE_EVAL: begin
			oam_temp_full_addr = {1'b0, oam_temp_slot, (n_ovr || ~oam_temp_wren) ? 2'b00 : oam_addr[1:0]};
			oam_temp_ex_full_addr = {1'b1, oam_temp_slot_ex[2:0], oam_addr_ex[1:0]};

			if (in_visible_frame_r) begin
				oam_db = ~write_cycle ? oamd : oam_temp_wren ? oamd : oamtd;
				oam_ex_db = oamxd;
				`ifdef EXTRA_SPRITES
				oam_temp_ex_wren = (~ex_ovr && write_cycle);
				`endif
				oam_temp_wren_adj = (oam_temp_wren && write_cycle);
			end
		end

		STATE_FETCH: begin
			oam_temp_full_addr = {1'b0, feed_cnt[5:3], feed_cnt[2:0] > 3 ? 2'b11 : feed_cnt[1:0]};
			oam_temp_ex_full_addr = {1'b1, feed_cnt[5:3] + 1'd1, feed_cnt[1:0]};
		end

		default: begin
			oam_ex_db = rendering ? oamxtd : oamxd;
			oam_db = rendering ? oamtd : oamd;
		end
	endcase
end

dpram #(.widthad_a(6), .width_a(8)) OAM_temp_ram //64 * 8 bits
(
	.clock_a   (clk),
	.address_a (oam_temp_full_addr),
	.data_a    (oam_state == STATE_EVAL ? oam_bus : 8'hFF),
	.wren_a    (oam_temp_wren_adj),
	.q_a       (oamtd),

	.clock_b   (clk),
	.address_b (oam_temp_ex_full_addr),
	.data_b    (oam_state == STATE_EVAL ? oam_ex_data : 8'hFF),
	.wren_b    (oam_temp_ex_wren),
	.q_b       (oamxtd)
);

logic [7:0] oam_db;
logic [7:0] dram_glitch;
logic [7:0] oam_data_delay;
logic overflow;

always_ff @(posedge clk) begin :oam_eval
reg [1:0] eval_counter;

if (reset) begin
	oam_temp_slot <= 0;
	oam_temp_wren <= 1;
	n_ovr <= 0;
	repeat_count <= 0;
	sprite0 <= 0;
	sprite0_curr <= 0;
	feed_cnt <= 0;
	overflow <= 0;
	eval_counter <= 0;
	ram_corruption_data <= 0;
	`ifdef EXTRA_SPRITES
	oam_bus_ex <= 32'hFFFFFFFF;
	sprite_data_ex <= '{8'hFF, 8'hFF, 8'hFF, 8'hFF};
	sprite_compare <= '{8'hFF, 8'hFF, 8'hFF, 8'hFF};
	spr_counter <= 0;
	oam_addr_ex <= 0;
	ex_ovr <= 0;
	oam_temp_slot_ex <= 0;
	`endif

end else if (pclk1) begin
	// I believe technically oam_data represents the ppu's internal data bus and should be assign to
	// open bus if not driven here, but for now, no behavior relies on this so we can just keep it
	// simple.
//	oam_write <= in_visible_frame_r && ~overflow && end_of_oam_or_secondary_oam_overflow && write_cycle;
	if (rendering || oam_data_read) begin
		oam_data <= oam_db;
		oam_ex_data <= oam_ex_db;
	end

	if (end_of_line) begin
		sprite0 <= sprite0_curr;
		sprite0_curr <= 0; // set if the cycle is 65 and the evaluator decides to copy (copy_sprite_sec_oam)
		oam_temp_slot <= 0;
		oam_temp_wren <= 1;
		n_ovr <= 0;
		repeat_count <= 0;
		feed_cnt <= 0;
		eval_counter <= 0;
		`ifdef EXTRA_SPRITES
		oam_bus_ex <= 32'hFFFFFFFF;
		sprite_data_ex <= '{8'hFF, 8'hFF, 8'hFF, 8'hFF};
		sprite_compare <= '{8'hFF, 8'hFF, 8'hFF, 8'hFF};
		spr_counter <= 0;
		ex_ovr <= 0;
		oam_temp_slot_ex <= 0;
		oam_addr_ex <= 0;
		masked_sprites <= 0;
		`endif
	end

	if (oam_state == STATE_CLEAR) begin               // Initialization state
		if (~write_cycle)
			ram_corruption_data <= oamd;

		`ifdef EXTRA_SPRITES
		// During init, we hunt for the 8th sprite in OAM, so we know where to start for extra sprites
		if (in_visible_frame_r) begin
			if (~&spr_counter) begin
				oam_addr_ex[7:2] <= oam_addr_ex[7:2] + 1'd1;
				if (scanline[7:0] >= oamxd && scanline[7:0] < oamxd + (obj_size ? 16 : 8))
					spr_counter <= spr_counter + 1'b1;
			end
		end
		`endif
	end

	if (oam_state == STATE_EVAL) begin             // Evaluation State
		if (in_visible_frame_r) begin
			//On odd cycles, data is read from (primary) OAM
			if (write_cycle) begin
				// This phase has exactly enough cycles to evaluate all 64 sprites if 8 are on the current line,
				// so extra sprite evaluation has to be done seperately.
				`ifdef EXTRA_SPRITES
				if (&spr_counter && ~ex_ovr) begin
					if (~|oam_addr_ex[1:0]) begin
						if (scanline[7:0] >= oamxd &&
							scanline[7:0] < oamxd + (obj_size ? 16 : 8)) begin
							if (oam_temp_slot_ex == 0) begin
								oam_bus_ex[oam_addr_ex[1:0]] <= oamxd;
							end
							if (oam_temp_slot_ex < 8) begin
								{ex_ovr, oam_addr_ex} <= oam_addr_ex + 9'd1;
							end
						end else begin
							{ex_ovr, oam_addr_ex} <= oam_addr_ex + 9'd4;
						end

					end else begin
						if (oam_temp_slot_ex == 0) begin
							oam_bus_ex[oam_addr_ex[1:0]] <= oamxd;
						end
						if (&oam_addr_ex[1:0]) oam_temp_slot_ex <= oam_temp_slot_ex + 1'b1;
						{ex_ovr, oam_addr_ex} <= oam_addr_ex + 9'd1;
					end
				end
				`endif

				if (~n_ovr) begin
					if (~|eval_counter) begin // m is 0
						if (scanline[7:0] >= oam_data && scanline[7:0] < oam_data + (obj_size ? 16 : 8)) begin
							if (~oam_temp_wren)
								overflow <= 1;
							else begin
								sprite_compare[oam_addr[1:0]] <= oam_data;
								if (oam_temp_slot && (sprite_compare[oam_addr[1:0]] == oam_data))
									repeat_count <= repeat_count + 4'd1;
							end
							if (~|oam_addr[7:2])
								sprite0_curr <= 1'b1;
							eval_counter <= eval_counter + 2'd1;
							{n_ovr, oam_addr} <= {1'b0, oam_addr} + 9'd1; // is good, copy
						end else begin
							if (~oam_temp_wren) begin  // Sprite overflow bug emulation
								{n_ovr, oam_addr[7:2]} <= oam_addr[7:2] + 7'd1;
								oam_addr[1:0] <= oam_addr[1:0] + 2'd1;
							end else begin                              // skip to next sprite
								{n_ovr, oam_addr} <= oam_addr + 9'd4;
							end
						end
					end else begin
						eval_counter <= eval_counter + 2'd1;
						{n_ovr, oam_addr} <= {1'b0, oam_addr} + 9'd1;
						if (oam_temp_wren) begin
							sprite_compare[oam_addr[1:0]] <= oam_data;
							if (|oam_temp_slot && ~&oam_addr[1:0] && (sprite_compare[oam_addr[1:0]] == oam_data))
								repeat_count <= repeat_count + 4'd1;

						end
						if (&eval_counter) begin // end of copy
							if (oam_temp_wren) begin
								oam_temp_slot <= oam_temp_slot + 1'b1;
							end else begin
								n_ovr <= 1;
							end

							if (oam_temp_slot == 7)
								oam_temp_wren <= 0;
						end
					end
				end else begin
					oam_addr <= {oam_addr[7:2] + 1'd1, 2'b00};
				end
			end

		end
	end

	if (oam_state == STATE_FETCH) begin
		// OAMADDR is set to 0 during each of ticks 257-320 (the sprite tile loading interval) of the pre-render
		// and visible scanlines.
		`ifdef EXTRA_SPRITES
		if (repeat_count >= 21)
			masked_sprites <= 1;
		`endif

		feed_cnt <= feed_cnt + 1'd1;

		if (rendering) begin
			oam_addr <= 0;
			sprite_data_ex[feed_cnt[1:0]] <= oamxtd;

			if (&feed_cnt[2:0]) begin
				oam_bus_ex <= {sprite_data_ex[3], sprite_data_ex[2], sprite_data_ex[1], sprite_data_ex[0]};
			end
		end
	end

end

// Writes to OAMDATA during rendering (on the pre-render line and the visible lines 0-239,
// provided either sprite or background rendering is enabled) do not modify values in OAM,
// but do perform a glitchy increment of OAMADDR, bumping only the high 6 bits (i.e., it bumps
// the [n] value in PPU sprite evaluation - it's plausible that it could bump the low bits instead
// depending on the current status of sprite evaluation). This extends to DMA transfers via OAMDMA,
// since that uses writes to $2004.

// Appears to have a delay of exactly four PCLK0 cycles from the falling edge of the signal.

if (pclk0) begin
	if (write_cycle)
		spr_overflow <= overflow;

	oam_data_write_sr <= {oam_data_write_sr[1:0], oam_data_write};
	if (oam_data_write_sr[2] && ~rendering) begin
		oam_addr <= oam_addr_next;
	end else if (oam_data_write_sr[2]) begin
		oam_addr[7:2] <= oam_addr_next[7:2];
	end
	if (oam_data_write) begin
		oam_data_write_sr <= 3'b001;
		oam_data_latch <= oam_din;
	end
end

if (oam_addr_write) begin
	oam_addr <= oam_din;
end

if (v_eq_261) begin
	overflow <= 0;
	spr_overflow <= 0;
end

end // End Always

logic [7:0] oam_data_latch;
logic [2:0] oam_data_write_sr; 

endmodule


// Generates addresses in VRAM where we'll fetch sprite graphics from,
// and populates load, load_in so the SpriteGen can be loaded.
module SpriteAddressGen(
	input         clk,
	input         ce,
	input         enabled,          // If unset, |load| will be all zeros.
	input         obj_size,         // 0: Sprite Height 8, 1: Sprite Height 16.
	input         obj_patt,         // Object pattern table selection
	input   [8:0] scanline,
	input latch_nametable,
	input latch_attrtable,
	input latch_pattern1,
	input latch_pattern2,
	input load_pattern2,
	input   [7:0] temp,       // Input temp data from SpriteTemp. #0 = Y Coord, #1 = Tile, #2 = Attribs, #3 = X Coord
	input   [7:0] vram_data,  // Byte of VRAM in the specified address
	output [12:0] vram_addr,// Low bits of address in VRAM that we'd like to read.
	output  [3:0] load,      // Which subset of load_in that is now valid, will be loaded into SpritesGen.
	output [26:0] load_in  // Bits to load into SpritesGen.
);

logic [7:0] temp_tile, temp_tile_l;    // Holds the tile that we will get
logic [3:0] temp_y, temp_y_l;       // Holds the Y coord (will be swapped based on FlipY).
logic flip_x, flip_y, flip_x_l, flip_y_l;     // If incoming bitmap data needs to be flipped in the X or Y direction.
logic dummy_sprite, dummy_sprite_l; // Set if attrib indicates the sprite is invalid.

wire load_y =    (load_cnt == 0);            // 256 00 N 257 01
wire load_tile = (load_cnt == 1);            // 257 01   258 10 N
wire load_attr = (load_cnt == 2) && enabled; // 258 10 N 259 11
wire load_x =    (load_cnt == 3) && enabled; // 259 11   260 00 S
                                             // 260 00 S 262 01
wire load_pix1 = latch_pattern1 && enabled;    // 261 01   262 10 S
                                             // 262 10 S 263 11
wire load_pix2 = latch_pattern2 && enabled;    // 263 11   264 01 N
logic [2:0] load_cnt;

// Flip incoming vram data based on flipx. Zero out the sprite if it's invalid. The bits are already flipped once.
wire [7:0] vram_f =
	dummy_sprite ? 8'd0 :
	!flip_x ? {vram_data[0], vram_data[1], vram_data[2], vram_data[3], vram_data[4], vram_data[5], vram_data[6], vram_data[7]} :
	vram_data;

wire [3:0] y_f = temp_y ^ {flip_y, flip_y, flip_y, flip_y};
assign load = {load_pix1, load_pix2, load_x, load_attr};
assign load_in = {vram_f, vram_f, temp, temp[1:0], temp[5]};

// If $2000.5 = 0, the tile index data is used as usual, and $2000.3
// selects the pattern table to use. If $2000.5 = 1, the MSB of the range
// result value become the LSB of the indexed tile, and the LSB of the tile
// index value determines pattern table selection. The lower 3 bits of the
// range result value are always used as the fine vertical offset into the
// selected pattern.

assign temp_y = (load_y) ? scanline_y[3:0] : temp_y_l;
assign temp_tile = (load_tile) ? temp : temp_tile_l;
assign {flip_y, flip_x, dummy_sprite} = (load_attr) ? {temp[7:6], temp[4]} :
	{flip_y_l, flip_x_l, dummy_sprite_l};

assign vram_addr = {obj_size ? temp_tile[0] :
	obj_patt, temp_tile[7:1], obj_size ? y_f[3] : temp_tile[0], load_pattern2, y_f[2:0] };

wire [7:0] scanline_y = scanline[7:0] - temp;

always @(posedge clk) if (ce) begin
	if (enabled)
		load_cnt <= load_cnt + 3'd1;
	else
		load_cnt <= 0;

	if (load_y) temp_y_l <= scanline_y[3:0];
	if (load_tile) temp_tile_l <= temp;
	if (load_attr) {flip_y_l, flip_x_l, dummy_sprite_l} <= {temp[7:6], temp[4]};
end

endmodule  // SpriteAddressGen

`ifdef EXTRA_SPRITES
// Condensed sprite address generator for extra sprites
module SpriteAddressGenEx(
	input clk,
	input ce,
	input enabled,          // If unset, |load| will be all zeros.
	input obj_size,         // 0: Sprite Height 8, 1: Sprite Height 16.
	input obj_patt,         // Object pattern table selection
	input latch_pattern1,
	input latch_pattern2,
	input [7:0] scanline,
	input [31:0] temp,      // Input temp data from SpriteTemp. #0 = Y Coord, #1 = Tile, #2 = Attribs, #3 = X Coord
	input [7:0] vram_data,  // Byte of VRAM in the specified address
	output [12:0] vram_addr,// Low bits of address in VRAM that we'd like to read.
	output [3:0] load,      // Which subset of load_in that is now valid, will be loaded into SpritesGen.
	output [26:0] load_in,  // Bits to load into SpritesGen.
	output use_ex,          // If extra sprite address should be used
	input masked_sprites
);

// We keep an odd structure here to maintain compatibility with the existing sprite modules
// which are constrained by the behavior of the original system.
wire load_y =    (load_cnt == 0);            // 256 00 N 257 01
wire load_tile = (load_cnt == 1);
wire load_attr = (load_cnt == 2) && enabled;
wire load_x =    (load_cnt == 3) && enabled;
wire load_pix1 = latch_pattern1 && enabled;
wire load_pix2 = latch_pattern2 && enabled;

reg [7:0] pix1_latch, pix2_latch;

logic [3:0] temp_y, temp_y_l;       // Holds the Y coord (will be swapped based on FlipY).

wire [7:0] scanline_y = scanline[7:0] - temp[7:0];
wire [7:0] tile   = temp[15:8];
wire [7:0] attr   = temp[23:16];
wire [7:0] temp_x = temp[31:24];

wire flip_x = attr[6];
wire flip_y = attr[7];
wire dummy_sprite = attr[4];
logic [2:0] load_cnt;

assign use_ex = ~dummy_sprite && ~load_cnt[2] && ~masked_sprites;
assign temp_y = (load_y) ? scanline_y[3:0] : temp_y_l;

// Flip incoming vram data based on flipx. Zero out the sprite if it's invalid. The bits are already flipped once.
wire [7:0] vram_f =
	dummy_sprite || masked_sprites ? 8'd0 :
	!flip_x ? {vram_data[0], vram_data[1], vram_data[2], vram_data[3], vram_data[4], vram_data[5], vram_data[6], vram_data[7]} :
	vram_data;

wire [3:0] y_f = temp_y[3:0] ^ {flip_y, flip_y, flip_y, flip_y};
assign load = {load_pix1, load_pix2, load_x, load_attr};
assign load_in = {pix1_latch, pix2_latch, load_temp, load_temp[1:0], load_temp[5]};

logic [7:0] load_temp;
always_comb begin
	load_temp = 8'd0;
	case (load_cnt)
		0: load_temp = temp_y;
		1: load_temp = tile;
		2: load_temp = attr;
		3,4,5,6,7: load_temp = temp_x;
	endcase
end

// If $2000.5 = 0, the tile index data is used as usual, and $2000.3
// selects the pattern table to use. If $2000.5 = 1, the MSB of the range
// result value become the LSB of the indexed tile, and the LSB of the tile
// index value determines pattern table selection. The lower 3 bits of the
// range result value are always used as the fine vertical offset into the
// selected pattern.
assign vram_addr = {obj_size ? tile[0] : obj_patt,
	tile[7:1], obj_size ? y_f[3] : tile[0], load_cnt[1], y_f[2:0] };
always @(posedge clk) if (ce) begin
	if (enabled)
		load_cnt <= load_cnt + 3'd1;
	else
		load_cnt <= 0;

	if (load_y) temp_y_l <= scanline_y[3:0];
	if (load_tile) pix1_latch <= vram_f;
	if (load_x) pix2_latch <= vram_f;
end

endmodule  // SpriteAddressGenEx
`endif

module BgPainter(
	input clk,
	input pclk0,
	input clear,
	input enable,             // Shift registers activated
	input latch_nametable,
	input latch_attrtable,
	input latch_pattern1,
	input latch_pattern2,
	input [2:0] fine_x_scroll,
	input [14:0] vram_v,
	output [7:0] name_table,  // VRAM name table to read next.
	input [7:0] vram_data,
	output [3:0] pixel
);

reg [15:0] playfield_pipe_1;       // Name table pixel pipeline #1
reg [15:0] playfield_pipe_2;       // Name table pixel pipeline #2
reg [8:0]  playfield_pipe_3;       // Attribute table pixel pipe #1
reg [8:0]  playfield_pipe_4;       // Attribute table pixel pipe #2
reg [7:0] current_name_table;      // Holds the current name table byte
reg [1:0] current_attribute_table; // Holds the 2 current attribute table bits
reg [7:0] bg0;                     // Pixel data for last loaded background
wire [7:0] bg1 =  vram_data;

initial begin
	playfield_pipe_1 = 0;
	playfield_pipe_2 = 0;
	playfield_pipe_3 = 0;
	playfield_pipe_4 = 0;
	current_name_table = 0;
	current_attribute_table = 0;
	bg0 = 0;
end

always @(posedge clk) if (pclk0) begin
	if (enable) begin
		if (latch_nametable)
			current_name_table <= vram_data;
		
		if (latch_attrtable) begin
			current_attribute_table <=
				(!vram_v[1] && !vram_v[6]) ? vram_data[1:0] :
				( vram_v[1] && !vram_v[6]) ? vram_data[3:2] :
				(!vram_v[1] &&  vram_v[6]) ? vram_data[5:4] :
				vram_data[7:6];
		end

		if (latch_pattern1)
			bg0 <= vram_data; // Pattern table bitmap #0

		playfield_pipe_1[14:0] <= playfield_pipe_1[15:1];
		playfield_pipe_2[14:0] <= playfield_pipe_2[15:1];
		playfield_pipe_3[7:0] <= playfield_pipe_3[8:1];
		playfield_pipe_4[7:0] <= playfield_pipe_4[8:1];

		if (latch_pattern2) begin
			playfield_pipe_1[15:8] <= {bg0[0], bg0[1], bg0[2], bg0[3], bg0[4], bg0[5], bg0[6], bg0[7]};
			playfield_pipe_2[15:8] <= {bg1[0], bg1[1], bg1[2], bg1[3], bg1[4], bg1[5], bg1[6], bg1[7]};
			playfield_pipe_3[8] <= current_attribute_table[0];
			playfield_pipe_4[8] <= current_attribute_table[1];
		end
	end

	if (clear) begin
		playfield_pipe_1 <= 0;
		playfield_pipe_2 <= 0;
		playfield_pipe_3 <= 0;
		playfield_pipe_4 <= 0;
		current_name_table <= 0;
		current_attribute_table <= 0;
		bg0 <= 0;
	end

end

assign name_table = current_name_table;

wire [3:0] i = {1'b0, fine_x_scroll};

assign pixel = enable ? {playfield_pipe_4[i], playfield_pipe_3[i], playfield_pipe_2[i], playfield_pipe_1[i]} : 4'd0;

endmodule  // BgPainter

module PixelMuxer(
	input  logic [3:0] bg,
	input  logic [3:0] obj,
	input  logic       obj_prio,
	output logic [4:0] out,
	output logic       is_obj
);

wire bg_valid = |bg[1:0];
wire obj_valid = |obj[1:0];

assign is_obj = obj_valid && ~(obj_prio && bg_valid);
assign out = (bg_valid | obj_valid) ? (is_obj ? {1'b1, obj} : {1'b0, bg}) : 5'd0;

endmodule


module PaletteRam
(
	input logic clk,
	input logic ce,
	input logic [4:0] addr,
	input logic [5:0] din,
	input logic write_ce,
	input logic reset,
	output logic [5:0] dout
);

logic [4:0] addr_clipped;
logic [5:0] ram_out;

assign addr_clipped = |addr[1:0] ? addr : {1'b0, addr[3:0]};

logic [5:0] palette[32];
assign palette = '{
	6'h00, 6'h01, 6'h00, 6'h01,
	6'h00, 6'h02, 6'h02, 6'h0D,
	6'h08, 6'h10, 6'h08, 6'h24,
	6'h00, 6'h00, 6'h04, 6'h2C,
	6'h09, 6'h01, 6'h34, 6'h03,
	6'h00, 6'h04, 6'h00, 6'h14,
	6'h08, 6'h3A, 6'h00, 6'h02,
	6'h00, 6'h20, 6'h2C, 6'h08
};

assign dout = reset ? 6'h00 : ram_out;

logic [5:0] clear_addr;
always_ff @(posedge clk) begin
	clear_addr <= clear_addr + 1'd1;
end

spram #(.addr_width(5), .data_width(6)) palette_ram
(
	.clock   (clk),
	.address (reset ? clear_addr : addr_clipped),
	.data    (reset ? palette[clear_addr] : din),
	.enable  (reset | ce),
	.wren    (write_ce | reset),
	.q       (ram_out)
);

endmodule  // PaletteRam

module XYDecoder
(
	input logic clk,
	input logic reset,
	input logic pclk0,
	input logic pclk1,
	input logic [8:0] cycle,
	input logic [8:0] scanline,
	input logic rendering_enabled,
	output logic rendering,
	output logic [8:0] hpos,
	output logic [8:0] vpos,
	output logic [63:0] timing_signals
);

// In the actual chip, almost every one of these is gated by pclk1, so in this implementation
// it will be assigned on pclk0, however, care must be taken in any continuous logic which should be
// +1 whatever timing group the clocked logic is.

assign rendering = rendering_enabled && (vpos < 240 || vpos == 511);

always @(posedge clk) if (pclk0) vpos <= scanline;

assign timing_signals[63:32] = 0;

assign hpos = cycle;
assign timing_signals[H_MOD8_0_OR_1R] = (~cycle[2] && ~cycle[1]) && rendering;
assign timing_signals[H_MOD8_2_OR_3R] = (~cycle[2] &&  cycle[1]) && rendering;
assign timing_signals[H_MOD8_4_OR_5R] = ( cycle[2] && ~cycle[1]) && rendering;
assign timing_signals[H_MOD8_6_OR_7R] = ( cycle[2] &&  cycle[1]) && rendering;
assign timing_signals[H_EQ_256] = cycle == 256;
assign timing_signals[H_EQ_270] = cycle == 270;
assign timing_signals[H_EQ_279] = cycle == 279;
assign timing_signals[H_EQ_304] = cycle == 304;
assign timing_signals[H_EQ_308] = cycle == 308;
assign timing_signals[H_EQ_323] = cycle == 323;
assign timing_signals[H_EQ_328] = cycle == 328;
assign timing_signals[H_LT_64R] = cycle < 64 && rendering;
assign timing_signals[H_LT_256R] = ~cycle[8] && rendering;
assign timing_signals[H_EQ_63R] = cycle == 63 && rendering;
assign timing_signals[H_EQ_65R] = cycle == 65 && rendering;
assign timing_signals[H_EQ_255R] = cycle == 255 && rendering;
assign timing_signals[H_EQ_339R] = cycle == 339 && rendering;
assign timing_signals[H_EQ_0_7_OR_256_263] = (cycle >= 0 && cycle <= 7) || (cycle >= 256 && cycle <= 263);
assign timing_signals[H_EQ_256_TO_319R] = (cycle >= 256 && cycle <= 319) && rendering;
assign timing_signals[H_EQ_270_TO_327] = (cycle >= 270 && cycle <= 327);
assign timing_signals[H_EQ_320_TO_335R] = (cycle >= 320 && cycle <= 335) && rendering;
assign timing_signals[H_EQ_279_TO_303] = (cycle >= 279 && cycle <= 303);
assign timing_signals[IN_VISIBLE_FRAME] = (~cycle[8] && scanline < 240);
assign timing_signals[IN_VISIBLE_FRAME_R] = (~cycle[8] && scanline < 240) && rendering;
assign timing_signals[V_EQ_0] = scanline == 0;
assign timing_signals[V_EQ_240] = scanline == 240;
assign timing_signals[V_EQ_261] = scanline == 511; // We do pre-render as 511 aka -1
assign timing_signals[V_EQ_241] = scanline == 241;
assign timing_signals[V_EQ_244] = scanline == 244;
assign timing_signals[V_EQ_247] = scanline == 247;
assign timing_signals[V_EQ_255] = scanline == 255;
assign timing_signals[V_EQ_261_I] = scanline == 511;

endmodule


module debug_dots(
	input enable,
	input [5:0] color,
	input custom1,
	input custom2,
	input w2000,
	input w2001,
	input r2002,
	input w2003,
	input r2004,
	input w2004,
	input w2005,
	input w2006,
	input r2007,
	input w2007,
	output [5:0] new_color
);

always_comb begin
	new_color = color;
	if (enable) begin
		if (custom1)
			new_color = 6'h31; // Light Blue
		else if (custom2)
			new_color = 6'h34; // Light Purple
		else if (w2000)
			new_color = 6'h16; // Red
		else if (w2001)
			new_color = 6'h03; // Violet
		else if (r2002)
			new_color = 6'h17; // Orange
		else if (w2003)
			new_color = 6'h15; // Pink
		else if (r2004)
			new_color = 6'h09; // Dark Green
		else if (w2004)
			new_color = 6'h28; // Yellow
		else if (w2005)
			new_color = 6'h1A; // Green
		else if (w2006)
			new_color = 6'h12; // Dim Blue
		else if (r2007)
			new_color = 6'h21; // Medium Blue
		else if (w2007)
			new_color = 6'h06; // Dark Orange
	end
end

endmodule


//********************************************************************************//
//*******************************  PPU  ******************************************//
//********************************************************************************//


module PPU(
	// Physical pins
	input  logic        clk,              // CORE clock
	input  logic        CS_n,             // Chip Select, defined as phi2 is high && address is in the PPU range
	input  logic        RESET,            // input clock  21.48 MHz / 4. 1 clock cycle = 1 pixel
	input  logic  [7:0] DIN,              // input data from cpu bus
	input  logic  [7:0] VRAM_DIN,         // ppu data, not conflated with ppu_address in our model
	input  logic  [2:0] AIN,              // input address from CPU
	input  logic        RW,               // Read = high, write = low
	input  logic  [3:0] EXT_IN,           // EXT pins input
	output logic        INT_n,            // one while inside vblank
	output logic        VRAM_R,           // read from vram active
	output logic        VRAM_W,           // write to vram active
	output logic [13:0] VRAM_AB,          // vram address, not conflated with data in our model
	output logic  [7:0] DOUT,             // output data to CPU bus
	output logic  [7:0] VRAM_DOUT,        // ppu data, not conflated with ppu_address in our model
	output logic  [3:0] EXT_OUT,          // EXT output
	output logic        ALE,              // Address Latch Enable, used to deal with the shared ppu_ab and ppu_db

	// Abstract pins
	input  logic        EXTRA_SPRITES,
	input  logic  [1:0] MASK,
	input  logic        CE,               // Clock enable to reduce FPGA timing stress
	input  logic        CE2,              // represents pclk1
	input  logic  [1:0] SYS_TYPE,         // System type. 0 = NTSC 1 = PAL 2 = Dendy 3 = Vs.
	input  logic        NES_RESET,        // Indicates reset should be held for 1 frame like US NES
	input  logic        DEBUG_DOTS,       // enable debug dot drawing
	output logic        VRAM_R_EX,        // use extra sprite address
	output logic [13:0] VRAM_A_EX,        // vram address for extra sprites
	output logic  [5:0] COLOR,            // output color value, one pixel outputted every clock, replaces composite pin
	output logic        HBLANK,
	output logic        HSYNC,
	output logic        VBLANK,
	output logic        VSYNC,
	output logic  [2:0] EMPHASIS,
	output logic  [8:0] SCANLINE,
	output logic  [8:0] CYCLE,
	output logic        SHORT_FRAME,
	//savestates
	input [63:0]  SaveStateBus_Din,
	input [ 9:0]  SaveStateBus_Adr,
	input         SaveStateBus_wren,
	input         SaveStateBus_rst,
	input         SaveStateBus_load,
	output [63:0] SaveStateBus_Dout,
	
	input  [7:0]  Savestate_OAMAddr,     
	input         Savestate_OAMRdEn,    
	input         Savestate_OAMWrEn,    
	input  [7:0]  Savestate_OAMWriteData,
	output [7:0]  Savestate_OAMReadData
	// Missing pins
	// VID - Represented as Color and Emphasis outputs
);


// Persistant State
logic [7:0] delay_2001, latch_2001;
logic [7:0] delay_2000, latch_2000;
logic HVTog;
logic sprite0_hit_bg;
logic [7:0] vram_latch;
logic hv_latch;
logic [5:0] color_pipe[4];
logic read_old;
logic write_old;
logic [7:0] latched_dout;
logic refresh_high, refresh_low;
logic [23:0] decay_high;
logic [23:0] decay_low;
logic vbl_flag;
logic [7:0] w2007_buf;
logic [14:0] w2007_abuf;

// Timing signals
logic [3:0][8:0] hpos;
logic [3:0][63:0] t;
logic [8:0] vpos;
logic [13:0] vram_a;
logic is_rendering_d;
logic [4:0] w2007_ended;
logic w2007_reg;
logic [4:0] r2007_ended;
logic r2007_reg;
wire [63:0] t1, t2, t3, t4;
logic w2007_enabled_d, r2007_enabled_d;

// Wires
wire obj0_on_line; // True if sprite#0 is included on the current line
wire sprite_overflow;
wire [5:0] color3;
wire load_sprite;
wire [7:0] oam_read_bus;
wire [12:0] sprite_vram_addr_ex;
wire [3:0] spriteset_load_ex;
wire [26:0] spriteset_load_in_ex;
wire use_ex;
wire [7:0] bg_name_table;
wire [3:0] bg_pixel_noblank;
wire [31:0] oam_bus_ex;
wire masked_sprites;
wire [7:0] oam_bus;
wire [4:0] pixel;
wire held_reset;
wire use_extra_sprites;
wire pclk0, pclk1;
wire end_of_line;
wire entering_vblank;
wire is_rendering;
wire [14:0] vram_v;
wire [2:0] fine_x_scroll;
wire [4:0] obj_pixel_noblank;
wire [12:0] sprite_vram_addr;
wire is_obj0_pixel;            // True if obj_pixel originates from sprite0.
wire [3:0] spriteset_load;     // Which subset of the |load_in| to load into SpriteSet
wire [26:0] spriteset_load_in; // Bits to load into SpriteSet

// Address decoder signals
wire w2000, w2001, r2002, w2003, r2004, w2004, w2005, w2006, w2007, r2007;
wire w2006a = w2006 && ~HVTog;
wire w2006b = w2006 && HVTog;
wire w2005a = w2005 && ~HVTog;
wire w2005b = w2005 && HVTog;
wire w2007_delayed;
wire w2007_enabled = w2007_ended[3] && ~w2007_ended[1]; // Writes appear to last two full PPU cycles, so we use the second of the two
wire r2007_enabled = r2007_ended[3] && ~r2007_ended[1];

// Reads and Writes
wire read = RW & ~CS_n;
wire write = ~RW & ~CS_n;
wire write_ce = write & ~write_old;
wire read_ce = read & ~read_old;

// Palette and VRAM
wire is_pal_address = &vram_a[13:8] & ~is_rendering_d;
wire palette_write = w2007_enabled_d && is_pal_address;
wire [4:0] pram_addr = t3[IN_VISIBLE_FRAME_R] ? pixel : (is_pal_address ? vram_a[4:0] : (master_mode ? 5'd0 : {1'd0, EXT_IN}));
wire vram_r_ppudata = r2007_enabled;
wire rendering_enabled = enable_objects | enable_playfield;

// Colors and Masking
wire show_obj = (object_clip || ~clip_area) && enable_objects && t3[IN_VISIBLE_FRAME_R];
wire [4:0] obj_pixel = {obj_pixel_noblank[4:2], show_obj ? obj_pixel_noblank[1:0] : 2'd0};
wire show_bg = (playfield_clip || ~clip_area) && enable_playfield && t3[IN_VISIBLE_FRAME_R];
wire [3:0] bg_pixel = {bg_pixel_noblank[3:2], show_bg ? bg_pixel_noblank[1:0] : 2'd0};
wire clip_area = t3[H_EQ_0_7_OR_256_263] || ~t3[IN_VISIBLE_FRAME];
wire pal_mask = ~|SCANLINE || CYCLE < 2 || CYCLE > 253;
wire auto_mask = (MASK == 2'b11) && ~object_clip && ~playfield_clip;
wire mask_left = clip_area && ((|MASK && ~&MASK) || auto_mask);
wire mask_right = CYCLE > 247 && MASK == 2'b10;
wire mask_pal = (|SYS_TYPE && pal_mask); // PAL/Dendy masks scanline 0 and 2 pixels on each side with black.
wire [5:0] color2 = (mask_right | mask_left | mask_pal) ? 6'h0E : color3;
wire not_greyscale = (in_draw_range || (vram_r_ppudata && is_pal_address)) && ~grayscale;
wire [5:0] color1 = not_greyscale ? color_pipe[0] : {color_pipe[0][5:4], 4'b0};

// Extra Sprites
`ifdef EXTRA_SPRITES
assign use_extra_sprites = EXTRA_SPRITES;
`else
assign use_ex = 0;
assign use_extra_sprites = 0;
assign sprite_vram_addr_ex = 0;
`endif

// Output Pins
assign INT_n = ~(vbl_flag && vbl_enable);
assign EXT_OUT = master_mode ? pram_addr[3:0] : EXT_IN;
assign DOUT = latched_dout;
assign VRAM_W = w2007_enabled && ~is_pal_address && ~is_rendering;
assign VRAM_DOUT = w2007_enabled ? w2007_buf : DIN;
assign VRAM_R = vram_r_ppudata || (is_rendering_d && vram_read_cycle);
assign ALE = is_rendering ? ~vram_read_cycle : (r2007 || w2007_enabled);
assign VRAM_AB = w2007_enabled ? w2007_abuf[13:0] : vram_a;
assign VRAM_A_EX = {1'b0, sprite_vram_addr_ex};
//assign COLOR = color1;

logic vram_read_cycle;


always_comb begin


	// CPU Address decoder
	{w2000, w2001, r2002, w2003, w2004, r2004, w2005, w2006, r2007, w2007} = 0;
	case ({write, read, AIN})
		{1'b1, 1'b0, 3'd0}: w2000 = 1;
		{1'b1, 1'b0, 3'd1}: w2001 = 1;
		{1'b0, 1'b1, 3'd2}: r2002 = 1;
		{1'b1, 1'b0, 3'd3}: w2003 = 1;
		{1'b0, 1'b1, 3'd4}: r2004 = 1;
		{1'b1, 1'b0, 3'd4}: w2004 = 1;
		{1'b1, 1'b0, 3'd5}: w2005 = 1;
		{1'b1, 1'b0, 3'd6}: w2006 = 1;
		{1'b0, 1'b1, 3'd7}: r2007 = 1;
		{1'b1, 1'b0, 3'd7}: w2007 = 1;
		default: {w2000, w2001, r2002, w2003, w2004, r2004, w2005, w2006, r2007, w2007} = 0;
	endcase
end

// After spending a few sultry afternoons with visual 2c02, it seems that writes to the PPU follow a
// pattern most of the time. Read and Write are almost always goverened by three inputs: The cpu's
// read-or-write signal, the CE signal (called CS here) which is defined as phi2 AND the cpu address
// is in ppu range, and lastly by the lowest three bits of the address bus itself. In practice what
// this means is that when (write & phi2) are true, the CPU latches to an internal register, but the
// rest of the chip doesn't see this yet. When phi2 goes low, finally the chip reconnects the
// latching register to the internal wires and the effects of the writes take effect. The exceptions
// to this are Enable NMI, Slave Mode, and Grayscale which appear run wires directly to the latching
// register, and thus take effect as soon as (write & ce) are true. HVTog, 2006 and 2005 writes seem
// to behave the same as described above.

// These three signals tap directly into the latch register and apply instantly
wire vbl_enable = ~held_reset && w2000 ? DIN[7] : delay_2000[7];
wire master_mode = ~held_reset && w2000 ? DIN[6] : delay_2000[6];
wire grayscale = ~held_reset && w2001 ? DIN[0] : delay_2001[0];

// 2000 Latched data, only applies after the write signal goes low
wire [7:0] val_2000 = ~w2000 ? delay_2000 : latch_2000;

wire addr_inc = val_2000[2];
wire obj_patt = val_2000[3];
wire bg_patt = val_2000[4];
wire obj_size = val_2000[5];

// 2001 Latched data, only applies after the write signal goes low
wire [7:0] val_2001 = ~w2001 ? delay_2001 : latch_2001;

wire playfield_clip = val_2001[1];
wire object_clip = val_2001[2];
wire enable_playfield = val_2001[3];
wire enable_objects = val_2001[4];

assign EMPHASIS[1:0] = ~write || held_reset ?
	(|SYS_TYPE ? {delay_2001[5], delay_2001[6]} : delay_2001[6:5]) :
	(|SYS_TYPE ? {latch_2001[5], latch_2001[6]} : latch_2001[6:5]);
assign EMPHASIS[2] = ~held_reset && w2001 ? DIN[7] : delay_2001[7];

debug_dots debug_d(
	.enable     (DEBUG_DOTS),
	.color      (color1),
	.custom1    (palette_write),
	.custom2    (0),
	.w2000      (w2000),
	.w2001      (w2001),
	.r2002      (r2002),
	.w2003      (w2003),
	.r2004      (r2004),
	.w2004      (w2004),
	.w2005      (w2005),
	.w2006      (w2006),
	.r2007      (r2007),
	.w2007      (w2007),
	.new_color  (COLOR)
);

ClockGen clock(
	.clk                 (clk),
	.ce                  (CE),
	.ce2                 (CE2),
	.reset               (RESET),
	.nes_reset           (NES_RESET),
	.h_eq_339r           (t1[H_EQ_339R]),
	.v_eq_261            (t1[V_EQ_261]),
	.v_eq_255            (t[0][V_EQ_255]),
	.held_reset          (held_reset),
	.sys_type            (SYS_TYPE),
	.scanline            (SCANLINE),
	.cycle               (CYCLE),
	.end_of_line         (end_of_line),
	.entering_vblank     (entering_vblank),
	.short_frame         (SHORT_FRAME),
	.pclk0               (pclk0),
	.pclk1               (pclk1)
);

VramGen vram_v0(
	.clk                 (clk),
	.reset               (held_reset),
	.pclk0               (pclk0),
	.pclk1               (pclk1),
	.ppu_incr            (addr_inc),
	.read_ce             (read_ce),
	.write_ce            (write_ce),
	.is_rendering        (is_rendering),
	.rendering_enabled   (rendering_enabled),
	.ain                 (AIN),
	.din                 (DIN),
	.read                (read),
	.write               (write),
	.v_eq_261            (t1[V_EQ_261]),
	.HVTog               (HVTog),
	.h_eq_255r           (t2[H_EQ_255R]),
	.h_mod8_6_or_7r      (t2[H_MOD8_6_OR_7R]),
	.h_lt_256r           (t2[H_LT_256R]),
	.h_eq_320_to_335r    (t2[H_EQ_320_TO_335R]),
	.h_eq_279_to_303     (t1[H_EQ_279_TO_303]),
	.hpos_0              (hpos[2][0]),
	.w2000               (w2000),
	.w2005a              (w2005a),
	.w2005b              (w2005b),
	.w2006a              (w2006a),
	.w2006b              (w2006b),
	.w2007               (w2007_enabled_d),
	.r2007               (r2007_enabled_d),
	.vram_addr           (vram_v),
	.fine_x_scroll       (fine_x_scroll)
);

wire h_eq_63_255_or_339_r = t3[H_EQ_63R] || t3[H_EQ_255R] || t3[H_EQ_339R];

OAMEval spriteeval (
	.clk                  (clk),
	.pclk0                (pclk0),
	.pclk1                (pclk1),
	.reset                (held_reset),
	.h_lt_64r             (t3[H_LT_64R]),
	.h_eq_65r             (t3[H_EQ_65R]),
	.h_lt_256r            (t3[H_LT_256R]),
	.h_eq_256_to_319r     (t3[H_EQ_256_TO_319R]),
	.h_eq_63_255_or_339_r (h_eq_63_255_or_339_r),
	.in_visible_frame_r   (t3[IN_VISIBLE_FRAME_R]),
	.hpos_0               (hpos[3][0]),
	.rendering            (is_rendering),
	.v_eq_261             (t2[V_EQ_261]),
	.end_of_line          (end_of_line),
	.obj_size             (obj_size),
	.scanline             (SCANLINE),
	.hpos                 (hpos[3]),
	.oam_bus              (oam_bus),
	.oam_read_bus         (oam_read_bus),
	.oam_bus_ex           (oam_bus_ex),
	.oam_addr_write       (w2003),
	.oam_data_write       (w2004),
	.oam_data_read        (r2004),
	.oam_din              (DIN),
	.spr_overflow         (sprite_overflow),
	.sprite0              (obj0_on_line),
	.PAL                  (SYS_TYPE[0]),
	.masked_sprites       (masked_sprites),
	.sprite_load          (load_sprite)
);

// FIXME: sprLoadFlag and etc appear to be on pclk1
SpriteAddressGen address_gen(
	.clk            (clk),
	.ce             (pclk0),
	.enabled        (load_sprite),            // Load sprites between 256..319
	.obj_size       (obj_size),
	.scanline       (SCANLINE),
	.load_pattern2  (load_pattern2),
	.latch_pattern1 (latch_pattern1),
	.latch_pattern2 (latch_pattern2),
	.obj_patt       (obj_patt),               // Object size and pattern table
	.temp           (oam_bus),                // Info from temp buffer.
	.vram_addr      (sprite_vram_addr),       // [out] VRAM Address that we want data from
	.vram_data      (VRAM_DIN),               // [in] Data at the specified address
	.load           (spriteset_load),
	.load_in        (spriteset_load_in)       // Which parts of SpriteGen to load
);

`ifdef EXTRA_SPRITES
SpriteAddressGenEx address_gen_ex(
	.clk            (clk),
	.ce             (pclk0),
	.enabled        (load_sprite),            // Load sprites between 256..319
	.latch_pattern1 (latch_pattern1),
	.latch_pattern2 (latch_pattern2),
	.obj_size       (obj_size),
	.scanline       (SCANLINE[7:0]),
	.obj_patt       (obj_patt),               // Object size and pattern table
	.temp           (oam_bus_ex),             // Info from temp buffer.
	.vram_addr      (sprite_vram_addr_ex),    // [out] VRAM Address that we want data from
	.vram_data      (VRAM_DIN),               // [in] Data at the specified address
	.load           (spriteset_load_ex),
	.load_in        (spriteset_load_in_ex),   // Which parts of SpriteGen to load
	.use_ex         (use_ex),
	.masked_sprites (masked_sprites)
);
`endif

wire spr_bgr_en = t3[IN_VISIBLE_FRAME_R];
SpriteSet sprite_gen(
	.clk           (clk),
	.ce            (pclk0),
	.enable        (spr_bgr_en),
	.load          (spriteset_load),
	.load_in       (spriteset_load_in),
	.load_ex       (spriteset_load_ex),
	.load_in_ex    (spriteset_load_in_ex),
	.bits          (obj_pixel_noblank),
	.is_sprite0    (is_obj0_pixel),
	.extra_sprites (use_extra_sprites)
);

wire bgp_en = t3[H_LT_256R] || t3[H_EQ_320_TO_335R];

BgPainter bg_painter(
	.clk            (clk),
	.pclk0          (pclk0),
	.clear          (CYCLE == 310),
	.latch_nametable(latch_nametable),
	.latch_attrtable(latch_attrtable),
	.latch_pattern1 (latch_pattern1),
	.latch_pattern2 (latch_pattern2),
	.enable         (bgp_en),
	.fine_x_scroll  (fine_x_scroll),
	.vram_v         (vram_v),
	.name_table     (bg_name_table),
	.vram_data      (VRAM_DIN),
	.pixel          (bg_pixel_noblank)
);

PixelMuxer pixel_muxer(
	.bg       (bg_pixel[3:0]),
	.obj      (obj_pixel[3:0]),
	.obj_prio (obj_pixel[4]),
	.out      (pixel)
);

PaletteRam palette_ram(
	.clk        (clk),
	.reset      (held_reset),
	.ce         (pclk0),
	.addr       (pram_addr), // Read addr
	.din        (w2007_buf[5:0]),  // Value to write
	.dout       (color3),    // Output color
	.write_ce   (palette_write) // Condition for writing
);

XYDecoder decoder(
	.clk                 (clk),
	.pclk0               (pclk0),
	.pclk1               (pclk1),
	.rendering_enabled   (rendering_enabled),
	.cycle               (CYCLE),
	.scanline            (SCANLINE),
	.rendering           (is_rendering),
	.hpos                (hpos[0]),
	.vpos                (vpos),
	.timing_signals      (t[0])
);

logic sprite0;

logic pos_eq_279_224_to_278_247;
logic pos_eq_270_261_to_269_241;
logic in_range_1;

wire in_range_2 = ~(hpos[2] >= 256 && hpos[2] < 279) && ~in_range_1; // Disables the video completely (sync?)
wire in_range_3 = ~(hpos[2] >= 308 && hpos[2] < 323) && ~in_range_2; // Enabled video and palette p1. Color is delayed on pclk1. (BLANK?)
wire in_draw_range = ~t3[H_EQ_270_TO_327] && pos_eq_270_261_to_269_241;

wire blank_high = ~(in_range_2 || in_range_3);
wire blank_low = ~in_range_2;

logic [12:0] pat_address;

assign t1 = pclk1 ? t[0] : t[1];
assign t2 = t[2];
assign t3 = t[3];

wire load_nametable = ~(is_rendering && (((t2[H_LT_256R] || t2[H_EQ_320_TO_335R]) && t2[H_MOD8_2_OR_3R]) || hpos[2][2]));
wire load_attrtable = t2[H_MOD8_2_OR_3R] && (t2[H_LT_256R] || t2[H_EQ_320_TO_335R]);
wire load_pattern1 = t2[H_MOD8_4_OR_5R];
wire load_pattern2 = t2[H_MOD8_6_OR_7R];
wire load_sprites = t3[H_EQ_256_TO_319R];
wire load_sprnt = is_rendering && hpos[2][2];

logic latch_nametable;
logic latch_attrtable;
logic latch_pattern1;
logic latch_pattern2;
logic bgr_transparent;
logic spr0_transparent;

always @(posedge clk) begin
	read_old <= read;
	write_old <= write;

	if (pclk1) begin
		pat_address <= t2[H_EQ_256_TO_319R] ? sprite_vram_addr : {bg_patt, bg_name_table, load_pattern2, vram_v[14:12]};

		in_range_1 <= t2[H_EQ_279_TO_303] || pos_eq_279_224_to_278_247;

		sprite0 <= is_obj0_pixel && t1[IN_VISIBLE_FRAME_R] && |obj_pixel[1:0];
		if (
			t2[IN_VISIBLE_FRAME_R] &&
			obj0_on_line        &&    // Sprite zero on current line.
			~spr0_transparent &&
			bgr_transparent            // Background pixel not transparent.
			) begin
				sprite0_hit_bg <= 1;
		end

		latch_nametable <= load_nametable && vram_read_cycle && is_rendering;
		latch_attrtable <= load_attrtable && vram_read_cycle; //(t1[H_LT_256R] || t1[H_EQ_320_TO_335R])
		latch_pattern1 <= load_sprnt && ~hpos[2][1] && vram_read_cycle;
		latch_pattern2 <= load_sprnt && hpos[2][1] && vram_read_cycle;
		vram_read_cycle <= 0;

		
	end

	if (pclk0) begin
		bgr_transparent <= |bg_pixel[1:0];
		spr0_transparent <= ~sprite0;
		// VRAM Address
		if (t2[H_EQ_256_TO_319R])
			VRAM_R_EX <= use_ex && EXTRA_SPRITES;
		else
			VRAM_R_EX <= 0;
		
		vram_read_cycle <= is_rendering && hpos[1][0]; // FIXME: This is off by one. It should read when the cycle is even, but the sdram needs time to read..
		if (load_nametable)
			vram_a <= {vram_v[13] | is_rendering, vram_v[12] & ~is_rendering, vram_v[11:0]};                                        // Name Table 1-2
		else if (load_attrtable)
			vram_a <= {vram_v[13] | is_rendering, vram_v[12] & ~is_rendering, vram_v[11:10], 4'b1111, vram_v[9:7], vram_v[4:2]};    // Attribute table 3-4
		else if (load_sprnt)
			vram_a <= {~(is_rendering & hpos[1][2]), pat_address[12:4], hpos[1][1], pat_address[2:0]};
	end

	// Clocked timing gates
	if (pclk0) begin
		hpos[1] <= hpos[0];
		hpos[3] <= hpos[2];
		t[3] <= t[2];
	end else if (pclk1) begin
		t[1] <= t[0]; // To capture changes in rendering enabled;
		hpos[2] <= hpos[1];
		t[2] <= t1;
	end

	if (pclk0) begin
		w2007_enabled_d <= w2007_enabled;
		r2007_enabled_d <= r2007_enabled;

		w2007_ended[0] <= ~w2007 && w2007_reg;
		w2007_ended[2] <= w2007_ended[1];
		w2007_ended[4] <= w2007_ended[3];
		
		r2007_ended[0] <= ~r2007 && r2007_reg;
		r2007_ended[2] <= r2007_ended[1];
		r2007_ended[4] <= r2007_ended[3];

		is_rendering_d <= is_rendering;
		if (t[0][H_EQ_279_TO_303] && t[0][V_EQ_244])
			pos_eq_279_224_to_278_247 <= 1;
		else if (t[0][H_EQ_279_TO_303] && t[0][V_EQ_247])
			pos_eq_279_224_to_278_247 <= 0;

		if (t1[H_EQ_270_TO_327] && t[0][V_EQ_244])
			pos_eq_270_261_to_269_241 <= 0;
		else if (t1[H_EQ_270_TO_327] && t[0][V_EQ_261])
			pos_eq_270_261_to_269_241 <= 1;

		HSYNC <= t1[H_EQ_279_TO_303];
		if (t1[H_EQ_328])
			HBLANK <= 0;
		if (t1[H_EQ_270])
			HBLANK <= 1;

		if (t[0][V_EQ_244] && t1[H_EQ_279_TO_303])
			VSYNC <= 1;
		if (t[0][V_EQ_247] && t1[H_EQ_279_TO_303])
			VSYNC <= 0;
		if (t[0][V_EQ_241] && t1[H_EQ_270_TO_327])
			VBLANK <= 1;
		if (t[0][V_EQ_261_I] && t1[H_EQ_270_TO_327])
			VBLANK <= 0;

		if (t1[V_EQ_261])
			vbl_flag <= 0;
		else if (entering_vblank)
			vbl_flag <= 1;

		color_pipe <= '{color2, color_pipe[0], color_pipe[1], color_pipe[2]};

		if (decay_high > 0)
			decay_high <= decay_high - 1'b1;
		else
			latched_dout[7:5] <= 3'b000;

		if (decay_low > 0)
			decay_low <= decay_low - 1'b1;
		else
			latched_dout[4:0] <= 5'b00000;
	end
	
	if (pclk1) begin
		w2007_ended[1] <= w2007_ended[0];
		w2007_ended[3] <= w2007_ended[2];

		r2007_ended[1] <= r2007_ended[0];
		r2007_ended[3] <= r2007_ended[2];
	end

	case (AIN)
		0: begin // PPU Control Register 1
			if (write) delay_2000 <= DIN;
		end

		1: begin // PPU Control Register 2
			if (write) delay_2001 <= DIN;
		end

		2: begin
			if (read_ce)
				latched_dout[7] <= vbl_flag;
			if (read) begin
				latched_dout[5] <= sprite_overflow;
				latched_dout[6] <= sprite0_hit_bg;
				hv_latch <= 0;
				vbl_flag <= 0;
				refresh_high <= 1'b1;
			end
		end

		4: if (read) begin // FIXME: Pclk0 seems suspect
			latched_dout <= oam_read_bus;
			refresh_high <= 1'b1;
			refresh_low <= 1'b1;
		end

		5, 6: if (write) hv_latch <= ~HVTog;

		7: begin
			if (read)
				r2007_reg <= 1;
			if (is_pal_address) begin
				if (read) begin
					latched_dout[5:0] <= color3;
					refresh_low <= 1'b1;
				end
			end else begin
				if (read_ce) begin
					latched_dout <= vram_latch;
					refresh_high <= 1'b1;
					refresh_low <= 1'b1;
				end
			end
			if (write) begin
				w2007_buf <= DIN;
				w2007_abuf <= vram_v;
				w2007_reg <= 1;
			end
		end
	endcase

	if (write) begin
		refresh_high <= 1'b1;
		refresh_low <= 1'b1;
		latched_dout <= DIN;
	end else begin
		HVTog <= hv_latch;
		latch_2000 <= delay_2000;
		latch_2001 <= delay_2001;
	end

	if (refresh_high) begin
		decay_high <= 3221590; // aprox 600ms decay rate
		refresh_high <= 0;
	end

	if (refresh_low) begin
		decay_low <= 3221590;
		refresh_low <= 0;
	end

	if (vram_r_ppudata)
		vram_latch <= VRAM_DIN;

	if (pclk1 && t2[V_EQ_261]) begin
		sprite0_hit_bg <= 0;
		sprite0 <= 0;
	end

	if (pclk1) begin
		if (w2007_ended[2]) begin
			w2007_reg <= 0;
		end 
		if (r2007_ended[2]) begin
			r2007_reg <= 0;
		end
	end
	if (held_reset) begin
		is_rendering_d <= 0;
		vbl_flag <= 0;
		sprite0_hit_bg <= 0;
		delay_2000 <= 8'd0;
		delay_2001 <= 8'd0;
		latch_2000 <= 8'd0;
		latch_2001 <= 8'd0;
		w2007_reg <= 0;
		r2007_reg <= 0;
		vram_latch <= 0;
		HVTog <= 0;
		hv_latch <= 0;
	end

	if (RESET) begin
		t[3:1] <= 0;
		hpos[3:1] <= 0;
		decay_high <= 0;
		decay_low <= 0;
		latched_dout <= 8'd0;
		read_old <= 0;
		write_old <= 0;
	end
end

endmodule  // PPU
