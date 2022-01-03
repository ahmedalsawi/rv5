`timescale 1ns/1ns

`define OP_RANGE 6:0
`define RD_RANGE  11:7
`define FUNCT3_RANGE 14:12
`define RS1_RANGE 19:15
`define RS2_RANGE 24:20
`define IMM_11_0_RANGE 31:20

`define SIM

module signext #(parameter SIZE=32, parameter OSIZE=12) (
	output  [SIZE-1:0] y,
	input  [OSIZE-1:0] a
	);
	assign y = {{(SIZE-OSIZE){a[OSIZE-1]}}, a};
endmodule

module ram #(parameter WIDTH=32, parameter ADDR=32) (
	input wire clk,
	input wire we,
    input wire [ WIDTH - 1: 0] din,
    input wire [ADDR-1 : 0] addr,
    output wire [ WIDTH - 1: 0] dout
);
	// FIXME define ram big enough. iverilog doesn't work with large arrays for some reason
	//reg [WIDTH-1:0] mem [ 2**ADDR-1 : 0];
	reg [WIDTH-1:0] mem [ 100 : 0]; 

	assign dout = mem[addr]; 

	//always @(addr) begin
	//	$display("%t Reading mem[%0x]=%0x", $time, addr, mem[addr]);
	//end

	always @(posedge clk) 	begin
		if (we) begin
			$display("%t Writing ram[0x%0x]=0x%0x", $time, addr, din);
			mem[addr] = din;
		end
	end
endmodule

module rom #(parameter WIDTH=32, parameter ADDR=32) (
    input  wire [ADDR  - 1 : 0] addr,
    output wire [WIDTH - 1 : 0] dout
);

	reg [WIDTH-1:0] mem [ 100 : 0];

	assign dout = mem[addr]; 

`ifdef SIM
	initial begin
		$readmemh("rom.hex", mem, 0,2);
	end

	generate
	  genvar idx;
	  for(idx = 0; idx < 100; idx = idx+1) begin: rom
	    wire [31:0] tmp;
	    assign tmp = mem[idx];
	  end
	endgenerate
`endif

endmodule

module regfile#(parameter WIDTH=32) (
	input clk,
	input [4:0] addr1,
	output [31:0] dout1,
	
	input [4:0] addr2,
	output [31:0] dout2,

	input [4:0] addr3,
	input [31:0] din3,
	input we3
);
	reg [WIDTH-1:0] mem [0:31] ;
	
	// x0 is zero
	assign dout1 = addr1 == 0 ? 5'b00000: mem[addr1];
	assign dout2 = addr2 == 0 ? 5'b00000: mem[addr2];

	always @(posedge clk) begin
		// Don't write to x0
		if (we3 && (addr3 != 5'b00000)) begin
			$display("%t Writing regfile[%0d]=0x%0x", $time, addr3, din3);
			mem[addr3] <= din3;
		end
	end

`ifdef SIM
integer i;
initial begin
	for (i=0 ; i < 32; i++)
		mem[i] <= 30;
end
generate
  genvar idx;
  for(idx = 0; idx < 32; idx = idx+1) begin: x
    wire [31:0] tmp;
    assign tmp = mem[idx];
  end
endgenerate
`endif
endmodule


module alu(
	input [31:0] alu_in1,
	input [31:0] alu_in2,
	input [5:0] alu_control,
	output zero,
	output reg [31:0] alu_result
);

    always @(alu_control or alu_in1 or alu_in2)
    begin
        case (alu_control) // TODO
         0 : alu_result = alu_in1 + alu_in2;
        endcase 
    end

	assign zero = alu_result == 0 ? 1 : 0;
endmodule

/****************
*****************/
module rv5
(
input  rst,
input  clk
);

	// Instruction fetch
	reg  [31:0] pc;
	wire [31:0] pc_;
	wire [31:0] instr;
	
	assign pc_ = pc + 1;
	always @(posedge clk) begin
		if (rst)
			pc = 0;
		else
			pc = pc_;
	end

	rom u_instruct_mem(
		.addr(pc),
		.dout(instr)
	);

	// Instructon decode
	reg rf3_we_control;
	reg [5:0] alu_control;
	reg mem_we;
	reg imm_mux;

	wire [6:0]  opcode;
	wire [2:0]  funct3;
	wire [4:0]  rf1, rf2, rf3;
	wire [31:0] rf1_do, rf2_do, rf3_di;
	wire [11:0] imm11_0;
	wire [31:0] imm11_0_extended;

	assign opcode   = instr[`OP_RANGE];
	assign funct3	= instr[`FUNCT3_RANGE];	
	assign rf1 		= instr[`RS1_RANGE];
	assign rf2 		= instr[`RS2_RANGE];
	assign rf3 		= instr[`RD_RANGE];
	assign imm11_0 = (imm_mux == 0 )? instr[`IMM_11_0_RANGE] : {instr[31:25], instr[11:7]};

	regfile u_reg_file(
		.clk(clk),
		.addr1(rf1),
		.dout1(rf1_do),
		.addr2(rf2),
		.dout2(rf2_do),
		.addr3(rf3),
		.din3(rf3_di),
		.we3(rf3_we_control)
	);

	signext u_signext(imm11_0_extended, imm11_0);

	always @(opcode, funct3, rst) begin
		// Default control signals
		rf3_we_control 	<= 0;
		alu_control 	<= 0;
		mem_we 			<= 0;
		imm_mux 		<= 0;

		if(rst) begin end
		// In reset, Keep default control signals
		else begin
        case (opcode)
			7'b0000011 :
				case (funct3)
				3'b010 : // LW
					begin
						rf3_we_control 	<= 1;
						alu_control 	<= 0;
						mem_we 			<= 0;
						imm_mux 		<= 0;
					end
				endcase
				
			7'b0100011 :
				case (funct3)
				3'b010 : //SW
					begin
						rf3_we_control 	<= 0;
						alu_control 	<= 0;
						mem_we 			<= 1;
						imm_mux 		<= 1;
					end
				endcase
			endcase 
		end
	end
	
	// Execution
	wire [31:0] alu_result;

	alu u_alu(
		.alu_in1(rf1_do),
		.alu_in2(imm11_0_extended),
		.alu_result(alu_result),
		.alu_control(alu_control)
	);

	wire [31:0] mem_dout;

	ram u_data_mem(
		.clk(clk),
    	.addr(alu_result),
    	.dout(mem_dout),
		.we(mem_we),
    	.din(rf2_do)
	);

	// write-back
	assign rf3_di = mem_dout;

endmodule

module top;
	reg clk, rst;
	rv5 dut(.clk(clk), .rst(rst));

	initial begin
		rst = 1;
		#20;
		rst = 0;
	end
	initial begin
		clk = 0;
		forever clk = #5 ~clk; 
	end
	initial begin #100 $finish(); end
	initial begin $dumpvars(0,dut); end
endmodule 