
//////////////////////////////////////////////////////////
// Definition of a D flip flop with asyncronous reset  //
/////////////////////////////////////////////////////////

module dff_async_rst (
  input data,
  input clk,
  input reset,
  output reg q);

  always @ ( posedge clk or posedge reset)    
    if (reset) begin
      q <= 1'b0;
    end  else begin
      q <= data;
    end

endmodule

//////////////////////////////////////////////////////////
// Definition of a D Latch  with asyncronous reset  //
/////////////////////////////////////////////////////////

module dltch_async_rst (
  input data,
  input clk,
  input reset,
  output reg q);

  always @ (clk or reset or data)    
    if (reset) begin
      q <= 1'b0;
    end  else if (clk) begin
      q <= data;
    end

endmodule

//////////////////////////////////////////////////////////
// Definition of a D Latch  without  reset  //
/////////////////////////////////////////////////////////

module dltch (
  input data,
  input clk,
  output reg q);

  always @ (clk or data)    
    if (clk) begin
      q <= data;
    end

endmodule

///////////////////////////////////////////////////////////////////////
// Definition of the prll D register with flops
///////////////////////////////////////////////////////////////////////

module prll_d_reg #(parameter bits = 32)(
  input clk,
  input reset,
  input [bits-1:0] D_in,
  output [bits-1:0] D_out
);
  genvar i;
  generate
    for(i = 0; i < bits; i=i+1) begin:bit_
      dff_async_rst prll_regstr_(.data(D_in[i]),.clk(clk),.reset(reset),.q(D_out[i]));
    end
  endgenerate

endmodule

///////////////////////////////////////////////////////////////////////
// Definition of the prll D register with Lathces 
///////////////////////////////////////////////////////////////////////

module prll_d_ltch_no_rst #(parameter bits = 32)(
  input clk,
  input [bits-1:0] D_in,
  output [bits-1:0] D_out
);
  genvar i;
  generate
    for(i = 0; i < bits; i=i+1) begin:bit_
      dltch prll_regstr_(.data(D_in[i]),.clk(clk),.q(D_out[i]));
    end
  endgenerate

endmodule

///////////////////////////////////////////////////////////////////////
// Definition of the prll D register with Lathces 
///////////////////////////////////////////////////////////////////////

module prll_d_ltch #(parameter bits = 32)(
  input clk,
  input reset,
  input [bits-1:0] D_in,
  output [bits-1:0] D_out
);
  genvar i;
  generate
    for(i = 0; i < bits; i=i+1) begin:bit_
      dltch_async_rst prll_regstr_(.data(D_in[i]),.clk(clk),.reset(reset),.q(D_out[i]));
    end
  endgenerate

endmodule

///////////////////////////////////////////////////////////////////////
// Definition of a positve edge detector 
///////////////////////////////////////////////////////////////////////

module pos_edge(
 input clk,
 `ifdef COMP_TEST
    input deleteme,
 `endif
 output out
);
 `ifdef COMP_TEST
    wire neg_clk;
    not #(0,3) inv_clk(neg_clk,clk);
    and  and_posdg (out,deleteme,neg_clk);
 `else
    wire neg_clk;
    not #(0,3) inv_clk(neg_clk,clk);
    and  and_posdg (out,clk,neg_clk);
 `endif
endmodule


///////////////////////////////////////////////////////////////////////
// Definition of a negative edge detector 
///////////////////////////////////////////////////////////////////////

module neg_edge(
 input clk,
 `ifdef COMP_TEST
    input deleteme,
 `endif
 output out
);
 `ifdef COMP_TEST
    wire neg_clk;
    not #(3,0) inv_clk(neg_clk,clk);
    nor nor_ngdg (out,deleteme,neg_clk);
 `else
    wire neg_clk;
    not #(3,0) inv_clk(neg_clk,clk);
    nor nor_ngdg (out,clk,neg_clk);
 `endif
endmodule

///////////////////////////////////////////////////////////////////////
// Definition of the FIFO with Flip_Flops 
///////////////////////////////////////////////////////////////////////
module fifo_flops #(parameter depth = 16,parameter bits = 32)(
  input [bits-1:0] Din,
  output reg [bits-1:0] Dout,
  input push,
  input pop,
  input clk,
  output reg full,
  output reg pndng,
  input rst
);
  wire [bits-1:0] q[depth-1:0];
  reg [$clog2(depth):0] count;
  reg [bits-1:0] aux_mux [depth-1:0];
  reg [bits-1:0] aux_mux_or [depth-2:0];

  genvar i;
  generate
    for(i=0;i<depth;i=i+1)begin:_dp_
       if(i==0)begin: _dp2_
         prll_d_reg #(bits) D_reg(.clk(push),.reset(rst),.D_in(Din),.D_out(q[i]));
         always@(*)begin
           aux_mux[i]=(count==i+1)?q[i]:{bits{1'b0}};
         end    
       end else begin: _dp3_
         prll_d_reg #(bits) D_reg(.clk(push),.reset(rst),.D_in(q[i-1]),.D_out(q[i]));
         always@(*)begin
           aux_mux[i]=(count==i+1)?q[i]:{bits{1'b0}};
         end    
       end
    end
  endgenerate

  generate
  for(i=0;i<depth-2;i=i+1)begin:_nu_
    always@(*)begin
      aux_mux_or[i]=aux_mux[i] | aux_mux_or[i+1];
    end
  end
  endgenerate

  always@(*)begin
    aux_mux_or[depth-2] = aux_mux [depth-1]|aux_mux[depth-2];
    Dout=aux_mux_or[0];  
  end

  always@(posedge clk)begin
  if(rst) begin
    count <= 0;
  end else begin
  
    case({push,pop})
      2'b00: count <= count;
      2'b01: begin
        if(count == 0) begin
          count <= 0;
        end else begin
          count <=count - 1;
        end
      end
      2'b10:begin
         if(count == depth)begin
           count <= count;
         end else begin
           count <= count+1;
        end
      end
      2'b11: count <= count;
    endcase
  end
  pndng <= (count==0)?{1'b0}:{1'b1};
  full <=(count == depth)?{1'b1}:{1'b0};
end
endmodule


///////////////////////////////////////////////////////////////////////
// Definition of the FIFO with Flip_Flops no full
///////////////////////////////////////////////////////////////////////
module fifo_flops_no_full #(parameter depth = 16,parameter bits = 32)(
  input [bits-1:0] Din,
  output reg [bits-1:0] Dout,
  input push,
  input pop,
  input clk,
  //output reg full,
  output reg pndng,
  input rst
);
  wire [bits-1:0] q[depth-1:0];
  reg [$clog2(depth):0] count;
  reg [$clog2(depth):0] nxt_count;
  reg [bits-1:0] aux_mux [depth-1:0];
  reg [bits-1:0] aux_mux_or [depth-2:0];
  reg clk_gen;

  assign clk_gen = ~clk & push;

  genvar i;
  generate
    for(i=0;i<depth;i=i+1)begin:_dp_
       if(i==0)begin: _dp2_
         prll_d_reg #(bits) D_reg(.clk(clk_gen),.reset(rst),.D_in(Din),.D_out(q[i]));
         always@(*)begin
           aux_mux[i]=(count==i+1)?q[i]:{bits{1'b0}};
         end    
       end else begin: _dp3_
         prll_d_reg #(bits) D_reg(.clk(clk_gen),.reset(rst),.D_in(q[i-1]),.D_out(q[i]));
         always@(*)begin
           aux_mux[i]=(count==i+1)?q[i]:{bits{1'b0}};
         end    
       end
    end
  endgenerate

  generate
  for(i=0;i<depth-2;i=i+1)begin:_nu_
    always@(*)begin
      aux_mux_or[i]=aux_mux[i] | aux_mux_or[i+1];
    end
  end
  endgenerate

  always@(*)begin
    aux_mux_or[depth-2] = aux_mux [depth-1]|aux_mux[depth-2];
    Dout=aux_mux_or[0];  
  end

  always@(*)begin
    case({push,pop})
      2'b00: nxt_count <= count;
      2'b01: begin
        if(count == 0) begin
          nxt_count <= 0;
        end else begin
          nxt_count <=count - 1;
        end
      end
      2'b10:begin
         if(count == depth)begin
           nxt_count <= count;
         end else begin
           nxt_count <= count+1;
        end
      end
      2'b11: nxt_count <= count;
    endcase
    pndng <= (count==0)?{1'b0}:{1'b1};
end
  always@(posedge clk or posedge rst)begin
    if(rst) begin
      count = 0;
    end else begin
      count = nxt_count;
    end
  end
   `ifdef DEBUG
      always@(posedge push)begin
        if(count == depth)begin
          $display ("Fifo overflow at time %g:",$time,$sformatf("%m"));
        end 
      end
    `endif  

endmodule

///////////////////////////////////////////////////////////////////////
// Definition of the FIFO with Latches
///////////////////////////////////////////////////////////////////////
module fifo_ltch #(parameter depth = 16,parameter bits = 32)(
  input [bits-1:0] Din,
  output reg [bits-1:0] Dout,
  input push,
  input pop,
  input clk,
  output reg full,
  output reg pndng,
  input rst
);
  wire [bits-1:0] q[depth-1:0];
  wire gen_clk[depth-1:0];
  logic  enbld_clk;
  reg [$clog2(depth):0] count;
  reg [bits-1:0] aux_mux [depth-1:0];
  reg [bits-1:0] aux_mux_or [depth-2:0];

    
     wire gen_clk_hld[depth-1:1];
     wire clk_dlyd;
     buf #(3,3) buf_dly_clk(clk_dlyd,clk); 
     buf #(2,2) buf_hld_n (gen_clk_hld[depth-1],gen_clk[depth-1]);
     pos_edge posedg_dtct (.clk(enbld_clk),.out(gen_clk[depth-1]));
     always@(*) begin
       enbld_clk <= clk_dlyd & push;
     end
   
  genvar i;
  generate
    for(i=0;i<depth;i=i+1)begin:_dp_
       if(i==0)begin: _dp2_
             neg_edge neg_edg_dtct(.clk(gen_clk_hld[i+1]),.out(gen_clk[i])); 
             prll_d_ltch #(bits) D_reg(.clk(gen_clk[i]),.reset(rst),.D_in(Din),.D_out(q[i]));
             always@(*)begin
               aux_mux[i]=(count==i+1)?q[i]:{bits{1'b0}};
             end
       end else begin: _dp3_
          if(i==(depth-1))begin: _dp4_
             prll_d_ltch #(bits) D_reg(.clk(gen_clk[i]),.reset(rst),.D_in(q[i-1]),.D_out(q[i]));
             always@(*)begin
               aux_mux[i]=(count==i+1)?q[i]:{bits{1'b0}};
             end 
          end else begin: _dp5_
               buf #(2,2) buf_hld (gen_clk_hld[i],gen_clk[i]);
               neg_edge neg_edg_dtct (.clk(gen_clk_hld[i+1]),.out(gen_clk[i])); 
               prll_d_ltch #(bits) D_reg(.clk(gen_clk[i]),.reset(rst),.D_in(q[i-1]),.D_out(q[i]));
               always@(*)begin
                 aux_mux[i]=(count==i+1)?q[i]:{bits{1'b0}};
               end 
          end
       end
    end
  endgenerate

  generate
  for(i=0;i<depth-2;i=i+1)begin:_nu_
    always@(*)begin
      aux_mux_or[i]=aux_mux[i] | aux_mux_or[i+1];
    end
  end
  endgenerate

  always@(*)begin
    aux_mux_or[depth-2] = aux_mux [depth-1]|aux_mux[depth-2];
    Dout=aux_mux_or[0];  
  end

  always@(posedge clk)begin
  if(rst) begin
    count <= 0;
  end else begin
  
    case({push,pop})
      2'b00: count <= count;
      2'b01: begin
        if(count == 0) begin
          count <= 0;
        end else begin
          count <=count - 1;
        end
      end
      2'b10:begin
         if(count == depth)begin
           count <= count;
         end else begin
           count <= count+1;
        end
      end
      2'b11: count <= count;
    endcase
  end
  pndng <= (count==0)?{1'b0}:{1'b1};
  full <=(count == depth)?{1'b1}:{1'b0};
end
endmodule

///////////////////////////////////////////////////////////////////////
// Definition of the FIFO with Latches and no reset
///////////////////////////////////////////////////////////////////////
module fifo_ltch_no_rst #(parameter depth = 16,parameter bits = 32)(
  input [bits-1:0] Din,
`ifdef COMP_TEST
  input [depth-1:0] deleteme,
`endif
  output reg [bits-1:0] Dout,
  input push,
  input pop,
  input clk,
//  output reg full,
  output reg pndng,
  input rst
);
  wire [bits-1:0] q[depth-1:0];
  wire gen_clk[depth-1:0];
  logic  enbld_clk;
  reg [$clog2(depth):0] count;
  reg [bits-1:0] aux_mux [depth-1:0];
  reg [bits-1:0] aux_mux_or [depth-2:0];

     wire gen_clk_hld[depth-1:1];
     wire clk_dlyd;
     buf #(3,3) buf_dly_clk(clk_dlyd,clk); 
     buf #(2,2) buf_hld_n (gen_clk_hld[depth-1],gen_clk[depth-1]);
     `ifdef COMP_TEST
       pos_edge posedg_dtct (.deleteme(deleteme[depth-1]),.clk(enbld_clk),.out(gen_clk[depth-1]));
     `else
       pos_edge posedg_dtct (.clk(enbld_clk),.out(gen_clk[depth-1]));
     `endif
     and gen_enbl_clk(enbld_clk,clk_dlyd,push);
   
  genvar i;
  generate
    for(i=0;i<depth;i=i+1)begin:_dp_
       if(i==0)begin: _dp2_
            `ifdef COMP_TEST
               neg_edge neg_edg_dtct (.deleteme(deleteme[i]),.clk(gen_clk_hld[i+1]),.out(gen_clk[i]));
            `else
               neg_edge neg_edg_dtct(.clk(gen_clk_hld[i+1]),.out(gen_clk[i])); 
            `endif
             prll_d_ltch_no_rst #(bits) D_reg(.clk(gen_clk[i]),.D_in(Din),.D_out(q[i]));
             always@(*)begin
               aux_mux[i]=(count==i+1)?q[i]:{bits{1'b0}};
             end
       end else begin: _dp3_
          if(i==(depth-1))begin: _dp4_
             prll_d_ltch_no_rst #(bits) D_reg(.clk(gen_clk[i]),.D_in(q[i-1]),.D_out(q[i]));
             always@(*)begin
               aux_mux[i]=(count==i+1)?q[i]:{bits{1'b0}};
             end 
          end else begin: _dp5_
               buf #(2,2) buf_hld (gen_clk_hld[i],gen_clk[i]);
              `ifdef COMP_TEST
                 neg_edge neg_edg_dtct (.deleteme(deleteme[i]),.clk(gen_clk_hld[i+1]),.out(gen_clk[i]));
               `else
                 neg_edge neg_edg_dtct (.clk(gen_clk_hld[i+1]),.out(gen_clk[i])); 
               `endif
               prll_d_ltch_no_rst #(bits) D_reg(.clk(gen_clk[i]),.D_in(q[i-1]),.D_out(q[i]));
               always@(*)begin
                 aux_mux[i]=(count==i+1)?q[i]:{bits{1'b0}};
               end 
          end
       end
    end
  endgenerate

  generate
  for(i=0;i<depth-2;i=i+1)begin:_nu_
    always@(*)begin
      aux_mux_or[i]=aux_mux[i] | aux_mux_or[i+1];
    end
  end
  endgenerate

  always@(*)begin
    aux_mux_or[depth-2] = aux_mux [depth-1]|aux_mux[depth-2];
    Dout=aux_mux_or[0];  
  end

  always@(posedge clk)begin
  if(rst) begin
    count <= 0;
  end else begin
  
    case({push,pop})
      2'b00: count <= count;
      2'b01: begin
        if(count == 0) begin
          count <= 0;
        end else begin
          count <=count - 1;
        end
      end
      2'b10:begin
         if(count == depth)begin
           count <= count;
         end else begin
           count <= count+1;
        end
      end
      2'b11: count <= count;
    endcase
  end
  pndng <= (count==0)?{1'b0}:{1'b1};
// full <=(count == depth)?{1'b1}:{1'b0};
end
endmodule

///////////////////////////////////////////////////////////////////////
// Definition of the reset logic requiered by the ntrpt_cam_fifo
///////////////////////////////////////////////////////////////////////
module rst_lgc #(parameter N=0, parameter depth = 16) (
  input [$clog2(depth):0] count,
  input pop,
  input rst,
  output reg rst_out
);
    reg equal;
 `ifdef TESTING
    reg [$clog2(depth):0] delay_count;
    genvar i;
    generate
      for(i=0;i<$clog2(depth);i=i+1)begin:_dp_
        buf #(2,2) buf_dly_count(delay_count[i],count[i]);
      end
    endgenerate
    always@(*) begin
      equal <= (count == N)?{1'b1}:{1'b0};
      rst_out <= (rst ||(pop && equal));
    end
  `else
    always@(*) begin
      equal <= (count == N)?{1'b1}:{1'b0};
      rst_out <= (rst ||(pop && equal));
    end
  `endif
endmodule


///////////////////////////////////////////////////////////////////////
// Definition of the cam FIFO with Latches for the interrupt controller
///////////////////////////////////////////////////////////////////////
module ntrpt_cam_fifo #(parameter depth = 16,parameter bits = 32)(
  input [bits-1:0] Din,
  output reg [bits-1:0] Dout,
  input push,
  input pop,
  input clk,
//  output reg full,
  output reg pndng,
  output reg MTIP,
  input reset
);
  wire [bits-1:0] q[depth-1:0];
  wire gen_clk[depth-1:0];
  wire rst[depth-1:0];
  reg [depth-1:0] MTIP_partial;
  logic  enbld_clk;
  reg [$clog2(depth):0] count;
  reg [bits-1:0] aux_mux [depth-1:0];
  reg [bits-1:0] aux_mux_or [depth-2:0];
  

    
  `ifdef TESTING
     wire gen_clk_hld[depth-1:1];
     wire clk_dlyd;
     buf #(3,3) buf_dly_clk(clk_dlyd,clk); 
     buf #(2,2) buf_hld_n (gen_clk_hld[depth-1],gen_clk[depth-1]);
     pos_edge posedg_dtct (.clk(enbld_clk),.out(gen_clk[depth-1]));
     always@(*) begin
       enbld_clk <= clk_dlyd & push;
     end
  `else
    pos_edge posedg_dtct (.clk(enbld_clk),.out(gen_clk[depth-1]));
    always@(*) begin
      enbld_clk <= clk & push;
    end
  `endif
   
  genvar i;
  generate
    for(i=0;i<depth;i=i+1)begin:_dp_
       rst_lgc #(.N(i),.depth(depth)) rst_lgc_lvl(.count(count),.pop(pop),.rst(reset),.rst_out(rst[i]));

       if(i==0)begin: _dp2_
         `ifdef TESTING
             neg_edge neg_edg_dtct(.clk(gen_clk_hld[i+1]),.out(gen_clk[i])); 
             prll_d_ltch #(bits) D_reg(.clk(gen_clk[i]),.reset(rst[i]),.D_in(Din),.D_out(q[i]));
             always@(*)begin
               MTIP_partial[i] = (q[i][15:0] == {16'h0080})? {1'b1}: {1'b0};
               aux_mux[i]=(count==i+1)?q[i]:{bits{1'b0}};
             end
           `else
             neg_edge neg_edg_dtct(.clk(gen_clk[i+1]),.out(gen_clk[i])); 
             prll_d_ltch #(bits) D_reg(.clk(gen_clk[i]),.reset(rst[i]),.D_in(Din),.D_out(q[i]));
             always@(*)begin
               MTIP_partial[i] = (q[i][15:0] == {16'h0080})? {1'b1}: {1'b0};
               aux_mux[i]=(count==i+1)?q[i]:{bits{1'b0}};
             end
           `endif    
       end else begin: _dp3_
          if(i==(depth-1))begin: _dp4_
             prll_d_ltch #(bits) D_reg(.clk(gen_clk[i]),.reset(rst[i]),.D_in(q[i-1]),.D_out(q[i]));
             always@(*)begin
               MTIP_partial[i] = (q[i][15:0] == {16'h0080})? {1'b1}: {1'b0};
               aux_mux[i]=(count==i+1)?q[i]:{bits{1'b0}};
             end 
          end else begin: _dp5_
           `ifdef TESTING
               buf #(2,2) buf_hld (gen_clk_hld[i],gen_clk[i]);
               neg_edge neg_edg_dtct (.clk(gen_clk_hld[i+1]),.out(gen_clk[i])); 
               prll_d_ltch #(bits) D_reg(.clk(gen_clk[i]),.reset(rst[i]),.D_in(q[i-1]),.D_out(q[i]));
               always@(*)begin
                 MTIP_partial[i] = (q[i][15:0] == {16'h0080})? {1'b1}: {1'b0};
                 aux_mux[i]=(count==i+1)?q[i]:{bits{1'b0}};
               end 
           `else
             neg_edge neg_edg_dtct(.clk(gen_clk[i+1]),.out(gen_clk[i])); 
             prll_d_ltch #(bits) D_reg(.clk(gen_clk[i]),.reset(rst[i]),.D_in(q[i-1]),.D_out(q[i]));
             always@(*)begin
               MTIP_partial[i] = (q[i][15:0] == {16'h0080})? {1'b1}: {1'b0};
               aux_mux[i]=(count==i+1)?q[i]:{bits{1'b0}};
             end 
           `endif  
          end
       end
    end
  endgenerate

  generate
  for(i=0;i<depth-2;i=i+1)begin:_nu_
    always@(*)begin
      aux_mux_or[i]=aux_mux[i] | aux_mux_or[i+1];
    end
  end
  endgenerate

  always@(*)begin
    aux_mux_or[depth-2] <= aux_mux [depth-1]|aux_mux[depth-2];
    Dout <=aux_mux_or[0];  
    MTIP <= (MTIP_partial == 0)?{1'b0}: {1'b1};
  end

  always@(posedge clk)begin
  if(reset) begin
    count <= 0;
  end else begin
  
    case({push,pop})
      2'b00: count <= count;
      2'b01: begin
        if(count == 0) begin
          count <= 0;
        end else begin
          count <=count - 1;
        end
      end
      2'b10:begin
         if(count == depth)begin
           count <= count;
         end else begin
           count <= count+1;
        end
      end
      2'b11: count <= count;
    endcase
  end
  pndng <= (count==0)?{1'b0}:{1'b1};
//  full <=(count == depth)?{1'b1}:{1'b0};
end
endmodule


module mem_latch #(parameter bits= 32, parameter entradas = 10)(
  input [$clog2(entradas-1)-1:0] direcciones,
  input [bits-1:0]datos_in,
  input write,
  output [bits-1:0]datos_out
  ); 
  
  wire [bits-1:0]datos_out_entrada[entradas]; 
  wire [bits-1:0]datos_in_entrada[entradas]; 
  wire clk_entrada[entradas];
  wire [entradas-1:0] select_entrada;
    
  genvar b,d;
  generate
    for(d = 0; d < entradas; d=d+1) begin:_depth_
      for(b = 0; b < bits; b=b+1) begin:_bit_
        dltch Ram_latch(.data(datos_in[b]),.clk(clk_entrada[d]),.q(datos_out_entrada[d][b]));
      end
      assign select_entrada[d] = (direcciones == d)?1:0;
      assign clk_entrada[d] = select_entrada[d]&write;
      assign datos_out = (select_entrada[d])?datos_out_entrada[d]:{bits{1'bz}};
    end
  endgenerate

endmodule


module tri_buf (a,b,en);
    input a;
    output b;
    input en;
    wire a,en;
    wire b;
    
   assign b = (en) ? a : 1'bz;
     	  	 
endmodule

///////////////////////////////////////////////////////////////
// Definition of a serial to parallel signal converter block // 
//////////////////////////////////////////////////////////////

module parallel_serial (
  input S_in,
  input P_in,
  input sel_P_S,
  output S_out,
  output P_out   
  );

  tri_buf serial(.a(S_in),.b(S_out),.en(~sel_P_S));
  tri_buf parallel_in (.a(P_in),.b(S_out),.en(sel_P_S));
//to send Pot to hiz when sel_p_s = 0 enable the line below and disable the
//line after that one
//  tri_buf parallel_out (.a(S_in),.b(P_out),.en(sel_P_S)); 
  assign P_out = S_in;

endmodule

//////////////////////////////////////////////////////////////////////////////
// Definition of a register block which can be readed and writed either in //
// parallel or in series                                                   //
/////////////////////////////////////////////////////////////////////////////

module serializer #(parameter pckg_sz = 32) (
  input sel_p_s,
  input s_in,
  input rst,
  input clk,
  input [pckg_sz-1:0] P_in,
  output s_out,
  output [pckg_sz-1:0] P_out
  );
  wire [pckg_sz-1:0] q;
  wire [pckg_sz-1:0] d;

  genvar i;
  generate
    for ( i = 0; i < pckg_sz; i = i+1 )
      begin : _bit
        dff_async_rst dff (.data(d[i]),.clk(clk),.reset(rst),.q(q[i]));
      end
    for( i = 0; i < pckg_sz-1; i = i+1 )
      begin: bt
        parallel_serial pts (.S_in(q[i]),.P_in(P_in[i+1]),.sel_P_S(sel_p_s),.S_out(d[i+1]),.P_out(P_out[i]));
      end
  endgenerate
  assign d[0] = (sel_p_s)?P_in[0]:s_in;
  assign s_out =(~sel_p_s)?q[pckg_sz-1]:1'bz;
  assign P_out[pckg_sz-1] = q[pckg_sz-1];
endmodule

////////////////////////////////////////////////////////////////////////
// Definition of an in order counter from 0 to a parametrized number //
////////////////////////////////////////////////////////////////////////

module Counter#(parameter mx_cnt = 32) (count, clk, rst);
  output reg [$clog2(mx_cnt)-1:0] count;
  input clk;
  input rst;
 
     

  always @(posedge clk or posedge rst)
       if (rst)
           count = 0;
       else
         count = count + 1;
endmodule

//////////////////////////////////////////////////////////////////////////////
// Definition of the read state machine for the bus interconnect controller //
//////////////////////////////////////////////////////////////////////////////

module Read_st_Mchn (
  input condition_r,
  output reg rdi,
  input reset,
  input clk,
  output reg [1:0] s_ds_r,
  output reg s_cmp,
  output reg rst_cntr_r,
  output reg rst_r,
  output reg p_s_r,
  output reg en_r,
  output reg push
  );
  
  reg [2:0] nxt_st;
  wire [2:0] cur_st;
  //state registers
  dff_async_rst st0(.data(nxt_st[0]),.clk(clk),.reset(reset),.q(cur_st[0]));
  dff_async_rst st1(.data(nxt_st[1]),.clk(clk),.reset(reset),.q(cur_st[1]));
  dff_async_rst st2(.data(nxt_st[2]),.clk(clk),.reset(reset),.q(cur_st[2])); 
  
  //nextstate decoder
 always@(*) begin
  case ({cur_st,condition_r})
      4'b0001:  nxt_st = {3'b001}; 
      4'b0000:  nxt_st = {3'b001}; 
      4'b0011:  nxt_st = {3'b011}; 
      4'b0010:  nxt_st = {3'b001}; 
      4'b0111:  nxt_st = {3'b111}; 
      4'b0110:  nxt_st = {3'b011}; 
      4'b1011:  nxt_st = {3'b000}; 
      4'b1010:  nxt_st = {3'b000}; 
      4'b1101:  nxt_st = {3'b000}; 
      4'b1100:  nxt_st = {3'b000}; 
      4'b1111:  nxt_st = {3'b110}; 
      4'b1110:  nxt_st = {3'b101}; 
      default:  nxt_st = {3'b000};  
    endcase
  //Output Logic
  case(cur_st)
    3'b000: begin
            rdi = 1'b0;
            s_ds_r = 2'b00;
            s_cmp = 1'b1;
            rst_cntr_r = 1'b1;
            rst_r = 1'b1;
            p_s_r = 1'b0;
            en_r = 1'b0;
            push = 1'b0;
    end
    3'b001: begin
            rdi = 1'b1;
            s_ds_r = 2'b00;
            s_cmp = 1'b1;
            rst_cntr_r = 1'b0;
            rst_r = 1'b0;
            p_s_r = 1'b0;
            en_r = 1'b0;
            push = 1'b0;
    end
    3'b011: begin
            rdi = 1'b0;
            s_ds_r = 2'b10;
            s_cmp = 1'b1;
            rst_cntr_r = 1'b0;
            rst_r = 1'b0;
            p_s_r = 1'b0;
            en_r = 1'b1;
            push = 1'b0;
    end
    3'b111: begin
            rdi = 1'b0;
            s_ds_r = 2'b01;
            s_cmp = 1'b0;
            rst_cntr_r = 1'b0;
            rst_r = 1'b0;
            p_s_r = 1'b1;
            en_r = 1'b0;
            push = 1'b0;
    end
    3'b110: begin
            rdi = 1'b0;
            s_ds_r = 2'b00;
            s_cmp = 1'b0;
            rst_cntr_r = 1'b0;
            rst_r = 1'b0;
            p_s_r = 1'b1;
            en_r = 1'b0;
            push = 1'b1;
    end
    3'b101: begin
            rdi = 1'b0;
            s_ds_r = 2'b00;
            s_cmp = 1'b0;
            rst_cntr_r = 1'b0;
            rst_r = 1'b0;
            p_s_r = 1'b1;
            en_r = 1'b0;
            push = 1'b0;
    end
    default: begin
            rdi = 1'b0;
            s_ds_r = 2'b00;
            s_cmp = 1'b1;
            rst_cntr_r = 1'b1;
            rst_r = 1'b1;
            p_s_r = 1'b0;
            en_r = 1'b0;
            push = 1'b0;
    end
    endcase
    end
endmodule

///////////////////////////////////////////////////////////////////////////////
// Definition of the Write state machine for the bus interconnect controller //
///////////////////////////////////////////////////////////////////////////////

module  Write_st_Mchn(
  input clk,
  input reset,
  input condition_w,
  output reg bs_bsy,
  output reg bs_rqst,
  output reg [1:0] s_ds_w,
  output reg rst_cntr_w,
  output reg rst_w,
  output reg p_s_w,
  output reg en_w,
  output reg pop 
  );
 
  //state registers
  reg [2:0] nxt_st;
  wire [2:0] cur_st;
  
  dff_async_rst st0(.data(nxt_st[0]),.clk(clk),.reset(reset),.q(cur_st[0]));
  dff_async_rst st1(.data(nxt_st[1]),.clk(clk),.reset(reset),.q(cur_st[1]));
  dff_async_rst st2(.data(nxt_st[2]),.clk(clk),.reset(reset),.q(cur_st[2])); 

  //nextstate decoder
   always@(*) begin 
   case ({cur_st,condition_w})
      4'b0001:  nxt_st = 3'b001;
      4'b0000:  nxt_st = 3'b001;
      4'b0101:  nxt_st = 3'b100;
      4'b0100:  nxt_st = 3'b100;
      4'b0011:  nxt_st = 3'b011;
      4'b0010:  nxt_st = 3'b001;
      4'b0111:  nxt_st = 3'b111;
      4'b0110:  nxt_st = 3'b111;
      4'b1011:  nxt_st = 3'b010;
      4'b1010:  nxt_st = 3'b101;
      4'b1001:  nxt_st = 3'b000;
      4'b1000:  nxt_st = 3'b100;
      4'b1111:  nxt_st = 3'b101;
      4'b1110:  nxt_st = 3'b101;
      default:  nxt_st = 3'b000; 
    endcase
  //Output Logic
  case(cur_st)
    3'b000: begin
            bs_bsy = 1'b0;
            bs_rqst = 1'b0;
            s_ds_w  = 2'b10;
            rst_cntr_w = 1'b1;
            rst_w = 1'b1;
            p_s_w = 1'b1;
            en_w = 1'b0;
            pop = 1'b0;
    end
    3'b001: begin
            bs_bsy = 1'b0;
            bs_rqst = 1'b0;
            s_ds_w  = 2'b10;
            rst_cntr_w = 1'b0;
            rst_w = 1'b0;
            p_s_w = 1'b1;
            en_w = 1'b0;
            pop = 1'b0;
    end
    3'b010: begin
            bs_bsy = 1'b1;
            bs_rqst = 1'b1;
            s_ds_w  = 2'b00;
            rst_cntr_w = 1'b0;
            rst_w = 1'b0;
            p_s_w = 1'b0;
            en_w = 1'b0;
            pop = 1'b0;
    end
    3'b011: begin
            bs_bsy = 1'b0;
            bs_rqst = 1'b0;
            s_ds_w  = 2'b00;
            rst_cntr_w = 1'b1;
            rst_w = 1'b0;
            p_s_w = 1'b1;
            en_w = 1'b1;
            pop = 1'b0;
    end
    3'b111: begin
            bs_bsy = 1'b0;
            bs_rqst = 1'b1;
            s_ds_w  = 2'b00;
            rst_cntr_w = 1'b1;
            rst_w = 1'b0;
            p_s_w = 1'b0;
            en_w = 1'b0;
            pop = 1'b1;
    end
    3'b101: begin
            bs_bsy = 1'b0;
            bs_rqst = 1'b1;
            s_ds_w  = 2'b00;
            rst_cntr_w = 1'b0;
            rst_w = 1'b0;
            p_s_w = 1'b0;
            en_w = 1'b0;
            pop = 1'b0;
    end
    3'b100: begin
            bs_bsy = 1'b1;
            bs_rqst = 1'b1;
            s_ds_w  = 2'b01;
            rst_cntr_w = 1'b0;
            rst_w = 1'b0;
            p_s_w = 1'b0;
            en_w = 1'b1;
            pop = 1'b0;
    end
    default: begin
            bs_bsy = 1'b0;
            bs_rqst = 1'b0;
            s_ds_w  = 2'b10;
            rst_cntr_w = 1'b1;
            rst_w = 1'b1;
            p_s_w = 1'b1;
            en_w = 1'b0;
            pop = 1'b0;
    end
    endcase
    end
endmodule

//////////////////////////////////////////////////////////////////////////////
// Definition of Control block for the Bus controller 
/////////////////////////////////////////////////////////////////////////////

module ntrfs_cntrl #(parameter pckg_sz = 32, parameter ntrfs_id = 0, parameter broadcast = {8{1'b1}}) (
  input clk,
  input reset,
  input [pckg_sz-1:0] D_in,
  input bs_grnt,
  input pndng,
  inout bs_bsy,
  output bs_rqst,
  output rst_w,
  output rst_r,
  output p_s_w,
  output p_s_r,
  output en_w,
  output en_r,
  output push,
  output pop
  );
    wire [$clog2(pckg_sz):0] count_w;
    wire [$clog2(pckg_sz):0] count_r;
    wire [1:0] s_ds_r;
    wire [1:0] s_ds_w;
    reg cond_r;
    reg cond_w;
    wire rst_cntr_w;
    wire rst_cntr_r;
    wire rdi;
    wire clk_cntr_w = en_w && clk;
    wire clk_cntr_r = en_r && clk;
    wire cnt_eq_w = (count_w == pckg_sz)?{1'b1}:{1'b0};
    wire s_cmp;
    reg rd_cmp_out;
    reg bdcst;
    wire bs_bsy_pre;
    localparam aux = (pckg_sz > 256)?$clog2(pckg_sz)-1:7;
    reg [aux:0]  rd_cmp_a;
    reg [aux:0]  rd_cmp_b;

    always @(*) begin
       rd_cmp_a = (s_cmp)?count_r:D_in[pckg_sz-1:pckg_sz-8];
       rd_cmp_b = (s_cmp)?pckg_sz-1:ntrfs_id;
 
     rd_cmp_out = (rd_cmp_a == rd_cmp_b)?{1'b1}:{1'b0};   
     bdcst = (D_in[pckg_sz-1:pckg_sz-8]=={8{1'b1}})?{1'b1}:{1'b0};

    case(s_ds_r)
       2'b00:  cond_r = ~bs_grnt && bs_bsy;
       2'b01:  cond_r = rd_cmp_out || bdcst;
       2'b10:  cond_r = rd_cmp_out;
       default:  cond_r = 0;
    endcase

   case(s_ds_w)
       2'b00:  cond_w = bs_grnt && rdi;
       2'b01:  cond_w = cnt_eq_w;
       2'b10:  cond_w = pndng;
       default: cond_w = 0;
    endcase
    
//     bs_bsy_aux = (bs_grnt)?bs_bsy_pre:{1'bz};
end
    tri_buf bs_bsy_tri_buf (bs_bsy_pre,bs_bsy,bs_grnt);
    Counter #(pckg_sz*2) counter_w (.count(count_w), .clk(clk_cntr_w), .rst(rst_cntr_w));
    Counter #(pckg_sz*2) counter_r (.count(count_r), .clk(clk_cntr_r), .rst(rst_cntr_r));
  
    Read_st_Mchn rdstmchn (.condition_r(cond_r),
                           .rdi(rdi),
                           .reset(reset),
                           .clk(clk),
                           .s_ds_r(s_ds_r),
                           .s_cmp(s_cmp),
                           .rst_cntr_r(rst_cntr_r),
                           .rst_r(rst_r),
                           .p_s_r(p_s_r),
                           .en_r(en_r),
                           .push(push));

   Write_st_Mchn wtstmchn (.clk(clk),
                           .reset(reset),
                           .condition_w(cond_w),
                           .bs_bsy(bs_bsy_pre),
                           .bs_rqst(bs_rqst),
                           .s_ds_w(s_ds_w),
                           .rst_cntr_w(rst_cntr_w),
                           .rst_w(rst_w),
                           .p_s_w(p_s_w),
                           .en_w(en_w),
                           .pop(pop));
endmodule


//////////////////////////////////////////////////////////////////////////////
// Definition of a signle bus Interface 
/////////////////////////////////////////////////////////////////////////////

module bs_ntrfs #(parameter pckg_sz = 32, parameter ntrfs_id = 0, parameter broadcast = {8{1'b1}}) (
  input clk,
  input reset,
  input bs_grnt,
  input pndng,
  input [pckg_sz-1:0] D_pop,
  output [pckg_sz-1:0] D_push,
  output push,
  output pop,
  output bs_rqst,
  inout bus,
  inout bs_bsy
);

  wire clk_rd;
  wire clk_wt;
  wire en_r;
  wire en_w;
  assign clk_rd = clk && en_r;
  assign clk_wt = clk && en_w;
  wire rst_r;
  wire rst_w;
  wire p_s_w;
  wire p_s_r;
  wire bus_pre_wd;
  assign bus = (bs_grnt)?bus_pre_wd:1'bz;

  ntrfs_cntrl #(pckg_sz,ntrfs_id,broadcast) cntrl(
   .clk(clk),
   .reset(reset),
   .D_in(D_push),
   .bs_grnt(bs_grnt),
   .pndng(pndng),
   .bs_bsy(bs_bsy),
   .bs_rqst(bs_rqst),
   .rst_w(rst_w),
   .rst_r(rst_r),
   .p_s_w(p_s_w),
   .p_s_r(p_s_r),
   .en_w(en_w),
   .en_r(en_r),
   .push(push),
   .pop(pop)
  );

serializer #(pckg_sz) srlzr_wt(
   .sel_p_s(p_s_w),
   .s_in({1'b0}),
   .rst(rst_w),
   .clk(clk_wt),
   .P_in(D_pop),
   .s_out(bus_pre_wd),
   .P_out()
  );
serializer #(pckg_sz) srlzr_rd(
   .sel_p_s(p_s_r),
   .s_in(bus),
   .rst(rst_r),
   .clk(clk_rd),
   .P_in({pckg_sz{1'b0}}),
   .s_out(),
   .P_out(D_push)
  );
endmodule

///////////////////////////////////////////////////////////////////////
// Definition of an in order counter from 0 to a parametrized number //
// The difference from the module Counter is that this one will stop //
// at m-1 and reset to 0 while the other will keep counting until the//
// count bits overflow                                               //
///////////////////////////////////////////////////////////////////////

module Counter_arb#(parameter mx_cnt = 32) (count, clk, rst);
  output reg [$clog2(mx_cnt)-1:0] count;
  input clk;
  input rst;

 
     always @(posedge clk or posedge rst)begin
       if (rst)begin
           count <= 0;
       end else begin
         if(count == mx_cnt-1)begin
           count <= 0;
         end else begin
           count <= count + 1;
         end
       end
     end
endmodule


///////////////////////////////////////////////////////////////////////
// Definition of the Arbiter block 
///////////////////////////////////////////////////////////////////////

module Arbiter#(parameter M = 4)(
 input reset,
 input clk,
 input [M-1:0] bs_rqst,
 output reg  [M-1:0] bs_grnt,
 output reg bs_bsy
);

  wire [$clog2(M)-1:0] count;
  reg cntr_clk;
  reg cntr_clk_en;
  reg rqst_xst;
  reg [M-1:0] bs_rqst_flg;

  Counter_arb #(M) cntr_arb (.count(count), .clk(cntr_clk), .rst(reset));

//int i =0;
  genvar i;
  generate
//    for(i=0;i<M; i=i+1)
//    begin// : _bit
//      always @(*)
//      begin
      for(i=0;i<M; i=i+1)begin:_nu_
         always@(*)begin
         bs_rqst_flg[i] = (i == count)?{1'b1}:{1'b0};
         bs_grnt[i] = bs_rqst_flg[i] && bs_rqst[i];
      end
      end    
//    end
  endgenerate

  always @(*)
  begin
     rqst_xst <= (bs_rqst == 0)?{1'b0}:{1'b1};
     cntr_clk_en <= (bs_grnt == 0 )?{1'b1}:{1'b0}; 
     bs_bsy <=(bs_grnt == 0)?{1'b0}:{1'bz};
     cntr_clk <= clk && cntr_clk_en && rqst_xst;
  end
endmodule


///////////////////////////////////////////////////////////////////////
// Definition of the Top Bus System 
///////////////////////////////////////////////////////////////////////

module bs_gnrtr #(parameter drvrs = 4, parameter pckg_sz = 16, parameter broadcast = {8{1'b1}}) (
  input clk,
  input reset,
  input [drvrs-1:0] pndng,
  output [drvrs-1:0] push,
  output [drvrs-1:0] pop,
  input [drvrs-1:0][pckg_sz-1:0] D_pop,
  output [drvrs-1:0][pckg_sz-1:0] D_push
);
  wire bus;
  wire bs_bsy;
  wire [drvrs-1:0] bs_rqst;
  wire [drvrs-1:0] bs_grnt;
  
  genvar i;
  generate
    for (i=0; i < drvrs; i=i+1)
    begin: ID
      bs_ntrfs #(pckg_sz,i,broadcast) ntrfs (
        .clk(clk),
        .reset(reset),
        .bs_grnt(bs_grnt[i]),
        . pndng(pndng[i]),
        .D_pop(D_pop[i]),
        .D_push(D_push[i]),
        .push(push[i]),
        .pop(pop[i]),
        .bs_rqst(bs_rqst[i]),
        .bus(bus),
        .bs_bsy(bs_bsy)
      );
    end
  endgenerate
 
  Arbiter#(drvrs) arb_inst (.reset(reset),.clk(clk),.bs_rqst(bs_rqst),.bs_grnt(bs_grnt),.bs_bsy(bs_bsy));
endmodule


///////////////////////////////////////////////////////////////////////
// Libraries intendedn for the version of the bus with no central arbiter
// n_rbtr 
///////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Definition of the arbiter state machine
///////////////////////////////////////////////////////////////////////////////

module  Arbiter_st_Mchn(
  input clk,
  input reset,
  input condition_a,
  output trn_chng_nthng_t_snd 
  );
 
  //state registers
  reg  nxt_st;
  
  dff_async_rst st0(.data(nxt_st),.clk(clk),.reset(reset),.q(trn_chng_nthng_t_snd));

  //nextstate decoder
   always@(*) begin 
     case ({trn_chng_nthng_t_snd,condition_a})
      2'b00:  nxt_st = 1'b0;
      2'b01:  nxt_st = 1'b1;
      2'b10:  nxt_st = 1'b0;
      2'b11:  nxt_st = 1'b0;
     endcase
   end
endmodule

//////////////////////////////////////////////////////////////////////////////
// Definition of Control block for the Bus controller no central arbiter
// version 
/////////////////////////////////////////////////////////////////////////////

module ntrfs_cntrl_n_rbtr #(parameter pckg_sz = 32, 
                            parameter ntrfs_id = 0, 
                            parameter broadcast = {8{1'b1}},
                            parameter drvrs = 4) (
  input clk,
  input reset,
  input [pckg_sz-1:pckg_sz-8] D_in,
  output  bs_grnt,
  input pndng,
  inout  bs_bsy,
  inout trn_chng,
  output rst_w,
  output rst_r,
  output p_s_w,
  output p_s_r,
  output en_w,
  output en_r,
  output push,
  output pop
  );
    wire bs_rqst;
    reg trn_chng_pre;
    wire [$clog2(drvrs)-1:0] cnt_rbtr;
    wire [$clog2(pckg_sz):0] count_w;
    wire [$clog2(pckg_sz):0] count_r;
    wire [1:0] s_ds_r;
    wire [1:0] s_ds_w;
    reg cond_r;
    reg cond_w;
    wire rst_cntr_w;
    wire rst_cntr_r;
    wire rdi;
    wire clk_cntr_w = en_w && clk;
    wire clk_cntr_r = en_r && clk;
    wire cnt_eq_w = (count_w == pckg_sz)?{1'b1}:{1'b0};
    wire s_cmp;
    reg rd_cmp_out;
    reg bdcst;
    wire bs_bsy_pre;
    localparam aux = (pckg_sz > 256)?$clog2(pckg_sz)-1:7;
    reg [aux:0]  rd_cmp_a;
    reg [aux:0]  rd_cmp_b;
    reg c_a;    
    wire trn_chng_nthng_t_snd;
    reg bs_grnt_pre;

    always @(posedge clk)begin
      bs_grnt_pre = (cnt_rbtr == ntrfs_id)?{1'b1}:{1'b0};
    end
    
   dff_async_rst bs_grnt_dly(.data(bs_grnt_pre),.clk(clk),.reset(reset),.q(bs_grnt));

    always @(*) begin
       trn_chng_pre = rst_w|| trn_chng_nthng_t_snd;
       c_a = bs_grnt && ~bs_rqst;
       rd_cmp_a = (s_cmp)?count_r:D_in[pckg_sz-1:pckg_sz-8];
       rd_cmp_b = (s_cmp)?pckg_sz-1:ntrfs_id;
 
     rd_cmp_out = (rd_cmp_a == rd_cmp_b)?{1'b1}:{1'b0};   
     bdcst = (D_in[pckg_sz-1:pckg_sz-8]=={8{1'b1}})?{1'b1}:{1'b0};

    case(s_ds_r)
       2'b00:  cond_r = ~bs_grnt && bs_bsy;
       2'b01:  cond_r = rd_cmp_out || bdcst;
       2'b10:  cond_r = rd_cmp_out;
       default:  cond_r = 0;
    endcase

   case(s_ds_w)
       2'b00:  cond_w = bs_grnt && rdi;
       2'b01:  cond_w = cnt_eq_w;
       2'b10:  cond_w = pndng;
       default:  cond_w = 0;
    endcase
    
   //  bs_bsy_aux = (bs_grnt)?bs_bsy_pre:{1'bz};
   end
    tri_buf bs_bsy_tri_buf(.a(bs_bsy_pre),.b(bs_bsy),.en(bs_grnt));

    Counter_arb#(drvrs) arb_cntr(.count(cnt_rbtr),.clk(trn_chng),.rst(reset));
    Arbiter_st_Mchn arb_st_mchn (.clk(clk),.reset(reset),.condition_a(c_a),.trn_chng_nthng_t_snd(trn_chng_nthng_t_snd));
    Counter #(pckg_sz*2) counter_w (.count(count_w), .clk(clk_cntr_w), .rst(rst_cntr_w));
    Counter #(pckg_sz*2) counter_r (.count(count_r), .clk(clk_cntr_r), .rst(rst_cntr_r));
    tri_buf buf_trn_chng(.a(trn_chng_pre),.b(trn_chng),.en(bs_grnt));
  
    Read_st_Mchn rdstmchn (.condition_r(cond_r),
                           .rdi(rdi),
                           .reset(reset),
                           .clk(clk),
                           .s_ds_r(s_ds_r),
                           .s_cmp(s_cmp),
                           .rst_cntr_r(rst_cntr_r),
                           .rst_r(rst_r),
                           .p_s_r(p_s_r),
                           .en_r(en_r),
                           .push(push));

   Write_st_Mchn wtstmchn (.clk(clk),
                           .reset(reset),
                           .condition_w(cond_w),
                           .bs_bsy(bs_bsy_pre),
                           .bs_rqst(bs_rqst),
                           .s_ds_w(s_ds_w),
                           .rst_cntr_w(rst_cntr_w),
                           .rst_w(rst_w),
                           .p_s_w(p_s_w),
                           .en_w(en_w),
                           .pop(pop));
endmodule
//////////////////////////////////////////////////////////////////////////////
// Definition of a signle bus Interface No central arbiter version n_rbtr 
/////////////////////////////////////////////////////////////////////////////

module bs_ntrfs_n_rbtr #(parameter pckg_sz = 32, parameter ntrfs_id = 0, parameter broadcast = {8{1'b1}},parameter drvrs = 4)(
  input clk,
  input reset,
  input pndng,
  input [pckg_sz-1:0] D_pop,
  output [pckg_sz-1:0] D_push,
  output push,
  output pop,
  inout bus,
  inout bs_bsy,
  inout trn_chng
);
  wire bs_grnt;
  wire clk_rd;
  wire clk_wt;
  wire en_r;
  wire en_w;
  assign clk_rd = clk && en_r;
  assign clk_wt = clk && en_w;
  wire rst_r;
  wire rst_w;
  wire p_s_w;
  wire p_s_r;
  wire bus_pre_wd;
  assign bus = (bs_grnt)?bus_pre_wd:1'bz;

  ntrfs_cntrl_n_rbtr #(pckg_sz,ntrfs_id,broadcast,drvrs) cntrl(
   .clk(clk),
   .reset(reset),
   .D_in(D_push[pckg_sz-1:pckg_sz-8]),
   .bs_grnt(bs_grnt),
   .pndng(pndng),
   .bs_bsy(bs_bsy),
   .trn_chng(trn_chng),
   .rst_w(rst_w),
   .rst_r(rst_r),
   .p_s_w(p_s_w),
   .p_s_r(p_s_r),
   .en_w(en_w),
   .en_r(en_r),
   .push(push),
   .pop(pop)
  );

serializer #(pckg_sz) srlzr_wt(
   .sel_p_s(p_s_w),
   .s_in({1'b0}),
   .rst(rst_w),
   .clk(clk_wt),
   .P_in(D_pop),
   .s_out(bus_pre_wd),
   .P_out()
  );
serializer #(pckg_sz) srlzr_rd(
   .sel_p_s(p_s_r),
   .s_in(bus),
   .rst(rst_r),
   .clk(clk_rd),
   .P_in({pckg_sz{1'b0}}),
   .s_out(),
   .P_out(D_push)
  );
endmodule

///////////////////////////////////////////////////////////////////////
// Definition of the Top Bus System 
///////////////////////////////////////////////////////////////////////

module bs_gnrtr_n_rbtr #(parameter bits = 1,parameter drvrs = 4, parameter pckg_sz = 16, parameter broadcast = {8{1'b1}}) (
  input clk,
  input reset,
  input  pndng[bits-1:0][drvrs-1:0],
  output push[bits-1:0][drvrs-1:0],
  output pop[bits-1:0][drvrs-1:0],
  input  [pckg_sz-1:0] D_pop[bits-1:0][drvrs-1:0],
  output [pckg_sz-1:0] D_push[bits-1:0][drvrs-1:0]
);
  wire bus[bits-1:0];
  wire bs_bsy[bits-1:0];
  wire trn_chng[bits-1:0];
  
  genvar b;
  genvar i;
  generate
    for(b=0; b < bits; b=b+1)
    begin: BUS
      for (i=0; i < drvrs; i=i+1)
      begin: ID
        bs_ntrfs_n_rbtr #(pckg_sz,i,broadcast,drvrs) ntrfs (
          .clk(clk),
          .reset(reset),
          .pndng(pndng[b][i]),
          .D_pop(D_pop[b][i]),
          .D_push(D_push[b][i]),
          .push(push[b][i]),
          .pop(pop[b][i]),
          .bus(bus[b]),
          .trn_chng(trn_chng[b]),
          .bs_bsy(bs_bsy[b])
        );
      end
    end
  endgenerate
endmodule

///////////////////////////////////////////////////////////////////////
// Definition of a parallel bus 
///////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////
// Definition of a simple parallel n bits bus 
///////////////////////////////////////////////////////////////////////

module prll_rgstr #(parameter bits =32) (
  input clk,
  input [bits-1:0] D,
  input reset,
  output [bits-1:0] Q
);
  genvar i;
  generate
    for(i = 0 ;i < bits;i = i+1) begin: bit_
      dff_async_rst flop (.data(D[i]),.clk(clk),.reset(reset),.q(Q[i])); 
    end
  endgenerate
endmodule

///////////////////////////////////////////////////////////////////////
// Definition of the control state machine for the read of the parallel
// interfase 
///////////////////////////////////////////////////////////////////////

module prll_rd_st_mchn (
  input c_r,
  input reset,
  input clk,
  output reg rst_r,
  output reg push,
  output reg rdi,
  output reg s_ds_r
);
  wire [2:0] st; 
  reg [2:0] ft_st;

  dff_async_rst st_flop_0 (.data(ft_st[0]),.clk(clk),.reset(reset),.q(st[0]));
  dff_async_rst st_flop_1 (.data(ft_st[1]),.clk(clk),.reset(reset),.q(st[1]));
  dff_async_rst st_flop_2 (.data(ft_st[2]),.clk(clk),.reset(reset),.q(st[2]));
 
  always@(*)begin
    case({st,c_r})
      4'b0000: ft_st = {3'b001};
      4'b0001: ft_st = {3'b001};
      4'b0010: ft_st = {3'b001};
      4'b0011: ft_st = {3'b011};
      4'b0110: ft_st = {3'b010};
      4'b0111: ft_st = {3'b111};
      4'b1110: ft_st = {3'b000};
      4'b1111: ft_st = {3'b000};
      4'b0100: ft_st = {3'b000};
      4'b0101: ft_st = {3'b000};
      default: ft_st = {3'b000};
    endcase
    
    push = (st==7)?{1'b1}:{1'b0};
    rst_r = (st==0)?{1'b1}:{1'b0};
    rdi = (st==1)?{1'b1}:{1'b0};
    s_ds_r = (st==3)?{1'b1}:{1'b0};
    
  end
endmodule

///////////////////////////////////////////////////////////////////////
// Definition of the control state machine for the write of the parallel
// interfase 
///////////////////////////////////////////////////////////////////////

module prll_wt_st_mchn (
  input c_w,
  input reset,
  input clk,
  output reg rst_w,
  output reg pop,
  output reg wrt_pre,
  output reg s_ds_w,
  output reg bs_rqst,
  output reg ld_w
);
  wire [2:0] st; 
  wire c_r;
  reg [2:0] ft_st;

  dff_async_rst st_flop_0 (.data(ft_st[0]),.clk(clk),.reset(reset),.q(st[0]));
  dff_async_rst st_flop_1 (.data(ft_st[1]),.clk(clk),.reset(reset),.q(st[1]));
  dff_async_rst st_flop_2 (.data(ft_st[2]),.clk(clk),.reset(reset),.q(st[2]));
 
  always@(*)begin
    case({st,c_w})
      4'b0000: ft_st = {3'b001};
      4'b0001: ft_st = {3'b001};
      4'b0010: ft_st = {3'b001};
      4'b0011: ft_st = {3'b011};
      4'b0110: ft_st = {3'b111};
      4'b0111: ft_st = {3'b111};
      4'b1110: ft_st = {3'b101};
      4'b1111: ft_st = {3'b101};
      4'b1010: ft_st = {3'b101};
      4'b1011: ft_st = {3'b100};
      4'b1000: ft_st = {3'b000};
      4'b1001: ft_st = {3'b000};
      default: ft_st = {3'b000};
    endcase
    
    pop = (st==7)?{1'b1}:{1'b0};
    rst_w = (st==0)?{1'b1}:{1'b0};
    s_ds_w = (st==1)?{1'b1}:{1'b0};
    wrt_pre = (st==4)?{1'b1}:{1'b0};
    bs_rqst = ((st==4)||(st==5)||(st==7))?{1'b1}:{1'b0};
    ld_w = (st==3)?{1'b1}:{1'b0};
    
  end
endmodule

///////////////////////////////////////////////////////////////////////
// Definition of the control interfase for the prll bus 
///////////////////////////////////////////////////////////////////////

module prll_intrfs_cntrl #(parameter id = 0, parameter bdcst = 255, parameter drvrs = 4) (
  input clk,
  input reset,
  input [7:0] D_in,
  input pndng,
  output ld_w,
  output rst_w,
  output rst_r,
  output bs_grnt,
  output push,
  output pop,
  inout trn_chng,
  inout wrt
);
  reg c_r;
  reg bs_grnt_pre;
  reg c_w;
  reg sv_flg;
  reg c_a;
  wire s_ds_r;
  wire s_ds_w;
  reg  trn_chng_pre;
  reg  wt_flg;
  reg rd_flg;
  wire trn_chng_nthng_t_snd;
  wire wrt_pre;
  wire bs_rqst;
  wire rdi;
  wire [$clog2(drvrs)-1:0] cnt_rbtr;
  
  dff_async_rst bs_grnt_dly (.data(bs_grnt_pre),.clk(clk),.reset(reset),.q(bs_grnt));
  Counter_arb#(drvrs) arb_cntr(.count(cnt_rbtr),.clk(trn_chng),.rst(reset));
  Arbiter_st_Mchn arb_st_mchn (.clk(clk),.reset(reset),.condition_a(c_a),.trn_chng_nthng_t_snd(trn_chng_nthng_t_snd));
   prll_wt_st_mchn wt_st_mchn(.c_w(c_w),.reset(reset),.clk(clk),.rst_w(rst_w),.pop(pop),.wrt_pre(wrt_pre),.s_ds_w(s_ds_w),.bs_rqst(bs_rqst),.ld_w(ld_w));
   prll_rd_st_mchn rd_st_mchn(.c_r(c_r),.reset(reset),.clk(clk),.rst_r(rst_r),.push(push),.rdi(rdi),.s_ds_r(s_ds_r));
   tri_buf trn_chng_buf(.a(trn_chng_pre),.b(trn_chng),.en(bs_grnt_pre));
   tri_buf wrt_buf(.a(wrt_pre),.b(wrt),.en(bs_grnt_pre));

  always@(*)begin
    wt_flg = rdi && bs_grnt;
    c_w = (s_ds_w)?pndng:wt_flg;
    trn_chng_pre = trn_chng_nthng_t_snd || rst_w;
    rd_flg = wrt && ~bs_grnt;
    sv_flg = ((D_in==id)||(D_in==bdcst))?{1'b1}:{1'b0};
    c_r = (s_ds_r)?sv_flg:rd_flg;
    bs_grnt_pre = (cnt_rbtr == id)?{1'b1}:{1'b0};
    c_a = bs_grnt && ~bs_rqst;
  end
endmodule


///////////////////////////////////////////////////////////////////////
// Definition of the prll bus interface 
///////////////////////////////////////////////////////////////////////

module prll_bs_ntrfs #(parameter drvrs = 4, parameter bits = 32, parameter id = 0,parameter bdcst = 255)(
  output [bits-1:0] D_push,
  input pndng,
  input clk,
  input reset,
  inout [bits-1:0] bus,
  inout trn_chng,
  inout wrt,
  output pop,
  output push,
  input [bits-1:0] D_pop
);
  wire rst_r;
  wire rst_w;
  wire ld_w;
  wire bs_grnt;
  wire [bits-1:0] bus_pre_w;
  reg ld_r;

  prll_d_reg #(bits) D_reg_rd(.clk(ld_r),.reset(rst_r),.D_in(bus),.D_out(D_push));
  prll_d_reg #(bits) D_reg_wt(.clk(ld_w),.reset(rst_w),.D_in(D_pop),.D_out(bus_pre_w));
  prll_intrfs_cntrl #(id,bdcst,drvrs) prll_cntrl(.clk(clk),
						 .reset(reset),
						 .D_in(D_push[bits-1:bits-8]),
						 .pndng(pndng),
 						 .ld_w(ld_w),
						 .rst_w(rst_w),
   						 .rst_r(rst_r),
						 .bs_grnt(bs_grnt),
						 .push(push),
						 .pop(pop),
						 .trn_chng(trn_chng),
						 .wrt(wrt));
  genvar i;
  generate
    for(i=0;i<bits;i=i+1) begin:bit_
     tri_buf bus_buf (.a(bus_pre_w[i]),.b(bus[i]),.en(bs_grnt)); 
    end
  endgenerate

  always@(*)begin
    ld_r <= ~bs_grnt && wrt;
    
  end
endmodule

///////////////////////////////////////////////////////////////////////
// Definition of the prll bus system
///////////////////////////////////////////////////////////////////////
  
module prll_bs_gnrtr_n_rbtr #(parameter buses = 1,parameter bits = 1,parameter drvrs = 4, parameter broadcast = {8{1'b1}}) (
  input clk,
  input reset,
  input  pndng[buses-1:0][drvrs-1:0],
  output push[buses-1:0][drvrs-1:0],
  output pop[buses-1:0][drvrs-1:0],
  input  [bits-1:0] D_pop[buses-1:0][drvrs-1:0],
  output [bits-1:0] D_push[buses-1:0][drvrs-1:0]
);
  wire [bits-1:0] bus[buses-1:0];
  wire trn_chng[buses-1:0];
  wire wrt[buses-1:0];
  
  genvar b;
  genvar i;
  generate
    for(b=0; b < buses; b=b+1)begin:_bus_ 
      for(i=0;i<drvrs;i=i+1)begin:ntrfs 
        prll_bs_ntrfs #(drvrs,bits,i,broadcast) prll_bus_instance (
        .D_push(D_push[b][i]),
        .pndng(pndng[b][i]),
        .clk(clk),
        .reset(reset),
        .bus(bus[b]),
        .trn_chng(trn_chng[b]),
        .wrt(wrt[b]),
        .pop(pop[b][i]),
        .push(push[b][i]),
        .D_pop(D_pop[b][i])
        );
      end
//        always@(*) begin
          assign bus[b]= reset?{bits{1'b0}}:{bits{1'bz}};
//          assign trn_chng[b] = reset?{bits{1'b0}}:{bits{1'bz}};
//          assign wrt[b] = reset?{bits{1'b0}}:{bits{1'bz}};
//        end
    end
  endgenerate
endmodule

///////////////////////////////////////////////////////////////////////
// Definition of the prll bus system with homogeneus fifos
///////////////////////////////////////////////////////////////////////
  
module prll_bs_gnrtr_n_rbtr_fifo #(parameter buses = 1,parameter bits = 1,parameter drvrs = 4, parameter broadcast = {8{1'b1}},parameter depth = 2) (
  input clk,
  input reset,
  output pndng[buses-1:0][drvrs-1:0],
  input  push[buses-1:0][drvrs-1:0],
  input  pop[buses-1:0][drvrs-1:0],
  output [bits-1:0] D_pop[buses-1:0][drvrs-1:0],
  input  [bits-1:0] D_push[buses-1:0][drvrs-1:0],
  output full_in[buses-1:0][drvrs-1:0],
  output full_out[buses-1:0][drvrs-1:0]
);
  wire  pndng_int[buses-1:0][drvrs-1:0];
  wire  push_int[buses-1:0][drvrs-1:0];
  wire  pop_int[buses-1:0][drvrs-1:0];
  wire  [bits-1:0] D_in_int [buses-1:0][drvrs-1:0];
  wire  [bits-1:0] D_out_int [buses-1:0][drvrs-1:0];

  
  genvar b;
  genvar i;
  generate
    for(b=0; b < buses; b=b+1)begin:_bus_ 
      for(i=0;i<drvrs;i=i+1)begin:ntrfs 
        fifo_flops #(.depth(depth),.bits(bits)) fifo_in(
          .Din(D_push[b][i]),
          .Dout(pop_int[b][i]),
          .push(push[b][i]),
          .pop(pop_int[b][i]),
          .full(full_in[b][i]),
          .pndng(pndng_int[b][i]),
          .rst(reset),
          .clk(clk)
        );
     
        fifo_flops #(.depth(depth),.bits(bits)) fifo_out(
          .Din(D_in_int[b][i]),
          .Dout(D_pop[b][i]),
          .push(push_int[b][i]),
          .pop(pop[b][i]),
          .full(full_out[b][i]),
          .pndng(pndng[b][i]),
          .rst(reset),
          .clk(clk)
        );
        
      end
    end
  endgenerate

   prll_bs_gnrtr_n_rbtr #(.buses(buses),.bits(bits),.drvrs(drvrs),.broadcast(broadcast)) bus_interfase (
    .clk(clk),
    .reset(reset),
    .pndng(pndng_int),
    .push(push_int),
    .pop(pop_int),
    .D_pop(D_out_int),
    .D_push(D_in_int)
  );
endmodule

module conector #(parameter size = 40) (
  input  [size-1:0] in,
  output [size-1:0] out
);

  genvar i;
  generate
    for(i=0;i<size;i=i+1) begin
      buf(out[i],in[i]);
    end
  endgenerate
endmodule

module router_bus_gnrtr #(parameter pck_sz = 40, parameter num_ntrfs=4, parameter broadcast = {8{1'b1}}, parameter fifo_depth=4,parameter id_c = 0,parameter id_r = 0,parameter columns= 4, parameter rows = 4)(
  input clk,
  input reset,
  input[pck_sz-1:0] data_out_i_in[num_ntrfs-1:0],
  input pndng_i_in[num_ntrfs-1:0],
  input pop[num_ntrfs-1:0],
  output popin[num_ntrfs-1:0],
  output pndng[num_ntrfs-1:0],
  output [pck_sz-1:0] data_out[num_ntrfs-1:0]
);
  wire pop_i;
  wire push_i;
  wire [num_ntrfs-1:0]pndng_i;
  wire [pck_sz-1:0] data_out_i[num_ntrfs-1:0];
  wire [$clog2(num_ntrfs)-1:0]trn;
  wire [pck_sz-1:0] data_in_i;
  
  genvar i;
  generate
    for(i=0;i<num_ntrfs; i=i+1)begin:_nu_
      router_bus_interface #(.pck_sz(pck_sz),.num_ntrfs(num_ntrfs), .ntrfs_id(i),.broadcast(broadcast),.fifo_depth(fifo_depth),.id_c(id_c),.id_r(id_r),.rows(rows), .columns(columns)) rtr_ntrfs_ (
        .clk(clk),
        .reset(reset),
        .data_in_i(data_in_i),
        .trn(trn),
        .pop(pop[i]),
        .pop_i(pop_i),
        .push_i(push_i),
        .data_out_i(data_out_i[i]),
        .data_out_i_in(data_out_i_in[i]),
        .data_out(data_out[i]),
        .pndng(pndng[i]),
        .pndng_i(pndng_i[i]),
        .popin(popin[i]),
        .pndng_i_in(pndng_i_in[i])
    );
    end
  endgenerate
  Router_arbiter #(.num_ntrfs(num_ntrfs),.pck_sz(pck_sz)) arbitro(
  .reset(reset),
  .clk(clk),
  .pndng_i(pndng_i),
  .data_out_i(data_out_i),
  .trn(trn),
  .push_i(push_i),
  .pop_i(pop_i),
  .data_in_i(data_in_i)
);
endmodule 


module router_bus_interface #(parameter pck_sz = 40, parameter num_ntrfs=4, parameter [7:0]ntrfs_id = 0, parameter broadcast = {8{1'b1}}, parameter fifo_depth=4, parameter id_c=0,parameter id_r=0, parameter rows= 4, parameter columns=4) (
  input clk,
  input reset,
  input [pck_sz-1:0]data_in_i,
  input [$clog2(num_ntrfs)-1:0]trn,
  input pop_i,
  input push_i,
  input pop,
  output [pck_sz-1:0]data_out_i,
  input [pck_sz-1:0]data_out_i_in,
  output [pck_sz-1:0]data_out,
  output pndng,
  output pndng_i,
  output logic popin,
  input pndng_i_in
  );
  logic pre_psh;
  logic pre_pop;
  logic psh;

  fifo_flops_no_full #(.depth(fifo_depth),.bits(pck_sz))fifo_out (
    .Din(data_in_i),
    .Dout(data_out),
    .push(psh),
    .pop(pop),
    .clk(clk),
    .pndng(pndng),
    .rst(reset)
  );
  
  s_routing_table #(.id_r(id_r),.id_c(id_c),.pckg_sz(pck_sz), .rows(rows),.columns(columns)) rt (
  .Data_in(data_out_i_in),
  .Data_out_i(data_out_i)
);

`ifdef DEBUG
  always@(posedge pop) begin
    $display("ntrfs: Message send in terminal: %g router ID: %g %g at time %g", ntrfs_id,id_r,id_c,$time );
    $display("trgt_r: %g", data_out[pck_sz-9:pck_sz-12]);
    $display("trgt_c: %g", data_out[pck_sz-13:pck_sz-16]);
    $display("mode: %g",data_out[pck_sz-17]);
    $display("src: %g",data_out[pck_sz-18:pck_sz-25]);
    $display("id: %g",data_out[pck_sz-26:pck_sz-33]);
    $display("pyld: %h",data_out[pck_sz-34:0]);
  end
  always@(posedge popin) begin
    $display("ntrfs: Message received  in terminal: %g router ID: %g %g at time %g", ntrfs_id,id_r,id_c,$time );
    $display("trgt_r: %g", data_out_i_in[pck_sz-9:pck_sz-12]);
    $display("trgt_c: %g", data_out_i_in[pck_sz-13:pck_sz-16]);
    $display("mode: %g",data_out_i_in[pck_sz-17]);
    $display("src: %g",data_out_i_in[pck_sz-18:pck_sz-25]);
    $display("id: %g",data_out_i_in[pck_sz-26:pck_sz-33]);
    $display("pyld: %h",data_out_i_in[pck_sz-34:0]);
  end
`endif

  assign psh = pre_psh & push_i;
  assign popin = pre_pop & pop_i;
  assign pre_psh = ((ntrfs_id == data_in_i[pck_sz-1:pck_sz-8])|(data_in_i[pck_sz-1:pck_sz-8]== broadcast))?1:0; 
  assign pre_pop = (ntrfs_id == trn)?1:0;
  assign pndng_i = pndng_i_in;
  
endmodule

module rtr_rbtr_cntrl (
  input clk,
  input rst,
  input pndng,
  output logic cnt_en,
  output logic push_i,
  output logic pop_i
);
 reg [1:0]cur_st;
 logic [1:0]nxt_st;
 parameter rst_st = 0;
 parameter psh1_st = 1;
 parameter cnt1_st = 2;
 parameter pop1_st = 3;
 
 //lógica de siguiente estado
 always_comb begin
   case(cur_st)
     rst_st: begin
       nxt_st <= pndng?psh1_st:cnt1_st;
     end 
     psh1_st: nxt_st <= pop1_st;
     pop1_st: nxt_st <= cnt1_st;
     cnt1_st: nxt_st <= rst_st;
     default: nxt_st <= rst;
  endcase
 end
 //refrescamiento de la máquina de estados
 always@(posedge clk or posedge rst) begin
   cur_st <= rst?rst_st:nxt_st;
 end
 // lógica de salida
 always_comb begin
  case(cur_st)
    rst_st: begin
      cnt_en <= 0;
      push_i <= 0;
      pop_i <= 0;
    end
    psh1_st: begin
      cnt_en <= 0;
      push_i <= 1;
      pop_i <= 0;
    end
    pop1_st: begin
      cnt_en <= 0;
      push_i <= 0;
      pop_i <= 1;
    end
    cnt1_st: begin
      cnt_en <=1;
      push_i <= 0;
      pop_i <= 0;
    end
  endcase
 end

endmodule

module tri_buf_mux #(parameter size =8) (
    input [size-1:0]a,
    output [size-1:0]b,
    input en
);
    
   assign b = (en)?a:{size{1'bz}};
     	  	 
endmodule

module param_mux #(parameter num_slct_lns = 2, parameter pck_sz = 4) (
  input  [num_slct_lns-1:0] select,
  input  [pck_sz-1:0]input_signal[(2**num_slct_lns)-1:0],
  output [pck_sz-1:0] out
);
  logic hot_bit_slct[(2**num_slct_lns)-1:0];
  genvar i;
  generate
      for(i=0;i<(2**num_slct_lns); i=i+1)begin:_nu_
         always_comb begin
           hot_bit_slct[i] <= (i == select)?{1'b1}:{1'b0};
         end
           tri_buf_mux #(.size(pck_sz)) buf_select (.a(input_signal[i]),.b(out),.en(hot_bit_slct[i])); 
      end    
  endgenerate
endmodule

module param_mux_single_bit #(parameter num_slct_lns = 2) (
  input  [num_slct_lns-1:0] select,
  input  [(2**num_slct_lns)-1:0]input_signal,
  output out
);
  logic hot_bit_slct[(2**num_slct_lns)-1:0];
  genvar i;
  generate
      for(i=0;i<(2**num_slct_lns); i=i+1)begin:_nu_
         always_comb begin
           hot_bit_slct[i] <= (i == select)?{1'b1}:{1'b0};
         end
           tri_buf buf_select (.a(input_signal[i]),.b(out),.en(hot_bit_slct[i])); 
      end    
  endgenerate
endmodule

module Router_arbiter #(parameter num_ntrfs=4, parameter pck_sz = 32) (
  input reset,
  input clk,
  input [num_ntrfs-1:0]pndng_i,
  input [pck_sz-1:0]data_out_i[num_ntrfs-1:0],
  output [$clog2(num_ntrfs)-1:0]trn,
  output push_i,
  output pop_i,
  output [pck_sz-1:0]data_in_i
);
  logic clk_cntr;
  logic clk_rtr_rbtr_cntrl;
  logic clk_en;
  logic cnt_en;
  wire pndng;

Counter_arb #(.mx_cnt(num_ntrfs)) contador(
  .count(trn), 
  .clk(clk_cntr), 
  .rst(reset)
 );

  always_comb begin
    clk_cntr <= clk_rtr_rbtr_cntrl & cnt_en;
    clk_rtr_rbtr_cntrl <= clk & clk_en;
    clk_en <= (pndng_i == 0)?0:1;
  end

 
param_mux_single_bit #(.num_slct_lns($clog2(num_ntrfs))) pndng_mx(
 .select(trn),
 .input_signal(pndng_i),
 .out(pndng)
);

param_mux #(.num_slct_lns($clog2(num_ntrfs)),.pck_sz(pck_sz)) data_mx(
 .select(trn),
 .input_signal(data_out_i),
 .out(data_in_i)
);
  
rtr_rbtr_cntrl arbitro (
  .clk(clk_rtr_rbtr_cntrl),
  .rst(reset),
  .pndng(pndng),
  .cnt_en(cnt_en),
  .push_i(push_i),
  .pop_i(pop_i)
);
endmodule

module s_routing_table #(parameter id_r =0, parameter id_c = 0, parameter pckg_sz =32, parameter columns=4, parameter rows=4) (
  input [pckg_sz-1:0] Data_in,
  output logic [pckg_sz-1:0] Data_out_i
);
  always_comb begin
    Data_out_i[pckg_sz-9:0] <= Data_in[pckg_sz-9:0];
    if((id_r != rows)&(id_r != 1)&(id_c != columns)&(id_c != 1)) begin // si se trata de un router que no está en el marco limítrofe
      if(Data_in[pckg_sz-17]) begin //si el modo es 1 entonces rutea primero fila
        if(Data_in[pckg_sz-9:pckg_sz-12] < id_r) begin
          Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd0;
        end
        if(Data_in[pckg_sz-9: pckg_sz-12] > id_r) begin
          Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd2;
        end
        if(Data_in[pckg_sz-9: pckg_sz-12] == id_r) begin
          if(Data_in[pckg_sz-13: pckg_sz-16] < id_c) begin
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd3;
          end
          if(Data_in[pckg_sz-13: pckg_sz-16] > id_c) begin
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd1;
          end
          if(Data_in[pckg_sz-13: pckg_sz-16]== id_c) begin
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd4;
          end
        end
      end else begin // si el modo es 0 rutea primero columna
        if(Data_in[pckg_sz-13: pckg_sz-16] < id_c) begin
          Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd3;
        end
        if(Data_in[pckg_sz-13: pckg_sz-16] > id_c) begin
          Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd1;
        end
        if(Data_in[pckg_sz-13: pckg_sz-16] == id_c) begin
          if(Data_in[pckg_sz-9: pckg_sz-12] < id_r) begin
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd0;
          end
          if(Data_in[pckg_sz-9: pckg_sz-12] > id_r) begin
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd2;
          end
          if(Data_in[pckg_sz-9: pckg_sz-12] == id_r) begin
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd4;
          end
        end
      end
    end else begin // si se trata de un router que está en el marco limítrofe
      if(((Data_in[pckg_sz-9:pckg_sz-12] < id_r)&(id_r == 1))| 
         ((Data_in[pckg_sz-9:pckg_sz-12] > id_r)&(id_r == rows))| 
         ((Data_in[pckg_sz-13:pckg_sz-16] < id_c)&(id_c == 1))| 
         ((Data_in[pckg_sz-13:pckg_sz-16] > id_c)&(id_c == columns))) begin // si es un caso de salida del mesh

        if((Data_in[pckg_sz-9:pckg_sz-12] < id_r)&(id_r == 1)) begin // si está en el borde superior y la fila es menor
          if(Data_in[pckg_sz-13: pckg_sz-16] == id_c) begin // si está en la columna correcta
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd0;
          end
          if(Data_in[pckg_sz-13: pckg_sz-16] < id_c)begin // si está en una columna mayor
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd3;
          end
          if(Data_in[pckg_sz-13: pckg_sz-16] > id_c)begin // si está en una columna menor
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd1;
          end
        end
        if((Data_in[pckg_sz-9:pckg_sz-12] > id_r)&(id_r == rows)) begin // si está en el borde inferior y la fila es mayor
          if(Data_in[pckg_sz-13: pckg_sz-16] == id_c) begin // si está en la columna correcta
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd2;
          end
          if(Data_in[pckg_sz-13: pckg_sz-16] < id_c)begin // si está en una columna mayor
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd3;
          end
          if(Data_in[pckg_sz-13: pckg_sz-16] > id_c)begin // si está en una columna menor
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd1;
          end
        end
        if((Data_in[pckg_sz-13:pckg_sz-16] < id_c)&(id_c == 1)) begin // si está en el borde izquierdo y la columna es menor
          if(Data_in[pckg_sz-9: pckg_sz-12] == id_r) begin // si está en la fila correcta
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd3;
          end
          if(Data_in[pckg_sz-9: pckg_sz-12] < id_r)begin // si está en una fila mayor
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd0;
          end
          if(Data_in[pckg_sz-9: pckg_sz-12] > id_r)begin // si está en una fila menor
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd2;
          end
        end
        if((Data_in[pckg_sz-13:pckg_sz-16] > id_c)&(id_c == columns)) begin // si está en el borde derecho y la columna es mayor
          if(Data_in[pckg_sz-9: pckg_sz-12] == id_r) begin // si está en la fila correcta
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd1;
          end
          if(Data_in[pckg_sz-9: pckg_sz-12] < id_r)begin // si está en una fila mayor
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd0;
          end
          if(Data_in[pckg_sz-9: pckg_sz-12] > id_r)begin // si está en una fila menor
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd2;
          end
        end
      end else begin // si no es un caso de salida
        if(Data_in[pckg_sz-17]) begin //si el modo es 1 entonces rutea primero fila
          if(Data_in[pckg_sz-9:pckg_sz-12] < id_r) begin
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd0;
          end
          if(Data_in[pckg_sz-9: pckg_sz-12] > id_r) begin
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd2;
          end
          if(Data_in[pckg_sz-9: pckg_sz-12] == id_r) begin
            if(Data_in[pckg_sz-13: pckg_sz-16] < id_c) begin
              Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd3;
            end
            if(Data_in[pckg_sz-13: pckg_sz-16] > id_c) begin
              Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd1;
            end
            if(Data_in[pckg_sz-13: pckg_sz-16]== id_c) begin
              Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd4;
            end
          end
        end else begin // si el modo es 0 rutea primero columna
          if(Data_in[pckg_sz-13: pckg_sz-16] < id_c) begin
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd3;
          end
          if(Data_in[pckg_sz-13: pckg_sz-16] > id_c) begin
            Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd1;
          end
          if(Data_in[pckg_sz-13: pckg_sz-16] == id_c) begin
            if(Data_in[pckg_sz-9: pckg_sz-12] < id_r) begin
              Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd0;
            end
            if(Data_in[pckg_sz-9: pckg_sz-12] > id_r) begin
              Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd2;
            end
            if(Data_in[pckg_sz-9: pckg_sz-12] == id_r) begin
              Data_out_i[pckg_sz-1:pckg_sz-8] <= 8'd4;
            end
          end
        end
      end
    end 
  end 
endmodule

module mesh_gnrtr #(parameter ROWS = 4, parameter COLUMS =4, parameter pckg_sz =40, parameter fifo_depth = 4, parameter bdcst= {8{1'b1}})(
  output logic pndng[ROWS*2+COLUMS*2],
  output [pckg_sz-1:0] data_out[ROWS*2+COLUMS*2],
  output logic popin[ROWS*2+COLUMS*2],
  input pop[ROWS*2+COLUMS*2],
  input [pckg_sz-1:0]data_out_i_in[ROWS*2+COLUMS*2],
  input pndng_i_in[ROWS*2+COLUMS*2],
  input clk,
  input reset
);
// vertical connections (not including connections to agents) 
  wire pndng_ver_2_0 [ROWS-1][COLUMS];
  wire [pckg_sz-1:0] data_out_ver_2_0 [ROWS-1][COLUMS];
  wire pop_ver_2_0 [ROWS-1][COLUMS];
  wire popin_ver_2_0 [ROWS-1][COLUMS];

  wire pndng_ver_0_2 [ROWS-1][COLUMS];
  wire [pckg_sz-1:0] data_out_ver_0_2 [ROWS-1][COLUMS];
  wire pop_ver_0_2 [ROWS-1][COLUMS];
  wire popin_ver_0_2 [ROWS-1][COLUMS];
// horizontal connections (not including connections to agents) 
  wire pndng_hor_1_3 [ROWS][COLUMS-1];
  wire [pckg_sz-1:0] data_out_hor_1_3 [ROWS][COLUMS-1];
  wire pop_hor_1_3 [ROWS][COLUMS-1];
  wire popin_hor_1_3 [ROWS][COLUMS-1];

  wire pndng_hor_3_1 [ROWS][COLUMS-1];
  wire [pckg_sz-1:0] data_out_hor_3_1 [ROWS][COLUMS-1];
  wire pop_hor_3_1 [ROWS][COLUMS-1];
  wire popin_hor_3_1 [ROWS][COLUMS-1];
 
  genvar R, C;
  generate
    for(R=1;R <= ROWS; R=R+1)begin:_rw_
      for(C=1;C <= COLUMS; C=C+1)begin:_clm_
        wire [pckg_sz-1:0] data_out_connected[3:0];
        wire [pckg_sz-1:0]data_out_i_in_connected [3:0];
        wire pndng_i_in_connected[3:0];
        wire pndng_connected[3:0];
        wire pop_connected[3:0];
        wire popin_connected[3:0];
        if(R == 1) begin
          if(C == 1) begin //upper left corner
              //UP
              conector #(.size(pckg_sz)) buf_data_out_0 (.out(data_out[0]),.in(data_out_connected[0]));
              conector #(.size(1)) buf_pndng_0 (.out(pndng[0]),.in(pndng_connected[0]));
              conector #(.size(1)) buf_popin_0 (.out(popin[0]),.in(popin_connected[0]));

              conector #(.size(1)) buf_pop_0 (.out(pop_connected[0]),.in(pop[0]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_0 (.out(data_out_i_in_connected[0]),.in(data_out_i_in[0]));
              conector #(.size(1)) buf_pndng_i_in_0 (.out(pndng_i_in_connected[0]),.in(pndng_i_in[0]));
              //LEFT
              conector #(.size(pckg_sz)) buf_data_out_3 (.out(data_out[COLUMS]),.in( data_out_connected[3]));
              conector #(.size(1)) buf_pndng_3 (.out(pndng[COLUMS]),.in(pndng_connected[3]));
              conector #(.size(1)) buf_popin_3 (.out(popin[COLUMS]),.in(popin_connected[3]));

              conector #(.size(1)) buf_pop_3 (.out(pop_connected[3]),.in(pop[COLUMS]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_3 (.out(data_out_i_in_connected[3]),.in(data_out_i_in[COLUMS]));
              conector #(.size(1)) buf_pndng_i_in_3 (.out(pndng_i_in_connected[3]),.in(pndng_i_in[COLUMS]));
              //RIGHT
              conector #(.size(pckg_sz)) buf_data_out_1 (.out(data_out_hor_1_3[R-1][C-1]),.in(data_out_connected[1]));
              conector #(.size(1)) buf_pndng_1 (.out(pndng_hor_1_3[R-1][C-1]),.in(pndng_connected[1]));
              conector #(.size(1)) buf_popin_1 (.out(popin_hor_1_3[R-1][C-1]),.in(popin_connected[1]));

              conector #(.size(1)) buf_pop_1 (.out(pop_connected[1]),.in(popin_hor_3_1[R-1][C-1]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_1 (.out(data_out_i_in_connected[1]),.in(data_out_hor_3_1[R-1][C-1]));
              conector #(.size(1)) buf_pndng_i_in_1 (.out(pndng_i_in_connected[1]),.in(pndng_hor_3_1[R-1][C-1]));
              //DOWN
              conector #(.size(pckg_sz)) buf_data_out_2 (.out(data_out_ver_2_0[R-1][C-1]),.in(data_out_connected[2]));
              conector #(.size(1)) buf_pndng_2 (.out(pndng_ver_2_0[R-1][C-1]),.in(pndng_connected[2]));
              conector #(.size(1)) buf_popin_2 (.out(popin_ver_2_0[R-1][C-1]),.in(popin_connected[2]));

              conector #(.size(1)) buf_pop_2 (.out(pop_connected[2]),.in(popin_ver_0_2[R-1][C-1]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_2 (.out(data_out_i_in_connected[2]),.in(data_out_ver_0_2[R-1][C-1]));
              conector #(.size(1)) buf_pndng_i_in_2 (.out(pndng_i_in_connected[2]),.in(pndng_ver_0_2[R-1][C-1]));
          end
          if(C ==COLUMS) begin //upper rigth corner
              //UP
              conector #(.size(pckg_sz)) buf_data_out_0 (.out(data_out[COLUMS-1]),.in(data_out_connected[0]));
              conector #(.size(1)) buf_pndng_0 (.out(pndng[COLUMS-1]),.in(pndng_connected[0]));
              conector #(.size(1)) buf_popin_0 (.out(popin[COLUMS-1]),.in(popin_connected[0]));

              conector #(.size(1)) buf_pop_0 (.out(pop_connected[0]),.in(pop[COLUMS-1]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_0 (.out(data_out_i_in_connected[0]),.in(data_out_i_in[COLUMS-1]));
              conector #(.size(1)) buf_pndng_i_in_0 (.out(pndng_i_in_connected[0]),.in( pndng_i_in[COLUMS-1]));
              //RIGHT
              conector #(.size(pckg_sz)) buf_data_out_1 (.out(data_out[2*COLUMS+ROWS] ),.in( data_out_connected[1]));
              conector #(.size(1)) buf_pndng_1 (.out(pndng[2*COLUMS+ROWS] ),.in( pndng_connected[1]));
              conector #(.size(1)) buf_popin_1 (.out(popin[2*COLUMS+ROWS] ),.in(popin_connected[1]));

              conector #(.size(1)) buf_pop_1 (.out(pop_connected[1] ),.in(pop[2*COLUMS+ROWS]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_1 (.out(data_out_i_in_connected[1]),.in(data_out_i_in[2*COLUMS+ROWS]));
              conector #(.size(1)) buf_pndng_i_in_1 (.out(pndng_i_in_connected[1]),.in( pndng_i_in[2*COLUMS+ROWS]));
              //LEFT
              conector #(.size(pckg_sz)) buf_data_out_3 (.out(data_out_hor_3_1[R-1][C-2] ),.in( data_out_connected[3]));
              conector #(.size(1)) buf_pndng_3 (.out(pndng_hor_3_1[R-1][C-2] ),.in( pndng_connected[3]));
              conector #(.size(1)) buf_popin_3 (.out(popin_hor_3_1[R-1][C-2] ),.in(popin_connected[3]));

              conector #(.size(1)) buf_pop_3 (.out(pop_connected[3] ),.in(popin_hor_1_3[R-1][C-2]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_3 (.out(data_out_i_in_connected[3]),.in(data_out_hor_1_3[R-1][C-2]));
              conector #(.size(1)) buf_pndng_i_in_3 (.out(pndng_i_in_connected[3]),.in( pndng_hor_1_3[R-1][C-2]));
              //DOWN
              conector #(.size(pckg_sz)) buf_data_out_2 (.out(data_out_ver_2_0[R-1][C-1] ),.in( data_out_connected[2]));
              conector #(.size(1)) buf_pndng_2 (.out(pndng_ver_2_0[R-1][C-1] ),.in( pndng_connected[2]));
              conector #(.size(1)) buf_popin_2 (.out(popin_ver_2_0[R-1][C-1] ),.in(popin_connected[2]));

              conector #(.size(1)) buf_pop_2 (.out(pop_connected[2] ),.in(popin_ver_0_2[R-1][C-1]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_2 (.out(data_out_i_in_connected[2]),.in(data_out_ver_0_2[R-1][C-1]));
              conector #(.size(1)) buf_pndng_i_in_2 (.out(pndng_i_in_connected[2]),.in( pndng_ver_0_2[R-1][C-1]));
          end
          if((C != COLUMS)&&(C != 1)) begin // First row (not corners)
              //UP
              conector #(.size(pckg_sz)) buf_data_out_0 (.out(data_out[C-1] ),.in( data_out_connected[0]));
              conector #(.size(1)) buf_pndng_0 (.out(pndng[C-1] ),.in( pndng_connected[0]));
              conector #(.size(1)) buf_popin_0 (.out(popin[C-1] ),.in(popin_connected[0]));

              conector #(.size(1)) buf_pop_0 (.out(pop_connected[0] ),.in(pop[C-1]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_0 (.out(data_out_i_in_connected[0]),.in(data_out_i_in[C-1]));
              conector #(.size(1)) buf_pndng_i_in_0 (.out(pndng_i_in_connected[0]),.in( pndng_i_in[C-1]));
              //LEFT
              conector #(.size(pckg_sz)) buf_data_out_3 (.out(data_out_hor_3_1[R-1][C-2] ),.in( data_out_connected[3]));
              conector #(.size(1)) buf_pndng_3 (.out(pndng_hor_3_1[R-1][C-2] ),.in( pndng_connected[3]));
              conector #(.size(1)) buf_popin_3 (.out(popin_hor_3_1[R-1][C-2] ),.in(popin_connected[3]));

              conector #(.size(1)) buf_pop_3 (.out(pop_connected[3] ),.in(popin_hor_1_3[R-1][C-2]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_3 (.out(data_out_i_in_connected[3]),.in(data_out_hor_1_3[R-1][C-2]));
              conector #(.size(1)) buf_pndng_i_in_3 (.out(pndng_i_in_connected[3]),.in( pndng_hor_1_3[R-1][C-2]));
              //RIGHT
              conector #(.size(pckg_sz)) buf_data_out_1 (.out(data_out_hor_1_3[R-1][C-1] ),.in( data_out_connected[1]));
              conector #(.size(1)) buf_pndng_1 (.out(pndng_hor_1_3[R-1][C-1] ),.in( pndng_connected[1]));
              conector #(.size(1)) buf_popin_1 (.out(popin_hor_1_3[R-1][C-1] ),.in(popin_connected[1]));

              conector #(.size(1)) buf_pop_1 (.out(pop_connected[1] ),.in(popin_hor_3_1[R-1][C-1]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_1 (.out(data_out_i_in_connected[1]),.in(data_out_hor_3_1[R-1][C-1]));
              conector #(.size(1)) buf_pndng_i_in_1 (.out(pndng_i_in_connected[1]),.in( pndng_hor_3_1[R-1][C-1]));
              //DOWN
              conector #(.size(pckg_sz)) buf_data_out_2 (.out(data_out_ver_2_0[R-1][C-1] ),.in( data_out_connected[2]));
              conector #(.size(1)) buf_pndng_2 (.out(pndng_ver_2_0[R-1][C-1] ),.in( pndng_connected[2]));
              conector #(.size(1)) buf_popin_2 (.out(popin_ver_2_0[R-1][C-1] ),.in(popin_connected[2]));

              conector #(.size(1)) buf_pop_2 (.out(pop_connected[2] ),.in(popin_ver_0_2[R-1][C-1]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_2 (.out(data_out_i_in_connected[2]),.in(data_out_ver_0_2[R-1][C-1]));
              conector #(.size(1)) buf_pndng_i_in_2 (.out(pndng_i_in_connected[2]),.in( pndng_ver_0_2[R-1][C-1]));
          end
        end
        if(R == ROWS) begin
          if(C == 1) begin //bottom left corner
              //UP
              conector #(.size(pckg_sz)) buf_data_out_0 (.out(data_out_ver_0_2[R-2][C-1] ),.in( data_out_connected[0]));
              conector #(.size(1)) buf_pndng_0 (.out(pndng_ver_0_2[R-2][C-1] ),.in( pndng_connected[0]));
              conector #(.size(1)) buf_popin_0 (.out(popin_ver_0_2[R-2][C-1] ),.in(popin_connected[0]));

              conector #(.size(1)) buf_pop_0 (.out(pop_connected[0] ),.in(popin_ver_2_0[R-2][C-1]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_0 (.out(data_out_i_in_connected[0]),.in(data_out_ver_2_0[R-2][C-1]));
              conector #(.size(1)) buf_pndng_i_in_0 (.out(pndng_i_in_connected[0]),.in( pndng_ver_2_0[R-2][C-1]));
              //LEFT
              conector #(.size(pckg_sz)) buf_data_out_3 (.out(data_out[COLUMS+ROWS-1] ),.in( data_out_connected[3]));
              conector #(.size(1)) buf_pndng_3 (.out(pndng[COLUMS+ROWS-1] ),.in( pndng_connected[3]));
              conector #(.size(1)) buf_popin_3 (.out(popin[COLUMS+ROWS-1] ),.in(popin_connected[3]));
              conector #(.size(1)) buf_pop_3 (.out(pop_connected[3] ),.in(pop[COLUMS+ROWS-1]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_3 (.out(data_out_i_in_connected[3]),.in(data_out_i_in[COLUMS+ROWS-1]));
              conector #(.size(1)) buf_pndng_i_in_3 (.out(pndng_i_in_connected[3]),.in( pndng_i_in[COLUMS+ROWS-1]));
              //RIGHT
              conector #(.size(pckg_sz)) buf_data_out_1 (.out(data_out_hor_1_3[R-1][C-1] ),.in( data_out_connected[1]));
              conector #(.size(1)) buf_pndng_1 (.out(pndng_hor_1_3[R-1][C-1] ),.in( pndng_connected[1]));
              conector #(.size(1)) buf_popin_1 (.out(popin_hor_1_3[R-1][C-1] ),.in(popin_connected[1]));

              conector #(.size(1)) buf_pop_1 (.out(pop_connected[1] ),.in(popin_hor_3_1[R-1][C-1]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_1 (.out(data_out_i_in_connected[1]),.in(data_out_hor_3_1[R-1][C-1]));
              conector #(.size(1)) buf_pndng_i_in_1 (.out(pndng_i_in_connected[1]),.in( pndng_hor_3_1[R-1][C-1]));
              //DOWN
              conector #(.size(pckg_sz)) buf_data_out_2 (.out(data_out[COLUMS+ROWS] ),.in( data_out_connected[2]));
              conector #(.size(1)) buf_pndng_2 (.out(pndng[COLUMS+ROWS] ),.in( pndng_connected[2]));
              conector #(.size(1)) buf_popin_2 (.out(popin[COLUMS+ROWS] ),.in(popin_connected[2]));

              conector #(.size(1)) buf_pop_2 (.out(pop_connected[2] ),.in(pop[COLUMS+ROWS]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_2 (.out(data_out_i_in_connected[2]),.in(data_out_i_in[COLUMS+ROWS]));
              conector #(.size(1)) buf_pndng_i_in_2 (.out(pndng_i_in_connected[2]),.in( pndng_i_in[COLUMS+ROWS]));
          end
          if(C == COLUMS) begin //bottom rigth corner
              //UP
              conector #(.size(pckg_sz)) buf_data_out_0 (.out(data_out_ver_0_2[R-2][C-1] ),.in( data_out_connected[0]));
              conector #(.size(1)) buf_pndng_0 (.out(pndng_ver_0_2[R-2][C-1] ),.in( pndng_connected[0]));
              conector #(.size(1)) buf_popin_0 (.out(popin_ver_0_2[R-2][C-1] ),.in(popin_connected[0]));

              conector #(.size(1)) buf_pop_0 (.out(pop_connected[0] ),.in(popin_ver_2_0[R-2][C-1]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_0 (.out(data_out_i_in_connected[0]),.in(data_out_ver_2_0[R-2][C-1]));
              conector #(.size(1)) buf_pndng_i_in_0 (.out(pndng_i_in_connected[0]),.in( pndng_ver_2_0[R-2][C-1]));
              //LEFT
              conector #(.size(pckg_sz)) buf_data_out_3 (.out(data_out_hor_3_1[R-1][C-2] ),.in( data_out_connected[3]));
              conector #(.size(1)) buf_pndng_3 (.out(pndng_hor_3_1[R-1][C-2] ),.in( pndng_connected[3]));
              conector #(.size(1)) buf_popin_3 (.out(popin_hor_3_1[R-1][C-2] ),.in(popin_connected[3]));

              conector #(.size(1)) buf_pop_3 (.out(pop_connected[3] ),.in(popin_hor_1_3[R-1][C-2]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_3 (.out(data_out_i_in_connected[3]),.in(data_out_hor_1_3[R-1][C-2]));
              conector #(.size(1)) buf_pndng_i_in_3 (.out(pndng_i_in_connected[3]),.in( pndng_hor_1_3[R-1][C-2]));
              //RIGHT
              conector #(.size(pckg_sz)) buf_data_out_1 (.out(data_out[2*COLUMS+2*ROWS-1] ),.in( data_out_connected[1]));
              conector #(.size(1)) buf_pndng_1 (.out(pndng[2*COLUMS+2*ROWS-1] ),.in( pndng_connected[1]));
              conector #(.size(1)) buf_popin_1 (.out(popin[2*COLUMS+2*ROWS-1] ),.in(popin_connected[1]));
              conector #(.size(1)) buf_pop_1 (.out(pop_connected[1] ),.in(pop[2*COLUMS+2*ROWS-1]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_1 (.out(data_out_i_in_connected[1]),.in(data_out_i_in[2*COLUMS+2*ROWS-1]));
              conector #(.size(1)) buf_pndng_i_in_1 (.out(pndng_i_in_connected[1]),.in( pndng_i_in[2*COLUMS+2*ROWS-1]));
              //DOWN
              conector #(.size(pckg_sz)) buf_data_out_2 (.out(data_out[2*COLUMS+ROWS-1] ),.in( data_out_connected[2]));
              conector #(.size(1)) buf_pndng_2 (.out(pndng[2*COLUMS+ROWS-1] ),.in( pndng_connected[2]));
              conector #(.size(1)) buf_popin_2 (.out(popin[2*COLUMS+ROWS-1] ),.in(popin_connected[2]));
              conector #(.size(1)) buf_pop_2 (.out(pop_connected[2] ),.in(pop[2*COLUMS+ROWS-1]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_2 (.out(data_out_i_in_connected[2]),.in(data_out_i_in[2*COLUMS+ROWS-1]));
              conector #(.size(1)) buf_pndng_i_in_2 (.out(pndng_i_in_connected[2]),.in( pndng_i_in[2*COLUMS+ROWS-1]));
          end
          if((C != COLUMS)&&(C != 1)) begin //Last row (not corners)
              //UP
              conector #(.size(pckg_sz)) buf_data_out_0 (.out(data_out_ver_0_2[R-2][C-1] ),.in( data_out_connected[0]));
              conector #(.size(1)) buf_pndng_0 (.out(pndng_ver_0_2[R-2][C-1] ),.in( pndng_connected[0]));
              conector #(.size(1)) buf_popin_0 (.out(popin_ver_0_2[R-2][C-1] ),.in(popin_connected[0]));

              conector #(.size(1)) buf_pop_0 (.out(pop_connected[0] ),.in(popin_ver_2_0[R-2][C-1]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_0 (.out(data_out_i_in_connected[0]),.in(data_out_ver_2_0[R-2][C-1]));
              conector #(.size(1)) buf_pndng_i_in_0 (.out(pndng_i_in_connected[0]),.in( pndng_ver_2_0[R-2][C-1]));
              //LEFT
              conector #(.size(pckg_sz)) buf_data_out_3 (.out(data_out_hor_3_1[R-1][C-2] ),.in( data_out_connected[3]));
              conector #(.size(1)) buf_pndng_3 (.out(pndng_hor_3_1[R-1][C-2] ),.in( pndng_connected[3]));
              conector #(.size(1)) buf_popin_3 (.out(popin_hor_3_1[R-1][C-2] ),.in(popin_connected[3]));

              conector #(.size(1)) buf_pop_3 (.out(pop_connected[3] ),.in(popin_hor_1_3[R-1][C-2]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_3 (.out(data_out_i_in_connected[3]),.in(data_out_hor_1_3[R-1][C-2]));
              conector #(.size(1)) buf_pndng_i_in_3 (.out(pndng_i_in_connected[3]),.in( pndng_hor_1_3[R-1][C-2]));
              //RIGHT
              conector #(.size(pckg_sz)) buf_data_out_1 (.out(data_out_hor_1_3[R-1][C-1] ),.in( data_out_connected[1]));
              conector #(.size(1)) buf_pndng_1 (.out(pndng_hor_1_3[R-1][C-1] ),.in( pndng_connected[1]));
              conector #(.size(1)) buf_popin_1 (.out(popin_hor_1_3[R-1][C-1] ),.in(popin_connected[1]));

              conector #(.size(1)) buf_pop_1 (.out(pop_connected[1] ),.in(popin_hor_3_1[R-1][C-1]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_1 (.out(data_out_i_in_connected[1]),.in(data_out_hor_3_1[R-1][C-1]));
              conector #(.size(1)) buf_pndng_i_in_1 (.out(pndng_i_in_connected[1]),.in( pndng_hor_3_1[R-1][C-1]));
              //DOWN
              conector #(.size(pckg_sz)) buf_data_out_2 (.out(data_out[COLUMS+ROWS-1+C] ),.in( data_out_connected[2]));
              conector #(.size(1)) buf_pndng_2 (.out(pndng[COLUMS+ROWS-1+C] ),.in( pndng_connected[2]));
              conector #(.size(1)) buf_popin_2 (.out(popin[COLUMS+ROWS-1+C] ),.in(popin_connected[2]));

              conector #(.size(1)) buf_pop_2 (.out(pop_connected[2] ),.in(pop[COLUMS+ROWS-1+C]));
              conector #(.size(pckg_sz)) buf_data_out_i_in_2 (.out(data_out_i_in_connected[2]),.in(data_out_i_in[COLUMS+ROWS-1+C]));
              conector #(.size(1)) buf_pndng_i_in_2 (.out(pndng_i_in_connected[2]),.in( pndng_i_in[COLUMS+ROWS-1+C]));
          end
        end 
        if((C == 1)&&(R != 1)&&(R != ROWS))begin //First colum (Not corners)
            //UP
            conector #(.size(pckg_sz)) buf_data_out_0 (.out(data_out_ver_0_2[R-2][C-1] ),.in( data_out_connected[0]));
            conector #(.size(1)) buf_pndng_0 (.out(pndng_ver_0_2[R-2][C-1] ),.in( pndng_connected[0]));
            conector #(.size(1)) buf_popin_0 (.out(popin_ver_0_2[R-2][C-1] ),.in(popin_connected[0]));

            conector #(.size(1)) buf_pop_0 (.out(pop_connected[0] ),.in(popin_ver_2_0[R-2][C-1]));
            conector #(.size(pckg_sz)) buf_data_out_i_in_0 (.out(data_out_i_in_connected[0]),.in(data_out_ver_2_0[R-2][C-1]));
            conector #(.size(1)) buf_pndng_i_in_0 (.out(pndng_i_in_connected[0]),.in( pndng_ver_2_0[R-2][C-1]));
            //LEFT
            conector #(.size(pckg_sz)) buf_data_out_3 (.out(data_out[COLUMS+R-1] ),.in( data_out_connected[3]));
            conector #(.size(1)) buf_pndng_3 (.out(pndng[COLUMS+R-1] ),.in( pndng_connected[3]));
            conector #(.size(1)) buf_popin_3 (.out(popin[COLUMS+R-1] ),.in(popin_connected[3]));

            conector #(.size(1)) buf_pop_3 (.out(pop_connected[3] ),.in(pop[COLUMS+R-1]));
            conector #(.size(pckg_sz)) buf_data_out_i_in_3 (.out(data_out_i_in_connected[3]),.in(data_out_i_in[COLUMS+R-1]));
            conector #(.size(1)) buf_pndng_i_in_3 (.out(pndng_i_in_connected[3]),.in( pndng_i_in[COLUMS+R-1]));
            //RIGHT
            conector #(.size(pckg_sz)) buf_data_out_1 (.out(data_out_hor_1_3[R-1][C-1] ),.in( data_out_connected[1]));
            conector #(.size(1)) buf_pndng_1 (.out(pndng_hor_1_3[R-1][C-1] ),.in( pndng_connected[1]));
            conector #(.size(1)) buf_popin_1 (.out(popin_hor_1_3[R-1][C-1] ),.in(popin_connected[1]));

            conector #(.size(1)) buf_pop_1 (.out(pop_connected[1] ),.in(popin_hor_3_1[R-1][C-1]));
            conector #(.size(pckg_sz)) buf_data_out_i_in_1 (.out(data_out_i_in_connected[1]),.in(data_out_hor_3_1[R-1][C-1]));
            conector #(.size(1)) buf_pndng_i_in_1 (.out(pndng_i_in_connected[1]),.in( pndng_hor_3_1[R-1][C-1]));
            //DOWN
            conector #(.size(pckg_sz)) buf_data_out_2 (.out(data_out_ver_2_0[R-1][C-1] ),.in( data_out_connected[2]));
            conector #(.size(1)) buf_pndng_2 (.out(pndng_ver_2_0[R-1][C-1] ),.in( pndng_connected[2]));
            conector #(.size(1)) buf_popin_2 (.out(popin_ver_2_0[R-1][C-1] ),.in(popin_connected[2]));

            conector #(.size(1)) buf_pop_2 (.out(pop_connected[2] ),.in(popin_ver_0_2[R-1][C-1]));
            conector #(.size(pckg_sz)) buf_data_out_i_in_2 (.out(data_out_i_in_connected[2]),.in(data_out_ver_0_2[R-1][C-1]));
            conector #(.size(1)) buf_pndng_i_in_2 (.out(pndng_i_in_connected[2]),.in( pndng_ver_0_2[R-1][C-1]));
        end
        if((C == COLUMS)&&(R != 1)&&(R != ROWS))begin //Last colum (Not corners)
            //UP
            conector #(.size(pckg_sz)) buf_data_out_0 (.out(data_out_ver_0_2[R-2][C-1] ),.in( data_out_connected[0]));
            conector #(.size(1)) buf_pndng_0 (.out(pndng_ver_0_2[R-2][C-1] ),.in( pndng_connected[0]));
            conector #(.size(1)) buf_popin_0 (.out(popin_ver_0_2[R-2][C-1] ),.in(popin_connected[0]));

            conector #(.size(1)) buf_pop_0 (.out(pop_connected[0] ),.in(popin_ver_2_0[R-2][C-1]));
            conector #(.size(pckg_sz)) buf_data_out_i_in_0 (.out(data_out_i_in_connected[0]),.in(data_out_ver_2_0[R-2][C-1]));
            conector #(.size(1)) buf_pndng_i_in_0 (.out(pndng_i_in_connected[0]),.in( pndng_ver_2_0[R-2][C-1]));
            //DOWN
            conector #(.size(pckg_sz)) buf_data_out_2 (.out(data_out_ver_2_0[R-1][C-1] ),.in( data_out_connected[2]));
            conector #(.size(1)) buf_pndng_2 (.out(pndng_ver_2_0[R-1][C-1] ),.in( pndng_connected[2]));
            conector #(.size(1)) buf_popin_2 (.out(popin_ver_2_0[R-1][C-1] ),.in(popin_connected[2]));

            conector #(.size(1)) buf_pop_2 (.out(pop_connected[2] ),.in(popin_ver_0_2[R-1][C-1]));
            conector #(.size(pckg_sz)) buf_data_out_i_in_2 (.out(data_out_i_in_connected[2]),.in(data_out_ver_0_2[R-1][C-1]));
            conector #(.size(1)) buf_pndng_i_in_2 (.out(pndng_i_in_connected[2]),.in( pndng_ver_0_2[R-1][C-1]));
            //LEFT
            conector #(.size(pckg_sz)) buf_data_out_3 (.out(data_out_hor_3_1[R-1][C-2] ),.in( data_out_connected[3]));
            conector #(.size(1)) buf_pndng_3 (.out(pndng_hor_3_1[R-1][C-2] ),.in( pndng_connected[3]));
            conector #(.size(1)) buf_popin_3 (.out(popin_hor_3_1[R-1][C-2] ),.in(popin_connected[3]));

            conector #(.size(1)) buf_pop_3 (.out(pop_connected[3] ),.in(popin_hor_1_3[R-1][C-2]));
            conector #(.size(pckg_sz)) buf_data_out_i_in_3 (.out(data_out_i_in_connected[3]),.in(data_out_hor_1_3[R-1][C-2]));
            conector #(.size(1)) buf_pndng_i_in_3 (.out(pndng_i_in_connected[3]),.in( pndng_hor_1_3[R-1][C-2]));
            //RIGHT
            conector #(.size(pckg_sz)) buf_data_out_1 (.out(data_out[2*COLUMS+ROWS-1+R] ),.in( data_out_connected[1]));
            conector #(.size(1)) buf_pndng_1 (.out(pndng[2*COLUMS+ROWS-1+R] ),.in( pndng_connected[1]));
            conector #(.size(1)) buf_popin_1 (.out(popin[2*COLUMS+ROWS-1+R] ),.in(popin_connected[1]));

            conector #(.size(1)) buf_pop_1 (.out(pop_connected[1] ),.in(pop[2*COLUMS+ROWS-1+R]));
            conector #(.size(pckg_sz)) buf_data_out_i_in_1 (.out(data_out_i_in_connected[1]),.in(data_out_i_in[2*COLUMS+ROWS-1+R]));
            conector #(.size(1)) buf_pndng_i_in_1 (.out(pndng_i_in_connected[1]),.in( pndng_i_in[2*COLUMS+ROWS-1+R]));
        end
        if((C != COLUMS)&&(C != 1)&&(R != 1)&&(R != ROWS))begin //Every router not connected to an agent
            //UP
            conector #(.size(pckg_sz)) buf_data_out_0 (.out(data_out_ver_0_2[R-2][C-1] ),.in( data_out_connected[0]));
            conector #(.size(1)) buf_pndng_0 (.out(pndng_ver_0_2[R-2][C-1] ),.in( pndng_connected[0]));
            conector #(.size(1)) buf_popin_0 (.out(popin_ver_0_2[R-2][C-1] ),.in(popin_connected[0]));

            conector #(.size(1)) buf_pop_0 (.out(pop_connected[0] ),.in(popin_ver_2_0[R-2][C-1]));
            conector #(.size(pckg_sz)) buf_data_out_i_in_0 (.out(data_out_i_in_connected[0] ),.in(data_out_ver_2_0[R-2][C-1]));
            conector #(.size(1)) buf_pndng_i_in_0 (.out(pndng_i_in_connected[0]),.in( pndng_ver_2_0[R-2][C-1]));
            //DOWN
            conector #(.size(pckg_sz)) buf_data_out_2 (.out(data_out_ver_2_0[R-1][C-1] ),.in( data_out_connected[2]));
            conector #(.size(1)) buf_pndng_2 (.out(pndng_ver_2_0[R-1][C-1] ),.in( pndng_connected[2]));
            conector #(.size(1)) buf_popin_2 (.out(popin_ver_2_0[R-1][C-1] ),.in(popin_connected[2]));

            conector #(.size(1)) buf_pop_2 (.out(pop_connected[2] ),.in(popin_ver_0_2[R-1][C-1]));
            conector #(.size(pckg_sz)) buf_data_out_i_in_2 (.out(data_out_i_in_connected[2]),.in(data_out_ver_0_2[R-1][C-1]));
            conector #(.size(1)) buf_pndng_i_in_2 (.out(pndng_i_in_connected[2]),.in( pndng_ver_0_2[R-1][C-1]));
            //LEFT
            conector #(.size(pckg_sz)) buf_data_out_3 (.out(data_out_hor_3_1[R-1][C-2] ),.in( data_out_connected[3]));
            conector #(.size(1)) buf_pndng_3 (.out(pndng_hor_3_1[R-1][C-2] ),.in( pndng_connected[3]));
            conector #(.size(1)) buf_popin_3 (.out(popin_hor_3_1[R-1][C-2] ),.in(popin_connected[3]));

            conector #(.size(1)) buf_pop_3 (.out(pop_connected[3] ),.in(popin_hor_1_3[R-1][C-2]));
            conector #(.size(pckg_sz)) buf_data_out_i_in_3 (.out(data_out_i_in_connected[3]),.in(data_out_hor_1_3[R-1][C-2]));
            conector #(.size(1)) buf_pndng_i_in_3 (.out(pndng_i_in_connected[3]),.in( pndng_hor_1_3[R-1][C-2]));
            //RIGHT
            conector #(.size(pckg_sz)) buf_data_out_1 (.out(data_out_hor_1_3[R-1][C-1] ),.in( data_out_connected[1]));
            conector #(.size(1)) buf_pndng_1 (.out(pndng_hor_1_3[R-1][C-1] ),.in( pndng_connected[1]));
            conector #(.size(1)) buf_popin_1 (.out(popin_hor_1_3[R-1][C-1] ),.in(popin_connected[1]));

            conector #(.size(1)) buf_pop_1 (.out(pop_connected[1] ),.in(popin_hor_3_1[R-1][C-1]));
            conector #(.size(pckg_sz)) buf_data_out_i_in_1 (.out(data_out_i_in_connected[1]),.in(data_out_hor_3_1[R-1][C-1]));
            conector #(.size(1)) buf_pndng_i_in_1 (.out(pndng_i_in_connected[1]),.in( pndng_hor_3_1[R-1][C-1]));
        end
          router_bus_gnrtr #(.pck_sz(pckg_sz),.num_ntrfs(4),.broadcast(bdcst),.fifo_depth(fifo_depth),.id_c(C),.id_r(R),.columns(COLUMS),.rows(ROWS)) rtr(
            .clk(clk),
            .reset(reset),
            .data_out_i_in(data_out_i_in_connected),
            .pndng_i_in(pndng_i_in_connected),
            .pop(pop_connected),
            .popin(popin_connected),
            .pndng(pndng_connected),
            .data_out(data_out_connected)
          );
          
      end
    end
  endgenerate
endmodule

/////////////////////////////////////////////////
// Implementación del bus paralelo con arbitro //
/////////////////////////////////////////////////

module prll_bus_interface_cn_rbtr #(parameter pck_sz = 40, parameter num_ntrfs=4, parameter [7:0]ntrfs_id = 0, parameter broadcast = {8{1'b1}}) (
  input clk,
  input reset,
  input [pck_sz-1:0]data_in_i,
  input [$clog2(num_ntrfs)-1:0]trn,
  input pop_i,
  input push_i,
  output logic [pck_sz-1:0]data_out_i,
  input [pck_sz-1:0]D_pop,
  output [pck_sz-1:0]D_push,
  output logic pndng_i,
  output logic pop,
  input pndng,
  output logic push
  );
  logic pre_psh;
  logic pre_pop;

  assign push = pre_psh & push_i;
  assign pop = pre_pop & pop_i;
  assign pre_psh = ((ntrfs_id == data_in_i[pck_sz-1:pck_sz-8])|(data_in_i[pck_sz-1:pck_sz-8]== broadcast))?1:0; 
  assign pre_pop = (ntrfs_id == trn)?1:0;
  assign pndng_i = pndng;
  assign data_out_i = D_pop;
  assign D_push = data_in_i;
  
endmodule


module prll_bus_gnrtr_cn_rbtr #(parameter pck_sz = 40, parameter num_ntrfs=4, parameter broadcast = {8{1'b1}})(
  input clk,
  input reset,
  input[pck_sz-1:0]D_pop[num_ntrfs-1:0],
  input pndng[num_ntrfs-1:0],
  output pop[num_ntrfs-1:0],
  output push[num_ntrfs-1:0],
  output [pck_sz-1:0] D_push[num_ntrfs-1:0]
);
  wire pop_i;
  wire push_i;
  wire [num_ntrfs-1:0]pndng_i;
  wire [pck_sz-1:0] data_out_i[num_ntrfs-1:0];
  wire [$clog2(num_ntrfs)-1:0]trn;
  wire [pck_sz-1:0] data_in_i;
  
  genvar i;
  generate
    for(i=0;i<num_ntrfs; i=i+1)begin:_nu_
    prll_bus_interface_cn_rbtr #(.pck_sz(pck_sz),.num_ntrfs(num_ntrfs),.ntrfs_id(i),.broadcast(broadcast)) rtr_ntrfs(
    .clk(clk),
    .reset(reset),
    .data_in_i(data_in_i),
    .trn(trn),
    .pop_i(pop_i),
    .push_i(push_i),
    .data_out_i(data_out_i[i]),
    .D_pop(D_pop[i]),
    .D_push(D_push[i]),
    .pndng_i(pndng_i[i]),
    .pop(pop[i]),
    .pndng(pndng[i]),
    .push(push[i])
    );
    end
  endgenerate
  Router_arbiter #(.num_ntrfs(num_ntrfs),.pck_sz(pck_sz)) arbitro(
  .reset(reset),
  .clk(clk),
  .pndng_i(pndng_i),
  .data_out_i(data_out_i),
  .trn(trn),
  .push_i(push_i),
  .pop_i(pop_i),
  .data_in_i(data_in_i)
);
endmodule 
