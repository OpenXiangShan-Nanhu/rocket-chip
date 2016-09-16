

/** This black-boxes an Async Set
  * Reg.
  *  
  * Because Chisel doesn't support
  * parameterized black boxes, 
  * we unfortunately have to 
  * instantiate a number of these.
  *  
  * We also have to hard-code the set/reset.
  *  
  *  Do not confuse an asynchronous
  *  reset signal with an asynchronously
  *  reset reg. You should still 
  *  properly synchronize your reset 
  *  deassertion.
  *  
  *  @param d Data input
  *  @param q Data Output
  *  @param clk Clock Input
  *  @param rst Reset Input
  *  @param en Write Enable Input
  * 
  */

module AsyncSetReg (
                      input      d,
                      output reg q,
                      input en,
                    
                      input      clk,
                      input      rst);
   
   always @(posedge clk or posedge rst) begin

      if (rst) begin
         q <= 1'b1;
      end else if (en) begin
         q <= d;
      end
   
   end
   

endmodule // AsyncSetReg

