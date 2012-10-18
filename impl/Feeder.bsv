import CFeeder::*;
import FIFOF::*;
import Types::*;

interface Feeder;
  method ActionValue#(ReqFromCore) feed;
endinterface

module mkFeeder#(Bool isData, Bit#(32) tId)(Feeder);
  FIFOF#(ReqFromCore) f <- mkFIFOF;
  Reg#(Bool) inited <- mkReg(False);
  Reg#(Counter) count <- mkReg(0);

  rule init(!inited);
    initialize(isData, tId);
    inited <= True;
  endrule

  rule downCount(inited && count != 0);
    count <= count - 1;
  endrule

  rule feedRl(inited && count == 0);
    if(isData)
    begin
      match {.to, .addr} <- getDataFeed(tId);
      if(to == 0)
        count <= addr;
      else
        f.enq(ReqFromCore{to: to, lineAddr: truncateLSB(addr)});
    end
    else
    begin
      let addr <- getInstFeed(tId);
      f.enq(ReqFromCore{to: 1, lineAddr: truncateLSB(addr)});
    end
  endrule

  method ActionValue#(ReqFromCore) feed;
    f.deq;
    return f.first;
  endmethod
endmodule

(* synthesize *)
module mkFeederInst(Feeder);
  let f <- mkFeeder(True, 0);
  return f;
endmodule