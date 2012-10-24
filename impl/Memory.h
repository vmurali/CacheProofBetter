#pragma once

#include "Fifo.h"
#include "CacheTypes.h"

typedef class memory {
private:
  Latency latency;
  Latency latWait;

  Fifo* reqToP,* respFromP,* respFromPF;

  void sendCResp(Index& cIndex) {
    FromP* resp = new FromP(false, cIndex, 0, 0, 2);
    latWait = latency;
    respFromP->enq(resp);
  }

  bool handleCReq() {
    if(reqToP->empty())
      return false;
    ReqToP* msg = (ReqToP*) reqToP->first();
    printf("memory got req %llx\n", msg->lineAddr);
    sendCResp(msg->index);
    reqToP->deq();
    delete msg;
    return true;
  }

public:
  memory(Fifo* _reqToP, Fifo* _respFromP,
         Latency _latWait) {
    latWait = _latWait;
    latency = 0;

    reqToP = _reqToP; respFromPF = _respFromP;

    Fifo* respFromP = new Fifo(1);
  }
  ~memory() {
    delete respFromP;
  }

  void cycle() {
    if(latWait != 0) {
      if(latWait > 1)
        latWait--;
      else if(latWait == 1 && !respFromP->empty() && !respFromPF->full()) {
        respFromPF->enq(respFromP->first());
        respFromPF->deq();
        latWait = 0;
      }
      return;
    }
    handleCReq();
  }
} Memory;
