%----------------------------------------------------------------------------%
% SWnew.ml contains the commands used in the case study to build a           %
% sliding window theory                                                      %
% Modified for HOL12 on 20/3/91 by RCO                                       %
%----------------------------------------------------------------------------%

%box 1%
loadf`startSW`;;

%box 2%
let  time = ":num"
and  data = ":*"
and  sequence = ":num"
and  non_packet = ":one" ;; 

let  packet = ":(^sequence # ^data) + ^non_packet" ;;
let  channel = ":^time -> ^packet" ;;

let  seqtime = ":^time->^sequence" ;;
let  datatime = ":^time->^data list" ;;

%box 3%
let set_non_packet = new_definition(`set_non_packet`,
  "set_non_packet:^packet = INR(one)");;

let good_packet = new_definition(`good_packet`,
  "good_packet (p:^packet) = (ISL p)");;

let new_packet = new_definition(`new_packet`,
 "(new_packet (ss:^sequence) (dd:^data)):^packet = (INL(ss,dd))");;
   
let label = new_definition(`label`,
 "label (p:^packet) = FST(OUTL p)");;

let message = new_definition(`message`,
 "message (p:^packet) = SND(OUTL p)");;

%box 4%
let INIT = new_definition(`INIT`,
  "INIT (source:^data list) (maxseq:^sequence)
        (rem :^datatime)  (s:^seqtime) 
        (sink:^datatime)  (r:^seqtime)  =
   ( ( 1 < maxseq )    /\ 
     (rem 0 = source)  /\  (s 0 = 0) /\ 
     (sink 0 = NIL)    /\  (r 0 = 0))");;

%box 5%
let CHANNEL= new_definition(`CHANNEL`,
   "CHANNEL (inC:^channel) (outC:^channel) =
      (!t:^time. (outC t = inC t) \/ (outC t = set_non_packet))" );;

%box 6%
 let DATA_TRANS = new_definition(`DATA_TRANS`, 
   "DATA_TRANS
      (rem:^datatime) (s:^seqtime) (SW:^sequence) 
      (maxseq:^sequence)
      (p:^time->^sequence->bool) (i:^seqtime)
      (dataS:^channel) =       
      ( (SW = (maxseq-1)) /\
      (!t:^time. 
        ( ((p t (i t)) ==> 
              ((~NULL(TLI (i t) (rem t))) /\ ((i t) < SW) )) /\
           ( ((p t (i t)) /\ ~(NULL(rem t)))          
                   => (dataS t = new_packet 
                                   (plusm(s t,i t,maxseq))
                                   (HDI (i t) (rem t)) )
                   |  (dataS t = set_non_packet ) ) ))) ");;   

%box 7%
let IN_WINDOW = new_definition(`IN_WINDOW`,
  "IN_WINDOW (p:^packet) (b:^sequence) (ws:^sequence) (maxseq:^sequence) =
    ( (good_packet p) /\
      ( subm(label p,b,maxseq) < ws )  )");;

%box 8%
let DATA_RECV = new_definition(`DATA_RECV`, 
  "DATA_RECV (dataR:^channel)
             (RW:^sequence) (maxseq:^sequence) 
             (sink:^datatime) (r:^seqtime)  =
  ( (RW = 1) /\
  (!t:^time.  
      (IN_WINDOW (dataR t) (r t) RW maxseq ) 
          => ( (r (t+1) = plusm(r t,1,maxseq)) /\ 
               (sink (t+1) = (APPEND (sink t) [message(dataR t)] ) )) 
          |  ( (r (t+1) = (r t)) /\ 
               (sink (t+1) = (sink t)) )))" );;

%box 9%
let ACK_TRANS = new_definition(`ACK_TRANS`,
   "ACK_TRANS (r:^seqtime) 
              (maxseq:^sequence)
              (q:^time->bool)
              (ackR:^channel) = 
    ( !t:^time. !dummy:^data.
      ( (q t) => (ackR t = new_packet (subm((r t),1,maxseq)) dummy )
              |  (ackR t = set_non_packet) ) )");;    

%box 10%
let ACK_RECV = new_definition(`ACK_RECV`,     
   "ACK_RECV (ackS:^channel) 
             (SW:^sequence)
             (maxseq:^sequence) 
             (rem:^datatime) 
             (s:^seqtime) = 
    (!t:^time.                                                              
        (IN_WINDOW (ackS t) (s t) SW maxseq)     
           => ( (s (t+1) = plusm(label(ackS t),1,maxseq) ) /\
                (rem (t+1) = 
                     (TLI (subm (plusm(label(ackS t),1,maxseq),s t,maxseq)) 
                          (rem t)) ) )
           |  ( (s (t+1) = (s t)) /\                                        
                (rem (t+1) = (rem t)) ) )");; 

%box 11%
let SENDER = new_definition(`SENDER`,
  "SENDER (maxseq:^sequence) 
          (SW:^sequence)
          (rem:^datatime) 
          (s:^seqtime) 
          (p:^time->^sequence->bool) (i:^seqtime)
          (dataS:^channel) 
          (ackS:^channel) = 
    ( (DATA_TRANS rem s SW maxseq p i dataS) /\
      (ACK_RECV ackS SW maxseq rem s) )");;

%box 12%
let ABORT = new_definition(`ABORT`,
  "ABORT (c:^time->num) (aborted:^time->bool) (maxT:num)
         (maxseq:^sequence) (SW:^sequence) 
         (s:^seqtime) (rem:^datatime) (ackS:^channel) =
    (!t:^time. 
      (c 0 = 0 ) /\ 
      (c (t+1) = ( (IN_WINDOW (ackS t) (s t) SW maxseq) => 0 | ((c t)+1) )) /\
      (aborted 0 = F) /\
      (aborted(t+1) = (((c t >= maxT) \/ (aborted t)) /\ ~(NULL(rem t)))))");;

%box 13%
let RECEIVER = new_definition(`RECEIVER`,
  "RECEIVER (maxseq:^sequence)
            (RW:^sequence)
            (sink:^datatime) 
            (r:^seqtime)
            (q:^time->bool)
            (ackR:^channel) 
            (dataR:^channel) =
    ( (ACK_TRANS r maxseq q ackR) /\
      (DATA_RECV dataR RW maxseq sink r) )");;

%box 14%
let IMPL = new_definition(`IMPL`,
  "IMPL (source:^data list)
        (maxseq:^sequence) 
        (rem:^datatime)  (s:^seqtime) (SW:^sequence)
        (p:^time->^sequence->bool) (i:^seqtime)
        (c:^time->num) (aborted:^time->bool) (maxT:num)
        (sink:^datatime) (r:^seqtime) (RW:^sequence)
        (q:^time->bool)
        (dataS:^channel) (dataR:^channel) (ackS:^channel) (ackR:^channel) =
  ( (INIT source maxseq rem s sink r) /\
    (SENDER maxseq SW rem s p i dataS ackS) /\
    (ABORT c aborted maxT maxseq SW s rem ackS) /\
    (CHANNEL dataS dataR) /\
    (RECEIVER maxseq RW sink r q ackR dataR) /\
    (CHANNEL ackR ackS) )");;



%box 15%
loadf`tacticsSW`;;

%box 16 - use instead of boxes 1 to 15 if you restart the session %
%%%  loadf`restartSW`;;  %%%

%box 17%
g("!source:^data list. !maxseq:^sequence.
   !rem:^datatime.  !s:^seqtime.
   !sink:^datatime. !r:^seqtime. !RW:^sequence.
   !dataR:^channel.

  (INIT source maxseq rem s sink r) /\
  (DATA_RECV dataR RW maxseq sink r)
 ==>
  ( !t:^time. (r t) < maxseq )");;

%box 18%
expand tactic2;;

%box 19%
expand tactic3;;
let r_in_range = save_top_thm `r_in_range`;;

%box 20%
let INIT_maxseq_1 = prove_thm(`INIT_maxseq_1`,
  "!source:^data list. !maxseq:^sequence. 
   !rem sink :^datatime.  !s r :^seqtime.
  (INIT source maxseq rem s sink r) ==> (1 < maxseq)",

  REWRITE_TAC[INIT] THEN REPEAT STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

%box 21%
let INIT_maxseq_0 = prove_thm(`INIT_maxseq_0`,
  "!source:^data list. !maxseq:^sequence.
   !rem sink :^datatime.  !s r :^seqtime.
   (INIT source maxseq rem s sink r) ==> (0 < maxseq)",
   
   REPEAT STRIP_TAC THEN IMP_RES_TAC INIT_maxseq_1 THEN
   IMP_RES_TAC ONE_LESS_0_LESS );;
 
%box 22%
g("!inC outC :^channel. !t:^time.
   (CHANNEL inC outC) /\
    good_packet (outC t)
 ==>
   ( (outC t) = (inC t) )");;

%box 23%
expand tactic5;;

%box 24%
expand( POP_ASSUM MP_TAC THEN POP_ASSUM(DISJ_CASES_TAC o SPEC_ALL));;

%box 25%
expand( ASM_REWRITE_TAC[] );;
expand( ASM_REWRITE_TAC [good_packet;set_non_packet;ISL]);;

let Lemma1A = save_top_thm`Lemma1A`;;

%box 26%
g("!r s :^seqtime.
   !q:^time->bool. !SW maxseq :^sequence.
   !ackS ackR :^channel.
   !t:^time.
     ACK_TRANS r maxseq q ackR /\
     CHANNEL ackR ackS /\
     IN_WINDOW (ackS t) (s t) SW maxseq 
    ==>
     (label(ackS t) = subm(r t,1,maxseq))" );;

%box 27%
expand( tactic6 Lemma1A);;

%box 28%
expand( ASM_REWRITE_TAC[label;new_packet;OUTL;FST] );;
expand(
      UNDISCH_TAC "good_packet((ackS:^channel) t)" THEN
      ASM_REWRITE_TAC[good_packet;set_non_packet;ISL] );;
let Lemma1 = save_top_thm`Lemma1`;;

%box 29%
g("!dataS:^channel.
   !maxseq:^sequence. !s:^seqtime. 
   !p:^time->^sequence->bool. !i:^seqtime. !rem:^datatime.
   !t:^time.
   (DATA_TRANS rem s SW maxseq p i dataS) /\ 
    good_packet(dataS t) /\
    (0 < maxseq)
  ==> 
   ((label(dataS t) = plusm(s t,i t,maxseq)) /\
    (message(dataS t) = (HDI (i t) (rem t))) /\
    ( ((i t)+1) < maxseq ) /\
    ( ~NULL(TLI (i t) (rem t)) ) )" );;

%box 30%
expand tactic7;;

%box 31%
expand( ASM_REWRITE_TAC[label;new_packet;OUTL;FST;message;SND] );;

%box 32%
expand tactic8;;

%box 33%
expand(
  UNDISCH_TAC "good_packet ((dataS:^channel) t)" THEN
  ASM_REWRITE_TAC [good_packet;set_non_packet;ISL] );;

let Lemma2A = save_top_thm`Lemma2A`;;

%box 34%
g("!dataR:^channel. 
  !r:^seqtime. !RW:^sequence. !maxseq:^sequence.
  !t:^time.
     ((IN_WINDOW (dataR t) (r t) RW maxseq) /\ (RW=1))
    ==>
     ( subm(label(dataR t),r t,maxseq) = 0 )");;

%box 35%
expand tactic10 ;;

let Lemma2B = save_top_thm `Lemma2B`;;

%box 36%
g("!dataR dataS :^channel.
   !maxseq  SW  RW :^sequence. 
   !rem sink :^datatime. !s r :^seqtime.
   !p:^time->^sequence->bool. !i:^seqtime.
   !t:^time.
  ( (DATA_TRANS rem s SW maxseq p i dataS ) /\
    (CHANNEL dataS dataR) /\
    (RW=1) /\
    (IN_WINDOW (dataR t) (r t) RW maxseq) /\
    ( 0 < maxseq ) )
  ==>
    ( i t = (subm(r t,s t,maxseq)) )" );;

%box 37%
expand( REPEAT STRIP_TAC THEN IMP_RES_TAC Lemma2B THEN POP_ASSUM MP_TAC);; 

%box 38%
expand( tactic11A Lemma1A THEN tactic11B Lemma2A );;

%box 39%
expand( DISCH_TAC THEN IMP_RES_TAC (SPECL 
      ["(s:^seqtime) t";"(i:^seqtime) t";"(r:^seqtime) t";"maxseq:num"] 
      change_sides) );;

let Lemma2C = save_top_thm`Lemma2C`;;

%box 40%
g("!dataR dataS :^channel.
   !maxseq SW RW :^sequence. 
   !rem sink :^datatime. !s r :^seqtime.
   !p:^time->^sequence->bool. !i:^seqtime.
   !t:^time.
  ( (DATA_TRANS rem s SW maxseq p i dataS ) /\
    (CHANNEL dataS dataR) /\
    (RW=1) /\
    (IN_WINDOW (dataR t) (r t) RW maxseq) /\
    ( 0 < maxseq ) )
  ==>
  ( ((HDI (subm(r t,s t,maxseq)) (rem t)) = message(dataR t) ) /\
    (~NULL(TLI (subm(r t,s t,maxseq)) (rem t))) /\
     ( (subm(r t,s t,maxseq)+1) < maxseq) )" );;

%box 41%
expand (tactic12 Lemma1A Lemma2A Lemma2C);;

let Lemma2 = save_top_thm`Lemma2`;;

%box 42%
g("!source:^data list. !rem sink:^datatime. 
   !SW:^sequence. !maxseq:^sequence. 
   !s r:^seqtime.  !q:^time->bool. 
   !ackS ackR dataR:^channel.
      ACK_TRANS r maxseq q ackR /\
      CHANNEL ackR ackS /\
      ACK_RECV ackS SW maxseq rem s /\
      INIT source maxseq rem s sink r /\
      DATA_RECV dataR RW maxseq sink r
     ==>
      (!t:^time.
        (IN_WINDOW(ackS t)(s t)SW maxseq => 
           ((s(t + 1) = r t) /\
            (rem(t + 1) = TLI(subm(r t,s t,maxseq))(rem t))) | 
           ((s(t + 1) = s t) /\ (rem(t + 1) = rem t))))" );;

%box 43%
expand(
  REPEAT STRIP_TAC THEN IMP_RES_TAC INIT_maxseq_0 THEN
  IMP_RES_TAC r_in_range THEN
  POP_ASSUM (ASSUME_TAC o SPEC_ALL) THEN
  IMP_RES_TAC (SPECL ["(r:^seqtime) t";"1";"maxseq:num"] plusm_subm) THEN
  UNDISCH_TAC "ACK_RECV (ackS:^channel) SW maxseq rem s" THEN 
  REWRITE_TAC[ACK_RECV] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (MP_TAC o SPEC_ALL) THEN COND_CASES_TAC
    REPEAT STRIP_TAC THEN IMP_RES_TAC Lemma1 THEN ASM_REWRITE_TAC[]);;

let Lemma3=save_top_thm`Lemma3`;;

%box 44%
g("!dataR dataS:^channel.
  !maxseq:^sequence.  !source:^data list.
  !rem sink:^datatime. !s r:^seqtime. !SW RW:^sequence.
  !p:^time->^sequence->bool. !i:^seqtime.
    INIT source maxseq rem s sink r  /\
    DATA_TRANS rem s SW maxseq p i dataS  /\
    CHANNEL dataS dataR  /\
    DATA_RECV dataR RW maxseq sink r
 ==>
  (!t:^time.
    (IN_WINDOW (dataR t) (r t) RW maxseq)
      => ((r(t+1)=plusm(r t,1,maxseq)) /\ 
          (sink(t+1)=
           (APPEND (sink t) [HDI (subm(r t,s t,maxseq)) (rem t)])) /\
          (~NULL(TLI (subm(r t,s t,maxseq)) (rem t))) /\
          ( (subm(r t,s t,maxseq)+1) < maxseq) )
      |  ((r(t+1)=(r t)) /\ 
          (sink(t+1)=(sink t)) ))" );;

%box 45%
expand(
  REPEAT STRIP_TAC THEN IMP_RES_TAC INIT_maxseq_0 THEN
  UNDISCH_TAC "DATA_RECV (dataR:^channel) RW maxseq sink r" THEN
  REWRITE_TAC[DATA_RECV] THEN DISCH_TAC THEN POP_ASSUM STRIP_ASSUME_TAC THEN
  POP_ASSUM (MP_TAC o SPEC_ALL) THEN
  COND_CASES_TAC THEN
    REPEAT STRIP_TAC THEN IMP_RES_TAC Lemma2 THEN ASM_REWRITE_TAC[]);;

let Lemma4 =save_top_thm`Lemma4`;;

%box 46%
g("!source:^data list. !maxseq:^sequence.
   !rem:^datatime.  !s:^seqtime. !SW:^sequence.
   !p:^time->^sequence->bool. !i:^seqtime.
   !c:^time->num. !aborted:^time->bool. !maxT:num.
   !sink:^datatime. !r:^seqtime. !RW:^sequence. !q:^time->bool.
   !dataS dataR ackS ackR:^channel.

   (IMPL source maxseq rem s SW p i c aborted maxT sink r RW q 
        dataS dataR ackS ackR)
 ==>
   ( !t:^time. 
      ( (APPEND (sink t) (TLI (subm(r t,s t,maxseq)) (rem t))) = source) )");;

%box 47%
expand( tactic15 [IMPL;SENDER;RECEIVER] );;

%box 48%
expand(
   IMP_RES_TAC INIT_maxseq_0 THEN
   IMP_RES_TAC (SPEC "maxseq:num" subm_self) THEN
   UNDISCH_TAC "INIT (source:^data list) maxseq rem s sink r" THEN
   REWRITE_TAC[INIT] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[APPEND;TLI] );;

%box 49%
expand( MP_TAC (SPEC_ALL Lemma3) THEN ASM_REWRITE_TAC[] THEN
        DISCH_TAC THEN POP_ASSUM (MP_TAC o SPEC_ALL) THEN
        COND_CASES_TAC THEN REPEAT STRIP_TAC );;

%box 50%
expand( MP_TAC (SPEC_ALL Lemma4) THEN ASM_REWRITE_TAC[] THEN
        DISCH_TAC THEN POP_ASSUM (MP_TAC o SPEC_ALL) THEN
        COND_CASES_TAC THEN REPEAT STRIP_TAC );;


%box 51%
expand(
  IMP_RES_TAC INIT_maxseq_1 THEN
  IMP_RES_TAC (SPECL ["(r:^seqtime) t";"maxseq:num"] plus_1_sub) THEN
  ASM_REWRITE_TAC[ADD1] );;

%box 52%
expand(
  IMP_RES_TAC HDI_TLI_1 THEN
  POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [ADD_SYM]) THEN
  ASM_REWRITE_TAC[(SYM (SPEC_ALL APPEND_ASSOC));HDI_TLI_2]);;

%box 53%
%box 54%
expand(
  IMP_RES_TAC INIT_maxseq_0 THEN
  IMP_RES_TAC (SPEC "maxseq:num" subm_self) THEN
  POP_ASSUM (ASSUME_TAC o SPEC "(r:^seqtime) t") THEN
  ASM_REWRITE_TAC[ADD1;TLI ] );;

%box 55%
expand( MP_TAC (SPEC_ALL Lemma4) THEN ASM_REWRITE_TAC[] THEN
        DISCH_TAC THEN POP_ASSUM (MP_TAC o SPEC_ALL) THEN
        COND_CASES_TAC THEN REPEAT STRIP_TAC );;

%box 56%
expand( tactic16 INIT_maxseq_0 r_in_range );;

%box 57%
expand( ASM_REWRITE_TAC[ADD1] );;

let SAFETY_THM = save_top_thm`SAFETY_THM`;;

%box 58%
let IMPL_LIVE_PARTS = 
prove_thm( 
  `IMPL_LIVE_PARTS`,
  "!source:^data list. !maxseq SW RW :^sequence.
   !rem sink :^datatime.  !s r :^seqtime.
   !p:^time->^sequence->bool. !i:^seqtime. !q:^time->bool.
   !c:^time->num. !aborted:^time->bool. !maxT:num.
   !dataS dataR ackS ackR :^channel.

  (IMPL source maxseq rem s SW p i c aborted maxT sink r RW q 
        dataS dataR ackS ackR)
  ==>
  ((INIT source maxseq rem s sink r ) /\
   (SENDER maxseq SW rem s p i dataS ackS ) /\
   (ABORT c aborted maxT maxseq SW s rem ackS))" ,
 tactic17 );;

%box 59%
let SW_value = 
prove_thm( 
  `SW_value`,
  "!rem:^datatime. !s:^seqtime. !SW maxseq:^sequence.
   !p:^time->^sequence->bool. !i:^seqtime.
   !dataS:^channel.   
  ( DATA_TRANS rem s SW maxseq p i dataS ) ==> ( SW = maxseq-1 )",
  tactic18 );;

%box 60%
g("!maxseq:^sequence.
   !rem sink:^datatime.  !s r:^seqtime. !SW :^sequence.
   !c:^time->num. !aborted:^time->bool. !maxT:num.
   !p:^time->^sequence->bool. !i:^seqtime.
   !ackS dataS :^channel.
   !source:^data list.

   (INIT source maxseq rem s sink r ) /\
   (SENDER maxseq SW rem s p i dataS ackS ) /\
   (ABORT c aborted maxT maxseq SW s rem ackS)
  ==>
   !t:^time. 
     ( (?x:num. ( rem(t+1) = (TLI x (rem t))) /\ (0<x)) /\ (c(t+1)=0) ) \/
       (( rem(t+1) = (rem t) ) /\ (c(t+1)=((c t)+1)) )");;

%box 61%
expand tactic19;;

%box 62%
expand( DISJ1_TAC THEN ASM_REWRITE_TAC[]);;

%box 63%
expand( tactic20 INIT_maxseq_0 SW_value );;

%box 64%
expand( DISJ2_TAC THEN ASM_REWRITE_TAC[] );;

let Liveness_1 = save_top_thm`Liveness_1`;;

%box 65%
let Liveness_2 = prove_thm(`Liveness_2`,
  "!maxseq:^sequence.
   !rem sink:^datatime.  !s:^seqtime. !SW:^sequence.
   !c:^time->num. !aborted:^time->bool. !maxT:num.
   !ackS:^channel.  
   (ABORT c aborted maxT maxseq SW s rem ackS)
  ==>
  !t:^time.
  ( (((c t >= maxT) \/ (aborted t)) /\ ~(NULL(rem t))) = aborted(t+1) )",
 tactic21 );;

%box 66%
g("!maxseq:^sequence.
   !rem sink:^datatime.  !s r:^seqtime. !SW :^sequence.
   !c:^time->num. !aborted:^time->bool. !maxT:num.
   !p:^time->^sequence->bool. !i:^seqtime.
   !ackS dataS :^channel.
   !source:^data list.
   (INIT source maxseq rem s sink r ) /\
   (SENDER maxseq SW rem s p i dataS ackS ) /\
   (ABORT c aborted maxT maxseq SW s rem ackS)
  ==>
  !n:num. !t:^time.
   ( ?x:num. ( rem(t+n) = (TLI x (rem t)) ) /\ (0<x)  ) \/
   (         ( rem(t+n) = (rem t)) /\ (n <= c(t+n)) )");;

%box 67%
expand(
  REPEAT GEN_TAC THEN DISCH_TAC THEN 
  POP_ASSUM (ASSUME_TAC o ( MP (SPEC_ALL Liveness_1) )) THEN 
  INDUCT_TAC );;

%box 68%
expand( REWRITE_TAC[ADD_CLAUSES;LESS_OR_EQ_0] );;

%box 69%
expand tactic21A ;;
expand tactic21B ;;

%box 70%
expand tactic22;;
expand tactic23;;

%box 71%
expand tactic21B;;

%box 72%
expand tactic23;;

%box 73%
expand(
  DISJ2_TAC THEN
  ASM_REWRITE_TAC[ADD1;REWRITE_RULE [ADD1] LESS_EQ_MONO_EQ] );;

let Liveness_3=save_top_thm `Liveness_3`;;

%box 74%
g("!maxseq:^sequence.
   !rem sink:^datatime.  !s r:^seqtime. !SW:^sequence.
   !c:^time->num. !aborted:^time->bool. !maxT:num.
   !p:^time->^sequence->bool. !i:^seqtime.
   !ackS dataS :^channel.
   !source:^data list.
   (INIT source maxseq rem s sink r ) /\
   (SENDER maxseq SW rem s p i dataS ackS ) /\
   (ABORT c aborted maxT maxseq SW s rem ackS)
  ==>
  !t:^time.
   (~NULL (rem (t+maxT)) )
  ==>
   ( ( ?x:num. ( rem(t+maxT) = (TLI x (rem t)) ) /\ (0<x)  ) \/
     ( aborted(t+maxT+1) ) )");;

%box 75%
expand( REPEAT GEN_TAC THEN DISCH_TAC THEN 
        POP_ASSUM STRIP_ASSUME_TAC THEN IMP_RES_TAC Liveness_3);;
expand( GEN_TAC THEN 
        POP_ASSUM (DISJ_CASES_TAC o SPECL ["t:num";"maxT:num"]) );;

%box 76%
expand( DISCH_TAC THEN DISJ1_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

expand( POP_ASSUM STRIP_ASSUME_TAC THEN DISCH_TAC THEN DISJ2_TAC THEN
        IMP_RES_TAC Liveness_2);;

expand( UNDISCH_TAC "(c(t + maxT)) >= maxT ==> aborted((t + maxT) + 1)" THEN
        REWRITE_TAC[GREATER_OR_EQ_LESS_OR_EQ] THEN
        ASM_REWRITE_TAC[ADD_ASSOC]);;

let Liveness = save_top_thm`Liveness`;;

%box 77%
g("!rem:^datatime. !maxT:num. 
   (!t:^time.
     ( NULL(rem (t+maxT))) \/ 
     ( ?x:num. (rem(t+maxT) = (TLI x (rem t)) ) /\ (0<x)) )
  ==>
   ( !n:num. LENGTH(rem(maxT * n)) <= (LENGTH(rem 0) - n ) )" );;

%box 78%
expand(
 REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC );;

%box 79%
expand( REWRITE_TAC[MULT_CLAUSES;SUB_0;LESS_EQ_REFL] );;

%box 80%
expand( UNDISCH_TAC "!t.
        NULL((rem:^datatime)(t + maxT)) \/
        (?x. (rem(t + maxT) = TLI x(rem t)) /\ 0 < x)" THEN
        DISCH_TAC THEN POP_ASSUM(DISJ_CASES_TAC o (SPEC "maxT*n")) );;
 
%box 81%  
expand tactic28;;
expand tactic29;;

let decreasing_rem_lemma = save_top_thm`decreasing_rem_lemma`;;

%box 82%
let LIVE_ASSUM =
new_definition(
  `LIVE_ASSUM`,
  "LIVE_ASSUM (aborted:^time->bool) (maxT:num) =
    ( !t:^time. ~(aborted (t + maxT + 1)) )" );;

%box 83%
g( "!maxseq:^sequence.                                                      
    !rem sink:^datatime.  !s r:^seqtime. !SW:^sequence.                  
    !c:^time->num. !aborted:^time->bool. !maxT:num.                         
    !p:^time->^sequence->bool. !i:^seqtime.                                 
    !ackS dataS :^channel.                                                  
    !source:^data list.                                                     
    (LIVE_ASSUM aborted maxT) /\ 
    (INIT source maxseq rem s sink r ) /\  
    (SENDER maxseq SW rem s p i dataS ackS ) /\        
    (ABORT c aborted maxT maxseq SW s rem ackS) 
   ==>                                                                      
    (rem (maxT * LENGTH(rem 0)) = [] )" );;

%box 84%
expand( tactic30 Liveness LIVE_ASSUM decreasing_rem_lemma);;

%box 85%
expand(
  POP_ASSUM (ASSUME_TAC o REWRITE_RULE  
     [SUB_SELF;LESS_OR_EQ;NOT_LESS_0;LENGTH_NIL]) THEN
  FIRST_ASSUM ACCEPT_TAC  );;
 
let LIVENESS = save_top_thm`LIVENESS`;;

%box 86%
g("!source:^data list. !maxseq:^sequence.
   !rem sink : ^datatime. !s r :^seqtime. !SW RW :^sequence.
   !p:^time->^sequence->bool. !i:^seqtime.  !q:^time->bool.
   !c:^time->num. !aborted:^time->bool. !maxT:num.
   !dataS dataR ackS ackR : ^channel.

  (IMPL source maxseq rem s SW p i c aborted maxT sink r RW q 
        dataS dataR ackS ackR) /\
  (LIVE_ASSUM aborted maxT)
  ==>
  ( ?t :^time. (sink t) = source )" );;

%box 87%
expand( 
  REPEAT STRIP_TAC THEN 
  IMP_RES_TAC IMPL_LIVE_PARTS THEN
  IMP_RES_TAC LIVENESS THEN
  IMP_RES_TAC SAFETY_THM THEN
  POP_ASSUM (ASSUME_TAC o (SPEC "maxT*LENGTH((rem:^datatime) 0)")) );;

%box 88%
expand(
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[TLI_NIL;APPEND_NIL] THEN DISCH_TAC);;

%box 89%
expand(
  EXISTS_TAC "maxT * LENGTH((rem:^datatime) 0)" THEN
  FIRST_ASSUM ACCEPT_TAC);;

let TOTAL_CORRECTNESS_THM = save_top_thm`TOTAL_CORRECTNESS_THM`;;

close_theory();;
quit();;
