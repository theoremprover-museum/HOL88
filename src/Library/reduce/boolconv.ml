%******************************************************************************
** LIBRARY:     reduce (Part I)                                              **
**                                                                           **
** DESCRIPTION: Conversions for reducing boolean expressions.                **
**                                                                           **
** AUTHOR:      John Harrison                                                **
**              University of Cambridge Computer Laboratory                  **
**              New Museums Site                                             **
**              Pembroke Street                                              **
**              Cambridge CB2 3QG                                            **
**              England.                                                     **
**                                                                           **
**              jrh@cl.cam.ac.uk                                             **
**                                                                           **
** DATE:        18th May 1991                                                **
******************************************************************************%

%-----------------------------------------------------------------------%
% dest_op - Split application down spine, checking head operator        %
%-----------------------------------------------------------------------%

let dest_op op tm = snd ((assert (curry $= op) # I) (strip_comb tm));;

%-----------------------------------------------------------------------%
% NOT_CONV "~F"  = |-  ~F = T                                           %
% NOT_CONV "~T"  = |-  ~T = F                                           %
% NOT_CONV "~~t" = |- ~~t = t                                           %
%-----------------------------------------------------------------------%

let NOT_CONV =
  let [c1;c2;c3] = CONJUNCTS
    (PROVE("(~T = F) /\ (~F = T) /\ (!t. ~~t = t)",
     REWRITE_TAC[NOT_CLAUSES]))
  and T = "T" and F = "F" and notop = "$~" in
  \tm. (let [xn] = dest_op notop tm in
        if xn = T then c1 else
        if xn = F then c2
        else let [xn] = dest_op notop xn in
             SPEC xn c3)
       ? failwith `NOT_CONV`;;

%-----------------------------------------------------------------------%
% AND_CONV "T /\ t" = |- T /\ t = t                                     %
% AND_CONV "t /\ T" = |- t /\ T = t                                     %
% AND_CONV "F /\ t" = |- F /\ t = F                                     %
% AND_CONV "t /\ F" = |- t /\ F = F                                     %
% AND_CONV "t /\ t" = |- t /\ t = t                                     %
%-----------------------------------------------------------------------%

let AND_CONV =
  let [c1;c2;c3;c4;c5] = CONJUNCTS
    (PROVE("(!t. T /\ t = t) /\ (!t. t /\ T = t) /\ (!t. F /\ t = F) /\
            (!t. t /\ F = F) /\ (!t. t /\ t = t)",REWRITE_TAC[AND_CLAUSES]))
  and T = "T" and F = "F" and andop = "$/\" and zv = "z:bool"
  and beqop = "=:bool->bool->bool" in
  \tm. (let [xn;yn] = dest_op andop tm in
        if xn = T then SPEC yn c1 else
        if yn = T then SPEC xn c2 else
        if xn = F then SPEC yn c3 else
        if yn = F then SPEC xn c4 else
        if xn = yn then SPEC xn c5 else
        if aconv xn yn then
            SUBST [(ALPHA xn yn,zv)]
                  (mk_comb(mk_comb(beqop,mk_comb(mk_comb(andop,xn),zv)),xn))
                  (SPEC xn c5)
        else fail)
       ? failwith `AND_CONV`;;

%-----------------------------------------------------------------------%
% OR_CONV "T \/ t" = |- T \/ t = T                                      %
% OR_CONV "t \/ T" = |- t \/ T = T                                      %
% OR_CONV "F \/ t" = |- F \/ t = t                                      %
% OR_CONV "t \/ F" = |- t \/ F = t                                      %
% OR_CONV "t \/ t" = |- t \/ t = t                                      %
%-----------------------------------------------------------------------%

let OR_CONV =
  let [c1;c2;c3;c4;c5] = CONJUNCTS
    (PROVE("(!t. T \/ t = T) /\ (!t. t \/ T = T) /\ (!t. F \/ t = t) /\
            (!t. t \/ F = t) /\ (!t. t \/ t = t)",REWRITE_TAC[OR_CLAUSES]))
  and T = "T" and F = "F" and orop = "$\/" and zv = "z:bool"
  and beqop = "=:bool->bool->bool" in
  \tm. (let [xn;yn] = dest_op orop tm in
        if xn = T then SPEC yn c1 else
        if yn = T then SPEC xn c2 else
        if xn = F then SPEC yn c3 else
        if yn = F then SPEC xn c4 else
        if xn = yn then SPEC xn c5 else
        if aconv xn yn then
            SUBST [(ALPHA xn yn,zv)]
                  (mk_comb(mk_comb(beqop,mk_comb(mk_comb(orop,xn),zv)),xn))
                  (SPEC xn c5)
        else fail)
       ? failwith `OR_CONV`;;

%-----------------------------------------------------------------------%
% IMP_CONV "T ==> t" = |- T ==> t = t                                   %
% IMP_CONV "t ==> T" = |- t ==> T = T                                   %
% IMP_CONV "F ==> t" = |- F ==> t = T                                   %
% IMP_CONV "t ==> F" = |- t ==> F = ~t                                  %
% IMP_CONV "t ==> t" = |- t ==> t = T                                   %
%-----------------------------------------------------------------------%

let IMP_CONV =
  let [c1;c2;c3;c4;c5] = CONJUNCTS
    (PROVE("(!t. (T ==> t) = t) /\ (!t. (t ==> T) = T) /\
            (!t. (F ==> t) = T) /\ (!t. (t ==> F) = ~t) /\
            (!t. (t ==> t) = T)",REWRITE_TAC[IMP_CLAUSES]))
  and T = "T" and F = "F" and impop = "$==>" and zv = "z:bool"
  and beqop = "=:bool->bool->bool" in
  \tm. (let [xn;yn] = dest_op impop tm in
        if xn = T then SPEC yn c1 else
        if yn = T then SPEC xn c2 else
        if xn = F then SPEC yn c3 else
        if yn = F then SPEC xn c4 else
        if xn = yn then SPEC xn c5 else
        if aconv xn yn then
            SUBST [(ALPHA xn yn,zv)]
                  (mk_comb(mk_comb(beqop,mk_comb(mk_comb(impop,xn),zv)),T))
                  (SPEC xn c5)
        else fail)
       ? failwith `IMP_CONV`;;

%-----------------------------------------------------------------------%
% BEQ_CONV "T = t" = |- T = t = t                                       %
% BEQ_CONV "t = T" = |- t = T = t                                       %
% BEQ_CONV "F = t" = |- F = t = ~t                                      %
% BEQ_CONV "t = F" = |- t = F = ~t                                      %
% BEQ_CONV "t = t" = |- t = t = T                                       %
%-----------------------------------------------------------------------%

let BEQ_CONV =
  let [c1;c2;c3;c4;c5] = CONJUNCTS
    (PROVE("(!t. (T = t) = t) /\ (!t. (t = T) = t) /\ (!t. (F = t) = ~t) /\
            (!t. (t = F) = ~t) /\ (!t:bool. (t = t) = T)",
           REWRITE_TAC[EQ_CLAUSES]))
  and T = "T" and F = "F"
  and beqop = "$=:bool->bool->bool" and zv = "z:bool" in
  \tm. (let [xn;yn] = dest_op beqop tm in
        if xn = T then SPEC yn c1 else
        if yn = T then SPEC xn c2 else
        if xn = F then SPEC yn c3 else
        if yn = F then SPEC xn c4 else
        if xn = yn then SPEC xn c5 else
        if aconv xn yn then EQT_INTRO (ALPHA xn yn)
        else fail)
       ? failwith `BEQ_CONV`;;

%-----------------------------------------------------------------------%
% COND_CONV "F => t1 | t2" = |- (T => t1 | t2) = t2                     %
% COND_CONV "T => t1 | t2" = |- (T => t1 | t2) = t1                     %
% COND_CONV "b => t | t    = |- (b => t | t) = t                        %
%-----------------------------------------------------------------------%

let COND_CONV =
  let [c1;c2;c3] = CONJUNCTS
    (PROVE("(!t1 t2. (T => t1 | t2) = (t1:*)) /\
            (!t1 t2. (F => t1 | t2) = (t2:*)) /\
            (!b t. (b => t | t) = (t:*))",
            REWRITE_TAC[COND_CLAUSES; COND_ID]))
  and T = "T" and F = "F" and ty = ":*" in
  \tm. (let (b,t1,t2) = dest_cond tm in
        if b = T then SPECL[t1;t2] (INST_TYPE[(type_of t1,ty)] c1) else
        if b = F then SPECL[t1;t2] (INST_TYPE[(type_of t1,ty)] c2) else
        if t1 = t2 then SPECL[b;t1] (INST_TYPE[(type_of t1,ty)] c3) else
        if aconv t1 t2 then
          TRANS (AP_TERM (rator tm) (ALPHA t2 t1))
                (SPECL [b; t1] (INST_TYPE [(type_of t1,ty)] c3))
        else fail)
       ? failwith `COND_CONV`;;
