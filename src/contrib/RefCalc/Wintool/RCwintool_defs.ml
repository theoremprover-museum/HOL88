% File: RCwintool_defs.ml

  Definitions for the window refinement theory `RCwintool`
%


% --- preliminary definitions --- %

let mk_relty(ty1,ty2) =
  mk_type(`fun`,[ty1;mk_type(`fun`,[ty2;mk_type(`bool`,[])])]);;


% --- add relations to the database --- %

add_relation(refines_refl,refines_trans);;
add_relation(implies_refl,implies_trans);;
add_relation(implies2_refl,implies2_trans);;
add_relation(implied_by_refl,implied_by_trans);;



% ----- Window-handling functions ----- %

% Transform a window, adding assumptions as conjectures %
let c_transform_win th =
   transform_win th o (itlist conjecture (hyp th));;
let C_TRANSFORM_WIN th = APPLY_TRANSFORM (c_transform_win th);;
%let c_match_transform_win th =
   match_transform_win th o (itlist conjecture (hyp th));; %
let c_match_transform_win th win =
   let old = rand(concl(UNDISCH_ALL(SPEC_ALL th))) in
   let terml,typl = match old (focus win) in
   let th1 = PBETA_RULE(INST terml(INST_TYPE typl (SPEC_ALL th))) in
   let th2 = UNDISCH_ALL th1 in
   (match_transform_win th2 o (itlist conjecture (hyp th2))) win;;
let C_MATCH_TRANSFORM_WIN th = APPLY_TRANSFORM (c_match_transform_win th);;

% Implement a spec with a loop, given parts of loop %
let spec_to_loop_win p0 q grd c inv t win = 
 let v,p = dest_abs(rand(focus win)) in
 let thm1 = MP (ISPECL[p0;q;grd;c;inv;t;p]spec_to_loop) (mono_CONV c)in
 let thm2 = UNDISCH_ALL (PBETA_RULE thm1) in
       c_match_transform_win thm2 win;;
let SPEC_TO_LOOP_WIN P0 q grd c inv t = 
       APPLY_TRANSFORM (spec_to_loop_win P0 q grd c inv t);;

% Perform data refinement of block, given abstraction relation R%
let block_dr_win R win = 
 let [p;c] = snd(strip_comb(focus win)) in
 let thm = MP (ISPECL[R;p;c]dr_block) (mono_CONV c) in
       transform_win thm win;;
let BLOCK_DR_WIN R = APPLY_TRANSFORM (block_dr_win R);;

% Perform data refinement of do %
let seq_dr_win (x:void) win = 
 let [lef;rig] = snd(strip_comb(focus win)) in
 let R = rand lef in
 let [c1;c2] = snd(strip_comb(rand(rator rig))) in
 let thm = MP(ISPECL[R;c1;c2]dr_seq)(mono_CONV c1) in
       c_transform_win thm win;;
let SEQ_DR_WIN x = APPLY_TRANSFORM (seq_dr_win x);;

% Perform data refinement of do %
let do_dr_win (x:void) win = 
 let [lef;rig] = snd(strip_comb(focus win)) in
 let R = rand lef in
 let [g;c] = snd(strip_comb(rand(rator rig))) in
 let thm = UNDISCH(PBETA_RULE(MP(ISPECL[R;g;c]dr_do)(mono_CONV c))) in
       c_transform_win thm win;;
let DO_DR_WIN x = APPLY_TRANSFORM (do_dr_win x);;

% Perform data refinement of nondass, given concrete nondass-relation %
let nondass_dr_win Q win = 
 let [t1;t2] = snd(strip_comb(focus win)) in
 let R = rand t1 in
 let P = rand(rand(rator t2)) in
 let thm = UNDISCH(PBETA_RULE(ISPECL[R;Q;P] dr_nondass_rule)) in
 c_match_transform_win thm win;;
let NONDASS_DR_WIN Q = APPLY_TRANSFORM (nondass_dr_win Q);;



% ----- Window closing rules for subcommands ----- %


% Closing after refining the right component of a seq

   |- c2 refines c3
-------------------------------------  SEQ_RIGHT_CLOSE "c1 seq c3"
   |- (c1 seq c2) refines (c1 seq c3)
%
let seq_mono_left = prove
 ("!(c1:^ptrans23) (c2:^ptrans12) c3.
      monotonic c1 ==> c2 ref c3 ==> (c1 seq c2) ref (c1 seq c3)",
    LPORT[monotonic_DEF;ref_DEF;seq_DEF] THEN REPEAT STRIP_TAC THEN
    POP_ASSUM (ASSUME_TAC o SPEC_ALL) THEN RES_TAC);;
let SEQ_RIGHT_CLOSE t th =
 (let t4,t3 = dest_comb (snd (dest_thm th)) in
  let t2,t1 = dest_comb t4 in
  let t5 = rand(rator t) in
  MATCH_MP (MATCH_MP (ISPECL[t5;t3;t1] 
                         (PORR[SYM (SPEC_ALL refines_DEF)] seq_mono_left))
                     (mono_CONV t5))
           th)
 ? failwith `SEQ_RIGHT_CLOSE`;;
store_rule ([RAND]
           ,(\t. let t1 = rator(rator t) ? mk_const(`skip`,ptrans) in
                 (t1 = mk_const(`seq`,type_of t1) ? false))
           ,(\foc. \rel. let ty = type_of(rand foc) ? mk_type(`bool`,[])
                         in let fty = mk_relty(ty,ty)
                         in mk_const(`refines`,fty) ? mk_const(`=`,fty))
           ,(\foc. \rel. mk_const(`refines`,type_of rel))
           ,(\foc. \hyps. hyps)
           ,(\foc. [])
           ,SEQ_RIGHT_CLOSE
           );;


% Closing after refining the left component of a seq

   |- c1 refines c2
-------------------------------------  SEQ_LEFT_CLOSE "c2 seq c3"
   |- (c1 seq c3) refines (c2 seq c3)
%
let seq_mono_right = prove
 ("!(c1:^ptrans23) c2 (c3:^ptrans12).
     c1 ref c2 ==> (c1 seq c3) ref (c2 seq c3)",
    LPORT[ref_DEF;seq_DEF] THEN SUPER_TAC);;
let SEQ_LEFT_CLOSE t th =
 (let t4,t3 = dest_comb (snd (dest_thm th)) in
  let t2,t1 = dest_comb t4 in 
  MATCH_MP (ISPECL[t3;t1;rand t] 
               (PORR[SYM (SPEC_ALL refines_DEF)] seq_mono_right))
           th)
 ? failwith `SEQ_LEFT_CLOSE`;;
store_rule ([RATOR;RAND]
           ,(\t. let t1 = rator(rator t) ? mk_const(`skip`,ptrans) in
                 (t1 = mk_const(`seq`,type_of t1) ? false))
           ,(\foc. \rel. let ty = type_of(rand(rator foc)) ? mk_type(`bool`,[])
                         in let fty = mk_relty(ty,ty)
                         in mk_const(`refines`,fty) ? mk_const(`=`,fty))
           ,(\foc. \rel. mk_const(`refines`,type_of rel))
           ,(\foc. \hyps. hyps)
           ,(\foc. [])
           ,SEQ_LEFT_CLOSE
           );;


% Closing after refining the body of block

   |- c' refines c
----------------------------------  BLOCK_CLOSE "block p c"
   |- (block p c') refines (block p c)
%
let submono_block = prove
 ("(c:^eptrans) ref c' ==> (block p c) ref (block p c')",
   LPORT[ref_DEF;block_DEF;implies_DEF] THEN BETA_TAC
   THEN REPEAT STRIP_TAC THEN RES_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM MATCH_ACCEPT_TAC);;
let BLOCK_CLOSE t th =
 (let t1,c = dest_comb (concl th) in
  let t2,c' = dest_comb t1 in 
  let p = rand(rator t) in
  MATCH_MP
   (ISPECL[c';c;p] 
      (GEN_ALL (DISCH_ALL (PORR[SYM (SPEC_ALL refines_DEF)] submono_block))))
   th)
 ? failwith `BLOCK_CLOSE`;;
store_rule ([RAND]
           ,(\t. let t1 = rator(rator t) ? mk_const(`skip`,ptrans) in
                 (t1 = mk_const(`block`,type_of t1) ? false))
           ,(\foc. \rel. let ty = type_of(rand foc) ? mk_type(`bool`,[])
                         in let fty = mk_relty(ty,ty)
                         in mk_const(`refines`,fty) ? mk_const(`=`,fty))
           ,(\foc. \rel. mk_const(`refines`,type_of rel))
           ,(\foc. \hyps. hyps)
           ,(\foc. [])
           ,BLOCK_CLOSE
           );;


% Closing after refining the body of a do

|- monotonic c    |- monotonic c'    |- c' refines c
------------------------------------------------------  DO_CLOSE "do g c"
             |- (do g c) refines (do g c)
%
let submono_do =
 let t1 = prove
  ("((c:^ptrans) q')implies(c' q') ==>
        ((g andd (c q')) or ((not g) andd q)) implies
        ((g andd (c' q')) or ((not g) andd q))",
   LRT[implies_DEF;and_DEF;or_DEF;not_DEF] THEN SUPER_TAC) in
 TAC_PROOF
  ((["monotonic (c:^ptrans)";"monotonic (c':^ptrans)"],
    "(c:^ptrans) ref c' ==> (do g c) ref (do g c')"),
   PORT[ref_DEF] THEN REPEAT STRIP_TAC THEN
   LPORT[UNDISCH(SPEC_ALL do_thm);UNDISCH (SPEC"c':^ptrans"(DISCH_ALL do_thm));
         fix_DEF;glb_DEF;implies_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
   UNDISCH_TAC "!q. ((c:^ptrans)q) implies (c' q)" THEN
   DISCH_THEN (\th. ASSUME_TAC (MATCH_MP (DISCH_ALL (SPEC "p:^pred" (ASSUME
    "!q.((c:^ptrans) q) implies (c' q)"))) th)) THEN
   IMP_RES_TAC t1 THEN EVERY_ASSUM (ASSUME_TAC o SPEC_ALL) THEN
   IMP_RES_TAC (CONJUNCT2 (CONJUNCT2 implies_prop)) THEN RES_TAC);;
let DO_CLOSE t th =
 (let t4,c = dest_comb (concl th) in
  let t2,c' = dest_comb t4 in 
  let g = rand(rator t) in
  MATCH_MP 
    (MATCH_MP
      (MATCH_MP 
        (ISPECL[c';c;g] (GEN_ALL (DISCH_ALL 
             (PORR[SYM (SPEC_ALL refines_DEF)] submono_do)))) 
        (mono_CONV c'))
      (mono_CONV c))
    th)
 ? failwith `DO_CLOSE`;;
store_rule ([RAND]
           ,(\t. let t1 = rator(rator t) ? mk_const(`skip`,ptrans) in
                 (t1 = mk_const(`do`,type_of t1) ? false))
           ,(\foc. \rel. let ty = type_of(rand foc) ? mk_type(`bool`,[])
                         in let fty = mk_relty(ty,ty)
                         in mk_const(`refines`,fty) ? mk_const(`=`,fty))
           ,(\foc. \rel.  mk_const(`refines`,type_of rel))
           ,(\foc. \hyps. hyps)
           ,(\foc. [])
           ,DO_CLOSE
           );;


% ----- Window closing rules for subpredicates ----- %


% Closing after weakening an assertion

   |- p' implied_by p
----------------------------------  ASSERTP_CLOSE "assert p"
   |- (assert p') refines (assert p)
%
let submonop_assert = prove
 ("(p:^pred) implies p' ==> (assert p) ref (assert p')",
   LPORT[ref_DEF;assert_DEF;implies_DEF;and_DEF] THEN BETA_TAC
   THEN REPEAT STRIP_TAC THEN RES_TAC THEN ART[]);;
let ASSERTP_CLOSE t th =
 (let (_,p'),p = (dest_comb # I) (dest_comb(concl th)) in
  MATCH_MP (ISPECL[p';p] (GEN_ALL (DISCH_ALL 
              (LPORR[SYM (SPEC_ALL implied_by_DEF);SYM (SPEC_ALL refines_DEF)]
                  submonop_assert))))
           th)
 ? failwith `ASSERTP_CLOSE`;;
store_rule ([RAND]
           ,(\t. let t1 = rator t ? mk_const(`skip`,ptrans) in
                 (t1 = mk_const(`assert`,type_of t1) ? false))
           ,(\foc. \rel. let ty = type_of(rand foc) ? mk_type(`bool`,[])
                         in let fty = mk_relty(ty,ty)
                         in mk_const(`implied_by`,fty) ? mk_const(`=`,fty))
           ,(\foc. \rel. mk_const(`refines`,type_of rel))
           ,(\foc. \hyps. hyps)
           ,(\foc. [])
           ,ASSERTP_CLOSE
           );;




% Closing after strengthening a demonic assignment

   |- P' implies2 P
------------------------------------  NONDASSP_CLOSE "nondass P"
   |- (nondass P') refines (nondass P)
%
let submonop_nondass = TAC_PROOF
 (([],"(!u:*s1. !v:*s2. P' u v ==> P u v) ==> (nondass P) ref (nondass P')"),
   LPORT[ref_DEF;nondass_DEF;implies_DEF] THEN BETA_TAC
   THEN REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC);;
let NONDASSP_CLOSE t th =
 (let [P';P] = snd(strip_comb(concl th)) in
  MATCH_MP (ISPECL[P';P] (GEN_ALL (DISCH_ALL 
             (LPORR[SYM(SPEC_ALL implies2_DEF);SYM(SPEC_ALL refines_DEF)] 
                   submonop_nondass))))
           th)
 ? failwith `NONDASSP_CLOSE`;;
store_rule ([RAND]
           ,(\t. let t1 = rator t ? mk_const(`skip`,ptrans) in
                 (t1 = mk_const(`nondass`,type_of t1) ? false))
           ,(\foc. \rel. let ty = type_of(rand foc) ? mk_type(`bool`,[])
                         in let fty = mk_relty(ty,ty)
                         in mk_const(`implies2`,fty) ? mk_const(`=`,fty))
           ,(\foc. \rel. mk_const(`refines`,type_of rel))
           ,(\foc. \hyps. hyps)
           ,(\foc. [])
           ,NONDASSP_CLOSE
           );;


% Closing after strengthening the initialisation of block

   |- p' implies p
----------------------------------  BLOCKP_CLOSE "block p c"
   |- (block p' c) refines (block p c)
%
let submonop_block = prove
 ("(p':^epred) implies p ==> (block p c) ref (block p' c)",
   LPORT[ref_DEF;block_DEF;implies_DEF] THEN BETA_TAC
   THEN REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC);;
let BLOCKP_CLOSE t th =
 (let (_,p'),p = (dest_comb # I) (dest_comb (concl th)) in
  let c = rand t in
  MATCH_MP
   (ISPECL[p';p;c] 
      (GEN_ALL (DISCH_ALL (PORR[SYM (SPEC_ALL refines_DEF)] submonop_block))))
   th)
 ? failwith `BLOCKP_CLOSE`;;
store_rule ([RATOR;RAND]
           ,(\t. let t1 = rator(rator t) ? mk_const(`skip`,ptrans) in
                 (t1 = mk_const(`block`,type_of t1) ? false))
           ,(\foc. \rel. let ty = type_of(rand(rator foc)) ? mk_type(`bool`,[])
                         in let fty = mk_relty(ty,ty)
                         in mk_const(`implies`,fty) ? mk_const(`=`,fty))
           ,(\foc. \rel. mk_const(`refines`,type_of rel))
           ,(\foc. \hyps. hyps)
           ,(\foc. [])
           ,BLOCKP_CLOSE
           );;

% --- functions for controlling the printing of conjectures --- %

let my_print_stack st =
    let rel_pic (tm:term) =
        if (is_const tm) then
            fst (dest_const tm)
        else
            `??` in
    let topwin = top_window st in
    let rel = rel_pic (relation topwin) in
    let rellen = length (explode rel) in
        print_string rel;
        print_string ` * `;
        print_ibegin (rellen + 4);
            print_unquoted_term (focus topwin);
        print_end ();
        print_newline ();;

let MY_PRINT_STACK  (():void) = my_print_stack (CURRENT_STACK ());;

% conj_print: flag for printing conjectures %
let conj_print b =
 let print1 (():void) =
  clear beg_stack_sig;
  clear set_stack_sig;
  clear psh_win_sig;
  clear cng_win_sig;
  clear pop_win_sig;
  handle beg_stack_sig (\_. PRINT_STACK ());
  handle set_stack_sig (\_. PRINT_STACK ());
  handle psh_win_sig PRINT_STACK;
  handle cng_win_sig PRINT_STACK;
  handle pop_win_sig PRINT_STACK in
 let print2 (():void) =
  clear beg_stack_sig;
  clear set_stack_sig;
  clear psh_win_sig;
  clear cng_win_sig;
  clear pop_win_sig;
  handle beg_stack_sig (\_. MY_PRINT_STACK ());
  handle set_stack_sig (\_. MY_PRINT_STACK ());
  handle psh_win_sig MY_PRINT_STACK;
  handle cng_win_sig MY_PRINT_STACK;
  handle pop_win_sig MY_PRINT_STACK in
 if b then print1() else print2();;
