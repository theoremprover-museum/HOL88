% mk_proofaux1.ml

  Auxiliary stuff needed in the proof theories: definitions
%

load_library `finite_sets`;;
load_library `more_lists`;;
new_theory  `proofaux`;;
loadf `defs/defs`;;


% General functions for handling lists  %

let EVERY2_DEF = new_list_rec_definition(`EVERY2_DEF`,
  "(EVERY2 (P:*->**->bool) [] yl = T) /\
   (EVERY2 P (CONS x xl) yl = P x (HD yl) /\ EVERY2 P xl (TL yl))");;
let EVERY2 = save_thm(`EVERY2`,prove
 ("(!(P:*->**->bool). EVERY2 P [] [] = T) /\
   (!(P:*->**->bool) x xl y yl.
        EVERY2 P (CONS x xl) (CONS y yl) = P x y /\ EVERY2 P xl yl)",
  REWRITE_TAC[EVERY2_DEF;HD;TL]) );;

let EVERY3_DEF = new_list_rec_definition(`EVERY3_DEF`,
  "(!P:*->**->***->bool. !yl. EVERY3 P [] yl zl = T) /\
   (!P x xl yl zl. EVERY3 P (CONS x xl) yl zl = 
                   P x (HD yl) (HD zl) /\ EVERY3 P xl (TL yl) (TL zl))");;
let EVERY3 = save_thm(`EVERY3`,prove
 ("(!(P:*->**->***->bool). EVERY3 P [] [] [] = T) /\
   (!(P:*->**->***->bool) x xl y yl.
      EVERY3 P(CONS x xl)(CONS y yl)(CONS z zl) = P x y z/\EVERY3 P xl yl zl)",
  REWRITE_TAC[EVERY3_DEF;HD;TL]) );;

let MAP1_DEF = new_list_rec_definition(`MAP1_DEF`,
  "(MAP1 (f:*->***) ([]:(*#**)list) = []) /\
   (MAP1 f (CONS xz xzl) = CONS(f(FST xz),SND xz) (MAP1 f xzl))");;

let XMAP2_DEF = new_list_rec_definition(`XMAP2_DEF`,
 "(XMAP2 (f:*->**->***) [] yl = []) /\
  (XMAP2 f (CONS x xl) yl = CONS(f x (HD yl))(XMAP2 f xl (TL yl)))");;
let XMAP2 = save_thm(`XMAP2`,prove
 ("(!(f:*->**->***). XMAP2 f [] [] = []) /\
   (!(f:*->**->***) x xl y yl.
      XMAP2 f (CONS x xl) (CONS y yl) = CONS(f x y) (XMAP2 f xl yl))",
  REWRITE_TAC[XMAP2_DEF;HD;TL]) );;

let FMAP_DEF = new_list_rec_definition(`FMAP_DEF`,
 "(FMAP ([]:(*->**)list) xl = []) /\
  (FMAP (CONS f fl) xl = CONS(f(HD xl))(FMAP fl (TL xl)))");;
let FMAP = save_thm(`FMAP`,prove
 ("(FMAP ([]:(*->**)list) [] = []) /\
   (!(f:*->**) fl x xl.
       FMAP (CONS f fl) (CONS x xl) = CONS(f x) (FMAP fl xl))",
  REWRITE_TAC[FMAP_DEF;HD;TL]) );;

let lor_DEF = new_list_rec_definition(`lor_DEF`,
  "(lor [] = F) /\
   (lor (CONS h t) = h \/ lor t)");;
let land_DEF = new_list_rec_definition(`land_DEF`,
  "(land [] = T) /\
   (land (CONS h t) = h /\ land t)");;

let mem_DEF = new_list_rec_definition(`mem_DEF`,
 "(mem x [] = F) /\
  (mem x (CONS (h:*) t) = (x = h) \/ mem x t)");;
let mem1_DEF = new_list_rec_definition(`mem1_DEF`,
 "(mem1 x [] = F) /\
  (mem1 x (CONS (h:*#**) t) = (x = FST h) \/ mem1 x t)");;
let mem2_DEF = new_list_rec_definition(`mem2_DEF`,
 "(mem2 x [] = F) /\
  (mem2 x (CONS (h:*#**) t) = (x = SND h) \/ mem2 x t)");;
let corr1_DEF = new_list_rec_definition(`corr1_DEF`,
 "(corr1 x [] = @y.T) /\
  (corr1 x (CONS (h:*#**) t) = ((x = FST h)=> SND h | corr1 x t))");;
let corr2_DEF = new_list_rec_definition(`corr2_DEF`,
 "(corr2 x [] = @y.T) /\
  (corr2 x (CONS (h:*#**) t) = ((x = SND h)=> FST h | corr2 x t))");;

let lmem_DEF = new_list_rec_definition(`lmem_DEF`,
 "(lmem [] l = T) /\
  (lmem (CONS (x:*) xl) l = mem x l /\ lmem xl l)");;

let idlist_DEF = new_list_rec_definition(`idlist_DEF`,
 "(idlist ([]:(*#*)list) = T) /\
  (idlist (CONS h t) = (FST h = SND h) /\ idlist t)");;

let LAPPEND_DEF = new_list_rec_definition(`LAPPEND_DEF`,
 "(LAPPEND [] = []) /\
  (LAPPEND (CONS (h:(*)list) t) = APPEND h (LAPPEND t))");;

let nocontr_DEF = new_list_rec_definition(`nocontr_DEF`,
 "(nocontr [] = T) /\
  (nocontr (CONS (xy:*#**) xyl) = 
     (~mem2 (SND xy) xyl \/ (corr2 (SND xy) xyl = FST xy)) /\
     nocontr xyl)");;


% --- functions on sets --- %

let SEVERY_SPEC = new_definition(`SEVERY_SPEC`,
  "SEVERY P (s:(*)set) = !x. x IN s ==> P x");;
let SEVERY_DEF = save_thm(`SEVERY_DEF`,prove
 ("(!(P:*->bool). SEVERY P {} = T) /\
   (!P(x:*)s. SEVERY P (x INSERT s) = P x /\ SEVERY P s)",
   CONJ_TAC THENL
   [LRT[SEVERY_SPEC;NOT_IN_EMPTY]
   ;REPEAT GEN_TAC THEN LRT[SEVERY_SPEC;IN_INSERT] THEN EQ_TAC THENL
    [STRIP_TAC THEN CONJ_TAC THENL
     [POP_ASSUM (ACCEPT_TAC o( RR[] o (SPEC "x:*")))
     ;GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ART[]
     ]
    ;STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN RES_TAC THEN ART[]
   ]]) );;
let EVERYS_DEF = new_list_rec_definition(`EVERYS_DEF`,
  "(EVERYS P ([]:((*)set)list) = T) /\
   (EVERYS P (CONS h t) = SEVERY P h /\ EVERYS P t)");;

% --- mixing sets and lists --- %

let LUNION_DEF = new_list_rec_definition(`LUNION_DEF`,
 "(LUNION ([]:((*)set)list) = {}) /\
  (LUNION (CONS h t) = h UNION (LUNION t))");;


% --- Auxiliary functions needed in proof about provability --- %


let PROX_DEF = new_list_rec_definition(`PROX_DEF`,
  "(PROX s [] = []) /\
   (PROX s (CONS (h:*#**#***) t) = 
      ((FST(SND h) = s) => PROX s t | CONS h (PROX s t)))");;

let EVERYX_DEF = new_list_rec_definition(`EVERYX_DEF`,
 "(EVERYX (R:*->**->bool) [] Y = T) /\
  (EVERYX R (CONS h t) Y = R h(HD Y) /\ EVERYX R t(TL Y))");;

