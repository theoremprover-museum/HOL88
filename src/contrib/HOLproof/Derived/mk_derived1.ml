% mk_derived1.ml

  HOL-proofs: derived inferences and related concepts
%

new_theory `derived`;;
%
load_library `finite_sets`;;
load_library `more_lists`;;
new_parent `proof`;;
loadf `defs/defs`;;
loadf `proof_convs`;;
loadf `defs/ld_pair`;;

let autoload_defs thy =
  map (\name. autoload_theory(`definition`,thy,name))
      (map fst (definitions thy));;
let autoload_thms thy =
  map (\name. autoload_theory(`theorem`,thy,name))
      (map fst (theorems thy));;

autoload_defs `proofaux`;;
autoload_thms `proofaux`;;
autoload_defs `Type`;;
autoload_thms `Type`;;
autoload_defs `Pterm`;;
autoload_thms `Pterm`;;
autoload_defs `inference`;;
autoload_thms `inference`;;
autoload_defs `proof`;;
autoload_thms `proof`;;
autoload_defs `derived`;;
autoload_thms `derived`;;
%

% --- the notion of a derived inference rule --- %

let Dinf_DEF = new_definition(`Dinf_DEF`,
  "Dinf Typl Conl Axil (name:string) s sl
    = EVERY Pseq_boolean  sl /\
      EVERY (Pseq_well_typed Typl Conl) sl
      ==> Provable Typl Conl (APPEND sl Axil) s");;


% --- proof with derived inferences --- %

let Is_Dproof_SPEC = new_list_rec_definition(`Is_Dproof_SPEC`,
 "(Is_Dproof Typl Conl Axil [] = T) /\
  (Is_Dproof Typl Conl Axil (CONS nssl P) = 
    Is_Dproof Typl Conl Axil P /\ 
    lmem(SND(SND nssl))(MAP (FST o SND) P) /\
    Dinf Typl Conl Axil (FST nssl) (FST(SND nssl)) (SND(SND nssl)))");;
let Is_Dproof_DEF = save_thm(`Is_Dproof_DEF`,prove(
 "(Is_Dproof Typl Conl Axil [] = T) /\
  (Is_Dproof Typl Conl Axil (CONS (n,s,sl) P) = 
    Is_Dproof Typl Conl Axil P /\ 
    lmem sl (MAP (FST o SND) P) /\ Dinf Typl Conl Axil n s sl)",
  RT[Is_Dproof_SPEC]));;


% --- Dproofs are OK --- %

let Dinf_Provable = mk_thm([],
 "!Typl Conl Axil name s sl.
   Dinf Typl Conl Axil name s sl /\ EVERY (Provable Typl Conl Axil) sl
      ==> Provable Typl Conl Axil s");;

let Dproof_Provable = save_thm(`Dproof_Provable`,prove
 ("!P. Is_Dproof Typl Conl Axil P
          ==> EVERY (Provable Typl Conl Axil) (MAP (FST o SND) P)",
  PORT[o_DEF] THEN INDUCT_THEN list_INDUCT ASSUME_TAC THENL
  [LRT[MAP;EVERY_DEF]
  ;P_PGEN_TAC "n:string,s:Psequent,sl:(Psequent)list" THEN
   LPORT[Is_Dproof_DEF;MAP;EVERY_DEF;o_DEF] THEN BETA_TAC THEN RT[] THEN
   REPEAT STRIP_TAC THEN RES_TAC THEN
   MATCH_MP_TAC Dinf_Provable THEN
   EXISTS_TAC "n:string" THEN EXISTS_TAC "sl:(Psequent)list" THEN
   ART[] THEN IMP_RES_TAC LMEM_EVERY
  ]) );;




