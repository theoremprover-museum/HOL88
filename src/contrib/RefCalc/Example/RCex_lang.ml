% RCex_lang.ml

  An example of defining a small language with wp-semantics
  
%

new_theory `RCex_lang`;;
new_parent `RCbounded`;;
new_parent `RCactsys`;;

let autoload_defs thy =
  map (\name. autoload_theory(`definition`,thy,name))
      (map fst (definitions thy));;
let autoload_thms thy =
  map (\name. autoload_theory(`theorem`,thy,name))
      (map fst (theorems thy));;
autoload_defs `RCcommand`;;
autoload_thms `RCcommand`;;
autoload_defs `RCactsys`;;
autoload_thms `RCactsys`;;
autoload_defs `RCbounded`;;
autoload_thms `RCbounded`;;

loadf `defs`;;


% define a new recursive type of program statements %
let Stmt = define_type `Stmt`
  `Stmt = ABORT
        | SKIP
        | ASSIGN (*->*)
        | SEQ Stmt Stmt
        | IF (*->bool) Stmt (*->bool) Stmt
        | DO (*->bool) Stmt`;;
let Stmt_induct =
 save_thm(`Stmt_induct`,prove_induction_thm Stmt);;

% Define the semantic function WP recursively over statements %
let WP_DEF = new_recursive_definition false Stmt `WP_DEF`
 "(WP (ABORT:(*)Stmt) = abort) /\
  (WP SKIP  = skip) /\
  (WP (ASSIGN e) = assign e) /\
  (WP (SEQ s s') = seq (WP s) (WP s')) /\
  (WP (IF b s b' s') = if2 (b,WP s) (b',WP s')) /\
  (WP (DO b s) = do b (WP s))";;

% Define semantic equivalence of statements %
let EQ_DEF = new_infix_definition(`EQ_DEF`,
 "$EQ (s:(*)Stmt) s' = (WP s = WP s')");;


% --- load definitions needed to prove facts about the language --- %

load_library `taut`;;

% --- all statements are monotonic and continuous --- %

let MONO = TAC_PROOF
 (([],"!s. monotonic (WP (s:(*)Stmt))"),
  INDUCT_THEN Stmt_induct MP_TAC THEN PORT[WP_DEF] THENL
  [MATCH_ACCEPT_TAC mono_abort
  ;MATCH_ACCEPT_TAC mono_skip
  ;MATCH_ACCEPT_TAC mono_assign
  ;REPEAT STRIP_TAC THEN MATCH_MP_TAC mono_seq THEN ART[]
  ;REPEAT STRIP_TAC THEN MATCH_MP_TAC mono_if2 THEN ART[]
  ;STRIP_TAC THEN MATCH_MP_TAC mono_do THEN ART[]
  ]);;

save_thm(`MONO`,MONO);;


% --- simple example 1: equivalence of SKIP and identity assignment  --- %

g "SKIP EQ (ASSIGN \(v:*).v)";;
e(LPORT[EQ_DEF;WP_DEF]);;
e(FUN_TAC THEN LPORT[skip_DEF;assign_DEF]);;
e(FUN_TAC THEN REFL_TAC);;


close_theory();;

