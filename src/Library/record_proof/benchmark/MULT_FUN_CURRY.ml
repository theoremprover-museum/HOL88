timer true;;

set_flag(`compile_on_the_fly`, true);;

new_theory `MULT_FUN_CURRY`;;

new_proof_file `MULT_FUN_CURRY.prf`;;

begin_proof`MULT_FUN_CURRY`;;
let MULT_FUN_CURRY =
 new_prim_rec_definition
  (`MULT_FUN_CURRY`,
   "(MULT_FUN_CURRY 0 i1 i2 m t =
     (t => (m,0,t) | ((i1=0)=>m|i2+m),0,T)) /\
    (MULT_FUN_CURRY (SUC n) i1 i2 m t =
     (t => (m,SUC n,t) |
           MULT_FUN_CURRY n i1 i2 ((i1=0)=>m|i2+m) (((n-1)=0) \/ (i2=0))))");;
end_proof();;

let MULT_FUN_CURRY_THM =
 prove_thm
  (`MULT_FUN_CURRY_THM`,
   "!i1 i2 m n t.
     MULT_FUN_CURRY n i1 i2 m t =
      (t => 
       (m,n,t) | 
       MULT_FUN_CURRY (n-1) i1 i2 ((i1=0)=>m|i2+m) ((((n-1)-1)=0)\/(i2=0)))",
   REPEAT GEN_TAC
    THEN STRUCT_CASES_TAC(SPEC "n:num" num_CASES)
    THEN ASM_CASES_TAC "t:bool"
    THEN ASM_REWRITE_TAC[MULT_FUN_CURRY;SUB;SUC_SUB1]);;

begin_proof`MULT_FUN`;;
let MULT_FUN =
 new_definition
  (`MULT_FUN`, "MULT_FUN((i1,i2),m,n,t) = MULT_FUN_CURRY n i1 i2 m t");;
end_proof();;

let MULT_FUN_DEF =
 prove_thm
  (`MULT_FUN_DEF`,
   "!i1 i2 m n t.
     MULT_FUN((i1,i2),m,n,t) =
      (t => 
       (m,n,t) | 
       MULT_FUN((i1,i2),((i1=0)=>m|i2+m),n-1,((((n-1)-1)=0) \/ (i2=0))))",
   REPEAT GEN_TAC
    THEN REWRITE_TAC[MULT_FUN]
    THEN ACCEPT_TAC(SPEC_ALL MULT_FUN_CURRY_THM));;

close_proof_file();;

quit();;
