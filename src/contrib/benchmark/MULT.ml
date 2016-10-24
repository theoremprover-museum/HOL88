% This file, when read into lcf_lsm, performs the verification of 
  the multiplier%

new_theory`MULT`;;

new_constant(`MULT`, ":num -> dev");;

new_axiom
 (`MULT`,
  "MULT m == dev{i1,i2,o}.{o=m}; MULT(i1*i2)");;

close_theory();;

new_theory `prims`;;

map new_constant [`MUX`          , ":dev";
                  `REG`          , ":num->dev";
                  `FLIPFLOP`     , ":bool->dev";
                  `DEC`          , ":dev";
                  `ADDER`        , ":dev";
                  `ZERO_TEST`    , ":dev";
                  `OR_GATE`      , ":dev";
                  `ZERO`         , ":dev"];;

map
 new_axiom
 [(`MUX`      , "MUX == dev{switch,i1:num,i2:num,o}.{o=(switch->i1|i2)};MUX");
  (`REG`      , "REG(n) == dev{i,o}.{o=n};REG(i)");
  (`FLIPFLOP` , "FLIPFLOP(t) == dev{i,o}.{o=t};FLIPFLOP(i)");
  (`DEC`      , "DEC == dev{i,o}.{o=(i-1)};DEC");
  (`ADDER`    , "ADDER == dev{i1,i2,o}.{o=(i1+i2)};ADDER");
  (`ZERO_TEST`, "ZERO_TEST == dev{i,o}.{o=(i=0)};ZERO_TEST");
  (`OR_GATE`  , "OR_GATE == dev{i1,i2,o}.{o=(i1 OR i2)};OR_GATE");
  (`ZERO`     , "ZERO == dev{o}.{o=0}; ZERO")];;

close_theory();;

new_theory`MULT_IMP`;;

new_parent`prims`;;

new_constant(`MULT_IMP` , ":num#num#bool -> dev");;

"[done;b1;b2;b3;b4]:bool list",
"[l1;l2;l3;l4;l5;l6;l7;l8;l9;l10]:num list";;

new_axiom
 (`MULT_IMP`,
  "MULT_IMP(m,n,t) ==
    [| MUX         rn[switch=done;i1=l9;i2=l8;o=l7]
     | REG(m)      rn[i=l7]
     | ADDER       rn[i1=l9;i2=o;o=l8]
     | DEC         rn[i=i1;o=l6]
     | MUX         rn[switch=done;i1=l6;i2=l4;o=l5]
     | MUX         rn[switch=done;i2=l3;o=l1]
     | REG(n)      rn[i=l1;o=l2]
     | DEC         rn[i=l2;o=l3]
     | DEC         rn[i=l3;o=l4]
     | ZERO        rn[o=l10]
     | MUX         rn[switch=b4;i1=l10;o=l9]
     | ZERO_TEST   rn[i=i1;o=b4]
     | ZERO_TEST   rn[i=l5;o=b1]
     | ZERO_TEST   rn[i=i2;o=b2]
     | OR_GATE     rn[i1=b1;i2=b2;o=b3]
     | FLIPFLOP(t) rn[i=b3;o=done] |]
    hide {b1,b2,b3,b4,l1,l2,l3,l4,l5,l6,l7,l8,l9,l10}");;

close_theory();;

new_theory`MULT_VER`;;

map new_parent [`MULT`;`MULT_IMP`];;

save_thm
 (`MULT_IMP_EXPAND`,
   EXPAND_IMP
    []
    (map
     (axiom `prims`)
     [`MUX`;`REG`;`FLIPFLOP`;`DEC`;`ADDER`;
      `ZERO_TEST`;`ZERO`;`OR_GATE`])
    (axiom `MULT_IMP` `MULT_IMP`));;

save_thm
 (`MULT_IMP_UNTIL`,
  UNTIL `mult_fn` `done` (theorem `MULT_VER` `MULT_IMP_EXPAND`));;

new_constant(`MULT_FN`, ":num#num#num#num#bool -> num#num#bool");;

new_axiom
 (`MULT_FN`,
   "!i1 i2 m n t.
     MULT_FN(i1,i2,m,n,t) ==
      (t ->
       (m,n,t) |
       MULT_FN
        (i1,
         i2,
         (t -> (i1 = 0 -> 0 | i2) | (i1 = 0 -> 0 | i2) + m),
         (t -> i1 | n - 1),
         ((t -> i1 - 1 | (n - 1) - 1) = 0) OR (i2 = 0)))");;

close_theory();;

let lemma =
  ASSUME
   "!i1 i2.
     MULT_FN(i1,i2,(i1=0->0|i2),i1,((i1-1)=0)OR(i2=0)) ==
      (i1*i2, (((i1-1)=0)OR(i2=0)->i1|1), T)";;

let th1 =
 MP 
  (SPEC "MULT_FN" (theorem `MULT_VER` `MULT_IMP_UNTIL`))
  (axiom `MULT_VER` `MULT_FN`);;

let th2 =
 REWRITE_RULE
  [BOOL_COND_CLAUSES;lemma]
  (SPEC "T" (SPEC "n" (SPEC "m" th1)));;

let th3 = UNIQUENESS (axiom `MULT` `MULT`) th2;;

save_thm(`CORRECTNESS`, th3);;



