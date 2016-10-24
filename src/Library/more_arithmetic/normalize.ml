%----------------------------------------------------------------

 FILE           : normalize.ml
 DESCRIPTION    : Defines a tactic for normalizing arithmetic 
                  expressions involving natural numbers.
 READS FILES    : <none>                                                
 WRITES FILES   : <none>
                                                                        
 AUTHOR         : P. J. Windley                                         
 DATE           : 20 FEB 89

----------------------------------------------------------------%
%< Some comments of WP:>%


%< because of the assymetry of "-" (3 - 6 = 0) this normalization does not
   normalize terms with substractions >%
  

%< to avoid the name clash with the :zet MULT_ASSOC>%

let NUM_MULT_ASSOC = theorem `arithmetic` `MULT_ASSOC`;;

%<-------------------------------------------------------------------------->%

% ADD3_SYM = |- !a b c. (a + b) + c = (a + c) + b %

let ADD3_SYM =
 TAC_PROOF
  (([], "!a b c. (a+b)+c = (a+c)+b"),
   REPEAT GEN_TAC
    THEN REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)]
    THEN SUBST_TAC[SPECL["b:num";"c:num"]ADD_SYM]
    THEN REFL_TAC);;

%<-------------------------------------------------------------------------->%

% MULT3_SYM = |- !a b c. (a * b) * c = (a * c) * b %

let MULT3_SYM =
 TAC_PROOF
  (([], "!a b c. (a*b)*c = (a*c)*b"),
   REPEAT GEN_TAC
    THEN REWRITE_TAC[SYM(SPEC_ALL NUM_MULT_ASSOC)]
    THEN SUBST_TAC[SPECL["b:num";"c:num"]MULT_SYM]
    THEN REFL_TAC);;

%<-------------------------------------------------------------------------->%

let const_name  = fst o dest_const;;

let var_name  = fst o dest_var;;

let is_plus_term t =
   if is_comb t & ((const_name (fst (strip_comb t))) = `+`) then
      true
   else
      false;;

let is_mult_term t =
   if is_comb t & ((const_name (fst (strip_comb t))) = `*`) then
      true
   else
      false;;

%<-------------------------------------------------------------------------->%

%
   ADD_SYM_CONV "a+b"      --> |- a+b     = b+a       if b << a
   ADD_SYM_CONV "(a+b)+c"  --> |- (a+b)+c = (a+c)+b   if c << b

%

let ADD_SYM_CONV t =
 let op1,[t1;t2] = strip_comb t
 in
 if op1 = "$+" & not (is_plus_term t1) & (t2 << t1)    % t=a+b %
  then SPECL[t1;t2]ADD_SYM
  else
   (let op2,[t3;t4] = strip_comb t1
    in
    if op1 = "$+" & op2 = "$+" & (t2 << t4)                % t=(a+b)+c %
     then SPECL[t3;t4;t2]ADD3_SYM
     else fail);;

%<-------------------------------------------------------------------------->%
%
   MULT_SYM_CONV "a*b"      --> |- a*b     = b*a       if b << a
   MULT_SYM_CONV "(a*b)*c"  --> |- (a*b)*c = (a*c)*b   if c << b

%

let MULT_SYM_CONV t =
 let op1,[t1;t2] = strip_comb t
 in
 if op1 = "$*" & not (is_mult_term t1) & (t2 << t1)    % t=a*b %
  then SPECL[t1;t2]MULT_SYM
  else
   (let op2,[t3;t4] = strip_comb t1
    in
    if op1 = "$*" & op2 = "$*" & (t2 << t4)                % t=(a*b)*c %
     then SPECL[t3;t4;t2]MULT3_SYM
     else fail);;

%<-------------------------------------------------------------------------->%

%
   ADD_ASSOC_CONV "a+(b+c)"  --> |- a+(b+c) = (a+b)+c
%

let ADD_ASSOC_CONV t =
 let op1,[t1;t2] = strip_comb t
 in
 let op2,[t3;t4] = strip_comb t2
 in
 if op1 = "$+"  & op2 = "$+"
  then SPECL[t1;t3;t4]ADD_ASSOC
  else fail;;

%<-------------------------------------------------------------------------->%

%
   ASSOC_ADD_CONV "(a+b)+c"  --> |- (a+b)+c = a+(b+c)
%

let assoc_add = (GEN_ALL o SYM o SPEC_ALL) ADD_ASSOC;;

let ASSOC_ADD_CONV t =
 let op1,[t1;t2] = strip_comb t
 in
 let op2,[t3;t4] = strip_comb t1
 in
 if op1 = "$+"  & op2 = "$+"
  then SPECL[t3;t4;t2] assoc_add
  else fail;;


%<-------------------------------------------------------------------------->%

%
   MULT_ASSOC_CONV "a*(b*c)"  --> |- a*(b*c) = (a*b)*c
%

let MULT_ASSOC_CONV t =
 let op1,[t1;t2] = strip_comb t
 in
 let op2,[t3;t4] = strip_comb t2
 in
 if op1 = "$*"  & op2 = "$*"
  then SPECL[t1;t3;t4] NUM_MULT_ASSOC
  else fail;;


%<-------------------------------------------------------------------------->%
%
   ASSOC_MULT_CONV "(a*b)*c"  --> |- (a*b)*c = a*(b*c)
%

let assoc_mult = (GEN_ALL o SYM o SPEC_ALL) NUM_MULT_ASSOC;;

let ASSOC_MULT_CONV t =
 let op1,[t1;t2] = strip_comb t
 in
 let op2,[t3;t4] = strip_comb t1
 in
 if op1 = "$*"  & op2 = "$*"
  then SPECL[t3;t4;t2] assoc_mult
  else fail;;

%<-------------------------------------------------------------------------->%

%
  WP - 15-6-1990, 
  ADD_DISTRIB_CONV "a*(b+c)" --> |- (a*b) + (a*c)
                   "(a+b)*c" --> |- (a*c) + (b*c)
%


let ADD_DISTRIB_CONV t = 
  let op1,[t2;t3] = strip_comb t
  in 
  let op2,l2 = strip_comb t2 and op3,l3 = strip_comb t3
  in
  if op1 = "$*" & op2 = "$+"
  then
      SPECL (l2 @ [t3]) RIGHT_ADD_DISTRIB
  if op1 = "$*" & op3 = "$+"
  then
      SPECL (l3 @ [t2]) LEFT_ADD_DISTRIB
  else fail;;



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

                   %< The normalization conversion  >%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

             %< normalization of term only containing + >%

let ADD_NORMALIZE_CONV = 
  TOP_DEPTH_CONV ADD_ASSOC_CONV
  THENC TOP_DEPTH_CONV ADD_SYM_CONV;;

%<-------------------------------------------------------------------------->%

                %< terms with + and *; without distributivity >%

let NORMALIZE_CONV = 
  TOP_DEPTH_CONV ADD_ASSOC_CONV
  THENC TOP_DEPTH_CONV ADD_SYM_CONV
  THENC TOP_DEPTH_CONV MULT_ASSOC_CONV
  THENC TOP_DEPTH_CONV MULT_SYM_CONV;;

%<-------------------------------------------------------------------------->%

                %< terms with + and *; with distributivity >%
                      %< WP 15-6-1990 >%

let NUM_NORMALIZE_CONV = 
     TOP_DEPTH_CONV ADD_DISTRIB_CONV
     THENC NORMALIZE_CONV;;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

                        %< The related tactics >%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


let ADD_NORMALIZE_TAC =
   CONV_TAC ADD_NORMALIZE_CONV
   THEN (REFL_TAC ORELSE ALL_TAC);;


let NORMALIZE_TAC =
   PURE_REWRITE_TAC [
       RIGHT_ADD_DISTRIB; 
       LEFT_ADD_DISTRIB; 
      ]       
   THEN CONV_TAC NORMALIZE_CONV
   THEN (REFL_TAC ORELSE ALL_TAC);;

%<-------------------------------------------------------------------------->%

% Example


set_goal([], "((((a + (b + a)) + (d + e)) + e) + f) + h =
         a + ((e + f) + ((e + (d + (b + a))) + h))");;

expand(NORMALIZE_TAC);;

expand(ADD_NORMALIZE_TAC);;

set_goal([],
   "(((((a * 2 * b) + (bee + a)) + (deer + (e * 2 * r))) + e) + f) + h =
       (b * a * 2) + ((e + f) + (((r * e * 2) + (deer + (bee + a))) + h))"
     );;

expand(NORMALIZE_TAC);;

set_goal([], "(adam + bee) * cable = (cable * bee) + (cable * adam)");;

expand(NORMALIZE_TAC);;

set_goal([],
   "((((((a + t) * 2 * b) + (bee + a)) + 
         (deer + (e * 2 * r))) + e) + (f * 4)) + h = 
    ((((((((2 * a) + ((2 * e) * r)) + (4 * f)) + ((2 * b) * t)) + a) +
       bee) + deer) + e) + h");;

expand(NORMALIZE_TAC);;
%
%<------------------------------------------------------------------------->%


