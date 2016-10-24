% File: RCcommand_ex1.ml

  Computing a simple weakest precondition
%


% compute what represents WP(x:=x+y;y:=x+y , y<=x) %

let th1 = REFL "((assign \(x,y).(x+y,y)) seq (assign \(x,y).(x,x+y)))
                (\(x,y).y <= x)";;

let th2 = RHS_RRL[seq_DEF;assign_DEF] th1;;

let th3 = RR[](PBETA_RULE th2);;

let th4 = PORR[ADD_SYM]ADD_MONO_LESS_EQ;;

let th5 = RR[NOT_LESS_0]
           (RHS_RRL[LESS_OR_EQ]
            (RR[ADD_CLAUSES]
             (SPECL ["m:num";"n:num";"0"] ADD_MONO_LESS_EQ)));;

let thm1 = RR[th4;th5]th3;;

%
thm1 = 
|- ((assign(\(x,y). (x + y,y))) seq (assign(\(x,y). (x,x + y))))
   (\(x,y). y <= x) =
   (\v. ((FST v) + (SND v)) <= (FST v))
%


let thm2 =
  RR[](CONV_RULE (RHS_CONV (PALPHA_CONV "(x:num,y:num)")) thm1);;

%
|- ((assign(\(x,y). (x + y,y))) seq (assign(\(x,y). (x,x + y))))
   (\(x,y). y <= x) =
   (\(x,y). (x + y) <= x)
%
