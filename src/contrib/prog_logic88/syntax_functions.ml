
%
  ML code for generating the semantic representation of a
  partial correctness specification from terms representing
  the concrete syntax.
%

lisp`(load (concat %lib-dir '|/prog_logic88/parse_hacks|))`;;
lisp`(load (concat %lib-dir '|/prog_logic88/print_hacks|))`;;

% Fancy parser and printer %

let pretty_on(():void)  = set_flag(`print_lang`, true)
and pretty_off(():void) = set_flag(`print_lang`, false);;

pretty_on();;

% Some stuff needed for HOL88, but included in the old HOL %


%
 mk_CONS_ty ty = ":^ty -> ^ty list -> ^ty list"
%

let mk_CONS_ty ty = 
 let listty = mk_type(`list`,[ty])
 in mk_type(`fun`,[ty; mk_type(`fun`,[listty;listty])]);;

%
 mk_NIL ty = "NIL:(^ty list)"
%

let mk_NIL ty = mk_const(`NIL`, mk_type(`list`,[ty]));;

%
 ol_cons tm1 tm2 = "CONS ^tm1 ^tm2"
%

let ol_cons tm1 tm2 = 
 mk_comb(mk_comb(mk_const(`CONS`, mk_CONS_ty(type_of tm1)),tm1), tm2);;

%
 mk_list ty [tm1; ... tmn] = "[^tm1; ... ;^tmn]:(^ty list)"
%

let mk_list ty l = itlist ol_cons l (mk_NIL ty);;

% dest_SPEC "SPEC P C Q"   --->   ("P","C","Q") %

let dest_SPEC tm =
 (let tm1,tm2 = dest_comb tm
  in
  let tm3,tm4 = dest_comb tm1
  in
  let tm5,tm6 = dest_comb tm3
  in
  if tm5 = "SPEC" 
   then (tm6,tm4,tm2) 
   else fail)
 ? failwith `dest_SPEC`;;

% dest_VAR "VAR X"   --->   "X" %

let dest_VAR tm =
 (let tm1,tm2 = dest_comb tm
  in
  if tm1 = "VAR" 
   then tm2
   else fail)
 ? failwith `dest_VAR`;;

% dest_ASSIGN "X := E"   --->   ("X","E") %

let dest_ASSIGN tm =
 (let tm1,tm2 = dest_comb tm
  in
  let tm3,tm4 = dest_comb tm1
  in
  if tm3 = "$:=" 
   then (tm4,tm2)
   else fail)
 ? failwith `dest_ASSIGN`;;

% dest_list "[C1; ... ;Cn]"   --->   ["C1"; ... ;"Cn"] %

letrec dest_list tm =
 (let tok,ty = dest_const tm
  in
  if tok = `NIL` then [] else fail)
 ?
 (let tm1,tm2 = dest_comb tm
  in
  let tm3,tm4 = dest_comb tm1
  in
  let tok,ty = dest_const tm3
  in
  if tok = `CONS` then tm4.(dest_list tm2) else fail)
 ? failwith `dest_list`;;

% dest_SEQ "C1; ... ;Cn"   --->   ["C1"; ... ;"Cn"] %

let dest_SEQ tm =
 (let tm1,tm2 = dest_comb tm
  in
  if tm1 = "SEQ" 
   then dest_list tm2
   else fail)
 ? failwith `dest_SEQ`;;

% dest_BLOCK "BLOCK[VAR X1; ... ;VAR Xm;C1; ... ;Cn]"   --->   
             (["X1"; ... ;"Xm"], ["C1"; ... ;"Cn"])
%

let dest_BLOCK tm =
 (let tm1,tm2 = dest_comb tm
  in
  if tm1 = "BLOCK" 
   then 
    (let l = dest_list tm2
     in
     let l1,l2 = partition (can dest_VAR) l
     in
     (map dest_VAR l1, l2))
   else fail)
 ? failwith `dest_BLOCK`;;

% dest_IF1 "IF1 S C"   --->   ("S", "C") %

let dest_IF1 tm =
 (let tm1,tm2 = dest_comb tm
  in
  let tm3,tm4 = dest_comb tm1
  in
  if tm3 = "IF1" 
   then (tm4,tm2)
   else fail)
 ? failwith `dest_IF1`;;

% dest_IF2 "IF1 S C1 C2"   --->   ("S", "C1", "C2") %

let dest_IF2 tm =
 (let tm1,tm2 = dest_comb tm
  in
  let tm3,tm4 = dest_comb tm1
  in
  let tm5,tm6 = dest_comb tm3
  in
  if tm5 = "IF2" 
   then (tm6,tm4,tm2)
   else fail)
 ? failwith `dest_IF2`;;

% dest_WHILE "WHILE S C"   --->   ("S", "C") %

let dest_WHILE tm =
 (let tm1,tm2 = dest_comb tm
  in
  let tm3,tm4 = dest_comb tm1
  in
  if tm3 = "WHILE" 
   then (tm4,tm2)
   else fail)
 ? failwith `dest_WHILE`;;

% dest_ASSERT "ASSERT A"   --->   "A" %

let dest_ASSERT tm =
 (let tm1,tm2 = dest_comb tm
  in
  if tm1 = "ASSERT" 
   then tm2
   else fail)
 ? failwith `dest_ASSERT`;;

% trans_term : term -> term -> term

     "s", " ... x ..."  -->  "\s. ... s `x` ..."
%

% Old version:

let trans_term s tm =
 letrec tr_fun tm =
 (
  (let tok,ty = dest_var tm
   in
   if ty = ":num" 
    then mk_comb(s, mk_const((`\`` ^ tok ^ `\``), ":string"))
    else fail)
  ? 
  (if is_const tm then tm else fail)
  ?
  (let rt,rd = dest_comb tm
   in
   mk_comb(tr_fun rt,tr_fun rd))
  ?
  failwith `trans_term`
 )
 in
 mk_abs(s,tr_fun tm);;
%

% "x"   --->   "`x`" %

let prime_var tm = mk_const(`\`` ^ fst(dest_var tm) ^ `\``,  ":string");;

%
 A ghost variable will be one that satisfies the predicate is_ghost.
 This is an assignable predicate; we initialize it to the predicate

    is_lower : tok -> bool   

 which tests whether a token is made up of lower case letters.
%

let is_lower tok =
 can (map (\x. let n = ascii_code x 
               in
               if not((96 < n) & (n < 122)) then fail))
     (explode tok);;

letref is_ghost = is_lower;;

let trans_term s tm =
 let subst_list = 
  mapfilter
   (\t. 
     if (type_of t = ":num") & (not(is_ghost(fst(dest_var t))))
     then (mk_comb(s, prime_var t),t)
     else fail)
   (frees tm)
 in 
 mk_abs(s, subst subst_list tm);;

% Test examples:

     trans_term "s:string->num" "x+1";;
     trans_term "s:string->num" "(X:num=x) /\ (Y:num=y)";;
     trans_term "s:string->num" "(R < Y) /\ (X = R + (Y*Q))";;
%

% TRANS_THM instantiates a theorem using INST 

     |- ... x ...  -->  |- !s. ... s `x` ..."

%

let TRANS_THM th =
 let s = "s:state"
 in
 let subst_list = 
  mapfilter
   (\t. 
     if (type_of t = ":num") & (not(is_ghost(fst(dest_var t))))
     then (mk_comb(s, prime_var t),t)
     else fail)
   (frees(concl th))
 in 
 GEN s (INST subst_list th);;

% trans_command : term -> term -> term gives the semantics of a command

    M{X:=E}  =
     MK_ASSIGN (`X`, M{E})

    M{SEQ[C1; ... ;Cn]}  =
     MK_SEQL[M{C1}; ... ; M{Cn}]

    M{BLOCK[VAR X1; ... ;VAR Xm;C1; ... ;Cn]}  =
     MK_BLOCKL [`X1`; ... ; `Xn`] [M{C1}; ... ; M{Cn}]

    M{IF1 S C}  =
     MK_IF1(M{S}, M{C})

    M{IF2 S C1 C2}  =
     MK_IF2(M{S}, M{C1}, (M{C2})

    M{WHILE S C}  =
     MK_WHILE(M{S}, M{C})
%

letrec trans_command s tm =
 (let tm1,tm2 = dest_ASSIGN tm
  in
  "MK_ASSIGN(^(prime_var tm1), ^(trans_term s tm2))")
 ?
 (let l = dest_SEQ tm
  in
  "MK_SEQL ^(mk_list ":command" (map (trans_command s) l))")
 ?
 (let l1,l2 = dest_BLOCK tm
  in
  "MK_BLOCKL 
    ^(mk_list ":string" (map prime_var l1))
    ^(mk_list ":command" (map (trans_command s) l2))")
 ?
 (let tm1,tm2 = dest_IF1 tm
  in
  "MK_IF1(^(trans_term s tm1),  ^(trans_command s tm2))")
 ?
 (let tm1,tm2,tm3 = dest_IF2 tm
  in
  "MK_IF2
    (^(trans_term s tm1), ^(trans_command s tm2), ^(trans_command s tm3))")
 ?
 (let tm1,tm2 = dest_WHILE tm
  in
  "MK_WHILE(^(trans_term s tm1), ^(trans_command s tm2))")
 ? 
 failwith `trans_command`;;

%
   trans "SPEC p c q"   --->   "MK_SPEC(M{p},M{c},M{q}"
%

let trans tm =
 let p,c,q = dest_SPEC tm
 and s = "s:string->num"
 in
 "MK_SPEC(^(trans_term s p),
          ^(trans_command s c),
          ^(trans_term s q))";;

% Examples:

   trans
     "SPEC ((X=x) /\ (Y=y)) 
           (BLOCK[VAR R; R:=X; X:=Y; Y:=R])
           ((X=y) /\ (Y=x))";;
   trans
     "SPEC T
           (BLOCK
            [R:=X;
             Q:=0;
             WHILE (Y <= R) (BLOCK[R:=(R-Y); Q:=(Q+1)])
            ])
           ((R < Y) /\ (X = R + (Y*Q)))";;

%

%
  Now some funtions for translating from the internal semantic representation
  to the external concrete syntax. These are useful for `pretty printing'.
%

% Commented-out because last and butlast are now defined in	%
% the basic HOL system [RJB 90.10.20].				%
%<
% last [x1;...;xn]   --->   xn %

letrec last l = last(tl l) ? hd l;;

% butlast [x1;...x(n-1);xn]   --->   [x1;...;x(n-1)] %

letrec butlast l =
 if null(tl l) then [] else (hd l).(butlast(tl l)) ? failwith `butlast`;;
>%

% unprime "`X`"   --->   "X:num" %

let unprime t =
 let x,() = dest_const t
 in
 mk_var(implode(butlast(tl(explode x))),":num");;

% untrans_term : term -> term

     "\s. ... s `x` ..."   --->   " ... x ... "
%

let untrans_term t =
 let s,t1 = dest_abs t
 in
 letrec u_fn t =
  if is_const t or is_var t
   then t
  if is_comb t
   then (if rator t = s 
          then (unprime o rand) t
          else (mk_comb o (u_fn # u_fn) o dest_comb) t)
  if is_abs t
   then (mk_abs o (I # u_fn) o dest_abs) t
  else fail
 in
 u_fn t1;;

% "(t1,...,tn)"   --->   ["t1";...;"tn"] %

letrec dest_tuple t =
 (let t1,t2 = dest_pair t
  in
  t1.dest_tuple t2
 ) ? [t];;

% untrans_command : term -> term 

    MK_ASSIGN (`X`, M{E}) =
     X := E

    MK_SEQL[M{C1}; ... ; M{Cn}] =
     SEQ[C1; ... ;Cn]

    MK_BLOCKL [`X1`; ... ; `Xn`] [M{C1}; ... ; M{Cn}] =
     BLOCK[VAR X1; ... ;VAR Xm;C1; ... ;Cn]

    MK_IF1(M{S}, M{C}) =
     IF1 S C

    MK_IF2(M{S}, M{C1}, (M{C2}) =
     IF2 S C1 C2

    MK_WHILE(M{S}, M{C}) =
     WHILE S C
%

% Obsolete (crashes HOL)

letrec untrans_command t =
 (let ctr,arg = strip_comb t
  in
  if ctr = "MK_ASSIGN"
   then
   (let arg1,arg2 = dest_pair(hd arg)
    in
    "^(unprime arg1) := ^(untrans_term arg2)")
  if ctr = "MK_SEQ"
   then
   (let c1,c2 = dest_pair(hd arg)
    in
    let uc1 = untrans_command c1
    and uc2 = untrans_command c2
    in
    let uc1l = dest_SEQ uc1 ? [uc1]
    and uc2l = dest_SEQ uc2 ? [uc2]
    in
    "SEQ ^(mk_list ":phrase" (uc1l @ uc2l))")
  if ctr = "MK_SEQL"
   then 
   (let l = dest_list(hd arg)
    in
    let t1 = mk_list ":phrase" (map untrans_command l)
    in
    "SEQ ^t1")
  if ctr = "MK_BLOCK"
   then
   (let x,c = dest_pair(hd arg)
    in
    let uc = untrans_command c
    and ux = unprime x
    in
    let ucl = dest_SEQ uc ? [uc]
    in
    "BLOCK ^(mk_list ":phrase" ("VAR ^ux".ucl))")
  if  ctr = "MK_BLOCKL"
   then
   (let [vars;body] = arg
    in
    let varsl = dest_list vars
    and bodyl = dest_list body
    in
    let varsl' = map (\t. mk_comb("VAR",unprime t)) varsl
    and bodyl' = map untrans_command bodyl
    in
    "BLOCK ^(mk_list ":phrase" (varsl'@bodyl'))")
  if ctr = "MK_IF1"
   then
   (let b,c = dest_pair(hd arg)
    in
    "IF1 ^(untrans_term b) ^(untrans_command c)")
  if ctr = "MK_IF2"
   then
   (let [b;c1;c2] = dest_tuple(hd arg)
    in
    "IF2 ^(untrans_term b) ^(untrans_command c1) ^(untrans_command c2)")
  if ctr = "MK_WHILE"
   then
   (let b,c = dest_pair(hd arg)
    in
    "WHILE ^(untrans_term b) ^(untrans_command c)")
  else fail
 ) ? failwith `untrans_command`;;
%


% dest_MK_SPEC "MK_SPEC(p,c,q)"   --->   ("p","c","q") %

let dest_MK_SPEC t =
 (let name,args = dest_comb t
  in
  if not(fst(dest_const(name))=`MK_SPEC`)
   then fail
   else ((I # dest_pair) o dest_pair) args
 ) ? failwith `dest_MK_SPEC`;;

%
   untrans_spec "MK_SPEC(M{p},M{c},M{q}"   --->   "SPEC p c q"
%

% Obsolete (uses untrans_command)
let untrans_spec t =
 (let p,c,q = dest_MK_SPEC t
  in
  "SPEC ^(untrans_term p) ^(untrans_command c) ^(untrans_term q)"
 ) ? failwith `untrans_spec`;;

let untrans = untrans_spec o concl;;
%

% Test Examples:

 untrans_command
  "MK_BLOCK
    (`X`, 
    MK_SEQ
     (MK_ASSIGN(`R`,(\s. s `X`)),
      MK_SEQ(MK_ASSIGN(`X`,(\s. s `Y`)),
             MK_ASSIGN(`Y`,(\s. s `R`)))))";;

 let t1 =
    trans
     "SPEC ((X=x) /\ (Y=y)) 
           (BLOCK[VAR R; R:=X; X:=Y; Y:=R])
           ((X=y) /\ (Y=x))";;

  untrans_spec t1;;

 let t2 =
    trans
     "SPEC T
           (BLOCK
            [R:=X;
             Q:=0;
             WHILE (Y <= R) (BLOCK[R:=(R-Y); Q:=(Q+1)])
            ])
           ((R < Y) /\ (X = R + (Y*Q)))";;

 untrans_spec t2;;

%

% dest_spec "MK_SPEC(p,c,q)" --> ("p","c","q") %

let dest_spec t =
 (let n,[p;c;q] = ((I # dest_tuple) o dest_comb) t
  in
  if n = "MK_SPEC"
   then (p,c,q)
   else fail
 ) ? failwith `dest_spec`;;

% dest_assign "MK_ASSIGN(x,e)" --> ("x","e") %

let dest_assign t =
 (let n,[x;e] = ((I # dest_tuple) o dest_comb) t
  in
  if n = "MK_ASSIGN"
   then (x,e)
   else fail
 ) ? failwith `dest_assign`;;

% dest_seq "c1;c2"  -->  ("c1","c2") %

letrec dest_seq t =
 (let n,[c1;c2] =  ((I # dest_tuple) o dest_comb) t
  in
  if n = "MK_SEQ"
   then (c1,c2)
   else fail
 ) ? failwith `dest_seq`;;

% dest_seql "c1;c2; ... ;cn"  -->  ["c1";"c2"; ... ;"cn"] %

letrec dest_seql t =
 (let c1,c2 = dest_seq t
  in
  dest_seql c1 @ dest_seql c2
 ) ? [t];;

% mk_seql ["c1";"c2"; ... ;"cn"]  -->  "c1;(c2; ... ;cn)"  %

letrec mk_seql l =
 (if null l 
   then fail
  if null(tl l)
   then hd l
   else "MK_SEQ(^(hd l),^(mk_seql(tl l)))"
 ) ? failwith `mk_seql`;;

% dest_assert "MK_ASSERT p"  -->  "p" %

letrec dest_assert t =
 (let n,p =  dest_comb t
  in
  if n = "MK_ASSERT"
   then p
   else fail
 ) ? failwith `dest_assert`;;

% dest_invariant "MK_INVARIANT p"  -->  "p" %

letrec dest_invariant t =
 (let n,p =  dest_comb t
  in
  if n = "MK_INVARIANT"
   then p
   else fail
 ) ? failwith `dest_invariant`;;

% dest_variant "MK_VARIANT p"  -->  "p" %

letrec dest_variant t =
 (let n,p =  dest_comb t
  in
  if n = "MK_VARIANT"
   then p
   else fail
 ) ? failwith `dest_variant`;;

% dest_if1 "MK_IF1(b,c)"  -->  ("b","c") %

letrec dest_if1 t =
 (let n,[b;c] =  ((I # dest_tuple) o dest_comb) t
  in
  if n = "MK_IF1"
   then (b,c)
   else fail
 ) ? failwith `dest_if1`;;

% dest_if2 "MK_IF1(b,c1,c2)"  -->  ("b","c1","c2") %

letrec dest_if2 t =
 (let n,[b;c1;c2] =  ((I # dest_tuple) o dest_comb) t
  in
  if n = "MK_IF2"
   then (b,c1,c2)
   else fail
 ) ? failwith `dest_if2`;;

% dest_while "MK_WHILE(b,c)"  -->  ("b","c") %

letrec dest_while t =
 (let n,[b;c] =  ((I # dest_tuple) o dest_comb) t
  in
  if n = "MK_WHILE"
   then (b,c)
   else fail
 ) ? failwith `dest_while`;;
