
% Apply a type instantiation and substitution:

 apply_inst_subst vl ([(t1,x1)...;(tm,xm)],[(ty1,v1)...;(tyn,vn)]) t 
  ---> 
 subst[tm,xm](...(subst[t1,x1](inst[tyn,vn](...(inst[ty1,v1]t)...))) ... )

%

let apply_inst_subst vl (l1,l2) t = 
 rev_itlist 
  (\pair term. subst[pair]term) 
  l1 
  (rev_itlist (\pair term. inst vl [pair]term) l2 t);;

% hol_match_fn : (term list ->
                 term ->
                 term ->
                 ((term # term) list # (type # type) list))

   hol_match_fn vl t1 t2    --->   (s,i)

  where s is a substitution, not involving variables in vl, and
  i is a type instantiation, such that:

      apply_subst (s,i) t1 

  beta-reduces to t2.
%

letrec hol_match_fn vl t1 t2 =
 if t1=t2
  then ([],[])
 if is_var t1
  then (if not(mem t1 vl) then ([t2,t1],[]) else fail)
 if is_const t1 & is_const t2 & can (match t1) t2
  then match t1 t2
 if is_comb t1 & is_var(rator t1) & is_var(rand t1)
  then
   (let f,x = dest_comb t1
    in
    ([mk_abs(x,t2),f],[]))
 if is_comb t1 & is_abs(rator t1) 
  then hol_match_fn vl (rhs(concl(BETA_CONV t1))) t2
 if is_comb t1 & is_comb t2
  then
   (let rat1,rnd1 = dest_comb t1
    and rat2,rnd2 = dest_comb t2
    in
    let s = hol_match_fn vl rat1 rat2
    in 
    let s' = 
     hol_match_fn vl (apply_inst_subst vl s rnd1) (apply_inst_subst vl s rnd2)
    in 
    (fst s @ fst s', snd s @ snd s'))
 if is_abs t1 & is_abs t2
  then
   (let v1,body1 = dest_abs t1
    and v2,body2 = dest_abs t2
    in
    if v1=v2
     then hol_match_fn (v1.vl) body1 body2
     else fail) % could try and do an alpha-conversion here %
  else fail;;

let hol_match = hol_match_fn [];;

% Examples:

#hol_match "x+1" "2+1";;
["2","x"],[] : ((term # term) list # (type # type) list)

#hol_match "x+(y+x)" "3+(z+3)";;
["3","x"; "z","y"],[] : ((term # term) list # (type # type) list)

#hol_match "x+x"  "(p*q)+(p*p)";;
["p * q","x"; "p","q"],[] : ((term # term) list # (type # type) list)

#hol_match "(x+x)>x" "((p*q)+(p*p))>(p*p)";;
["p * q","x"; "p","q"],[] : ((term # term) list # (type # type) list)

#hol_match "(x+x)>x" "((p*q)+(p*p))>(q*q)";;
["p * q","x"; "p","q"],[] : ((term # term) list # (type # type) list)

#hol_match "x+((p*q)+x)" "(r*s)+((4*4)+(r*r))";;
["r * s","x"; "4","p"; "4","q"; "r","s"], []
: ((term # term) list # (type # type) list)

#hol_match "(\x. x+y)z" "1+2";;
([("1", "z"); ("2", "y")], [])
: ((term # term) list # (type # type) list)

#hol_match "(\x. x+y)z" "(\x. x+2)1";;
evaluation failed     fail 

#hol_match "(\x. x+y)z" "(\w. w+2)1";;
evaluation failed     fail 

#hol_match "(\x:num. z:num)" "(\x:num. 1:num)";;
["1","z"],[] : ((term # term) list # (type # type) list)

#hol_match "(f:num->num)x" "x+y";;
["\x. x + y","f"],[] : ((term # term) list # (type # type) list)

#hol_match "(f:num->num)y" "x+y";;
["\y. x + y","f"],[] : ((term # term) list # (type # type) list)

#hol_match
  "P 0 /\ (!n. P n ==> P(SUC n)) ==> (!n. P n)"
  "m > 0 /\ (!n. m > n ==> m > SUC n) ==> (!n. m > n)";;
["$> m","P"],[] : ((term # term) list # (type # type) list)

#hol_match
  "P 0 /\ (!n. P n ==> P(SUC n)) ==> (!n. P n)"
  "0 < m /\ (!n. n < m ==> SUC n < m) ==> (!n. n < m)";;
evaluation failed     fail 

#hol_match "!x:*. x=x" "!x:num.x=x";;
[],[":num",":*"] : ((term # term) list # (type # type) list)

#hol_match 
  "!s:string->num. p' s ==> p s" 
  "!s:string->num. F ==> (s `X` = x) /\ (s `Y` = y)"
([("\s. F", "p'"); ("\s. (s `X` = x) /\ (s `Y` = y)", "p")], [])
: ((term # term) list # (type # type) list)
%


%
hol_match a given part of "th" to a term, instantiating "th".
The part should be free in the theorem, except for outer bound variables
%

let HOL_PART_MATCH partfn th tm =
 let pth = GSPEC (GEN_ALL th)  
 in
 let pat = partfn(concl pth) 
 in
 let matchfn = hol_match pat 
 in
 INST_TY_TERM (matchfn tm) pth;;

%
Matching Modus Ponens for implications of the form |- !x1 ... xn. P ==> Q 
Matches x1 ... xn : 	 |-  P'  ---->  |- Q'  
Matches all types in conclusion except those mentioned in hypotheses
%

letrec OUTER_BETA_CONV t =
 BETA_CONV t
 ? (MK_COMB o (OUTER_BETA_CONV # OUTER_BETA_CONV) o dest_comb) t
 ? (uncurry ABS o (I # OUTER_BETA_CONV) o dest_abs) t
 ? REFL t;;

let HOL_MATCH_MP impth th =
     let match = HOL_PART_MATCH (fst o dest_imp) impth ? failwith `HOL_MATCH_MP` 
     in
     MATCH_MP (CONV_RULE OUTER_BETA_CONV (match (concl th))) th;;

