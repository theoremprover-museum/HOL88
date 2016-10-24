
% ML type of goals with flagged assumptions %

lettype fgoal = (string # term)list # term;;

% ML type of tactics using flagged goals %

lettype ftactic = fgoal -> (fgoal list) # proof;;

% Suppose tac is a tactic such that:

     tac g = [g1;...;gn],p

  where each goal gi has the form ([ti1;...;tin],ti), then

     FLAG `flag` tac g = [fg1;...;fgn],p

  where fgi = [(`flag_i_1`,ti1);...;(`flag_i_n`,tin)]. Thus FLAG has ML type:

     FLAG : string -> tactic -> goal -> (fgoal list) # proof

  Before coding FLAG we need a couple of auxiliary functions.
%


% mapcount f [x1;x2; ... ;xn] = [f 1 x1; f 2 x2; ... ;f n xn] %

let mapcount f l =
 letrec fn n l = if null l then [] else f n (hd l).fn(n+1)(tl l)
 in
 fn 1 l;;

% flagfn m n `flag` ---> `flag_m_n` %

ml_curried_infix `++`;;

let $++ = concat;;

let flagfn m n tok =
 tok ++ `_` ++ (string_of_int m) ++ `_` ++ (string_of_int n);;

let FLAG flag (tac:tactic) g =
 let gl,p = tac g 
 in
 (mapcount(\m (A,t).(mapcount(\n t'.(flagfn m n flag, t'))A,t))gl, p);;

%
 FLAGIFY : string -> tactic -> ftactic
 
 Suppose fg = ([`f1`,t1; ... ;`fn`,tn],t) is a flagged goal.
 Suppose:

    tac ([t1;...;tn],t) = [g1;...;gn],p where gi = ([ti1;...;tin],ti)

 Then FLAGIFY `flag` tac fg = ([fg1;...;fgn],p) where

    fgi = ([fi1,ti1; ... ;fin,tin],ti)

 where fij is `fk` if tij=tk (so flags on assumptions that are
 `passed through' are preserved), otherwise it is `flag_i_j`
%

let FLAGIFY flag (tac:tactic) ((fl,t):fgoal) =
 let gl,p = tac(map snd fl,t)
 in
 (mapcount
  (\m (A,t).
    (mapcount(\n t'.((fst(rev_assoc t' fl) ? flagfn m n flag), t'))A,t))
  gl,
  p);;

%
 GET_ASMS : (string list) -> ((thm list) -> ftactic) -> ftactic

    GET_ASMS fl ftac fg ---> ftac thl fg

 where thl is the list of ASSUMEd assumptions in fg flagged by members of fl.
%

let GET_ASMS (fl:string list) (ftac:(thm list) -> ftactic) fg =
 let thl = mapfilter
            (\(flag,t).if mem flag fl then ASSUME t else fail)
            (fst fg)
 in
 ftac thl fg;;

%
 BEGIN_FLAG : string -> goal -> (fgoal list # proof)
 END_FLAG : fgoal -> (goal list # proof)
%

let BEGIN_FLAG (flag:string) (g:goal) = 
 ([(mapcount(\n t.(flag++`_`++(string_of_int n),t)) # I)g], (hd:proof));;

let END_FLAG (fg:fgoal) = ([(map snd # I) fg], (hd:proof));;

%
An example:

let g = (["x=1";"x=2";"x=3"], "(x=1)\/(x=2)\/(x=3)");;

let fgl1,p1 = BEGIN_FLAG `test` g;;

let tac flag =
 BEGIN_FLAG `test` 
  THEN GET_ASMS[flag](\thl.FLAGIFY `` (PURE_REWRITE_TAC thl));;

let tac1 = tac `test_1`
and tac2 = tac `test_2`
and tac3 = tac `test_3`;;

tac1 g;;

tac2 g;;

tac3 g;;

let fgl2,p2 = (tac2 THEN (FLAGIFY `` (REWRITE_TAC[]))) g;;

%