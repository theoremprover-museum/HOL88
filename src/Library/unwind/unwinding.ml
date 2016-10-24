%****************************************************************************%
% FILE          : unwinding.ml                                               %
% DESCRIPTION   : Rules for unfolding, unwinding, pruning, etc.              %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : Originally written for LCF-LSM by Mike Gordon (MJCG).      %
% 21.May.1985   : Additions by Tom Melham (TFM).                             %
% 10.Mar.1988   : Modifications by David Shepherd (DES) of INMOS.            %
% 24.Mar.1988   : Bug fixes by David Shepherd (DES).                         %
% 23.Apr.1990   : Modifications by Tom Melham (TFM).                         %
% 22.Aug.1991   : Additions and tidying-up by Richard Boulton (RJB).         %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 21st July 1992                                             %
%****************************************************************************%

%============================================================================%
% Tools for manipulating device implementations `by hand'                    %
%============================================================================%

%----------------------------------------------------------------------------%
% DEPTH_FORALL_CONV : conv -> conv                                           %
%                                                                            %
% DEPTH_FORALL_CONV conv "!x1 ... xn. body" applies conv to "body" and       %
% returns a theorem of the form:                                             %
%                                                                            %
%    |- (!x1 ... xn. body) = (!x1 ... xn. body')                             %
%----------------------------------------------------------------------------%

letrec DEPTH_FORALL_CONV conv tm =
 if (is_forall tm)
 then RAND_CONV (ABS_CONV (DEPTH_FORALL_CONV conv)) tm
 else conv tm;;

%----------------------------------------------------------------------------%
% DEPTH_EXISTS_CONV : conv -> conv                                           %
%                                                                            %
% DEPTH_EXISTS_CONV conv "?x1 ... xn. body" applies conv to "body" and       %
% returns a theorem of the form:                                             %
%                                                                            %
%    |- (?x1 ... xn. body) = (?x1 ... xn. body')                             %
%----------------------------------------------------------------------------%

letrec DEPTH_EXISTS_CONV conv tm =
 if (is_exists tm)
 then RAND_CONV (ABS_CONV (DEPTH_EXISTS_CONV conv)) tm
 else conv tm;;

%----------------------------------------------------------------------------%
% FLATTEN_CONJ_CONV : conv                                                   %
%                                                                            %
%    "t1 /\ ... /\ tn"                                                       %
%    ---->                                                                   %
%    |- t1 /\ ... /\ tn = u1 /\ ... /\ un                                    %
%                                                                            %
% where the RHS of the equation is a flattened version of the LHS.           %
%----------------------------------------------------------------------------%

let FLATTEN_CONJ_CONV t =
 CONJUNCTS_CONV (t,list_mk_conj (conjuncts t));;

%============================================================================%
% Moving universal quantifiers in and out of conjunctions                    %
%============================================================================%

%----------------------------------------------------------------------------%
% CONJ_FORALL_ONCE_CONV : conv                                               %
%                                                                            %
%    "(!x. t1) /\ ... /\ (!x. tn)"                                           %
%    ---->                                                                   %
%    |- (!x. t1) /\ ... /\ (!x. tn) = !x. t1 /\ ... /\ tn                    %
%                                                                            %
% where the original term can be an arbitrary tree of /\s, not just linear.  %
% The structure of the tree is retained in both sides of the equation.       %
%                                                                            %
% To avoid deriving incompatible theorems for IMP_ANTISYM_RULE when one or   %
% more of the ti's is a conjunction, the original term is broken up as well  %
% as the theorem. If this were not done, the conversion would fail in such   %
% cases.                                                                     %
%----------------------------------------------------------------------------%

let CONJ_FORALL_ONCE_CONV t =
 letrec conj_tree_map f t th =
  (let t1,t2 = dest_conj t
   and th1,th2 = CONJ_PAIR th
   in  CONJ (conj_tree_map f t1 th1) (conj_tree_map f t2 th2)
  ) ? (f th)
 in
  (let conjs = conjuncts t
   in
   if (length conjs = 1) then REFL t
   else
   let var = case (setify (map (fst o dest_forall) conjs))
             of [x] . x
              | (_) . fail
   in
   let th = GEN var (conj_tree_map (SPEC var) t (ASSUME t))
   in
   let th1 = DISCH t th
   and th2 = DISCH (concl th)
              (conj_tree_map (GEN var) t (SPEC var (ASSUME (concl th))))
   in  IMP_ANTISYM_RULE th1 th2
  ) ? failwith `CONJ_FORALL_ONCE_CONV`;;

%----------------------------------------------------------------------------%
% FORALL_CONJ_ONCE_CONV : conv                                               %
%                                                                            %
%    "!x. t1 /\ ... /\ tn"                                                   %
%    ---->                                                                   %
%    |- !x. t1 /\ ... /\ tn = (!x. t1) /\ ... /\ (!x. tn)                    %
%                                                                            %
% where the original term can be an arbitrary tree of /\s, not just linear.  %
% The structure of the tree is retained in both sides of the equation.       %
%----------------------------------------------------------------------------%

let FORALL_CONJ_ONCE_CONV t =
 letrec conj_tree_map f th =
  (let th1,th2 = CONJ_PAIR th
   in  CONJ (conj_tree_map f th1) (conj_tree_map f th2)
  ) ? (f th)
 in
  (let var = fst (dest_forall t)
   in
   let th = conj_tree_map (GEN var) (SPEC var (ASSUME t))
   in
   let th1 = DISCH t th
   and th2 = DISCH (concl th)
              (GEN var (conj_tree_map (SPEC var) (ASSUME (concl th))))
   in  IMP_ANTISYM_RULE th1 th2
  ) ? failwith `FORALL_CONJ_ONCE_CONV`;;

%----------------------------------------------------------------------------%
% CONJ_FORALL_CONV : conv                                                    %
%                                                                            %
%    "(!x1 ... xm. t1) /\ ... /\ (!x1 ... xm. tn)"                           %
%    ---->                                                                   %
%    |- (!x1 ... xm. t1) /\ ... /\ (!x1 ... xm. tn) =                        %
%       !x1 ... xm. t1 /\ ... /\ tn                                          %
%                                                                            %
% where the original term can be an arbitrary tree of /\s, not just linear.  %
% The structure of the tree is retained in both sides of the equation.       %
%----------------------------------------------------------------------------%

letrec CONJ_FORALL_CONV tm =
 (if (length (conjuncts tm) = 1)
  then fail
  else (CONJ_FORALL_ONCE_CONV THENC (RAND_CONV (ABS_CONV CONJ_FORALL_CONV))) tm
 ) ? REFL tm;;

%----------------------------------------------------------------------------%
% FORALL_CONJ_CONV : conv                                                    %
%                                                                            %
%    "!x1 ... xm. t1 /\ ... /\ tn"                                           %
%    ---->                                                                   %
%    |- !x1 ... xm. t1 /\ ... /\ tn =                                        %
%       (!x1 ... xm. t1) /\ ... /\ (!x1 ... xm. tn)                          %
%                                                                            %
% where the original term can be an arbitrary tree of /\s, not just linear.  %
% The structure of the tree is retained in both sides of the equation.       %
%----------------------------------------------------------------------------%

letrec FORALL_CONJ_CONV tm =
 if (is_forall tm)
 then (RAND_CONV (ABS_CONV FORALL_CONJ_CONV) THENC FORALL_CONJ_ONCE_CONV) tm
 else REFL tm;;

%----------------------------------------------------------------------------%
% CONJ_FORALL_RIGHT_RULE : thm -> thm                                        %
%                                                                            %
%     A |- !z1 ... zr.                                                       %
%           t = ?y1 ... yp. (!x1 ... xm. t1) /\ ... /\ (!x1 ... xm. tn)      %
%    -------------------------------------------------------------------     %
%     A |- !z1 ... zr. t = ?y1 ... yp. !x1 ... xm. t1 /\ ... /\ tn           %
%                                                                            %
%----------------------------------------------------------------------------%

let CONJ_FORALL_RIGHT_RULE th =
 CONV_RULE
  (DEPTH_FORALL_CONV (RAND_CONV (DEPTH_EXISTS_CONV CONJ_FORALL_CONV))) th
 ? failwith `CONJ_FORALL_RIGHT_RULE`;;

%----------------------------------------------------------------------------%
% FORALL_CONJ_RIGHT_RULE : thm -> thm                                        %
%                                                                            %
%     A |- !z1 ... zr. t = ?y1 ... yp. !x1 ... xm. t1 /\ ... /\ tn           %
%    -------------------------------------------------------------------     %
%     A |- !z1 ... zr.                                                       %
%           t = ?y1 ... yp. (!x1 ... xm. t1) /\ ... /\ (!x1 ... xm. tn)      %
%                                                                            %
%----------------------------------------------------------------------------%

let FORALL_CONJ_RIGHT_RULE th =
 CONV_RULE
  (DEPTH_FORALL_CONV (RAND_CONV (DEPTH_EXISTS_CONV FORALL_CONJ_CONV))) th
 ? failwith `FORALL_CONJ_RIGHT_RULE`;;

%============================================================================%
% Rules for unfolding                                                        %
%============================================================================%

%----------------------------------------------------------------------------%
% UNFOLD_CONV : thm list -> conv                                             %
%                                                                            %
%    UNFOLD_CONV thl                                                         %
%                                                                            %
%    "t1 /\ ... /\ tn"                                                       %
%    ---->                                                                   %
%    B |- t1 /\ ... /\ tn = t1' /\ ... /\ tn'                                %
%                                                                            %
% where each ti' is the result of rewriting ti with the theorems in thl. The %
% set of assumptions B is the union of the instantiated assumptions of the   %
% theorems used for rewriting. If none of the rewrites are applicable to a   %
% ti, it is unchanged.                                                       %
%----------------------------------------------------------------------------%

let UNFOLD_CONV thl =
 let net = mk_conv_net thl
 in
 let REWRITES_CONV net = \tm. FIRST_CONV (lookup_term net tm) tm
 in
 let THENQC conv1 conv2 tm =
    (let th1 = conv1 tm
     in  ((th1 TRANS (conv2 (rhs (concl th1)))) ? th1))
    ? (conv2 tm)
 in
 letrec CONJ_TREE_CONV conv tm =
    if (is_conj tm)
    then THENQC (RATOR_CONV (RAND_CONV (CONJ_TREE_CONV conv)))
                (RAND_CONV (CONJ_TREE_CONV conv))
                tm
    else conv tm
 in
 \t. if (null thl)
     then REFL t
     else CONJ_TREE_CONV (REWRITES_CONV net) t ? REFL t;;

%----------------------------------------------------------------------------%
% UNFOLD_RIGHT_RULE : thm list -> thm -> thm                                 %
%                                                                            %
%    UNFOLD_RIGHT_RULE thl                                                   %
%                                                                            %
%         A |- !z1 ... zr. t = ?y1 ... yp. t1 /\ ... /\ tn                   %
%    --------------------------------------------------------                %
%     B u A |- !z1 ... zr. t = ?y1 ... yp. t1' /\ ... /\ tn'                 %
%                                                                            %
% where each ti' is the result of rewriting ti with the theorems in thl. The %
% set of assumptions B is the union of the instantiated assumptions of the   %
% theorems used for rewriting. If none of the rewrites are applicable to a   %
% ti, it is unchanged.                                                       %
%----------------------------------------------------------------------------%

let UNFOLD_RIGHT_RULE thl th =
 CONV_RULE
  (DEPTH_FORALL_CONV (RAND_CONV (DEPTH_EXISTS_CONV (UNFOLD_CONV thl))))
  th
 ? failwith `UNFOLD_RIGHT_RULE`;;

%============================================================================%
% Rules for unwinding device implementations                                 %
%============================================================================%

%----------------------------------------------------------------------------%
% line_var : term -> term                                                    %
%                                                                            %
%    line_var "!y1 ... ym. f x1 ... xn = t"  ----> "f"                       %
%----------------------------------------------------------------------------%

let line_var tm =
 (fst o strip_comb o lhs o snd o strip_forall) tm ? failwith `line_var`;;

%----------------------------------------------------------------------------%
% line_name : term -> string                                                 %
%                                                                            %
%    line_name "!y1 ... ym. f x1 ... xn = t"  ----> `f`                      %
%----------------------------------------------------------------------------%

let line_name tm = (fst o dest_var o line_var) tm ? failwith `line_name`;;

%----------------------------------------------------------------------------%
% UNWIND_ONCE_CONV : (term -> bool) -> conv                                  %
%                                                                            %
% Basic conversion for parallel unwinding of equations defining wire values  %
% in a standard device specification.                                        %
%                                                                            %
% USAGE: UNWIND_ONCE_CONV p tm                                               %
%                                                                            %
% DESCRIPTION: tm should be a conjunction of terms, equivalent under         %
%              associative-commutative reordering to:                        %
%                                                                            %
%                   t1 /\ t2 /\ ... /\ tn.                                   %
%                                                                            %
%              The function p:term->bool is a predicate which will be        %
%              used to partition the terms ti for 1 <= i <= n into two       %
%              disjoint sets:                                                %
%                                                                            %
%                   REW = {ti | p ti} and OBJ = {ti | ~p ti}                 %
%                                                                            %
%              The terms ti for which p is true are then used as a set       %
%              of rewrite rules (thus they should be equations) to do a      %
%              single top-down parallel rewrite of the remaining terms.      %
%              The rewritten terms take the place of the original terms      %
%              in the input conjunction.                                     %
%                                                                            %
%              For example, if tm is:                                        %
%                                                                            %
%                 t1 /\ t2 /\ t3 /\ t4                                       %
%                                                                            %
%              and REW = {t1,t3} then the result is:                         %
%                                                                            %
%                 |-  t1 /\ t2 /\ t3 /\ t4 = t1 /\ t2' /\ t3 /\ t4'          %
%                                                                            %
%              where ti' is ti rewritten with the equations REW.             %
%                                                                            %
% IMPLEMENTATION NOTE:                                                       %
%                                                                            %
% The assignment:                                                            %
%                                                                            %
%    let pf,fn,eqns = trav p tm []                                           %
%                                                                            %
% makes                                                                      %
%                                                                            %
%    eqns = a list of theorems constructed by assuming each term for         %
%           which p is true, i.e., eqns = the list of rewrites.              %
%                                                                            %
%    fn   = a function which, when applied to a rewriting conversion         %
%           will reconstruct the original term in the original structure,    %
%           but with the subterms for which p is not true rewritten          %
%           using the supplied conversion.                                   %
%                                                                            %
%    pf   = a function which maps |- tm to [|- t1;...;|- tj] where each      %
%           ti is a term for which p is true.                                %
%----------------------------------------------------------------------------%

let UNWIND_ONCE_CONV =
 let REWRITES_CONV net = \tm. FIRST_CONV (lookup_term net tm) tm
 in
 let AND = mk_const (`/\\`,":bool->bool->bool")
 in
 letrec trav p tm rl =
  (let (l,r) = dest_conj tm
   in
   let (pf2,fn2,pf1,fn1,rew) = (I # (I # trav p l)) (trav p r rl)
   in
   let pf = $@ o (pf1 # pf2) o CONJ_PAIR
   in  (pf,(\rf. MK_COMB ((AP_TERM AND (fn1 rf)),(fn2 rf))),rew)
  ) ? if ((p tm) ? false)
      then ((\th.[th]),(\rf. REFL tm),(ASSUME tm . rl))
      else ((\th.[]),(\rf. rf tm),rl)
 in
  (\p tm.
   let (pf,fn,eqns) = trav p tm []
   in
   let rconv = ONCE_DEPTH_CONV (REWRITES_CONV (mk_conv_net eqns))
   in
   let th = fn rconv
   in
   let l,r = (dest_eq (concl th))
   in
   let lth = ASSUME l
   and rth = ASSUME r
   in
   let imp1 = DISCH l (EQ_MP (itlist PROVE_HYP (pf lth) th) lth)
   and imp2 = DISCH r (EQ_MP (SYM (itlist PROVE_HYP (pf rth) th)) rth)
   in  IMP_ANTISYM_RULE imp1 imp2
  ) ? failwith `UNWIND_ONCE_CONV`;;

%----------------------------------------------------------------------------%
% UNWIND_CONV : (term -> bool) -> conv                                       %
%                                                                            %
% Unwind device behaviour using line equations eqnx selected by p until no   %
% change.                                                                    %
%                                                                            %
% WARNING -- MAY LOOP!                                                       %
%                                                                            %
%    UNWIND_CONV p                                                           %
%                                                                            %
%    "t1 /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn"                         %
%    ---->                                                                   %
%    |- t1  /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn =                     %
%       t1' /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn'                      %
%                                                                            %
% where ti' (for 1 <= i <= n) is ti rewritten with the equations             %
% eqni (1 <= i <= m). These equations are the conjuncts for which the        %
% predicate p is true. The ti terms are the conjuncts for which p is false.  %
% The rewriting is repeated until no changes take place.                     %
%----------------------------------------------------------------------------%

letrec UNWIND_CONV p tm =
 let th = UNWIND_ONCE_CONV p tm
 in  if lhs (concl th) = rhs (concl th)
     then th
     else th TRANS (UNWIND_CONV p (rhs (concl th)));;

%----------------------------------------------------------------------------%
% UNWIND_ALL_BUT_CONV : string list -> conv                                  %
%                                                                            %
% Unwind all lines (except those in the list l) as much as possible.         %
%                                                                            %
% WARNING -- MAY LOOP!                                                       %
%                                                                            %
%    UNWIND_ALL_BUT_CONV l                                                   %
%                                                                            %
%    "t1 /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn"                         %
%    ---->                                                                   %
%    |- t1  /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn =                     %
%       t1' /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn'                      %
%                                                                            %
% where ti' (for 1 <= i <= n) is ti rewritten with the equations             %
% eqni (1 <= i <= m). These equations are those conjuncts with line name not %
% in l (and which are equations).                                            %
%----------------------------------------------------------------------------%

let UNWIND_ALL_BUT_CONV l tm =
 (let line_names = subtract (mapfilter line_name (conjuncts tm)) l
  in
  let p line = \tm. (line_name tm) = line
  in
  let itfn line = \th. th TRANS (UNWIND_CONV (p line) (rhs (concl th)))
  in
  itlist itfn line_names (REFL tm)
 ) ? failwith `UNWIND_ALL_BUT_CONV`;;

%----------------------------------------------------------------------------%
% UNWIND_AUTO_CONV : conv                                                    %
%                                                                            %
%    "?l1 ... lm. t1 /\ ... /\ tn"                                           %
%    ---->                                                                   %
%    |- (?l1 ... lm. t1 /\ ... /\ tn) = (?l1 ... lm. t1' /\ ... /\ tn')      %
%                                                                            %
% where tj' is tj rewritten with equations selected from the ti's. The       %
% function decides which equations to use by performing a loop analysis on   %
% the graph representing the dependencies of the lines. By this means the    %
% term can be unwound as much as possible without the risk of looping. The   %
% user is left to deal with the recursive equations.                         %
%                                                                            %
% There is some inefficiency in that certain lines may be used in unwinding  %
% even though they do not appear in any RHS's.                               %
%                                                                            %
% The algorithms used for loop analysis in this function have exponential    %
% complexity in the number of lines. However, steps are taken to limit this  %
% as much as possible. The internal function `next_combination' computes     %
% combinations of a list, but only as they are required. This puts the       %
% burden on time resources rather than space resources. The computation time %
% would be less if a complete list of combinations were computed in one go,  %
% but the list generated might exhaust memory. The first argument to         %
% `next_combination' is the list to find the combinations of. The second     %
% argument is the reverse of the previous combination. Initially this should %
% be the empty list. The result of a call is the reverse of the next         %
% combination. The function assumes that the source list is a set.           %
%                                                                            %
% Amongst other things, the internal function `graph_of_term' rearranges the %
% lines in the graph representation so that external lines come first. It is %
% important that the number of internal lines left unwound because of loops  %
% is minimised since it is the internal lines that are existentially         %
% quantified. Further manipulations by the user should be easier if any      %
% loops remaining do not involve existentially quantified variables.         %
%                                                                            %
% The algorithm for breaking loops is:                                       %
%                                                                            %
% 1. Isolate any loops of length one. Each such loop involves only one line  %
%    so must be broken at that line.                                         %
%                                                                            %
% 2. Eliminate from consideration the single element loops and any other     %
%    loop that will be broken by the elements in those loops.                %
%                                                                            %
% 3. Determine those loops that consist entirely of internal lines. All      %
%    other loops can be broken at an external line. A minimal set of         %
%    internal lines that break all the exclusively internal loops is then    %
%    computed. This may not be the only minimal set.                         %
%                                                                            %
% 4. Any loop broken by the minimal set of internal lines is eliminated from %
%    consideration. A list of external lines appearing in these remaining    %
%    loops is computed. From these external lines a minimal set that breaks  %
%    all the remaining loops is computed. This set will only be minimal      %
%    relative to the choice of minimal set of internals. A different choice  %
%    for the latter might have produced a smaller set of external lines.     %
%                                                                            %
% 5. The three lists of lines computed in 1-4 are concatenated and returned. %
%----------------------------------------------------------------------------%

let UNWIND_AUTO_CONV =
 let graph_of_term tm =
  (let internals,t = strip_exists tm
   in  let (lines,rhs_frees) =
          split (mapfilter ((((assert is_var) o fst o strip_comb) # frees) o
                            dest_eq o snd o strip_forall) (conjuncts t))
   in
   if (distinct lines)
   then let graph = combine (lines,map (intersect lines) rhs_frees)
        in  let (intern,extern) = partition (\p. mem (fst p) internals) graph
        in  extern @ intern
   else fail)
 in
 letrec loops_containing_line line graph chain =
  (let successors =
      map fst (filter (\(_,predecs). mem (hd chain) predecs) graph)
   in  let not_in_chain = filter (\line. not (mem line chain)) successors
   in  let new_chains = map (\line. line.chain) not_in_chain
   in  let new_loops = flat (map (loops_containing_line line graph) new_chains)
   in  if (mem line successors)
       then (rev chain).new_loops
       else new_loops)
 in
 letrec chop_at x l =
  (if (hd l = x)
   then ([],l)
   else let (l1,l2) = chop_at x (tl l)
        in  ((hd l).l1,l2))
 in
 let equal_loops lp1 lp2 =
  (if (set_equal lp1 lp2)
   then let (before,rest) = chop_at (hd lp1) lp2
        in  lp1 = (rest @ before)
   else false)
 in
 letrec distinct_loops lps =
  (if (null lps)
   then []
   else let (h.t) = lps
        in  if (exists (\lp. equal_loops lp h) t)
            then distinct_loops t
            else h.(distinct_loops t))
 in
 let loops_of_graph graph =
  (distinct_loops
    (flat
      (map (\line. loops_containing_line line graph [line]) (map fst graph))))
 in
 letrec list_after x l =
  (if (x = hd l)
   then tl l
   else list_after x (tl l))
 in
 letrec rev_front_of l n front =
  (if (n < 0) then fail
   if (n = 0) then front
   else rev_front_of (tl l) (n - 1) ((hd l).front))
 in
 letrec next_comb_at_this_level source n (h.t) =
  (let l = list_after h source
   in  if (length l > n)
       then (rev_front_of l (n + 1) []) @ t
       else next_comb_at_this_level source (n + 1) t)
 in
 let next_combination source previous =
  ((next_comb_at_this_level source 0 previous) ?
   (rev_front_of source ((length previous) + 1) []))
 in
 letrec break_all_loops lps lines previous =
  (let comb = next_combination lines previous
   in  if (forall (\lp. not (null (intersect lp comb))) lps)
       then comb
       else break_all_loops lps lines comb)
 in
 let breaks internals graph =
  (let loops = loops_of_graph graph
   in  let single_el_loops = filter (\l. length l = 1) loops
   in  let single_breaks = flat single_el_loops
   in  let loops' = filter (null o (intersect single_breaks)) loops
   in  let only_internal_loops =
              filter (\l. null (subtract l internals)) loops'
   in  let only_internal_lines = end_itlist union only_internal_loops ? []
   in  let internal_breaks =
              break_all_loops only_internal_loops only_internal_lines [] ? []
   in  let external_loops = filter (null o (intersect internal_breaks)) loops'
   in  let external_lines =
              subtract (end_itlist union external_loops ? []) internals
   in  let external_breaks =
              break_all_loops external_loops external_lines [] ? []
   in  single_breaks @ (rev internal_breaks) @ (rev external_breaks))
 in
 letrec conv dependencies used t =
  (let vars =
      map fst (filter ((\l. null (subtract l used)) o snd) dependencies)
   in  if (null vars)
       then REFL t
       else ((UNWIND_ONCE_CONV (\tm. mem (line_var tm) vars)) THENC
             (conv (filter (\p. not (mem (fst p) vars)) dependencies)
                   (used @ vars))) t)
 in
 \tm.
 (let internals = fst (strip_exists tm)
  and graph = graph_of_term tm
  in
  let brks = breaks internals graph
  in
  let dependencies =
   map (I # (\l. subtract l brks)) (filter (\p. not (mem (fst p) brks)) graph)
  in
  DEPTH_EXISTS_CONV (conv dependencies []) tm
 ) ? failwith `UNWIND_AUTO_CONV`;;

%----------------------------------------------------------------------------%
% UNWIND_ALL_BUT_RIGHT_RULE : string list -> thm -> thm                      %
%                                                                            %
% Unwind all lines (except those in the list l) as much as possible.         %
%                                                                            %
% WARNING -- MAY LOOP!                                                       %
%                                                                            %
%    UNWIND_ALL_BUT_RIGHT_RULE l                                             %
%                                                                            %
%     A |- !z1 ... zr.                                                       %
%           t =                                                              %
%           (?l1 ... lp. t1  /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn)     %
%    ---------------------------------------------------------------------   %
%     A |- !z1 ... zr.                                                       %
%           t =                                                              %
%           (?l1 ... lp. t1' /\ ... /\ eqn1 /\ ... /\ eqnm /\ ... /\ tn')    %
%                                                                            %
% where ti' (for 1 <= i <= n) is ti rewritten with the equations             %
% eqni (1 <= i <= m). These equations are those conjuncts with line name not %
% in l (and which are equations).                                            %
%----------------------------------------------------------------------------%

let UNWIND_ALL_BUT_RIGHT_RULE l th =
 CONV_RULE
  (DEPTH_FORALL_CONV (RAND_CONV (DEPTH_EXISTS_CONV (UNWIND_ALL_BUT_CONV l))))
  th
 ? failwith `UNWIND_ALL_BUT_RIGHT_RULE`;; 

%----------------------------------------------------------------------------%
% UNWIND_AUTO_RIGHT_RULE : thm -> thm                                        %
%                                                                            %
%     A |- !z1 ... zr. t = ?l1 ... lm. t1  /\ ... /\ tn                      %
%    ----------------------------------------------------                    %
%     A |- !z1 ... zr. t = ?l1 ... lm. t1' /\ ... /\ tn'                     %
%                                                                            %
% where tj' is tj rewritten with equations selected from the ti's. The       %
% function decides which equations to use by performing a loop analysis on   %
% the graph representing the dependencies of the lines. By this means the    %
% equations can be unwound as much as possible without the risk of looping.  %
% The user is left to deal with the recursive equations.                     %
%----------------------------------------------------------------------------%

let UNWIND_AUTO_RIGHT_RULE th =
 CONV_RULE (DEPTH_FORALL_CONV (RAND_CONV UNWIND_AUTO_CONV)) th
 ? failwith `UNWIND_AUTO_RIGHT_RULE`;; 

%============================================================================%
% Rules for pruning                                                          %
%============================================================================%

%----------------------------------------------------------------------------%
% EXISTS_DEL1_CONV : conv                                                    %
%                                                                            %
%    "?x. t"                                                                 %
%    ---->                                                                   %
%    |- (?x. t) = t                                                          %
%                                                                            %
% provided x is not free in t.                                               %
%                                                                            %
% Deletes one existential quantifier.                                        %
%----------------------------------------------------------------------------%

let EXISTS_DEL1_CONV tm =
 (let x,t = dest_exists tm
  in
  let th = ASSUME t
  in
  let th1 = DISCH tm (CHOOSE (x, ASSUME tm) th)
  and th2 = DISCH t (EXISTS (tm,x) th)
  in
  IMP_ANTISYM_RULE th1 th2
 ) ? failwith `EXISTS_DEL1_CONV`;;

%----------------------------------------------------------------------------%
% EXISTS_DEL_CONV : conv                                                     %
%                                                                            %
%    "?x1 ... xn. t"                                                         %
%    ---->                                                                   %
%    |- (?x1 ... xn. t) = t                                                  %
%                                                                            %
% provided x1,...,xn are not free in t.                                      %
%                                                                            %
% Deletes existential quantifiers. The conversion fails if any of the x's    %
% appear free in t. It does not perform a partial deletion; for example, if  %
% x1 and x2 do not appear free in t but x3 does, the function will fail; it  %
% will not return |- ?x1 ... xn. t = ?x3 ... xn. t.                          %
%----------------------------------------------------------------------------%

let EXISTS_DEL_CONV tm =
 letrec terms_and_vars tm =
  (let x,tm' = dest_exists tm
   in  (tm,x).(terms_and_vars tm')
  ) ? []
 in
 (let txs = terms_and_vars tm
  in
  let t = snd (dest_exists (fst (last txs))) ? tm
  in
  let th = ASSUME t
  in
  let th1 = DISCH tm (itlist (\(tm,x). CHOOSE (x, ASSUME tm)) txs th)
  and th2 = DISCH t (itlist EXISTS txs th)
  in
  IMP_ANTISYM_RULE th1 th2
 ) ? failwith `EXISTS_DEL_CONV`;;

%----------------------------------------------------------------------------%
% EXISTS_EQN_CONV : conv                                                     %
%                                                                            %
%    "?l. !y1 ... ym. l x1 ... xn = t"                                       %
%    ---->                                                                   %
%    |- (?l. !y1 ... ym. l x1 ... xn = t) = T                                %
%                                                                            %
% provided l is not free in t. Both m and n may be zero.                     %
%----------------------------------------------------------------------------%

let EXISTS_EQN_CONV t =
 (let l,ys,t1,t2 = (I # ((I # dest_eq) o strip_forall)) (dest_exists t)
  in
  let xs = snd ((assert (curry $= l) # I) (strip_comb t1))
  in
  let t3 = list_mk_abs (xs,t2)
  in
  let th1 =
   GENL ys (RIGHT_CONV_RULE LIST_BETA_CONV (REFL (list_mk_comb (t3,xs))))
  in
  EQT_INTRO (EXISTS (t,t3) th1)
 ) ? failwith `EXISTS_EQN_CONV`;;

%----------------------------------------------------------------------------%
% PRUNE_ONCE_CONV : conv                                                     %
%                                                                            %
% Prunes one hidden variable.                                                %
%                                                                            %
%    "?l. t1 /\ ... /\ ti /\ eq /\ t(i+1) /\ ... /\ tp"                      %
%    ---->                                                                   %
%    |- (?l. t1 /\ ... /\ ti /\ eq /\ t(i+1) /\ ... /\ tp) =                 %
%       (t1 /\ ... /\ ti /\ t(i+1) /\ ... /\ tp)                             %
%                                                                            %
% where eq has the form "!y1 ... ym. l x1 ... xn = b" and l does not appear  %
% free in the ti's or in b. The conversion works if eq is not present,       %
% i.e. if l is not free in any of the conjuncts, but does not work if l      %
% appears free in more than one of the conjuncts. Each of m, n and p may be  %
% zero.                                                                      %
%----------------------------------------------------------------------------%

let PRUNE_ONCE_CONV tm =
 (let x,t = dest_exists tm
  in
  let l1,l2 = partition (free_in x) (conjuncts t)
  in
  if (null l1) then EXISTS_DEL1_CONV tm
  else
  let [eq] = l1
  in
  let th1 = EXISTS_EQN_CONV (mk_exists (x,eq))
  in
  if (null l2) then th1
  else
  let conj = list_mk_conj l2
  in
  let th2 = AP_THM (AP_TERM "$/\" th1) conj
  in
  let th3 = EXISTS_EQ x (CONJUNCTS_CONV (t,mk_conj(eq,conj)))
  in
  let th4 = RIGHT_CONV_RULE EXISTS_AND_CONV th3
  in
  th4 TRANS th2 TRANS (CONJUNCT1 (SPEC conj AND_CLAUSES))
 ) ? failwith `PRUNE_ONCE_CONV`;;

%----------------------------------------------------------------------------%
% PRUNE_ONE_CONV : string -> conv                                            %
%                                                                            %
% Prunes one hidden variable.                                                %
%                                                                            %
%    PRUNE_ONE_CONV `lj`                                                     %
%                                                                            %
%    "?l1 ... lj ... lr. t1 /\ ... /\ ti /\ eq /\ t(i+1) /\ ... /\ tp"       %
%    ---->                                                                   %
%    |- (?l1 ... lj ... lr. t1 /\ ... /\ ti /\ eq /\ t(i+1) /\ ... /\ tp) =  %
%       (?l1 ... l(j-1) l(j+1) ... lr.                                       %
%         t1 /\ ... /\ ti /\ t(i+1) /\ ... /\ tp)                            %
%                                                                            %
% where eq has the form "!y1 ... ym. lj x1 ... xn = b" and lj does not       %
% appear free in the ti's or in b. The conversion works if eq is not         %
% present, i.e. if lj is not free in any of the conjuncts, but does not work %
% if lj appears free in more than one of the conjuncts. Each of m, n and p   %
% may be zero.                                                               %
%                                                                            %
% If there is more than one line with the specified name (but with different %
% types), the one that appears outermost in the existential quantifications  %
% is pruned.                                                                 %
%----------------------------------------------------------------------------%

letrec PRUNE_ONE_CONV v tm =
 (let x,tm' = dest_exists tm
  in  if (fst (dest_var x) = v)
      then if (is_exists tm')
           then (SWAP_EXISTS_CONV THENC
                 (RAND_CONV (ABS_CONV (PRUNE_ONE_CONV v)))) tm
           else PRUNE_ONCE_CONV tm
      else RAND_CONV (ABS_CONV (PRUNE_ONE_CONV v)) tm
 ) ? failwith `PRUNE_ONE_CONV`;;

%----------------------------------------------------------------------------%
% PRUNE_SOME_CONV : string list -> conv                                      %
%                                                                            %
% Prunes several hidden variables.                                           %
%                                                                            %
%    PRUNE_SOME_CONV [`li1`;...;`lik`]                                       %
%                                                                            %
%    "?l1 ... lr. t1 /\ ... /\ eqni1 /\ ... /\ eqnik /\ ... /\ tp"           %
%    ---->                                                                   %
%    |- (?l1 ... lr. t1 /\ ... /\ eqni1 /\ ... /\ eqnik /\ ... /\ tp) =      %
%       (?li(k+1) ... lir. t1 /\ ... /\ tp)                                  %
%                                                                            %
% where for 1 <= j <= k, each eqnij has the form:                            %
%                                                                            %
%    "!y1 ... ym. lij x1 ... xn = b"                                         %
%                                                                            %
% and lij does not appear free in any of the other conjuncts or in b.        %
% The li's are related by the equation:                                      %
%                                                                            %
%    {li1,...,lik} u {li(k+1),...,lir} = {l1,...,lr}                         %
%                                                                            %
% The conversion works if one or more of the eqnij's are not present,        %
% i.e. if lij is not free in any of the conjuncts, but does not work if lij  %
% appears free in more than one of the conjuncts. p may be zero, that is,    %
% all the conjuncts may be eqnij's. In this case the body of the result will %
% be T (true). Also, for each eqnij, m and n may be zero.                    %
%                                                                            %
% If there is more than one line with a specified name (but with different   %
% types), the one that appears outermost in the existential quantifications  %
% is pruned. If such a line name is mentioned twice in the list, the two     %
% outermost occurrences of lines with that name will be pruned, and so on.   %
%----------------------------------------------------------------------------%

letrec PRUNE_SOME_CONV vs tm =
 (if (null vs)
  then REFL tm
  else (PRUNE_SOME_CONV (tl vs) THENC PRUNE_ONE_CONV (hd vs)) tm
 ) ? failwith `PRUNE_SOME_CONV`;;

%----------------------------------------------------------------------------%
% PRUNE_CONV : conv                                                          %
%                                                                            %
% Prunes all hidden variables.                                               %
%                                                                            %
%    "?l1 ... lr. t1 /\ ... /\ eqn1 /\ ... /\ eqnr /\ ... /\ tp"             %
%    ---->                                                                   %
%    |- (?l1 ... lr. t1 /\ ... /\ eqn1 /\ ... /\ eqnr /\ ... /\ tp) =        %
%       (t1 /\ ... /\ tp)                                                    %
%                                                                            %
% where each eqni has the form "!y1 ... ym. li x1 ... xn = b" and li does    %
% not appear free in any of the other conjuncts or in b. The conversion      %
% works if one or more of the eqni's are not present, i.e. if li is not free %
% in any of the conjuncts, but does not work if li appears free in more than %
% one of the conjuncts. p may be zero, that is, all the conjuncts may be     %
% eqni's. In this case the result will be simply T (true). Also, for each    %
% eqni, m and n may be zero.                                                 %
%----------------------------------------------------------------------------%

letrec PRUNE_CONV tm =
 (if (is_exists tm)
  then (RAND_CONV (ABS_CONV PRUNE_CONV) THENC PRUNE_ONCE_CONV) tm
  else REFL tm
 ) ? failwith `PRUNE_CONV`;;

%----------------------------------------------------------------------------%
% PRUNE_SOME_RIGHT_RULE : string list -> thm -> thm                          %
%                                                                            %
% Prunes several hidden variables.                                           %
%                                                                            %
%    PRUNE_SOME_RIGHT_RULE [`li1`;...;`lik`]                                 %
%                                                                            %
%     A |- !z1 ... zr.                                                       %
%           t = ?l1 ... lr. t1 /\ ... /\ eqni1 /\ ... /\ eqnik /\ ... /\ tp  %
%    ----------------------------------------------------------------------- %
%     A |- !z1 ... zr. t = ?li(k+1) ... lir. t1 /\ ... /\ tp                 %
%                                                                            %
% where for 1 <= j <= k, each eqnij has the form:                            %
%                                                                            %
%    "!y1 ... ym. lij x1 ... xn = b"                                         %
%                                                                            %
% and lij does not appear free in any of the other conjuncts or in b.        %
% The li's are related by the equation:                                      %
%                                                                            %
%    {li1,...,lik} u {li(k+1),...,lir} = {l1,...,lr}                         %
%                                                                            %
% The rule works if one or more of the eqnij's are not present, i.e. if lij  %
% is not free in any of the conjuncts, but does not work if lij appears free %
% in more than one of the conjuncts. p may be zero, that is, all the         %
% conjuncts may be eqnij's. In this case the conjunction will be transformed %
% to T (true). Also, for each eqnij, m and n may be zero.                    %
%                                                                            %
% If there is more than one line with a specified name (but with different   %
% types), the one that appears outermost in the existential quantifications  %
% is pruned. If such a line name is mentioned twice in the list, the two     %
% outermost occurrences of lines with that name will be pruned, and so on.   %
%----------------------------------------------------------------------------%

let PRUNE_SOME_RIGHT_RULE vs th =
 CONV_RULE (DEPTH_FORALL_CONV (RAND_CONV (PRUNE_SOME_CONV vs))) th
 ? failwith `PRUNE_SOME_RIGHT_RULE`;;

%----------------------------------------------------------------------------%
% PRUNE_RIGHT_RULE : thm -> thm                                              %
%                                                                            %
% Prunes all hidden variables.                                               %
%                                                                            %
%     A |- !z1 ... zr.                                                       %
%           t = ?l1 ... lr. t1 /\ ... /\ eqn1 /\ ... /\ eqnr /\ ... /\ tp    %
%    ---------------------------------------------------------------------   %
%     A |- !z1 ... zr. t = t1 /\ ... /\ tp                                   %
%                                                                            %
% where each eqni has the form "!y1 ... ym. li x1 ... xn = b" and li does    %
% not appear free in any of the other conjuncts or in b. The rule works if   %
% one or more of the eqni's are not present, i.e. if li is not free in any   %
% of the conjuncts, but does not work if li appears free in more than one of %
% the conjuncts. p may be zero, that is, all the conjuncts may be eqni's. In %
% this case the result will be simply T (true). Also, for each eqni, m and n %
% may be zero.                                                               %
%----------------------------------------------------------------------------%

let PRUNE_RIGHT_RULE th =
 CONV_RULE (DEPTH_FORALL_CONV (RAND_CONV PRUNE_CONV)) th
 ? failwith `PRUNE_RIGHT_RULE`;;

%============================================================================%
% Functions which do unfolding, unwinding and pruning                        %
%============================================================================%

%----------------------------------------------------------------------------%
% EXPAND_ALL_BUT_CONV : string list -> thm list -> conv                      %
%                                                                            %
% Unfold with the theorems thl, then unwind all lines (except those in the   %
% list) as much as possible and prune the unwound lines.                     %
%                                                                            %
% WARNING -- MAY LOOP!                                                       %
%                                                                            %
%    EXPAND_ALL_BUT_CONV [`li(k+1)`;...;`lim`] thl                           %
%                                                                            %
%    "?l1 ... lm. t1 /\ ... /\ ui1 /\ ... /\ uik /\ ... /\ tn"               %
%    ---->                                                                   %
%    B |- (?l1 ... lm. t1 /\ ... /\ ui1 /\ ... /\ uik /\ ... /\ tn) =        %
%         (?li(k+1) ... lim. t1' /\ ... /\ tn')                              %
%                                                                            %
% where each ti' is the result of rewriting ti with the theorems in thl. The %
% set of assumptions B is the union of the instantiated assumptions of the   %
% theorems used for rewriting. If none of the rewrites are applicable to a   %
% conjunct, it is unchanged. Those conjuncts that after rewriting are        %
% equations for the lines li1,...,lik (they are denoted by ui1,...,uik) are  %
% used to unwind and the lines li1,...,lik are then pruned. If this is not   %
% possible the function will fail. It is also possible for the function to   %
% attempt unwinding indefinitely (to loop).                                  %
%                                                                            %
% The li's are related by the equation:                                      %
%                                                                            %
%    {li1,...,lik} u {li(k+1),...,lim} = {l1,...,lm}                         %
%----------------------------------------------------------------------------%

let EXPAND_ALL_BUT_CONV l thl tm =
 (DEPTH_EXISTS_CONV ((UNFOLD_CONV thl) THENC (UNWIND_ALL_BUT_CONV l)) THENC
  (\tm. let var_names = map (fst o dest_var) (fst (strip_exists tm))
        in  PRUNE_SOME_CONV (subtract var_names l) tm))
 tm
 ? failwith `EXPAND_ALL_BUT_CONV`;;

%----------------------------------------------------------------------------%
% EXPAND_AUTO_CONV : thm list -> conv                                        %
%                                                                            %
% Unfold with the theorems thl, then unwind as much as possible and prune    %
% the unwound lines.                                                         %
%                                                                            %
%    EXPAND_AUTO_CONV thl                                                    %
%                                                                            %
%    "?l1 ... lm. t1 /\ ... /\ ui1 /\ ... /\ uik /\ ... /\ tn"               %
%    ---->                                                                   %
%    B |- (?l1 ... lm. t1 /\ ... /\ ui1 /\ ... /\ uik /\ ... /\ tn) =        %
%         (?li(k+1) ... lim. t1' /\ ... /\ tn')                              %
%                                                                            %
% where each ti' is the result of rewriting ti with the theorems in thl. The %
% set of assumptions B is the union of the instantiated assumptions of the   %
% theorems used for rewriting. If none of the rewrites are applicable to a   %
% conjunct, it is unchanged. After rewriting the function decides which of   %
% the resulting terms to use for unwinding by performing a loop analysis on  %
% the graph representing the dependencies of the lines.                      %
%                                                                            %
% Suppose the function decides to unwind the lines li1,...,lik using the     %
% terms ui1',...,uik' respectively. Then after unwinding the lines           %
% li1,...,lik are pruned (provided they have been eliminated from the RHS's  %
% of the conjuncts that are equations, and from the whole of any other       %
% conjuncts) resulting in the elimination of ui1',...,uik'.                  %
%                                                                            %
% The li's are related by the equation:                                      %
%                                                                            %
%    {li1,...,lik} u {li(k+1),...,lim} = {l1,...,lm}                         %
%                                                                            %
% The loop analysis allows the term to be unwound as much as possible        %
% without the risk of looping. The user is left to deal with the recursive   %
% equations.                                                                 %
%----------------------------------------------------------------------------%

let EXPAND_AUTO_CONV thl tm =
 (DEPTH_EXISTS_CONV (UNFOLD_CONV thl) THENC
  UNWIND_AUTO_CONV THENC
  (\tm. let internals,conjs = (I # conjuncts) (strip_exists tm)
        in
        let vars =
         flat (map (frees o (\tm. rhs tm ? tm) o snd o strip_forall) conjs)
        in
        PRUNE_SOME_CONV (map (fst o dest_var) (subtract internals vars)) tm))
 tm
 ? failwith `EXPAND_AUTO_CONV`;;

%----------------------------------------------------------------------------%
% EXPAND_ALL_BUT_RIGHT_RULE : string list -> thm list -> thm -> thm          %
%                                                                            %
% Unfold with the theorems thl, then unwind all lines (except those in the   %
% list) as much as possible and prune the unwound lines.                     %
%                                                                            %
% WARNING -- MAY LOOP!                                                       %
%                                                                            %
%    EXPAND_ALL_BUT_RIGHT_RULE [`li(k+1)`;...;`lim`] thl                     %
%                                                                            %
%         A |- !z1 ... zr.                                                   %
%               t = ?l1 ... lm. t1 /\ ... /\ ui1 /\ ... /\ uik /\ ... /\ tn  %
%    ----------------------------------------------------------------------- %
%     B u A |- !z1 ... zr. t = ?li(k+1) ... lim. t1' /\ ... /\ tn'           %
%                                                                            %
% where each ti' is the result of rewriting ti with the theorems in thl. The %
% set of assumptions B is the union of the instantiated assumptions of the   %
% theorems used for rewriting. If none of the rewrites are applicable to a   %
% conjunct, it is unchanged. Those conjuncts that after rewriting are        %
% equations for the lines li1,...,lik (they are denoted by ui1,...,uik) are  %
% used to unwind and the lines li1,...,lik are then pruned. If this is not   %
% possible the function will fail. It is also possible for the function to   %
% attempt unwinding indefinitely (to loop).                                  %
%                                                                            %
% The li's are related by the equation:                                      %
%                                                                            %
%    {li1,...,lik} u {li(k+1),...,lim} = {l1,...,lm}                         %
%----------------------------------------------------------------------------%

let EXPAND_ALL_BUT_RIGHT_RULE l thl th =
 CONV_RULE (DEPTH_FORALL_CONV (RAND_CONV (EXPAND_ALL_BUT_CONV l thl))) th
 ? failwith `EXPAND_ALL_BUT_RIGHT_RULE`;;

%----------------------------------------------------------------------------%
% EXPAND_AUTO_RIGHT_RULE : thm list -> thm -> thm                            %
%                                                                            %
% Unfold with the theorems thl, then unwind as much as possible and prune    %
% the unwound lines.                                                         %
%                                                                            %
%    EXPAND_AUTO_RIGHT_RULE thl                                              %
%                                                                            %
%         A |- !z1 ... zr.                                                   %
%               t = ?l1 ... lm. t1 /\ ... /\ ui1 /\ ... /\ uik /\ ... /\ tn  %
%    ----------------------------------------------------------------------- %
%     B u A |- !z1 ... zr. t = ?li(k+1) ... lim. t1' /\ ... /\ tn'           %
%                                                                            %
% where each ti' is the result of rewriting ti with the theorems in thl. The %
% set of assumptions B is the union of the instantiated assumptions of the   %
% theorems used for rewriting. If none of the rewrites are applicable to a   %
% conjunct, it is unchanged. After rewriting the function decides which of   %
% the resulting terms to use for unwinding by performing a loop analysis on  %
% the graph representing the dependencies of the lines.                      %
%                                                                            %
% Suppose the function decides to unwind the lines li1,...,lik using the     %
% terms ui1',...,uik' respectively. Then after unwinding the lines           %
% li1,...,lik are pruned (provided they have been eliminated from the RHS's  %
% of the conjuncts that are equations, and from the whole of any other       %
% conjuncts) resulting in the elimination of ui1',...,uik'.                  %
%                                                                            %
% The li's are related by the equation:                                      %
%                                                                            %
%    {li1,...,lik} u {li(k+1),...,lim} = {l1,...,lm}                         %
%                                                                            %
% The loop analysis allows the term to be unwound as much as possible        %
% without the risk of looping. The user is left to deal with the recursive   %
% equations.                                                                 %
%----------------------------------------------------------------------------%

let EXPAND_AUTO_RIGHT_RULE thl th =
 CONV_RULE (DEPTH_FORALL_CONV (RAND_CONV (EXPAND_AUTO_CONV thl))) th
 ? failwith `EXPAND_AUTO_RIGHT_RULE`;;
