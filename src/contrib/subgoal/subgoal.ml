% 

Author:          R. A. Fleming

Affiliation:     Hewlett Packard Laboratories, Bristol

Address:         Hewlett Packard Laboratories,
                 Filton Road,
                 Stoke Gifford
                 Bristol BS12 6QZ
                 U.K.

Tel:             +44 272 799910

Fax:             +44 272 890554

Email:           ..!mcvax!ukc!hplb!raf
                 raf@hplb.lb.hp.co.uk

File:            Subgoal Package

Date:            17/12/90

This file contains a new subgoal package.

Its main purpose is to fix the package so that it remembers the tactics
used in the interactive construction of a proof.  This is to obviate the
need to work with two windows, one where a tactic is gradually being
constructed and one where it is interactively executed on the subgoal
package.  (I've got fed up with transfering tactics from one to the other.
I often fail to keep them in line, I get confused with deep nesting etc.)

At any point in the proof, the tactic can can be printed off by invoking
the function tacs.

There is a bye-product:  The package builds a "tactic tree" with tactics at
its nodes.  The user manipulates this.  A typical manipulation is an
"expansion" of its leaves (just like expand in the old package).  However
there are now more general ways of editing the tree.  The user may
re-expand or unexpand nodes that have already been expanded.  (Sometimes it
is useful even to re-expand proved nodes, in order to insert more efficient
tactics.)  There is also a facility for "factoring" tactics, transforming
e.g.
          A THENL [B THEN C; B THEN D]
to
          A THEN B THENL [C; D]

Warnings: 

1) The package is somewhat experimental.  The main reason for distribution
at this time is to get feedback on whether people find its features useful.
The interface is quite large.  This is part of the experiment.  I am not
sure what commands and facilities people will find useful.  Some of these
may be withdrawn.

2) The package does not yet do the validity checks done by the old package.

3) Proofs are kitted together using different functions than those used in
"THEN".  If I got the code wrong, the package may prove things the tactic
won't and vice-versa.  Also, after "factoring", the old theorems are
retained without re-proving them.

4) The package may get slow on large proofs.  To some extent this is
inevitable as it manipulates the leaves of (large) trees.  (But there is
scope for further optimisation.)

5) The package is currently limited in that while tactics which are
individually input to the package are treated as different nodes, compound
tactics input to the package at one go appear at one node in the tree and
cannot be split apart.  Note that if a partially complete tactic is printed
off and later re-input to the package, it will be treated as a single node,
and cannot be further edited.

Explanation
-----------

A goal is set up using the familiar g and set_goal procedures.

There is always a current tree containing the tactics and goals.  There is
a current "cursor" position within the tree.  This cursor can be at any
subtree within the current tree. Commands issued to the package effect the
current subtree.

The most typical tree manipulation is just to expand a node.  This can also
be "unexpanded" again.  Some further functions are supplied for doing
slightly more sophisticated expansions.  (See below.)

The is a "compact" function.  This factors tactics in the current subtree.  E.g.
it factors
           x THENL [a THEN b; a THEN c]
into
           x THEN a THENL [b; c]

As well as the cursor, there is also a "copy cursor".  Issuing a "copy"
command copies the subtree at the copy cursor into the place pointed at by
the cursor.

When subtrees are deleted, they are never really lost but saved on a list
of discarded trees.  The copy cursor can be placed on any of these
discarded trees (or any of their subtrees) so that they can be copied back
into the current tree.

Description of some commands
----------------------------

Commands requiring some explanation are treated here.  Others just appear
in the command summary below.

*********** e (tactic:string)      (= expand tactic)   

expands a node by applying a tactic.  (As per old package).  The may be
applied at any node in the proof, including non-leaf and already proven
nodes. 

Note that it takes a string parameter.  This can cause problems when
quoting HOL terms, as \ is a string escape.  Hence the user must input e.g.
e `SPEC_TAC "A/\\B"`
rather than
e (SPEC_TAC "A/\B")
as in the old package.  This is admittedly awful, and hence the alternative:

*********** r_e ()                 (= read_expand ())  

When the user types 

r_e();;

the system reads from the terminal until it encounters ;;.  No escapes are
required.  So the user may input
r_e();;
SPEC_TAC "A/\B";;

This, too, is a little long-winded unless you run HOL in an emacs
environment, in which case a macro for inserting 

r_e();;

can be defined (by

(defun expand ()
    (interactive)
    (insert "r_e();;\n")
)

) and this function bound to a function key, and the whole thing is quite
smooth.  (Similar macros can be defined for other favorite expansion
commands.)

Note: I am sorry to admit that on lengthy input, it is encouraged by a few
extra carriage returns.  I have no idea why.

************* te (tactic:string)    (= then_expand tactic)

is like e but applies the tactic to all the unexpanded subgoals of the
immediately superior subtree.  If it succeeds on all the subgoals, it
compacts the result.  This consequently results in a "THEN" node instead of
a "THENL" node.

************* es (tl:string list)   (= expands tl)

applies to all unexpanded subnodes of the current cursor position.  (Hence
the user will typically have to move the cursor to a higher position in the
tree.)  It expands each such node to the first tactic in the list to
succeed.  (This is hence a little like an ORELSE except that the particular
tactic to succeed is put into the tactic tree.)

************* r_es ()               (= read_expands ())

does an expands, but reads its list of tactics from the terminal.  The
tactics are separated by ;;.  The final tactic is indicated by a further
;;.  E.g.

r_es();;
STRIP_TAC;;BETA_TAC;;
ASM_REWRITE_TAC;;;;

*********** une ()                (or unexpand ())

Unexpands nodes.  Can be used on either proven or unproved nodes.

*********** r n                    (or rotate n)

Similar to the old rotation.  However, in the new package, the rotation is
around *all* the unproven leaf nodes.  (In the old package, the rotation was
only around the leaf nodes of the "current" non-leaf goal.)

*********** tacs ()

This prints off the current tactic tree. Its action can be modified by
assigning to some reference variables.  
print_tac_goals             prints the goals when set to true
print_tacs                  prints the tactics when set to true

*********** place ()

This prints the context around the current tactic position.  Its action can
be modified by assigning to some reference variables.
print_height               is an integer controlling how high up above the
                           current cursor position is printed
print_depth                is an integer controlling how deep below the
                           current cursor position is printed
 
These variables also control the context printing when moving around the tree.

*********** copy()

attempts to copy the subtree pointed at by the copy cursor to the position
pointed at by the current cursor.  This may be only partially successful in
that only some of the tree can be copied.

*********** swap ()

swaps the positions of the cursor and copy cursor.  If the copy cursor is
on a deleted tree, that tree becomes the current tree.

*********** c_newer(), c_older()

moves the copy cursor about on the list of discarded trees.  (The current
tree is always the newest.)  

*********** save_tree()

saves the current subtree at the front of the list of discarded subtrees.

The Implementation:
------------------

I am sorry to say that this is rather embarrassing.  I did not have a clue
how to get my hands on the ML parser.  I have therefore used inject_input.
The code at this point is completely horrifying.  Don't look.  (Note that
this also meant that the package could not be written as a read/eval/print
loop, which would have been nicer.)

COMMAND SUMMARY :
---------------
%
let tac_help() = print_string
`
expand             or e       expands node with string representing tactic
read_expand        or r_e     same as expand but reads tactic from terminal
then_expand        or es      expands subnodes with string representing tactic
read_then_expand   or r_te    same as then_expand but reads tactic from terminal
expands            or r_es    expands all subnodes with first of list of tactics
unexpand           or une     collapses node back into unexpanded node
left right up down            moves cursor around tactic tree
top bottom rotate  or r
c_left c_right c_up c_down    moves copy cursor around tactic tree
c_top
c_here                        moves copy cursor to cursor
swap                          swaps cursor and copy cursor
c_older c_newer               moves copy cursor between deleted trees
backup             or b       backs up to previous state
set_goal           or g       sets up goal for tactic package
place                         prints current cursor position
c_place                       prints position of copy cursor
save_tree                     saves current subtree
tacs                          prints off tactics in current tactic tree
pgoals                        prints off remaining unproved goals
top_goal                      prints off goal at cursor position currently
tac_tree_thm                  evaluates to theorem at current cursor position
tac_help                      prints this message
`;;


% ************ Basic type, projection functions etc. ********************* %

% 

Data-structure for remembering tactics applied and the goals they were
applied on. 

There is an invariant, which I did not bother to capture in the type.  The
(proof#goal) list/(proof#thm) list must be a singleton unless the node
resides within a singleton tac_node list.  The idea is that if it is not a
singleton, the node represents the B in a A THEN B, where A generates more
than one subgoal.  (The B is "factored".)

%

rectype tac_node = unexpanded of goal | 
                   subgoals of (tactic # string) # ((proof # goal) list) # (tac_node list) |
                   proofs of (tactic # string) # ((proof # thm) list) # (tac_node list);;

let thm_goal thm = hyp thm, concl thm;;

let is_unexpanded prf =
  (let unexpanded _ = prf in true)?false
and is_subgoals prf =
  (let subgoals _ = prf in true)?false
and is_proofs prf =
  (let proofs _ = prf in true)?false;;

let node_string prf =
  if is_unexpanded prf then failwith `node_string`
  else ((let subgoals (s,_,_) = prf in snd s)?(let proofs (s,_,_) = prf in snd s))
and node_tac prf =
  if is_unexpanded prf then failwith `node_tac`
  else ((let subgoals (s,_,_) = prf in fst s)?(let proofs (s,_,_) = prf in fst s))
and node_goals prf =
  ((let unexpanded g = prf in [g])
   ?(let subgoals (_,l,_) = prf in map snd l))
  ?(let proofs (_,l,_) = prf in map (thm_goal o snd) l)
and node_thms prf =
  (let proofs (_,l,_) = prf in map snd l)?failwith`node_thms`
and node_proofs prf =
  ((let subgoals (_,l,_) = prf in map fst l)?
   (let proofs (_,l,_) = prf in map fst l))?failwith`node_proofs`
and sub_nodes prf =
  ((let subgoals (_,_,l) = prf in l)
   ?(let proofs (_,_,l) = prf in l))?failwith`sub_nodes`;;

% ************************** Reference variables ********************** %

% The current tactic tree. %
letref current_tac_tree = unexpanded ([],"T");;

% This is the current address within the tactic. Earlier numbers in the
list relate to the higher addresses within the tree. %
letref current_place : int list = [];;

% This is temporary storage for theorems and goals, prior to printing.  
Doubtless this should all be done applicatively but it makes the code
simpler to do all this by side-effect. %
letref new_thm_dump : thm list = [];;
letref old_thm_dump : thm list = [];;
letref new_goal_dump : goal list = [];;

% Used to store discarded tactic trees. %
letref old_tac_trees : tac_node list = [];;
letref copy_place : int # (int list) = 0,[];;

% Used for backing up. %
letref backup_tac_tree_list : (tac_node#int list) list = [];;

% *************** Tactic tree constructor ************************ %

% check_goal needs to check alpha convertability --- too slow %

let check_goal (p,y) = p;;

%  if (concl p = snd y) & (forall (\x. mem x (fst y)) (hyp p)) then p
  else failwith`check_goal` %

% Proves node if all subgoals proved. %
let build_node (s,p,l) =
  if forall is_proofs l
  then let l' = if null (tl l) then node_thms (hd l) else map (hd o node_thms) l in
  let new_node = proofs(s,map(\x,y. x,check_goal(x l',y))p,l) in
  (new_thm_dump := (node_thms new_node)@new_thm_dump; new_node)
  else subgoals (s,p,l);;

% ******************************** Subtrees **************************** %

% Retrieves the sub-tree of prf at the address place. %
letrec tac_subtree prf place =
  (if null place then prf
   else if is_unexpanded prf then fail
   else tac_subtree (el (hd place) (sub_nodes prf)) (tl place))
  ?failwith`tac_subtree`;;

% ************ Functions for moving around tactic trees. *************** %

letrec const_list x n = if n=0 then [] else x.(const_list x (n-1));;

letrec right_place place n =
  if null (tl place) then [(hd place)+n]
  else (hd place).(right_place (tl place) n)
and left_place place n =
  if null (tl place) then 
  if hd place - n > 0 then [(hd place)-n] else failwith`left_place`
  else (hd place).(left_place (tl place) n)
and down_place place n =
  if null place then const_list 1 n
  else (hd place).(down_place (tl place) n)
and up_place place n =
  letrec f p n = if n=0 then [] else (hd p).(f (tl p)(n-1)) in
  (f place (length place - n))?failwith`up_place`;;

let go_up prf place n = (up_place place n)?failwith`up`
and go_down prf place n = 
  let place' = down_place place n in 
  ((let p = tac_subtree prf place' in place')?failwith`down`)
and go_right prf place n =
  let place' = right_place place n in
  ((let p = tac_subtree prf place' in place')?failwith`right`)
and go_left prf place n =
  (left_place place n)?failwith`left`;;

% Finds address of first node satisfying p. 
  Fails if none found. %
letrec first_tac_node p prf =
letrec f n l =
  if null l then failwith `first_tac_node`
  else if p (hd l) then [n]
       else ((n.(first_tac_node p (hd l)))
             ? f (n+1) (tl l)) in
if p prf then []
else f 1 (sub_nodes prf);;

let first_unexpanded = first_tac_node is_unexpanded;;

letrec all_tac_nodes p prf =
letrec f n l =
  if null l then []
  else let rest = 
       (map (\x. n.x)(if is_unexpanded (hd l) 
                      then [] else f 1 (sub_nodes (hd l))))
       @(f(n+1)(tl l)) in
       if p (hd l) then [n].rest else rest in
let rest = if is_unexpanded prf then [] else f 1 (sub_nodes prf) in
if p prf then [].rest else rest;;

let all_unexpandeds = all_tac_nodes is_unexpanded;;

let find_rotate x l =
letrec r l1 l2 = if x = hd l1 then l1,l2 else r (tl l1) ((hd l1).l2) in
(let l1,l2 = r l [] in l1@(rev l2))?failwith`find_rotate`;;

let rotatelist l = ((tl l)@[hd l])?[];;

let next_tac_node p prf place =
letrec bellow_to_right_of x y =
  if null x then true else if null y then false
  else if hd x > hd y then false
  else if hd x < hd y then true
  else bellow_to_right_of (tl x) (tl y) in
let prf' = tac_subtree prf place 
and x = all_tac_nodes p prf in
if p prf' then hd (rotatelist (find_rotate place x))
else ((find (bellow_to_right_of place) x)?(hd x));;

let next_unexpanded = next_tac_node is_unexpanded;;

% ********************** Tree substitution ****************************** %

% Procedure for saving discarded subtrees. %
let discard_tree prf =
  if is_unexpanded prf then () 
  else (old_tac_trees := prf.old_tac_trees; let x,y = copy_place in copy_place := x+1,y;());;

%  Substitutes prf' at place in prf. %
letrec tac_subst prf prf' place =
  letrec slist n x l =
  if n=1 then x.(tl l)
  else (hd l).(slist (n-1) x (tl l)) in
  if null place then prf'
  else if is_unexpanded prf then failwith `tac_subst`
  else ((let subgoals (s,p,l) = prf in
  subgoals (s,p,
            (slist (hd place) 
                   (tac_subst (el (hd place) l) prf' (tl place))
                   l)))
       ?let proofs (s,p,l) = prf in
        proofs (s,p,
                (slist (hd place) 
                       (tac_subst (el (hd place) l) prf' (tl place))
                       l)));;

% Goes up the tree unproving nodes. %
letrec unpercolate_proofs prf place =
   if place = [] then prf
   else let place' = up_place place 1 in
   ((let proofs(s,p,l) = tac_subtree prf place' in
     (old_thm_dump := (node_thms (proofs(s,p,l)))@old_thm_dump;
      unpercolate_proofs
       (tac_subst prf (subgoals(s,map(\x,y.x,thm_goal y)p,l)) place')
       place'))?prf);;

% Goes up the tree proving nodes. %
letrec percolate_proofs prf place =
  if null place then prf
  else let place' = up_place place 1 in
  let subgoals(s,p,l) = tac_subtree prf place' in
    if forall is_proofs l
    then percolate_proofs (tac_subst prf (build_node (s,p,l)) place') place'
    else prf;;

let tac_subst_perc prf prf' place =
  let prf'' = tac_subtree prf place in
  (discard_tree prf'';
  if is_proofs prf' & (not (is_proofs prf''))
  then percolate_proofs (tac_subst prf prf' place) place
  else if is_proofs prf'' & (not (is_proofs prf'))
  then (old_thm_dump := node_thms prf''; unpercolate_proofs (tac_subst prf prf' place) place)
  else tac_subst prf prf' place);;

% *********************** Tree manipulation functions *************************** %

letrec check_goals(pl,gl) =
  if null pl then []
  else (check_goal(hd pl,hd gl)).(check_goals(tl pl, tl gl));;

% Used for knitting together proofs when we have factored "THEN"s. %
let extract_list (n, m) x =
(letrec include m x = if m=0 then [] else (hd x).(include (m-1) (tl x)) in
include m (funpow n tl x))?failwith`extract_list`;;

let selected_sublist l =
letrec s l n = if null l then [] else (n, hd l).s (tl l) (n+(hd l)) in 
s l 0;;

let knit_proofs l pl = map(\x,y. x o (extract_list y)) (combine(pl,selected_sublist l));;

% Note that the goal matching is quite primitive.  E.g. re-ordering of hypotheses will
  result if no matching.  Hence old subtrees will sometimes not be placed in the tree
  against all expectations. %
letrec exp_node prf place gl (t, s) =
let sgsl,pl = split(map t gl) in
let sgsl',pl' = flat sgsl,knit_proofs(map length sgsl)pl in
if null sgsl' then
let new_node = proofs ((t,s),combine(pl',check_goals(map (\x.x[])pl',gl)),[]) in
(new_thm_dump := (node_thms new_node)@new_thm_dump; 
 tac_subst_perc prf new_node place)
else let new_node = build_node ((t,s),combine(pl',gl),map unexpanded sgsl') in
     (new_goal_dump := sgsl'@new_goal_dump;tac_subst_perc prf new_node place);;

% This expands a node of prf at place. %
let expand_tac_node tac prf place =
let prf' = tac_subtree prf place in
exp_node prf place (node_goals prf') tac;;

% Expands first of a list of tactics %
let expand_tacs_node taclist prf place =
let prf' = tac_subtree prf place in
let gl = node_goals prf' in
letrec el taclist =
if null taclist then failwith`expand_tacs`
else ((exp_node prf place gl (hd taclist))?el(tl taclist)) in
el taclist;;

% Expands first of a list of tactics on each unexpanded subnode. %
let expand_tacs_nodes taclist prf place =
  letrec x l = if null l then prf 
    else let prf' = x (tl l)
         in ((expand_tacs_node taclist prf' (hd l))?prf') in
  x (map (\y. place@y) (all_unexpandeds (tac_subtree prf place)));;

% Turns nodes into unexpanded nodes. %
let unexpand_tac_node prf place =
  let prf' = tac_subtree prf place in
  let gl = node_goals prf' in
  if length gl = 1
  then tac_subst_perc prf (unexpanded (hd gl)) place
  else let place' = up_place place 1 in
       let prf'' = tac_subtree prf place' in
       ((let subgoals (s,p,[x]) = prf'' in
          tac_subst_perc prf (subgoals (s,p,map unexpanded gl)) place')
       ?(let proofs (s,p,[x]) = prf'' in
         tac_subst_perc prf (subgoals (s,map(\x,y.x,thm_goal y)p,map unexpanded gl)) place'));;

% This does a little optimisation on the tree.  It factors, e.g.
           x THENL [a THEN b; a THEN c]
into
           x THEN a THENL [b; c]

There are other optimisations that could be done, but this function isn't
smart enough to do them. 

The implementation of the tactic identity check is very curious.  I have
used the ML function identity but this does not seem to work for lambda
abstractions.  An alternative is to compare the sources.  I have made a
blundering attempt to do so while taking account for white space.  To be on
the safe side, I have or'd the two tactic identity checks together.

%
let string_compare =
  let is_sep x = let x = ascii_code x in
    (x=0 or (33 > x & x < 46) or (58 > x & x < 63) or 
    (92 > x & x < 93) or x = 96 or x = 126) & (not(x=37))
  and white_space = [` `;`
`] in
  letrec comp_string s =
    if null s or (null (tl s)) then s
    else let x = if hd s = `
` then ` ` else hd s in
     if is_sep x & mem (hd (tl s)) white_space then comp_string (x.(tl (tl s)))
     else if x = ` ` & is_sep (hd (tl s)) then
     comp_string (tl s)
     else x.(comp_string (tl s)) in
  \t1 t2. (t1 = t2) or (comp_string(` `.(explode t1)@[` `]) = comp_string(` `.(explode t2)@[` `]));;

letrec compact_tac_tree prf = 
  if is_unexpanded prf then prf
  else (let subgoals (s,p,l) = prf in
  let l' = map compact_tac_tree l in
  if null l' then prf
  else if null (tl l') 
       then subgoals (s,p,l')
       else ((let sl = map (\x.node_tac x,node_string x) l'
            in if forall (\x. (fst x = fst (hd sl)) or string_compare (snd x) (snd (hd sl))) (tl sl)
               then let l'' = map sub_nodes l' in
                    let p'' = combine(knit_proofs(map length l'')(map(hd o node_proofs)l'),
                                      map(hd o node_goals)l') in
                    compact_tac_tree 
                      (subgoals (s,p,[subgoals (hd sl,p'',flat l'')]))
               else subgoals (s,p,l'))?subgoals(s,p,l')))
  ?let proofs (s,p,l) = prf in
  let l' = map compact_tac_tree l in
  if null l' then prf
  else if null (tl l') 
       then proofs (s,p,l')
       else ((let sl = map (\x.node_tac x,node_string x) l'
            in if forall (\x. (fst x = fst (hd sl)) or string_compare (snd x) (snd (hd sl))) (tl sl)
               then let l'' = map sub_nodes l' in
                    let p'' = combine(knit_proofs(map length l'')(map(hd o node_proofs)l'),
                                      map(hd o node_thms)l') in
                    compact_tac_tree 
                      (proofs (s,p, [proofs (hd sl,p'',flat l'')]))
               else proofs (s,p,l'))?proofs(s,p,l'));;

% Expands node by applying tactic to all subgoals, producing "THEN" node %
let then_expand_tac_node t prf place =
let place' = up_place place 1 in
let prf' = expand_tacs_nodes [t] prf place' in
tac_subst_perc prf' (compact_tac_tree (tac_subtree prf' place')) place';;

% Applies tactics in prf to goals gl. %
letrec interp_tac_tree gl prf =
if is_unexpanded prf then if null (tl gl) then unexpanded (hd gl) else failwith`interp_tac_tree`
else ((let sgsl,pl = split(map (node_tac prf) gl) in
let sgsl',pl' = flat sgsl,knit_proofs(map length sgsl)pl in
if null sgsl' then
let new_node = proofs ((node_tac prf,node_string prf),combine(pl',check_goals(map (\x.x[])pl',gl)),[]) in
(new_thm_dump := (node_thms new_node)@new_thm_dump; new_node)
else let prfl = sub_nodes prf in
     let new_subnodes = if null (tl prfl) then [interp_tac_tree sgsl' (hd prfl)]
                        else if length sgsl' = length prfl 
                        then map (\x,y. interp_tac_tree [x] y) (combine(sgsl',prfl))
                        else map unexpanded sgsl' in
     let new_node = build_node ((node_tac prf,node_string prf),combine(pl',gl),new_subnodes) in
     (new_goal_dump := (flat (map (node_goals o (tac_subtree new_node)) (all_unexpandeds new_node)))@new_goal_dump;
      new_node))
?if null (tl gl) then unexpanded (hd gl) else failwith `interp_tac_tree`);;

% Used for copying trees from one place to another. %
let insert_tac_tree prf prf' place =
let prf'' = tac_subtree prf place in
if node_goals prf'' = node_goals prf' then
tac_subst_perc prf prf' place else
(print_string`interpreting tactic tree`;print_newline();
 tac_subst_perc prf (interp_tac_tree (node_goals prf'') prf') place);;

% ****************** Procedures for printing info on tree manipulations ******************* %

let setup_tac_tree_updates () = (old_thm_dump := []; new_thm_dump := []; new_goal_dump := []);;

let remaining_goals prf place =
let prf' = tac_subtree prf place
and x = all_tac_nodes is_unexpanded prf in
(flat (map (node_goals o (tac_subtree prf))
        (find_rotate (if is_unexpanded prf' then place
                      else first_unexpanded prf') 
                     x)))?[];;

letrec printl f l =
  if null l then () 
  else if null (tl l) then f (hd l)
  else (f (hd l); print_newline(); printl f (tl l));;

let print_tac_tree_goals prf place =
let gls = rev (remaining_goals prf place) in
if null gls then (print_string`goal proved`; print_newline())
else (print_string`remaining goals:`; print_newline(); printl print_goal gls);;

let print_tac_tree_updates () =
  (if null old_thm_dump then ()
   else (print_string`discarded:`;print_newline();
         printl print_thm old_thm_dump; print_newline());
   if null new_thm_dump then ()
   else (print_string`proved:`;print_newline();
         printl print_thm new_thm_dump; print_newline());
   if null new_goal_dump then print_tac_tree_goals current_tac_tree []
   else (print_string`new goals:`;print_newline();
         printl print_goal (rev new_goal_dump); print_newline());
   old_thm_dump := []; new_thm_dump := []; new_goal_dump := []);;

let gen_tac_node_proc f =
  let old_stuff = current_tac_tree, current_place in
     (setup_tac_tree_updates ();
      current_tac_tree := f current_tac_tree current_place;
      print_tac_tree_updates();
      current_place := ((next_unexpanded current_tac_tree current_place)?[]);
      backup_tac_tree_list := old_stuff.backup_tac_tree_list;
      ());;

let current_copy_tree() = let x,y = copy_place in if x=0 then current_tac_tree else el x old_tac_trees;;

let current_copy_subtree() = let x,y = copy_place in tac_subtree (current_copy_tree()) y;;

let expand_tac_node_proc t s = gen_tac_node_proc (expand_tac_node (t,s))
and unexpand_tac_node_proc () = gen_tac_node_proc unexpand_tac_node
and expand_tacs_nodes_proc tl = gen_tac_node_proc (expand_tacs_nodes tl)
and then_expand_tac_node_proc t s = gen_tac_node_proc (then_expand_tac_node (t,s))
and copy () = gen_tac_node_proc (\x y. insert_tac_tree x (current_copy_subtree ()) y)
and compact () = gen_tac_node_proc (\x y. tac_subst x (compact_tac_tree (tac_subtree x y)) y);;

% ************************ Procedures for reading tactics from terminal ******************** %

letrec unescapes l =
  if null l then []
  else if hd l = 92 then 92.92.(unescapes (tl l))
  else (hd l).(unescapes (tl l));;

% --------------------------------------------------------------------- %
% ascii_ize added for HOL version 1.12.			 [TFM 90.12.19] %
% --------------------------------------------------------------------- %

let ascii_ize tok =
    let space = ascii_code ` ` in
        itlist (\n l. map ascii_code (explode n)@[space]@l) (words tok) [];;

let expand =
let ex = ascii_ize `expand_tac_node_proc(` 
and mid = ascii_ize `)\``
and stop = ascii_ize `\`;;`
in \t. let t' = ascii_ize t in
       inject_input (ex@t'@mid@(unescapes t')@stop);;

letrec asciized_pairs ss =
  if null ss then [] else if null (tl ss)
  then (hd ss)@(ascii_ize`,\``)@(unescapes(hd ss))@(ascii_ize`\``)@(asciized_pairs (tl ss))
  else (hd ss)@(ascii_ize`,\``)@(unescapes(hd ss))@(ascii_ize`\`;`)@(asciized_pairs (tl ss));;

let expands =
let ex = ascii_ize `expand_tacs_nodes_proc[` 
and stop = ascii_ize `];;`
in \t. let t' = asciized_pairs (map ascii_ize t) in
       inject_input (ex@t'@stop);;

letrec get_chars chars eoi =
  let x = tty_read () in
  if eoi 
  then if x=`;` then rev (tl chars) else get_chars ((ascii_code x).chars) false
  else get_chars ((ascii_code x).chars) (x=`;`);;

let read_expand =
let ex = ascii_ize `expand_tac_node_proc(` 
and mid = ascii_ize `)\``
and stop = ascii_ize `\`;;`
in \(). let t = get_chars [] false in
        inject_input (ex@t@mid@(unescapes t)@stop);;

let read_expands =
let ex = ascii_ize `expand_tacs_nodes_proc[` 
and stop = ascii_ize `];;` in
letrec get_chars_string () =
let x = get_chars [] false in
if forall (\y. y=32 or y=10) x then [] else (if hd x = 10 then tl x else x).(get_chars_string ()) in
\(). let t = asciized_pairs (get_chars_string()) in
     inject_input (ex@t@stop);;

let then_expand =
let ex = ascii_ize `then_expand_tac_node_proc(` 
and mid = ascii_ize `)\``
and stop = ascii_ize `\`;;`
in \t. let t' = ascii_ize t in
       inject_input (ex@t'@mid@(unescapes t')@stop);;

let read_then_expand =
let ex = ascii_ize `then_expand_tac_node_proc(`
and mid = ascii_ize `)\``
and stop = ascii_ize `\`;;`
in \(). let t = get_chars [] false in
        inject_input (ex@t@mid@(unescapes t)@stop);;

% *********************** Printing procedures ************************** %

let UNEXPANDED = ALL_TAC;;

letref print_tac_goals = false;;
letref print_tacs = true;;
letref print_place = false;;
letref print_depth = 2;;
letref print_height = 3;;

let print_tree prf place pgoals ptacs pplace depth =
letrec pp prf p =
let pnode () = 
 (if pgoals then printl print_goal (node_goals prf) else ();
  if is_unexpanded prf then if ptacs then print_string`UNEXPANDED` else ()
  else let s,l = (node_string prf, sub_nodes prf) in
       if ptacs & null l then print_string s
       else if null (tl l)
       then (if ptacs then print_string s else (); 
             print_string ` THEN`; print_newline(); 
             if length p = depth then print_string`...` else pp (hd l) (down_place p 1))
       else (if ptacs then print_string s else (); 
             print_string ` THENL`; print_newline();
             print_string`[`; 
             if length p = depth then print_string`...` 
             else pplist l (down_place p 1); print_string`]`)) in
  if p = place & pplace then
  (print_string` % ***> % `;pnode();print_string` % <*** % `)
  else pnode()
and pplist l p =
  if null (tl l) then pp (hd l) p
  else (pp (hd l) p; print_string`;`; print_newline(); pplist (tl l) (right_place p 1))
in (pp prf [];print_newline());;

let print_context prf place =
  let place' = (up_place place print_height)?[] in
  (if place' = [] then () else (print_string`...`; print_newline());
   print_tree (tac_subtree prf place') 
              (funpow (length place') tl place) print_tac_goals print_tacs true 
              ((let x = length place in
                if print_height > x then x else print_height)+print_depth));;

% ******************************** Miscellaneous ************************************* %

% This extracts the tactic from a tactic tree.  (I'm not sure what use it is, but it
ought to come in useful some time.) %
letrec tac_tree_tac prf =
if is_unexpanded prf then ALL_TAC 
else let prfl = sub_nodes prf in 
if null prfl then node_tac prf
else if null (tl prfl) then (node_tac prf) THEN (tac_tree_tac (hd prfl))
else (node_tac prf) THENL (map tac_tree_tac prfl);;

% ******************************** User interface commands **************************** %

let backup() =
  (discard_tree current_tac_tree;
   current_tac_tree,current_place := hd backup_tac_tree_list;
   backup_tac_tree_list := tl backup_tac_tree_list;
   print_tac_tree_goals current_tac_tree current_place);;

let rotate n =
  (backup_tac_tree_list := (current_tac_tree, current_place).backup_tac_tree_list;
   current_place := funpow n (next_unexpanded current_tac_tree) current_place;
   print_tac_tree_goals current_tac_tree current_place)?print_tac_tree_goals current_tac_tree current_place;;

let place() = print_context current_tac_tree current_place;;

let c_place() = print_context (current_copy_tree()) (snd copy_place);;

let move_c_place p = (copy_place := (fst copy_place), p (current_copy_tree()) (snd copy_place); c_place());;

let save_tree () = discard_tree (tac_subtree current_tac_tree current_place);;

let swap () = let x,y,z = current_place,copy_place in
              if y=0 then (current_place,copy_place := z,y,x; ())
              else (discard_tree current_tac_tree; 
                    current_tac_tree := el (y+1) old_tac_trees; 
                    current_place,copy_place := z,(1,x); ());;

let c_newer() = let x,y = copy_place in if x=0 then failwith`c_newer` else (copy_place:= x-1,[]; c_place())
and c_older() = let x,y = copy_place in if x+1>length old_tac_trees 
                then failwith`c_older` else (copy_place:=x+1,[];c_place());;

let set_goal t = (discard_tree current_tac_tree; current_tac_tree := unexpanded t; current_place := []; ());;

let e = expand
and te = then_expand
and es = expands
and une = unexpand_tac_node_proc
and g t = set_goal ([],t)
and b = backup
and r = rotate
and r_e = read_expand
and r_te = read_then_expand
and r_es = read_expands
and tacs () = print_tree current_tac_tree [] print_tac_goals print_tacs false 1000
and pgoals () = print_tac_tree_goals current_tac_tree current_place
and top_goal() = node_goals (tac_subtree current_tac_tree current_place)
and up n = (current_place := go_up current_tac_tree current_place n; place())
and down n = (current_place := go_down current_tac_tree current_place n; place())
and right n = (current_place := go_right current_tac_tree current_place n; place())
and left n = (current_place := go_left current_tac_tree current_place n; place())
and top() = (current_place := [];place())
and bottom() = (current_place := first_unexpanded current_tac_tree; place())
and c_up n = move_c_place (\x y. go_up x y n)
and c_down n = move_c_place (\x y. go_down x y n)
and c_left n = move_c_place (\x y. go_left x y n)
and c_right n = move_c_place (\x y. go_right x y n)
and c_top () = (copy_place := fst copy_place, []; c_place())
and c_here () = (copy_place := 0,current_place; ())
and tac_tree_thm () = hd (node_thms (tac_subtree current_tac_tree current_place));;


