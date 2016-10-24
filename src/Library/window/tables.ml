% --------------------------------------------------------------------- %
%       Copyright (c) Jim Grundy 1992                                   %
%       All rights reserved                                             %
%                                                                       %
% Jim Grundy, hereafter referred to as `the Author', retains the        %
% copyright and all other legal rights to the Software contained in     %
% this file, hereafter referred to as `the Software'.                   %
%                                                                       %
% The Software is made available free of charge on an `as is' basis.    %
% No guarantee, either express or implied, of maintenance, reliability, %
% merchantability or suitability for any purpose is made by the Author. %
%                                                                       %
% The user is granted the right to make personal or internal use        %
% of the Software provided that both:                                   %
% 1. The Software is not used for commercial gain.                      %
% 2. The user shall not hold the Author liable for any consequences     %
%    arising from use of the Software.                                  %
%                                                                       %
% The user is granted the right to further distribute the Software      %
% provided that both:                                                   %
% 1. The Software and this statement of rights is not modified.         %
% 2. The Software does not form part or the whole of a system           %
%    distributed for commercial gain.                                   %
%                                                                       %
% The user is granted the right to modify the Software for personal or  %
% internal use provided that all of the following conditions are        %
% observed:                                                             %
% 1. The user does not distribute the modified software.                %
% 2. The modified software is not used for commercial gain.             %
% 3. The Author retains all rights to the modified software.            %
%                                                                       %
% Anyone seeking a licence to use this software for commercial purposes %
% is invited to contact the Author.                                     %
% --------------------------------------------------------------------- %
%============================================================================%
% CONTENTS: reflexivity, transitivity, strengh and window rules tables.      %
%============================================================================%
%$Id: tables.ml,v 3.1 1993/12/07 14:15:19 jg Exp $%

begin_section relation_sec;;

    % Simple matching mp.                                               %
    let FAST_MATCH_MP th1 th2 =
	let matcher = match (fst (dest_imp (concl th1))) (concl th2) in
	    MP (INST_TY_TERM matcher th1) th2;;

    % Create and maintain a function called reflexive, shown below:         %
    %                                                                       %
    % ------- reflexive "t R t"                                             %
    %  t R t                                                                %
    letref refl_ptr = \tm:term.(failwith `reflexive`):thm;;

    let add_refl th = 
        let old_refl = refl_ptr in
            do
            (
                refl_ptr := \tm:term. (PART_MATCH I th tm) ? (old_refl tm)
            );;

    let reflexive tm = refl_ptr tm;;

    % Create and maintain a function called transitve, shown below:         %
    %  (H |- t R u /\ u R v)                                                %
    % ---------------------------- transitive                               %
    %       H |- t R v                                                      %
    letref trans_ptr = \t1t2:thm.(failwith `transitive`):thm;;

    let add_trans th =
	let old_trans = trans_ptr in
	let gth = GSPEC th in
	    do
	    (
		trans_ptr :=
		    \t1t2. (FAST_MATCH_MP gth t1t2) ? (old_trans t1t2)
	    );;

    let transitive tm = trans_ptr tm;;

    % known_relation rel is true iff the details of the relation rel have   %
    %   been added to the system with add_relation.                         %
    let known_relation rel =
        (let gv = genvar (dom rel) in
            can reflexive (mk_comb (mk_comb (rel, gv), gv))
        ) ? failwith `know_relation`;;

    % A list of theorems stating which relations are stonger than which.    %
    letref weakenings = [] : thm list;;

    % A table which stores for each relation the list of relations that     %
    %   are stonger than it.   This information can be infered from the     %
    %   weakenings table and is only duplicated here to increase            %
    %   performance.                                                        %
    letref weak_table = [] : (term # (term list)) list;;

    % check_weak_thm takes a theorem of the following form:                 %
    %   |- !x y. (x S y) ==> (x R y)                                        %
    % and returns the pair (S,R)                                            %
    % If the theorem it is given is not of the correct form, then it fails. %
    let check_weak_thm all_x_y_Sxy_imp_Rxy_th = 
        let ([],all_x_y_Sxy_imp_Rxy) = dest_thm all_x_y_Sxy_imp_Rxy_th in
        let ([x;y],Sxy_imp_Rxy) = strip_forall all_x_y_Sxy_imp_Rxy in
        let (Sxy,Rxy) = dest_imp Sxy_imp_Rxy in
        let (Sx,_) = dest_comb Sxy in
        let (S,_) = dest_comb Sx in
        let (Rx,_) = dest_comb Rxy in
        let (R,_) = dest_comb Rx in
            if all_x_y_Sxy_imp_Rxy =
                (
                    list_mk_forall 
                    (
                        [x;y]
                    ,
                        mk_imp
                        (
                            mk_comb(mk_comb(S,x),y)
                        ,
                            mk_comb(mk_comb(R,x),y)
                        )
                    )
                )
            then
                (S,R)
            else
                fail;;

    % MATCH_IMP_TRANS takes two thorems of the form                         %
    %   (|- A ==> B) and  (|- Y ==> Z).                                     %
    % It matches B to Y or Y to B and returns                               %
    % (|- (match A) ==> (match Z)                                           %
    let MATCH_IMP_TRANS th1 th2 =
        (IMP_TRANS
            (INST_TY_TERM
                (match
                    (snd (dest_imp (concl th1)))
                    (fst (dest_imp (concl th2)))
                )
                th1
            )
            th2
        ) ?
        (IMP_TRANS
            th1
            (INST_TY_TERM
                (match
                    (fst (dest_imp (concl th2)))
                    (snd (dest_imp (concl th1)))
                )
                th2
            )
        ) ? failwith `MATCH_IMP_TRANS` ;;

    % stronger r1 r2 is true if the relation r1 is recorded as being        %
    %   stronger than relation r2.                                          %
    let stronger (r1,r2) = 
        (let x = genvar (dom r1) in
         let y = genvar (dom r2) in
         let con =
            mk_imp (mk_comb(mk_comb(r1,x),y), mk_comb(mk_comb(r2,x),y))
         in
            exists (\th. can (uncurry match) ((concl th), con)) weakenings
        ) ? false;;

    % weaker r1 r2 is true if the relation r1 is recorded as being          %
    %   weaker than relation r2.                                            %
    let weaker (r1,r2) = 
        (let x = genvar (dom r1) in
         let y = genvar (dom r2) in
         let con =
            mk_imp (mk_comb(mk_comb(r2,x),y), mk_comb(mk_comb(r1,x),y))
         in
            exists (\th. can (uncurry match) ((concl th), con)) weakenings
        ) ? false;;

    % match_type matches up the types of its two parameters.                %
    let match_type tm1 tm2 =
        let v1 = mk_var(`v`, type_of tm1)
        and v2 = mk_var(`v`, type_of tm2)
        in
            snd (match v1 v2);;

    % rel_str rel gives a list of relations stronger than rel,              %
    %   in order of increasing strength.                                    %
    % This verion only works for the functions actually stored,             %
    %   like it might know that "=:*->*->bool" is stronger than itsself     %
    %   if that is stored (which it will be), but it wont be able to        %
    %   infer the "=:num->num->bool" is stronger than itsself.              %
    let rel_str r =
        let srs = map (\th. (rator (rator (rand (rator (concl th))))))
                      weakenings
        in
        let msrs = mapfilter (\s. inst [] (match_type s r) s) srs in
            sort weaker (term_setify (filter (\s. stronger (s,r)) msrs));;

    % Add a theorem that asserts one relation is stronger than another to   %
    %   the data base of information about relations.                       %
    let add_weak =
        letrec crush =  fun []  .   []
                         |  (h.t). 
                            if exists (\th. can (uncurry match)
                                                ((concl th), (concl h)))
                                      t
                            then
                                (crush t)
                            else
                                h.(crush t) in
        \wth.
            let (s,r) = check_weak_thm wth ?
                failwith `add_weak: theorem not of required form.`
            in
            let wthm = GSPEC wth in
            if exists (\t. can (uncurry match) ((concl t), (concl wthm)))
                      weakenings
            then
                failwith `No duplicate entries.`
            else if
                exists
                    (\t. can
                        (uncurry match)
                            (((mk_imp o (\(a,b).(b,a)) o dest_imp o concl) t),
                             (concl wthm)))
                    weakenings
            then
                failwith `No cycles in the graph of relative strengths.`
            else
                ((assert known_relation s) ?
                    failwith `add_weak: first relation is unknown.`);
                ((assert known_relation r) ?
                    failwith `add_weak: second relation is unknown.`);

                % Try to resove all the theorems we have against eachother  %
                %   to come up with some new ones.                          %
                letref newweaks = (crush (wthm.weakenings)) in
                    while (not (set_equal weakenings newweaks))
                    do
                    (
                        weakenings := newweaks;
                        newweaks :=
                            crush
                                (   weakenings
                                @   (flat (map (\t. mapfilter
                                                        (MATCH_IMP_TRANS t)
                                                        weakenings)
                                          weakenings))
                                )
                    );
                    let wrs =
                        term_setify
                            (map (\th. (rator (rator (rand (concl th)))))
                                 weakenings)
                    in 
                        do (weak_table := combine (wrs, map rel_str wrs));;

    %  (H |- t R s)                                                         %
    % -------------- weaken "Q"                                             %
    %  (H |- t Q s)                                                         %
    letrec weaken (Q : term) (th : thm) =
        let R = rator (rator (concl th)) in
            if Q = R then
                % The last clause will handle this case, but it is faster   %
                %   not to do any searching.                                %
                th
            else
                tryfind
                    (\t. 
                        let th1 = FAST_MATCH_MP t th in
                        let R = rator (rator (concl th1)) in
                            INST_TY_TERM (match R Q) th1
                    )
                    weakenings;;

    % Given a relation r, (relative_strengths r) returns a list of relation %
    %   which are stronger than r (including r itself) in order of          %
    %   increasing strength.                                                %
    let relative_strengths r =
        let (s,sl) = find (\(s,sl). can (uncurry match) (s, r)) weak_table in
        let mtch = snd (match s r) in
            map (inst [] mtch) sl;;

    let add_relation = 
        let check_refl_thm rth =
            (let rtm = concl rth in
            let (rx,rb) = dest_forall rtm in
            let rf = rator (rator rb) in
                if rtm = "!^rx. ^rf ^rx ^rx" then
                    rf
                else
                    fail
            ) ? failwith `reflexive theorem is not of the form:\L`^
                    `(|- !x. x R x).`
        and check_trans_thm tth =
            (let ttm =  concl tth in
             let ([tx;ty;tz],tb) = strip_forall ttm in
             let tf = rator (rator (rand tb)) in
                if ttm =
            "!^tx ^ty ^tz. ((^tf ^tx ^ty) /\ (^tf ^ty ^tz)) ==> (^tf ^tx ^tz)"
                then
                    tf
                else
                    fail
            ) ? failwith `transitive theorem is not of the form:\L`^
                    `(|- !x y z. ((x R y) /\ (y R Z)) ==> (x R z)).`
        in
            \(refl_thm,trans_thm). 
                let rf = check_refl_thm refl_thm
                and tf = check_trans_thm trans_thm
                in
                    if not ((is_const rf) & (is_const tf)) then
                        failwith `The relation being added\L`^
                            `must be defined as a constant.`
                else if not (rf = tf) then
                    failwith `The reflexive and transitive theorems\L`^
                        `must describe the same relation.`
                else
                    (
                        add_refl refl_thm;
                        add_trans trans_thm;
                        let x = mk_var(`x`,dom rf)
                        and y = mk_var(`y`,dom rf)
                        in
                            (add_weak (GENL [x;y] (IMP_REFL "^rf ^x ^y")))
                                ?? [`No duplicate entries.`] ();
                            let th = 
                                prove
                                (
                                    "!^x ^y. (^x = ^y) ==> (^rf ^x ^y)"
                                ,
                                    GEN_TAC THEN
                                    GEN_TAC THEN
                                    DISCH_TAC THEN
                                    (ONCE_ASM_REWRITE_TAC []) THEN
                                    (MATCH_ACCEPT_TAC refl_thm)
                                )
                            in
                                (add_weak th) ?? [`No duplicate entries.`] ()
                    ) ;;

    add_relation (EQ_REFL, EQ_TRANS);;
    add_relation (IMP_REFL_THM, IMP_TRANS_THM);;
    add_relation (PMI_REFL_THM, PMI_TRANS_THM);;

    (
        add_relation,
        reflexive,
        transitive,
        add_weak,
        weaken,
        relative_strengths
    );;
end_section relation_sec;;
let (
        add_relation,
        reflexive,
        transitive,
        add_weak,
        weaken,
        relative_strengths
    ) = it ;;

% A path is a list made up of RATOR, RAND AND BODY.                         %
% Paths are used to denote a particular subterm within a term.              %
type path_elt = RATOR | RAND | BODY;;

lettype path = path_elt list;;

% The function traverse takes a path and returns a function from            %
%   a term to the selected subterm.                                         %
let traverse =
    let translate =
        fun RATOR   .   rator
         |  RAND    .   rand
         |  BODY    .   body
    in
        \p. rev_itlist (curry $o) (map translate p) I;;

% A win_path denotes a path to a term within a window.                      %
% The term is either a subterm of the focus or of an element of the context.%
type win_path = FOCUS_PATH of path | CONTEXT_PATH of (term # path);;

% A window rule is composed of the following components:                    %
%   A path which describes the subterm which is to be the focus of the      %
%       child window as a funtion of the focus of the parent.               %
%   Funtions from the focus of the parent window to the following:          %
%       A boolean indicating whether this rule is valid for use on the      %
%           focus.                                                          %
%       Functions from the relation the user wishes to preserve in the      %
%           parent window to:                                               %
%           A term which is the relationship which will be preserved in the %
%               child window.                                               %
%           A term which is the relationship which will be preserved in the %
%               parent window.                                              %
%       A function from the hypotheses in the parent window to the          %
%           hypotheses in the child.                                        %
%   A list of terms which are the variables free in the child window        %
%       which are bound in the parent.                                      %
%       A function from the theorem generated by the child window to one    %
%           relavent to the parent.                                         %
lettype window_rule =   (   path
                        #   (term -> bool)
                        #   (term -> term -> term)
                        #   (term -> term -> term)
                        #   (term -> (thm list) -> (thm list))
                        #   (term -> (term list))
                        #   (term -> (thm -> thm))
                        );;

% Create and maintain a table of rules for opening at various positions     %
%   in a term.                                                              %
% The rules are stored in tree of assignable variables which is keyed       %
%   off the path.                                                           %

type (*,**) tree =
    TREE of
    (
        (((* list) # **) -> void)
    #
        ((* list) -> (((* list) # **) list))
    #
        (void -> void)
    );;

begin_section treesec;;

    let plant (TREE(plnt,_,_)) = plnt
    and harvest (TREE(_,hrvst,_)) = hrvst
    and purge (TREE(_,_,prg)) = prg;;

    letrec newtree (():void) =
        letref value = [] : (   (term -> bool)
                            #   (term -> term -> term)
                            #   (term -> term -> term)
                            #   (term -> (thm list) -> (thm list))
                            #   (term -> (term list))
                            #   (term -> (thm -> thm))
                            ) list
        and children = [] : (   path_elt
                            #   (
                                    (   path_elt
                                    ,   (   (term -> bool)
                                        #   (term -> term -> term)
                                        #   (term -> term -> term)
                                        #   (term -> (thm list) -> (thm list))
                                        #   (term -> (term list))
                                        #   (term -> (thm -> thm))
                                        )
                                    ) tree
                                )
                            ) list
        in
            TREE
            (
                (\(trail, element).
                    if trail = [] then
                        do (value := element.value)
                    else
                        let (hd_trail.tl_trail) = trail in
                        let chosen_child =
                            (snd (assoc hd_trail children)) ?
                            (let new_child = newtree () in
                                    children := (hd_trail,new_child).children;
                                    new_child)
                        in
                            plant chosen_child (tl_trail,element))
            ,
                (\trail.
                    if trail = [] then
                        map (\v. ([],v)) value
                    else
                        let (hd_trail.tl_trail) = trail in
                        let sub_tree_values =
                            (map
                                (\(t,v). ((hd_trail.t),v))
                                (harvest
                                    (snd (assoc hd_trail children))
                                    tl_trail)) ?
                            []
                        in
                            if null sub_tree_values then
                                map (\v. ([],v)) value
                            else
                                append (map (\v. ([],v)) value) sub_tree_values)
            ,
                (\(():void). do(value := []; children := []))
            );;

    let rule_tree = newtree ();;

    let store_rule = plant rule_tree
    and search_rule = harvest rule_tree
    and empty_rules = purge rule_tree;;

    (store_rule, search_rule, empty_rules);;

end_section treesec;;
    
let (store_rule, search_rule, empty_rules) = it;;
