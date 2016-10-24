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
% CONTENTS: the core functional window inference system                      %
%============================================================================%
%$Id: win.ml,v 3.1 1993/12/07 14:15:19 jg Exp $%

% A window is a tuple with the following components.                        %
%   A theorem which records the progress of the window.                     %
%   A set of theorems, the hyps of which are set of hyptheses which can     %
%       appear in the window's theorem.                                     %
%   A set of theorems relavent to the window.                               %
%   A set of suppositions relavent to the window.                           %
%   A list of variables which are implicitly bound by this window.          %
%       (The closer to the front of the list the tighter the binding.)      %
lettype window = (thm # (thm list) # (thm list) # (goal list) # (term list));;

% Find the theorem being held by a window.                                  %
let win_thm ((th, _, _, _, _):window) = th;;

% Find the relation being preserved by a window.                            %
let relation ((th, _, _, _, _):window) = rator (rator (concl th));;

% Find the focus of a window.                                               %
let focus ((th, _, _, _, _):window) = rand (rator (concl th));;

% Find the original focus of a window.                                      %
let origin ((th, _, _, _, _):window) = rand (concl th);;

% Find the variables bound by a window.                                     %
let bound ((_, _, _, _, bnd):window) = bnd;;

% Find the hypotheses theorems a window.                                    %
let hyp_thms ((_, hyps, _, _, _):window) = hyps;;

% Find the hypotheses of a window.                                          %
let hypotheses ((_, hyps, _, _, _):window) = term_setify (flat (map hyp hyps));;

% Find the displayed hypotheses of a window.                                %
let disp_hypotheses ((_, hyps, _, _, _):window) =
    term_setify (subtract (map concl hyps) [true_tm]);;

% Find the _all_ hypotheses of a window.                                    %
let all_hypotheses w = term_union (hypotheses w) (disp_hypotheses w);;

% Find the hypotheses that have been used in a window.                      %
let used_hypotheses ((th, _, _, _, _):window) = hyp th;;

% Find the relavent theorems of a window.                                   %
let lemma_thms ((_, _, thms, _, _):window) = thms;;

% Find the suppositions of a window.                                        %
let suppositions ((_, _, _, sups, _):window) = sups;;

% Find the conjectures of a window.                                         %
let conjectures win = 
    let hyps = all_hypotheses win in
    let sups = suppositions win in
        term_setify (map snd (filter (\s. term_subset (fst s) hyps) sups));;

% Find the used conjectures of a window.                                    %
let used_conjectures win =
    let used = hyp (win_thm win) in
    let hyps = all_hypotheses win in
    filter (\t. not (term_mem t hyps)) used;;

% Find the lemmas of a window.                                              %
let lemmas win =
    let handcs = term_union (all_hypotheses win) (conjectures win) in
    let thms = lemma_thms win in
        term_setify (map concl (filter (\t. term_subset (hyp t) handcs) thms));;

% The context of a window.                                                  %
let context win =
    term_setify ((all_hypotheses win) @ (lemmas win) @ (conjectures win));;

% Start transforming "foc" to arrive at (hyps |- foc' rel foc).          %
% Call with create_win "rel foc" [hypotheses] [lemma_thms]               %
let make_win relfoc sups bnds hyps thms = 
    let rel = rator relfoc in
    let foc = rand relfoc in
        (
            (reflexive (mk_comb (mk_comb (rel, foc), foc))),
            (thm_setify hyps),
            (thm_setify thms),
            (goal_setify sups),
        bnds
        ):window;;

let create_win relfoc hyps = make_win relfoc [] [] (map ASSUME hyps);;

% Transform a window (as above) with function fn and return the theorem.    %
let transform relfoc hyps thms fn =
    win_thm (fn (create_win relfoc hyps thms));;

% Hand back, if possible, a theorem with conclusion c and hypotheses, a %
%   subset of the current hypotheses and conjectures.                   %
%   (Tries to avoid assumptions which are bound by the window.)         %
%   (The fewer unused conjectures the better)                           %
let get_thm c win = 
    if ((term_mem c (lemmas win)) or (term_mem c (disp_hypotheses win)))
    then
        let okhyps = term_union (used_hypotheses win) (hypotheses win) in
        let handcs = term_union (hypotheses win) (conjectures win) in
        let bnds = bound win in
        let thms = (lemma_thms win) @
                   (hyp_thms win) @
                   (map ASSUME (hypotheses win))
        in
        let potentials =
            filter
                (\th. (aconv (concl th) c) & (term_subset (hyp th) handcs))
                thms
        in
        let better (t1,t2) =
            let nh1 = filter (\h. not (term_mem h okhyps)) (hyp t1) in
            let nh2 = filter (\h. not (term_mem h okhyps)) (hyp t2) in
            let bh1 = filter (\h. not (null (intersect (frees h) bnds))) nh1 in
            let bh2 = filter (\h. not (null (intersect (frees h) bnds))) nh2 in
                if (length bh1) < (length bh2) then
                    true
                else if (length bh1) > (length bh2) then
                    false
                else % (length bh1) = (length bh2) %
                    if (length nh1) < (length nh2) then
                        true
                    else if (length nh1) > (length nh2) then
                        false
                    else % (length nh1) = (length nh2) %
                        if (dest_thm t1) = ([concl t1], concl t1) then
                            true
                        else if (dest_thm t2) = ([concl t2], concl t2) then
                            false
                        else % they are both just assumed. %
                            if (concl t1) = c then
                                true
                            else
                                false
        in
            best better potentials
    else
        ASSUME c;;

% Add a supposition to a window.                                            %
let add_suppose sup win = 
    let thms = lemma_thms win in
    letref sups = suppositions win in
        if  (not (exists (\s.better_goal s sup) sups)) &
            (not (exists (\s.better_goal s sup) (map dest_thm thms))) &
            (not (term_mem (snd sup) (true_tm.(fst sup))))
        then
        (
            letref newsups = goal_setify
            (sup.(sups @ (map dest_thm thms)))
        in
                while (not (goal_set_equal sups newsups)) do
                (
                    sups := newsups;
                    newsups :=
                        goal_setify
                (   sups
                            @   (flat (map (\s. map (prove_hyp s) sups) sups))
                            )
                );
            sups := filter (\s1.not (exists (\s2.better_goal s2 s1)
                                            (map dest_thm thms))) sups;
            (win_thm win, hyp_thms win, thms, sups, bound win)
        )
        else
            win;;

% Add a conjecture to the current window.                                   %
let conjecture tm win =
    add_suppose (hypotheses win, tm) win;;

% Add a theorem to a window's relavent theorems set.                    %
let add_theorem th win = 
    letref thms = lemma_thms win in
        if  (not (exists (\t.better_thm t th) (lemma_thms win))) &
            (not (term_mem (concl th) (true_tm.(hyp th))))
        then
        (
        let hypthms = subtract (hyp_thms win) thms in
            letref newthms = (thm_setify (th.(thms @ hypthms))) in
            letref sups = suppositions win in
            let hyps = hyp_thms win in
                while (not (thm_set_equal thms newthms)) do
                (
                    thms := newthms;
                    newthms :=
                        thm_setify
                            (   thms
                            @   (flat (map (\t. map (PROVE_HYP t) thms) thms))
                            )
                );
        thms := subtract thms hypthms;
                sups := filter (\s1. not (exists (\s2.better_goal s2 s1)
                                                 (map dest_thm thms))) sups;
                let newwin = (win_thm win, hyps, thms, sups, bound win) in
                letref win_th = win_thm newwin in
                letref kills = term_intersect (lemmas newwin)
                                              (used_conjectures newwin)
        in
                    while (not (null kills)) do
                    (
                        win_th := PROVE_HYP (get_thm (hd kills) newwin) win_th;
                        kills := tl kills
                    );
                    (win_th, hyps, thms, sups, bound win)
        )
        else
            win;;

% If the current focus is f and relation is s and the transformation    %
%   tr = (h |- g s f) where h is a subset of the current hyps and conjs %
%   and s is stronger than r then we transform the focus to g.          %
let transform_win tr win =
    let (th, hyps, thms, sups, bnds) = win in 
    letref ctr = tr in
    letref kills = term_intersect (hyp ctr)
                      ((lemmas win) @ (disp_hypotheses win))
    in
            while (not (null kills)) do
            (
                ctr := PROVE_HYP (get_thm (hd kills) win) ctr;
                kills := tl kills
            );
        if (not (term_subset (hyp ctr)
                 (term_union (hypotheses win) (conjectures win))))
            then
            failwith `Transformation has bad hypothese.`
        else
        (
            let r = rator (rator (concl th)) in
            let newth = transitive (CONJ (weaken r ctr) th) in
                (newth, hyps, thms, sups, bnds)
        );;

% If the current focus is f and relation is s and the transformation    %
% tr = (h |- !x1...xn. g' s f') where h is a subset of the current      %
% and s is stronger than r and f' can be matched to f after x1...xn     %
% have been specialised, then we transformt the focus to g              %
% (that is g' with the same instantiations applied to it).              %
let match_transform_win tr win =
    transform_win (PART_MATCH rand tr (focus win)) win;;

% Apply the conversion to the focus.                                        %
let convert_win (c : conv) win =
    transform_win (SYM (c (focus win))) win;;

% Apply an inference rule(thm -> thm) to the current focus.                 %
% Only works if the relation is "<==" or weaker.                            %
let rule_win inf win = 
    let f = focus win in
        (transform_win (IMP_PMI (DISCH f (inf (ASSUME f)))) win) 
        ? failwith `rule_win: only preserves <==`;;

% Apply an inference rule to the theorem of a window.                       %
let thm_rule_win inf (win : window) =
    let (res, hyps, thms, sups, bnds) = win in
    let rel = rator (rator (concl res)) in
    let res' = inf res in
    let rel' = rator (rator (concl res')) in
    let orig = rand (concl res) in
    let orig' = rand (concl res') in
    let used' = hyp res' in
        if (orig' = orig)
         & (mem rel (relative_strengths rel'))
         & (term_subset used' (term_union (hypotheses win) (conjectures win)))
        then
            (weaken rel res', hyps, thms, sups, bnds)
        else
            failwith `thm_rule_win`;;

% Apply an inference rule to the focus of a window.                         %
% Rule must take the focus f and return the theorem |- f' r f.              %
let foc_rule_win inf (win : window) =
    (transform_win (inf (focus win)) win)
    ? failwith `foc_rule_win`;;

% Apply a tactic to the current focus.                                      %
% Only works if the tactic results in just 1 subgoal.                       %
% Only works if the relation is "==>".                                      %
% Only works sometimes.                                                     %
let tactic_win (tac:tactic) win =
    (
        let ([(new_hyps, newfoc)], proof) = tac ((hypotheses win), (focus win))
        in
            transform_win (DISCH newfoc (proof [ASSUME newfoc])) win
    ) ? failwith `tactic_win` ;;


% Functions for rewriting the window.                                      %
let gen_rewrite_win rewrite_fun built_in_rewrites =
    let REWL_CONV = GEN_REWRITE_CONV rewrite_fun built_in_rewrites in
        convert_win o REWL_CONV ;;

% Basic rewriting functions.                                                %
let pure_rewrite_win = gen_rewrite_win TOP_DEPTH_CONV []
and rewrite_win = gen_rewrite_win TOP_DEPTH_CONV basic_rewrites
and pure_once_rewrite_win = gen_rewrite_win ONCE_DEPTH_CONV []
and once_rewrite_win = gen_rewrite_win ONCE_DEPTH_CONV basic_rewrites;;

% Assumption rewrite variants.                                              %
let pure_asm_rewrite_win thl win =
    pure_rewrite_win ((map ASSUME (context win)) @ thl) win
and asm_rewrite_win thl win =
    rewrite_win ((map ASSUME (context win)) @ thl) win
and pure_once_asm_rewrite_win thl win =
    pure_once_rewrite_win ((map ASSUME (context win)) @ thl) win
and once_asm_rewrite_win thl win =
    once_rewrite_win ((map ASSUME (context win)) @ thl) win ;;

% Filtered assumption rewriting.                                            %
let filter_pure_asm_rewrite_win f thl win =
    pure_rewrite_win ((map ASSUME (filter f (context win))) @ thl) win
and filter_asm_rewrite_win f thl win =
    rewrite_win ((map ASSUME (filter f (context win))) @ thl) win
and filter_pure_once_asm_rewrite_win f thl win =
    pure_once_rewrite_win ((map ASSUME (filter f (context win))) @ thl) win
and filter_once_asm_rewrite_win f thl win =
    once_rewrite_win ((map ASSUME (filter f (context win))) @ thl) win;;

% Transfer the supposition and theorem sets from one window to another.    %
let transfer_sups_thms ((_, _, thms1, sups1, bnd1):window)
                       ((res2, hyps2, _, _, _):window) =
    (res2, hyps2, thms1, sups1, bnd1);;

% Open a new window at the subterm pointed to by p.                        %
% Finds the _best_ list of window rules to use in order to follow the path %
% p starting from a window with focus f hypothese hyps and which preserves %
% relation rel.                                                            %
% One list of rules is _better_ than another if.                           %
% 1. The relationship being preserved in the child window is weaker.       %
% 2. There are more hypotheses available in the child window.              %
% 3. The rules used from the start were more _specific_ to this case.      %
%    A rule is more _specific_ than another if.                            %
%    1. It follows a longer path.                                          %
%    2. It preserves a weaker relationship in the parent.                  %
%    3. It preserves a weaker relationship in the child.                   %
% 4. The rules used from the start were more recently added to the         %
%    database.                                                             %
let open_win_basis (FOCUS_PATH p) w = 
    let path_of (p,_,_) = flat (map (\(l,_,_,_,_).l) p) in
    let shorter (r1, r2) = prefix (path_of r1) (path_of r2) in
    let break ths = 
        let (oldths, newths) = partition (\t. hyp t = [concl t]) ths in
        let adds = subtract (map concl newths) [true_tm] in
        let gots = adds @ (map concl oldths) in
        let hyps = filter
                    (\t. not (exists (\u. aconv t u) gots))
                    (flat (map hyp newths)) in
            oldths @ (map ASSUME (adds @ hyps))
    in
    letrec all_steps pth root rls cnt =     
        if null rls then
            []
        else
            let (psl, pwin, close) = root in
            let pfoc = focus pwin in
            let prel = relation pwin in
            let phyps = hyp_thms pwin in
            let plems = lemma_thms pwin in
            let psups = suppositions pwin in
            let pbnds = bound pwin in
            let (rpt, rapp, rcrel, rprel, rhyps, rbnds, rinf).trls = rls in
               if (rapp pfoc)
               & (mem (rprel pfoc prel) (relative_strengths prel))
               then
                   let cfoc = traverse rpt pfoc in
                   let crel = rcrel pfoc prel in 
                   let chyps = thm_setify (rhyps pfoc (break phyps)) in
                   let clems = plems in
                   let csups = psups in
                   let cbnds = pbnds @ (rbnds pfoc) in
                       (    psl@[(rpt, (rprel pfoc prel), crel, chyps, cnt)],
                            (make_win
                                (mk_comb (crel, cfoc)) csups cbnds chyps clems),
                            (\cwin.
                                close
                                    (transform_win
                                        (rinf pfoc (win_thm cwin))
                                        (transfer_sups_thms cwin pwin)))
                        ).(all_steps pth root trls (cnt + 1))
               else
                   all_steps pth root trls (cnt + 1)
    in
    letrec better_rules rl1 rl2 =
        if (null rl1) & (null rl2) then
            false 
        else
            let ((p1,rp1,rc1,h1,c1).t1) = rl1 in
            let ((p2,rp2,rc2,h2,c2).t2) = rl2 in
            if (length p1) > (length p2) then
                true
            else if (length p2) > (length p1) then
                false
            else % (length p1) = (length p2) %
                if mem rp2 (tl (relative_strengths rp1)) then
                    true
                else if mem rp1 (tl (relative_strengths rp2)) then
                    false
                else % the relations are equal or uncomparable %
                    if mem rc2 (tl (relative_strengths rc1)) then
                        true
                    else if mem rc1 (tl (relative_strengths rc2)) then
                        false
                    else % the relations are equal or uncomparable %
                        if (length h1) > (length h2) then
                            true
                        else if (length h2) > (length h1) then
                            false
                        else % (length h1) = (length h2) %
                        if c2 > c1 then
                            true
                        else if c1 > c2 then
                            false
                        else % c1 = c2 %
                            better_rules t1 t2
    in
    let better_route r1 r2 =
        let (psl1, w1, _) = r1 in
        let (psl2, w2, _) = r2 in
        let rel1  = relation w1 in
        let rel2  = relation w2 in
        let hyps1 = hypotheses w1 in
        let hyps2 = hypotheses w2 in
            if mem rel2 (tl (relative_strengths rel1)) then
                r1
            else if mem rel1 (tl (relative_strengths rel2)) then
                r2
            else % the relations are equal or uncomparable %
                if (length hyps1) > (length hyps2) then 
                    r1
                else if (length hyps2) > (length hyps1) then
                   r2
                else % (length hyps1) = (length hyps2) %
                    if better_rules psl1 psl2 then
                        r1
                    else
                        r2
        in
    letrec crush_routes =
        fun [rt]            .   [rt]
         |  (r1.r2.trts)    .
                if (path_of r1) = (path_of r2) then
                    crush_routes ((better_route r1 r2).trts)
                else
                    r1.(crush_routes (r2.trts))
    in
    let rel = relation w in
    let hyps = hyp_thms w in
    letref routes =
         [([(([] : path), rel, rel, hyps, 0)], w, (I:window->window))]
    in
    while not (path_of (hd routes) = p) do
    (
        let (hrts.trts) = routes in
        let rempth = (after (path_of hrts) p) in
        let steps = sort shorter
             (all_steps
                rempth hrts (search_rule rempth) 1)
        in
            if (null steps) then failwith `No applicable window rule!`;
            routes := merge shorter trts steps;
            routes := crush_routes routes
    );
    let ((_, subwin, closefn)._) = routes in
        (subwin, (C (K closefn)):(window -> window -> window));;

% Open a window on a selected lemma or hypothesis.                          %
let open_context_basis (CONTEXT_PATH (tm, p)) win = 
    if (term_mem tm (context win))
    then
    (
        let subwin1 =
            make_win
                (mk_comb (pmi_tm, tm))
                (suppositions win)
                []
                (hyp_thms win)
                (lemma_thms win)
        in
        let closefn1 w = (add_theorem (UNDISCH (PMI_IMP (win_thm w)))) o 
                 (transfer_sups_thms w)
        in
        let (subwin2, closefn2) = open_win_basis (FOCUS_PATH p) subwin1 in
        let closefn w = closefn1 (closefn2 w subwin1) in
            (subwin2, closefn)
    )
    else
        failwith `There is no such term in the context.`;;

% Open a window on either the focus or the context.                         %
let gen_open_basis =
    fun (FOCUS_PATH p)          .   open_win_basis (FOCUS_PATH p)
     |  (CONTEXT_PATH (tm,p))   .   open_context_basis (CONTEXT_PATH (tm,p));;

% Postulate a lemma, or prove a conjecture.                                 %
let establish_basis (CONTEXT_PATH (tm,[])) win = 
    let (bad_sups,good_sups) = partition (\(_,c). c = tm) (suppositions win) in
    let subwin =
        make_win
            (mk_comb (imp_tm, tm))
	    good_sups
	    []
	    (hyp_thms win)
            (lemma_thms win)
    and closefn w = if (focus w) = true_tm then
			(itlist add_suppose bad_sups) o
                        (add_theorem (MP (win_thm w) TRUTH)) o
                        (transfer_sups_thms w)
                    else
                        failwith `This lemma is not proved yet!`
    in
        (subwin, closefn);;

let open_win p subwinfn win = 
    let (subwin, closefn) = open_win_basis (FOCUS_PATH p) win in
        closefn (subwinfn subwin) win;;

let open_context tm p subwinfn win = 
    let (subwin, closefn) = open_context_basis (CONTEXT_PATH (tm,p)) win in
        closefn (subwinfn subwin) win;;

let gen_open_win wp subwinfn win = 
    let (subwin, closefn) = gen_open_basis wp win in
        closefn (subwinfn subwin) win;;

let establish tm subwinfn win = 
    let (subwin, closefn) = establish_basis (CONTEXT_PATH (tm,[])) win in
        closefn (subwinfn subwin) win;;
