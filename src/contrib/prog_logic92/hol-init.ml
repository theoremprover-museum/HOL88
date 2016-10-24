loadf `Library/half`;;
loadf `Library/imp`;;
loadf `Library/rew_2.0`;;

%----------------------------------------------------------------------------%
% Old MATCH_MP reinstated: "new_exseq" relies on variable capture            %
%  [JRH 92.11.30]                                                            %
%----------------------------------------------------------------------------%

let MATCH_MP impth =
    let hy,(vs,imp) = (I # strip_forall) (dest_thm impth) in
    let pat = fst(dest_imp imp)
                ? failwith `MATCH_MP: not an implication` in
    let fvs = subtract (frees (fst(dest_imp imp))) (freesl hy) in
    let gth = GSPEC (GENL fvs (SPECL vs impth)) in
    let matchfn = match (fst(dest_imp(concl gth))) in
        \th. (MP (INST_TY_TERM (matchfn (concl th)) gth) th) ?
             failwith `MATCH_MP: does not match`;;
