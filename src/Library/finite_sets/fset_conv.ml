% ===================================================================== %
% FILE		: fset_conv.ml						%
% DESCRIPTION   : Conversions for taking unions and intersections of 	%
%		  finite sets, for deciding membership of finite sets,  %
%		  and so on.						%
%								        %
% AUTHOR        : T Melham						%
% DATE		: 92.02.15						%
% ===================================================================== %

% ===================================================================== %
% IN_CONV: decide membership for finite sets.				%
%									%
% A call to:								%
%									%
%	IN_CONV conv "x IN {x1,...,xn}"					%
%									%
% returns:								%
%									%
%	|- x IN {x1,...,xn} = T						%
%									%
% if x is syntactically identical to xi for some i, where 1<=i<=n, or	%
% if conv proves |- (x=xi)=T for some i, where 1<=i<=n; or it returns:	%
%									%
%	|- x IN {x1,...,xn} = F						%
%									%
% if conv proves |- (x=xi)=F for all 1<=i<=n.				%
% ===================================================================== %

let IN_CONV = 
    let check st = assert (\c. fst(dest_const c) = st) in
    let inI = theorem `finite_sets` `IN_INSERT` in
    let inE = GEN "x:*" (EQF_INTRO (SPEC "x:*" th)) where
	      th = theorem `finite_sets` `NOT_IN_EMPTY` in
    let T = "T" and F = "F" and gv = genvar ":bool" in
    let DISJ = AP_TERM "\/:bool->bool->bool" in
    let F_OR = el 3 (CONJUNCTS (SPEC gv OR_CLAUSES)) in
    let OR_T = el 2 (CONJUNCTS (SPEC gv OR_CLAUSES)) in
    letrec in_conv conv (eth,ith) x S = 
       (let (_,[y;S']) = (check `INSERT` # I) (strip_comb S) in
        let thm = SPEC S' (SPEC y ith) in
        let rectm = rand(rand(concl thm)) in
        if (aconv x y) then 
           EQT_INTRO (EQ_MP (SYM thm) (DISJ1 (ALPHA x y) rectm)) else
        (let eql = conv (mk_eq (x, y)) in
         let res = rand(concl eql) in
         if (res=T) then
            EQT_INTRO (EQ_MP (SYM thm) (DISJ1 (EQT_ELIM eql) rectm)) else
         if (res=F) then
            let rthm = in_conv conv (eth,ith) x S' in
            let thm2 = MK_COMB (DISJ eql,rthm) in
	    let thm3 = INST [rand(concl rthm),gv] F_OR in
                TRANS thm (TRANS thm2 thm3) else fail) ? 
         let rthm = in_conv conv (eth,ith) x S' in
	 if (rand(concl rthm)=T) then
	    let eqn = mk_eq(x,y) in
	    let thm2 = MK_COMB(DISJ (REFL eqn), rthm) in
	    let thm3 = TRANS thm2 (INST [eqn,gv] OR_T) in
	        TRANS thm thm3 else fail) ? 
       (let e = check `EMPTY` S in eth) in
    \conv tm. 
       (let (_,[x;S]) = (check `IN` # I) (strip_comb tm) in
        let ith = ISPEC x inI and eth = ISPEC x inE in
            in_conv conv (eth,ith) x S) ? failwith `IN_CONV`;;

% ===================================================================== %
% DELETE_CONV: delete an element from a finite set.			%
%									%
% A call to:								%
%									%
%	DELETE_CONV conv "{x1,...,xn} DELETE x"				%
%									%
% returns:								%
%									%
%	|-{x1,...,xn} DELETE x = {xi,...,xk}				%
%									%
% where for all xj in {xi,...,xk}, either conv proves |- xj=x or xj is  %
% syntactically identical to x and for all xj in {x1,...,xn} and NOT in %
% {xi,...,xj}, conv proves |- (xj=x)=F.					%
% ===================================================================== %

let DELETE_CONV = 
    let check st = assert (\c. fst(dest_const c) = st) in
    let bv = genvar ":bool" in
    let Edel = theorem `finite_sets` `EMPTY_DELETE` in
    let Dins = GENL ["y:*";"x:*"] (SPECL ["x:*";"y:*"] th) where 
      	       th = theorem `finite_sets` `DELETE_INSERT` in
    letrec del_conv conv (eth,ith) x S = 
       (let (_,[y;S']) = (check `INSERT` # I) (strip_comb S) in
        let thm = SPEC S' (SPEC y ith) in
        let eql = (aconv x y) => EQT_INTRO (ALPHA y x) | conv (mk_eq(y,x)) in
        let rthm = del_conv conv (eth,ith) x S' in
        let v = genvar (type_of S) in
        let pat = mk_eq(lhs(concl thm),mk_cond(bv,v,mk_comb(rator S,v))) in
	let thm2 = SUBST [rthm,v;eql,bv] pat thm in
	    TRANS thm2 (COND_CONV (rand(concl thm2)))) ? 
       (let e = check `EMPTY` S in eth) in
    \conv tm. 
       (let (_,[S;x]) = (check `DELETE` # I) (strip_comb tm) in
        let ith = ISPEC x Dins and eth = ISPEC x Edel in
            del_conv conv (eth,ith) x S) ? failwith `DELETE_CONV`;;


% ===================================================================== %
% UNION_CONV: compute the union of two sets.				%
%									%
% A call to:								%
%									%
%	UNION_CONV conv "{x1,...,xn} UNION S"				%
%									%
% returns:								%
%									%
%	|-{x1,...,xn} UNION S = xi INSERT ... (xk INSERT S)		%
%									%
% where for all xj in {x1,...,xn} but NOT in {xi,...,xk}, IN_CONV conv  %
% proves that |- xj IN S = T						%
% ===================================================================== %

let UNION_CONV = 
    let InU  = theorem `finite_sets` `INSERT_UNION` in
    let InUE = theorem `finite_sets` `INSERT_UNION_EQ` in
    let Eu  = CONJUNCT1 (theorem `finite_sets` `UNION_EMPTY`) in
    let check st = assert (\c. fst(dest_const c) = st) in 
    letrec strip_set tm = 
        (let [h;t] = snd ((check `INSERT` # I) (strip_comb tm)) in 
	     (h .(strip_set t))) ?
        (fst(dest_const tm) = `EMPTY` => [] | fail) in
    let mkIN = 
        let boolty = ":bool" in 
        \x s. let ty = type_of x in let sty = mk_type(`set`,[ty]) in
              let INty = mk_type(`fun`,[ty;mk_type(`fun`,[sty;boolty])]) in
	          mk_comb(mk_comb(mk_const(`IN`,INty),x),s) in
    let bv = genvar ":bool" in
    let itfn conv (ith,iith) x th = 
        let _,[S;T] = strip_comb(lhs(concl th)) in
        (let eql = IN_CONV conv (mkIN x T) in
         let thm = SPEC T (SPEC S (SPEC x ith)) in
	 let l,ins = (I # (rator o rand)) (dest_eq(concl thm)) in
	 let v = genvar (type_of S) in
	 let pat = mk_eq(l,mk_cond(bv,v,mk_comb(ins,v))) in
 	 let thm2 = SUBST [th,v;eql,bv] pat thm in
	    TRANS thm2 (COND_CONV (rand(concl thm2)))) ? 
        let v = genvar (type_of S) in
	let thm = SPEC T (SPEC S (SPEC x iith)) in
	let l,r = (I # rator) (dest_eq (concl thm)) in
	    SUBST [th,v] (mk_eq(l,mk_comb(r,v))) thm in
    \conv tm. 
       (let (_,[S1;S2]) = (check `UNION` # I) (strip_comb tm) in
        let els = strip_set S1 in
	let ty = hd(snd(dest_type(type_of S1))) in
        let ith = INST_TYPE [ty,":*"] InU in
        let iith = INST_TYPE [ty,":*"] InUE in
	    itlist (itfn conv (ith,iith)) els (ISPEC S2 Eu)) ? 
       failwith `UNION_CONV`;;


% ===================================================================== %
% INSERT_CONV: non-redundantly insert a value into a set.		%
%									%
% A call to:								%
%									%
%	INSERT_CONV conv "x INSERT S"					%
%									%
% returns:								%
%									%
%	|- x INSERT S = S						%
%									%
% if IN_CONV conv proves that |- x IN s = T, otherwise fail.		%
%									%
% Note that DEPTH_CONV (INSERT_CONV conv) can be used to remove 	%
% duplicate elements from a set, but the following conversion is 	%
% faster:								%
%									%
% letrec REDUCE_CONV conv tm =						%
%    (SUB_CONV (REDUCE_CONV conv) THENC (TRY_CONV (INSERT_CONV conv)))  %
%    tm;;								%
% ===================================================================== %

let INSERT_CONV = 
    let absth = let th = theorem `finite_sets` `ABSORPTION` in
                let th1 = fst(EQ_IMP_RULE (SPECL ["x:*";"s:(*)set"] th)) in
		    GENL ["x:*";"s:(*)set"] th1 in
    let check = assert (\c. fst(dest_const c) = `INSERT`) in
    let mkIN = 
        let boolty = ":bool" in 
        \x s. let ty = type_of x in let sty = mk_type(`set`,[ty]) in
              let INty = mk_type(`fun`,[ty;mk_type(`fun`,[sty;boolty])]) in
	          mk_comb(mk_comb(mk_const(`IN`,INty),x),s) in
    let isT = let T = "T" in \thm. rand(concl thm)=T in
    \conv tm.
        (let _,[x;s] = (check # I) (strip_comb tm) in
	 let thm = IN_CONV conv (mkIN x s) in
	 if (isT thm) then
	    MP (SPEC s (ISPEC x absth)) (EQT_ELIM thm) else fail) ? 
	failwith `INSERT_CONV`;;


% ===================================================================== %
% IMAGE_CONV: compute the image of a function on a finite set.		%
%									%
% A call to:								%
%									%
%	IMAGE_CONV conv iconv "IMAGE f {x1,...,xn}"			%
%									%
% returns:								%
%									%
%	|- IMAGE f {x1,...,xn} = {y1,...,yn}				%
%									%
% where conv proves |- f xi = yi for all 1<=i<=n.  The conversion also  %
% trys to use INSERT_CONV iconv to simplify insertion of the results 	%
% into the set {y1,...,yn}.						%
%									%
% ===================================================================== %

let IMAGE_CONV = 
    let Ith = theorem `finite_sets` `IMAGE_INSERT` and
        Eth = theorem `finite_sets` `IMAGE_EMPTY` in
    let check st = assert (\c. fst(dest_const c) = st) in
    letrec iconv IN cnv1 cnv2 ith eth s = 
       (let _,[x;t] = (check `INSERT` # I) (strip_comb s) in
        let thm1 = SPEC t (SPEC x ith) in
        let el = rand(rator(rand(concl thm1))) in
        let cth = MK_COMB(AP_TERM IN (cnv1 el),iconv IN cnv1 cnv2 ith eth t) in
	let thm2 = TRY_CONV (INSERT_CONV cnv2) (rand(concl cth)) in
            TRANS thm1 (TRANS cth thm2)) ? 
       (if (fst(dest_const s) = `EMPTY`) then eth else fail) in
    \conv1 conv2 tm.
        (let _,[f;s] = (check `IMAGE` # I) (strip_comb tm) in
     	 let _,[_;ty] = dest_type(type_of f) in
         let sty = mk_type(`set`,[ty]) in
     	 let INty = mk_type(`fun`, [ty;mk_type(`fun`,[sty;sty])]) in
     	 let IN = mk_const(`INSERT`, INty) in
             iconv IN conv1 conv2 (ISPEC f Ith) (ISPEC f Eth) s) ? 
	failwith `IMAGE_CONV`;;


