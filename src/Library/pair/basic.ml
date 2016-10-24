% --------------------------------------------------------------------- %
% 		Copyright (c) Jim Grundy 1992				%
%               All rights reserved                                     %
%									%
% Jim Grundy, hereafter referred to as `the Author', retains the	%
% copyright and all other legal rights to the Software contained in	%
% this file, hereafter referred to as `the Software'.			%
% 									%
% The Software is made available free of charge on an `as is' basis.	%
% No guarantee, either express or implied, of maintenance, reliability	%
% or suitability for any purpose is made by the Author.			%
% 									%
% The user is granted the right to make personal or internal use	%
% of the Software provided that both:					%
% 1. The Software is not used for commercial gain.			%
% 2. The user shall not hold the Author liable for any consequences	%
%    arising from use of the Software.					%
% 									%
% The user is granted the right to further distribute the Software	%
% provided that both:							%
% 1. The Software and this statement of rights is not modified.		%
% 2. The Software does not form part or the whole of a system 		%
%    distributed for commercial gain.					%
% 									%
% The user is granted the right to modify the Software for personal or	%
% internal use provided that all of the following conditions are	%
% observed:								%
% 1. The user does not distribute the modified software. 		%
% 2. The modified software is not used for commercial gain.		%
% 3. The Author retains all rights to the modified software.		%
%									%
% Anyone seeking a licence to use this software for commercial purposes	%
% is invited to contact the Author.					%
% --------------------------------------------------------------------- %
% CONTENTS: basic functions for dealing with paired abstractions.	%
% --------------------------------------------------------------------- %
%$Id: basic.ml,v 3.1 1993/12/07 14:42:10 jg Exp $%

% ------------------------------------------------------------------------- %
%  |- a = a'   |- b = b'                                                    %
% ----------------------  MK_PAIR                                           %
%   |- (a,b) = (a',b')                                                      %
% ------------------------------------------------------------------------- %

let MK_PAIR = 
    let mk_fun(y1,y2) = mk_type(`fun`,[y1;y2]) in
    let comma(y1,y2) = mk_const(`,`,mk_fun(y1,mk_fun(y2,mk_prod(y1,y2)))) in
    \(t1,t2).
        let y1 = type_of (rand (concl t1))
        and y2 = type_of (rand (concl t2)) in
            MK_COMB ((AP_TERM (comma(y1,y2)) t1),t2);;

% ------------------------------------------------------------------------- %
% Paired abstraction                                                        %
%                                                                           %
%         A |- t1 = t2                                                      %
%     -----------------------  (provided p is not free in A)                %
%      A |- (\p.t1) = (\p.t2)                                               %
% ------------------------------------------------------------------------- %

letrec PABS p th =
    (if is_var p then
	ABS p th
    else % is_pair %
	let (p1, p2) = dest_pair p in
	    let t1 = PABS p2 th in
	    let t2 = PABS p1 t1 in
	    let pty = type_of p in
	    let p1ty = type_of p1 in
	    let p2ty = type_of p2 in
	    let cty = type_of (rand (concl th)) in
		AP_TERM
		(mk_const
		(`UNCURRY`,
		  mk_type
		  (`fun`,[mk_type(`fun`,[p1ty;mk_type(`fun`,[p2ty;cty])]);
			 mk_type(`fun`,[pty;cty])])))
		t2
    ) ? failwith `PABS`;;

% ----------------------------------------------------------------------- %
% PABS_CONV conv "\p. t[p]" applies conv to t[p]                          %
% ----------------------------------------------------------------------- %

let PABS_CONV conv tm =
    let (bp,body) = (dest_pabs tm ? failwith `PABS_CONV`) in
    let bodyth = conv body in
	(PABS bp bodyth ? failwith `PABS_CONV`);;

% ----------------------------------------------------------------------- %
% PSUB_CONV conv tm: applies conv to the subterms of tm.                  %
% ----------------------------------------------------------------------- %

let PSUB_CONV conv tm =
    if is_pabs tm then
	PABS_CONV conv tm
    else if is_comb tm then
	let (rator,rand) = dest_comb tm in
	    MK_COMB (conv rator, conv rand)
    else (ALL_CONV tm);;

% ------------------------------------------------------------------------- %
% CURRY_CONV "(\(x,y).f)(a,b)" = (|- ((\(x,y).f)(a,b)) = ((\x y. f) a b))   %
% ------------------------------------------------------------------------- %

let CURRY_CONV =
    let gfty = ":* -> (** -> ***)" 
    and gxty = ":*"
    and gyty = ":**"
    and gpty = ":*#**"
    and grange = ":***" in
    let gf = genvar gfty
    and gx = genvar gxty
    and gy = genvar gyty
    and gp = genvar gpty in
    let uncurry_thm = SPECL [gf;gx;gy] UNCURRY_DEF
    and pair_thm = SYM (SPEC gp PAIR) in
    let (fgp,sgp) = dest_pair (rand (concl pair_thm)) in
    let pair_uncurry_thm = 
	(CONV_RULE
	    ((RATOR_CONV o RAND_CONV o RAND_CONV) (K (SYM pair_thm))))
	    (SPECL [gf;fgp;sgp] UNCURRY_DEF) in
    \tm.
	(let (f,p) = (rand # I) (dest_comb tm) in
	let fty = type_of f in
	let range = hd(tl(snd(dest_type(hd(tl(snd(dest_type fty))))))) in
	let gfinst = mk_var(fst (dest_var gf), fty) in
	    if is_pair p then
		let (x,y) = dest_pair p in
		let xty = type_of x
		and yty = type_of y in
		let gxinst = mk_var(fst (dest_var gx), xty)
		and gyinst = mk_var(fst (dest_var gy), yty) in
		    INST_TY_TERM
			([(f,gfinst);(x,gxinst);(y,gyinst)],
			 [(xty,gxty);(yty,gyty);(range,grange)])
			uncurry_thm
	    else
		let pty = type_of p in
		let gpinst = mk_var(fst (dest_var gp), pty) in
		let (xty,yty) = dest_prod pty in
		    (INST_TY_TERM
			([(f,gfinst);(p,gpinst)],
			 [(xty,gxty);(yty,gyty);(range,grange)])
			pair_uncurry_thm)
	) ? failwith `CURRY_CONV` ;;

% ------------------------------------------------------------------------- %
% UNCURRY_CONV "(\x y. f) a b" = (|- ((\x y. f) a b) = ((\(x,y).f)(x,y)))   %
% ------------------------------------------------------------------------- %

let UNCURRY_CONV = 
    let gfty = ":* -> (** -> ***)" 
    and gxty = ":*"
    and gyty = ":**"
    and grange = ":***" in
    let gf = genvar gfty
    and gx = genvar gxty
    and gy = genvar gyty in
    let uncurry_thm = SYM (SPECL [gf;gx;gy] UNCURRY_DEF) in
    \tm.
	(let ((f,x),y) = (dest_comb # I) (dest_comb tm) in
	let fty = type_of f in
	let range = hd(tl(snd(dest_type(hd(tl(snd(dest_type fty))))))) in
	let gfinst = mk_var(fst (dest_var gf), fty) in
	let xty = type_of x
	and yty = type_of y in
	let gxinst = mk_var(fst (dest_var gx), xty)
	and gyinst = mk_var(fst (dest_var gy), yty) in
	    INST_TY_TERM
		([(f,gfinst);(x,gxinst);(y,gyinst)],
		 [(xty,gxty);(yty,gyty);(range,grange)])
		uncurry_thm
	) ? failwith `UNCURRY_CONV` ;;

% ------------------------------------------------------------------------- %
% PBETA_CONV "(\p1.t)p2" = (|- (\p1.t)p2 = t[p2/p1])                        %
% ------------------------------------------------------------------------- %

let PBETA_CONV =
    % pairlike p x: takes a pair structure p and a term x.		%
    % It returns the struture ((change, thm), assoclist)		%
    % where change is true if x does not have the same structure as p.  %
    % if changes is true then thm is a theorem of the form (|-x'=x) 	%
    % where x' is of the same structure as p, created by makeing terms	%
    % into pairs of the form (FST t,SND t).                             %
    % assoc thm list is a list of theorms for all the subpairs of x that%
    % required changing along the correspoing subpair from p.		%
    let pairlike =
	let mk_fun(y1,y2) = mk_type(`fun`,[y1;y2]) in
	let comma(y1,y2) = mk_const(`,`,mk_fun(y1,mk_fun(y2,mk_prod(y1,y2)))) in
	letrec int_pairlike p x =
	    if is_pair p then
		let (p1,p2) = dest_pair p in
		    if is_pair x then
			let (x1,x2) = dest_pair x in
			let ((cl,lt),pl) = (int_pairlike p1 x1)
			and ((cr,rt),pr) = (int_pairlike p2 x2) in
			let (c,t) =
			    if cl & cr then
				(true,MK_PAIR(lt,rt))
			    else if cl then
				let ty1 = type_of x1
				and ty2 = type_of x2 in
				let comm = comma(ty1,ty2) in
				    (true,AP_THM (AP_TERM comm lt) x2)
			    else if cr then
				let ty1 = type_of x1
				and ty2 = type_of x2 in
				let comm = comma(ty1,ty2) in
				    (true,AP_TERM (mk_comb(comm,x1)) rt)
			    else
				(false,TRUTH)
			in
			    if c then
				((true,t),(p,t).(pl@pr))
			    else
				((false,TRUTH),[])
		    else
			let th1 = ISPEC x PAIR in
			let x' = rand (rator (concl th1)) in
			let (x'1,x'2) = dest_pair x' in
			let ((cl,lt),pl) = (int_pairlike p1 x'1)
			and ((cr,rt),pr) = (int_pairlike p2 x'2) in
			let t =
			    if cl & cr then
				(MK_PAIR(lt,rt)) TRANS th1
			    else if cl then
				let ty1 = type_of x'1
				and ty2 = type_of x'2 in
				let comm = comma(ty1,ty2) in
				    (AP_THM (AP_TERM comm lt) x'2) TRANS th1
			    else if cr then
				let ty1 = type_of x'1
				and ty2 = type_of x'2 in
				let comm = comma(ty1,ty2) in
				    (AP_TERM (mk_comb(comm,x'1)) rt) TRANS th1
			    else
				th1
			in
			    ((true,t),(p,t).(pl@pr))
	    else 
		((false,TRUTH),[])
	in
	    int_pairlike
    % find_CONV mask assl:                                        	%
    % mask is the body of the original abstraction, containing 		%
    % instances of the bound pair p and it subcomponents.		%
    % assl is the theorem list generated by pairlike that will allow	%
    % us to find these pairs and map them back into nonpairs where	%
    % possible.								%
    and find_CONV mask assl =
	letrec search m pthl = 
	    (true, (K (snd (assoc m assl))))
	    ? if is_comb m then
		let (f,b) = dest_comb m in
		let (ff,fc) = search f pthl
		and (bf,bc) = search b pthl in
		    (if ff & bf then
			(true, (RATOR_CONV fc) THENC (RAND_CONV bc))
		    else if ff then
			(true, (RATOR_CONV fc))
		    else if bf then
			(true, (RAND_CONV bc))
		    else
			(false, ALL_CONV))
	    else if is_abs m then
		let (v,b) = dest_abs m in
		    let pthl' = filter (\(p,_). not (free_in v p)) pthl in
		    (if null pthl' then
			(false, ALL_CONV)
		    else
			(let (bf,bc) = search b pthl' in
			    if bf then
				(true, ABS_CONV bc)
			    else
				(false, ALL_CONV)))
	    else
		(false, ALL_CONV)
	in
		snd (search mask assl)
    in
    letrec INT_PBETA_CONV tm =
	let ((p,b),a) = (dest_pabs # I) (dest_comb tm) in
	    if is_var p then
		BETA_CONV tm
	    else % is_pair p %
		(   CURRY_CONV THENC
		    (RATOR_CONV INT_PBETA_CONV) THENC
		    INT_PBETA_CONV
		) tm
    in
    \tm.
	let ((p,b),a) = (dest_pabs # I) (dest_comb tm) in
	let ((dif,difthm),assl) = pairlike p a in
	if dif then
	    (   (RAND_CONV (K (SYM difthm))) THENC
		INT_PBETA_CONV THENC
		(find_CONV b assl)
	    ) tm
	else
	    INT_PBETA_CONV tm;;

let PBETA_RULE = CONV_RULE (DEPTH_CONV PBETA_CONV)
and PBETA_TAC = CONV_TAC (DEPTH_CONV PBETA_CONV) ;;

let RIGHT_PBETA th =
    TRANS th (PBETA_CONV (snd (dest_eq (concl th)))) ? failwith `RIGHT_PBETA`;;

letrec LIST_PBETA_CONV tm =
    (let (f,a) = dest_comb tm in
	RIGHT_PBETA (AP_THM (LIST_PBETA_CONV f) a)
    ) ? REFL tm;;

let RIGHT_LIST_PBETA th =
    TRANS th (LIST_PBETA_CONV (snd (dest_eq (concl th))));;

let LEFT_PBETA th =
    CONV_RULE (RATOR_CONV (RAND_CONV PBETA_CONV)) th ? failwith `LEFT_PBETA`;;

let LEFT_LIST_PBETA th =
    CONV_RULE (RATOR_CONV (RAND_CONV LIST_PBETA_CONV)) th ?
	failwith `LEFT_LIST_PBETA`;;

% ------------------------------------------------------------------------- %
% UNPBETA_CONV "p" "t" = (|- t = (\p.t)p)                                   %
% ------------------------------------------------------------------------- %

let UNPBETA_CONV v tm =
    (SYM (PBETA_CONV (mk_comb(mk_pabs(v,tm),v))))
    ? failwith `UNPBETA_CONV`;;

% ------------------------------------------------------------------------- %
% CURRY_UNCURRY_THM = |- !f. CURRY(UNCURRY f) = f                           %
% ------------------------------------------------------------------------- %

let CURRY_UNCURRY_THM =
    let th1 = prove
		("CURRY (UNCURRY (f:*->**->***)) x y = f x y",
		 REWRITE_TAC [UNCURRY_DEF; CURRY_DEF]) in
    let th2 = GEN "y:**" th1 in
    let th3 = EXT th2 in
    let th4 = GEN "x:*" th3 in
    let th4 = EXT th4 in
	GEN "f:*->**->***" th4;;

% ------------------------------------------------------------------------- %
% UNCURRY_CURRY_THM = |- !f. UNCURRY(CURRY f) = f                           %
% ------------------------------------------------------------------------- %

let UNCURRY_CURRY_THM =
    let th1 = prove
		("UNCURRY (CURRY (f:(*#**)->***)) (x,y) = f(x,y)",
		 REWRITE_TAC [CURRY_DEF; UNCURRY_DEF]) in
    let th2 = INST [("FST (z:*#**)", "x:*"); ("SND (z:*#**)", "y:**")] th1 in
    let th3 = CONV_RULE (RAND_CONV (RAND_CONV (K (ISPEC "z:*#**" PAIR)))) th2 in
    let th4 = CONV_RULE
		(RATOR_CONV (RAND_CONV (RAND_CONV (K (ISPEC "z:*#**" PAIR)))))
		th3 in
    let th5 = GEN "z:*#**" th4 in
    let th6 = EXT th5 in
	GEN "f:(*#**)->***" th6;;

% ------------------------------------------------------------------------- %
% PETA_CONV "\p. f p" = (|- (\p. f p) = t)                                  %
% ------------------------------------------------------------------------- %

let PETA_CONV tm =
    (let (p,fp) = dest_pabs tm in
    let (f,p') = dest_comb fp in
    let x = genvar (type_of p) in
    if (p = p') & (not (occs_in p f)) then
	EXT (GEN x (PBETA_CONV (mk_comb(tm,x))))
    else
	fail
    ) ? failwith `PETA_CONV`;;

% ------------------------------------------------------------------------- %
% PALPHA_CONV p2 "\p1. t" = (|- (\p1. t) = (\p2. t[p2/p1]))                 %
% ------------------------------------------------------------------------- %
    
letrec PALPHA_CONV np tm =
    (let (op,_) = dest_pabs tm in
	if is_var np then
	    if is_var op then
		ALPHA_CONV np tm
	    else % is_pair op %
		let np' = genvar (type_of np) in
		let t1 =  PBETA_CONV (mk_comb(tm, np')) in
		let t2 = ABS np' t1 in
		let t3 = CONV_RULE (RATOR_CONV (RAND_CONV ETA_CONV)) t2 in
		    CONV_RULE (RAND_CONV (ALPHA_CONV np)) t3
	else % is_pair np %
	    if is_var op then
		let np' = genlike np in
		let t1 = PBETA_CONV (mk_comb(tm, np')) in
		let t2 = PABS np' t1 in
		let th3 = CONV_RULE (RATOR_CONV (RAND_CONV PETA_CONV)) t2 in
		    CONV_RULE (RAND_CONV (PALPHA_CONV np)) th3 
	    else % is_pair op %
		let (np1,np2) = dest_pair np in
		    CONV_RULE
			(RAND_CONV (RAND_CONV (PABS_CONV (PALPHA_CONV np2))))
			((RAND_CONV (PALPHA_CONV np1)) tm)
    ) ? failwith `PALPHA_CONV` ;;

% ------------------------------------------------------------------------- %
% For any binder B:                                                         %
% GEN_PALPHA_CONV p2 "B p1. t" = (|- (B p1. t) = (B p2. t[p2/p1]))          %
% ------------------------------------------------------------------------- %

let GEN_PALPHA_CONV p tm = 
    (if is_pabs tm then
	PALPHA_CONV p tm
    else if is_binder (fst (dest_const (rator tm))) then
	AP_TERM (rator tm) (PALPHA_CONV p (rand tm))
    else
	fail
    ) ? failwith `GEN_PALPHA_CONV`;;

% ------------------------------------------------------------------------- %
% Iff t1 and t2 are alpha convertable then                                  %
% PALPHA t1 t2 = (|- t1 = t2)                                               %
%                                                                           %
% Note the PALPHA considers "(\x.x)" and "\(a,b).(a,b)" to be               %
%   alpha convertable where ALPHA does not.                                 %
% ------------------------------------------------------------------------- %

letrec PALPHA t1 t2 =
    (if t1 = t2 then
	REFL t1
    else if (is_pabs t1) & (is_pabs t2) then
	let (p1,b1) = dest_pabs t1 
	and (p2,b2) = dest_pabs t2 in
	    if is_var p1 then
		let th1 = PALPHA_CONV p1 t2 in
		let b2' = pbody (rand (concl th1)) in
		    (PABS p1 (PALPHA b1 b2')) TRANS (SYM th1)
	    else
		let th1 = PALPHA_CONV p2 t1 in
		let b1' = pbody (rand (concl th1)) in
		    th1 TRANS (PABS p2 (PALPHA b2 b1'))
    else if (is_comb t1) & (is_comb t2) then
	let (t1f,t1a) = dest_comb t1 in
	let (t2f,t2a) = dest_comb t2 in
	let thf = PALPHA t1f t2f in
	let tha = PALPHA t1a t2a in
	    (AP_THM thf t1a) TRANS (AP_TERM t2f tha)
    else
	fail
    ) ? failwith `PALPHA`;;

let paconv = curry (can (uncurry PALPHA));;

% ------------------------------------------------------------------------- %
% PAIR_CONV : conv -> conv                                                  %
%                                                                           %
% If the argument of the resulting conversion is a pair, this conversion    %
% recusively applies itself to both sides of the pair.                      %
% Otherwise the basic conversion is applied to the argument.                %
% ------------------------------------------------------------------------- %

letrec PAIR_CONV c t =
   if (is_pair t) then
       MK_PAIR (((PAIR_CONV c)#(PAIR_CONV c)) (dest_pair t))
    else
       c t;;

% ------------------------------------------------------------------------- %
% CURRY_ONE_ONE_THM = |- (CURRY f = CURRY g) = (f = g)                      %
% ------------------------------------------------------------------------- %

let CURRY_ONE_ONE_THM =
    let th1 = ASSUME "(f:(*#**)->***) = g" in
    let th2 = AP_TERM "CURRY:((*#**)->***)->(*->**->***)" th1 in
    let th3 = DISCH_ALL th2 in
    let thA = ASSUME "(CURRY (f:(*#**)->***)) = (CURRY g)" in
    let thB = AP_TERM "UNCURRY:(*->**->***)->((*#**)->***)" thA in
    let thC = PURE_REWRITE_RULE [UNCURRY_CURRY_THM] thB in
    let thD = DISCH_ALL thC in
	IMP_ANTISYM_RULE thD th3 ;;

% ------------------------------------------------------------------------- %
% UNCURRY_ONE_ONE_THM = |- (UNCURRY f = UNCURRY g) = (f = g)                %
% ------------------------------------------------------------------------- %

let UNCURRY_ONE_ONE_THM =
    let th1 = ASSUME "(f:*->**->***) = g" in
    let th2 = AP_TERM "UNCURRY:(*->**->***)->((*#**)->***)" th1 in
    let th3 = DISCH_ALL th2 in
    let thA = ASSUME "(UNCURRY (f:*->**->***)) = (UNCURRY g)" in
    let thB = AP_TERM "CURRY:((*#**)->***)->(*->**->***)" thA in
    let thC = PURE_REWRITE_RULE [CURRY_UNCURRY_THM] thB in
    let thD = DISCH_ALL thC in
	IMP_ANTISYM_RULE thD th3 ;;
