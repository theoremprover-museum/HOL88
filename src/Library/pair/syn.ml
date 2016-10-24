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
% CONTENTS: functions on the syntax of paired abstractions and          %
%           quantifications.                                            %
% --------------------------------------------------------------------- %
%$Id: syn.ml,v 3.1 1993/12/07 14:42:10 jg Exp $%

% ===================================================================== %
% Constructors for paired HOL syntax.                                   %
% ===================================================================== %

let mk_pabs =
    let mk_uncurry cf =
	let tycf = type_of cf in
	let uncurry_type ty =
	    let (tycon1, [tya; tyb]) = (dest_type ty) in
	    let (tycon2, [tyba; tybb]) = (dest_type tyb) in
		assert (curry $= `fun`) tycon1 ;
		assert (curry $= `fun`) tycon2 ;
		mk_type (`fun`, [mk_type(`prod`,[tya;tyba]); tybb ])
	in
	    mk_comb
	    (   mk_const(`UNCURRY`,mk_type(`fun`,[tycf;uncurry_type tycf])) ,
		cf                                                          )
    in
    letrec mpa (p,t) =
	if is_var p then
	    mk_abs (p, t)
	else % is_pair p %
	    let (v1,v2) = dest_pair p in
		mk_uncurry (mpa (v1, (mpa (v2, t))))
    in
	\pt. mpa pt ? failwith `mk_pabs`;;

let mk_pforall (x,t) =
    let ty = type_of x in
    let allty = mk_type(`fun`,[mk_type(`fun`,[ty;bool_ty]);bool_ty]) in
	mk_comb(mk_const(`!`,allty),mk_pabs(x,t)) ? failwith `mk_pforall`;;

let mk_pexists (x,t) =
    let ty = type_of x in
    let exty = mk_type(`fun`,[mk_type(`fun`,[ty;bool_ty]);bool_ty]) in
	mk_comb(mk_const(`?`,exty),mk_pabs(x,t)) ? failwith `mk_pexists`;;

let mk_pselect (x,t) =
    let ty = type_of x in
    let selty = mk_type(`fun`,[mk_type(`fun`,[ty;bool_ty]);ty]) in
	mk_comb(mk_const(`@`, selty), mk_pabs(x,t)) ? failwith `mk_pselect`;;

% ===================================================================== %
% Destructors for paired HOL syntax.                                    %
% ===================================================================== %

letrec dest_pabs tm =
    (if (is_abs tm) then
	dest_abs tm
    else if fst (dest_const (rator tm)) = `UNCURRY` then
	let (v1,b1) = dest_pabs (rand tm) in
	let (v2,b2) = dest_pabs b1 in
	    (mk_pair(v1,v2), b2)
    else fail) ? failwith `dest_pabs`;;

let dest_pforall =
    let check = assert (\c. fst(dest_const c) = `!`) in
    \tm. (let (_,b) = (check # I) (dest_comb tm) in dest_pabs b) ?
	failwith `dest_pforall`;;

let dest_pexists =
    let check = assert (\c. fst(dest_const c) = `?`) in
    \tm. (let (_,b) = (check # I) (dest_comb tm) in dest_pabs b) ?
	 failwith `dest_pexists`;;

let dest_pselect =
    let check = assert (\c. fst(dest_const c) = `@`) in
    \tm. (let (_,b) = (check # I) (dest_comb tm) in dest_pabs b) ?
	 failwith `dest_pselect`;;

% ===================================================================== %
% Discriminators for paired HOL syntax.                                 %
% ===================================================================== %

let is_pabs    = can dest_pabs and
    is_pforall = can dest_pforall and
    is_pexists = can dest_pexists and
    is_pselect = can dest_pselect;;

% ===================================================================== %
% All the elements in a pair struture.                                  %
% ===================================================================== %

letrec rip_pair p = ($@ ((rip_pair # rip_pair) (dest_pair p))) ? [p];;

% ===================================================================== %
% Check if a term is a pair structure of variables.                     %
% ===================================================================== %

let is_pvar = (forall is_var) o rip_pair ;;

% ===================================================================== %
% Paired version of variant.                                            %
% ===================================================================== %

let pvariant =
    letrec uniq l =
	if null l then
	    []
	else
	    let (h.t) = l in
		h.(uniq (filter (\e. not (e = h)) t)) in
    letrec variantl avl vl = 
	if null vl then
	    []
	else
	    let (h.t) = vl in
	    let h' = (variant (avl@(filter is_var t)) h) in
		(h',h).(variantl (h'.avl) t)
    in
    \pl p.
	let avoid = (flat (map ((map (assert is_var)) o rip_pair) pl)) in
	let originals =
	    uniq (map (assert (\p. (is_var p) or (is_const p))) (rip_pair p)) in
	let sub = variantl avoid originals in
	    subst sub p;;

% ===================================================================== %
% Generates a pair structure of variable with the same structure as     %
% its parameter.                                                        %
% ===================================================================== %

letrec genlike p =
    if is_pair p then
	mk_pair ((genlike # genlike) (dest_pair p))
    else
	genvar (type_of p);;

% ===================================================================== %
% Iterated paired constructors:                                         %
%                                                                       %
%  * list_mk_pabs ([p1;...;pn],t)           --->   "\p1 ... pn.t"       %
%  * list_mk_pforall ([p1;...;pn],t)        --->   "!p1 ... pn.t"       %
%  * list_mk_pexists ([p1;...;pn],t)        --->   "?p1 ... pn.t"       %
% ===================================================================== %

let list_mk_pabs (pl, t) =
    (itlist (curry mk_pabs) pl t) ? failwith `list_mk_pabs`;;
let list_mk_pforall (pl, t) =
    (itlist (curry mk_pforall) pl t) ? failwith `list_mk_pforall`;;
let list_mk_pexists (pl, t) =
    (itlist (curry mk_pexists) pl t) ? failwith `list_mk_pexists`;;

% ===================================================================== %
% Iterated paired destructors:                                          %
%                                                                       %
%  * strip_abs "\p1 ... pn. t"           --->   [p1; ...; pn], t        %
%  * strip_forall "!p1 ... pn. t"        --->   [p1; ...; pn], t        %
%  * strip_exists "?p1 ... pn. t"        --->   [p1; ...; pn], t        %
% ===================================================================== %
letrec strip_pabs tm =
    (let (bp,body) = dest_pabs tm in
     let (bps,core) = strip_pabs body in
	(bp.bps, core))
    ? ([],tm);;

letrec strip_pforall tm =
    (let (bp,body) = dest_pforall tm in
     let (bps,core) = strip_pforall body in
	(bp.bps,core))
    ? ([],tm);;

letrec strip_pexists tm =
    (let (bp,body) = dest_pexists tm in
     let (bps,core) = strip_pexists body in
	(bp.bps,core))
    ? ([],tm);;

% ===================================================================== %
% Paired bound variable and body.                                       %
% ===================================================================== %

let bndpair tm = fst (dest_pabs tm) ? failwith `bndpair`
and pbody tm = snd (dest_pabs tm) ? failwith `pbody` ;;

% ===================================================================== %
% Occurence check for bound pairs.                                      %
% occs_in p t    true iff any of the variables in p occure free in t    %
% ===================================================================== %

let occs_in =
    letrec occs_check vl t =
	if is_const t then
	    false
	else if is_var t then
	    mem t vl
	else if is_comb t then
	    let (t1,t2) = dest_comb t in
		(occs_check vl t1) or (occs_check vl t2)
	else % is_abs %
	    let (x,b) = dest_abs t in
		occs_check (filter (\v. (not (v = x))) vl) b
    in
	\p t.
	    if is_pvar p then
		let vs = frees p in
		    occs_check vs t
	    else
		failwith `occs_in: not a pvar`;;

% ===================================================================== %
% Extra support of manipulating product types.                          %
% ===================================================================== %

let is_prod t =
    let (ty_name, l) = dest_type t in
	((ty_name = `prod`) & ((length l) = 2)) ;;

let dest_prod t =
    (let (ty_name, [ty1;ty2]) = dest_type t in
	if ty_name = `prod` then
	    (ty1,ty2)
	else
	    fail
    ) ? failwith `dest_prod`;;

let mk_prod (ty1,ty2) = mk_type (`prod`,[ty1;ty2]);;
