%****************************************************************************%
% ML code to support definitions of Z-style schemas.                         %
%****************************************************************************%

%============================================================================%
% Preliminaries.                                                             %
%============================================================================%

new_special_symbol `|-?`;;
new_special_symbol `><`;;
new_special_symbol `::`;;
new_special_symbol `<->`;;
new_special_symbol `-+>`;;
new_special_symbol `-->`;;
new_special_symbol `+>`;;
new_special_symbol `<+`;;
new_special_symbol `(+)`;;
new_special_symbol `^^`;;
new_special_symbol `|->`;;
new_special_symbol `..`;;
new_special_symbol `|\\/|`;;
new_special_symbol `|/\\|`;;
new_special_symbol `|==>|`;;
new_special_symbol `|~|`;;
new_special_symbol `=/=`;;

new_alphanum `!`;;
new_alphanum `?`;;

%----------------------------------------------------------------------------%
% Load ELIMINATE_TACS from contrib/smarttacs.                                %
%----------------------------------------------------------------------------%

load_contrib `smarttacs/ELIMINATE_TACS`;;

load_library `sets`;;
load_library `string`;;
load_library `taut`;;
load_library `reduce`;;
load_library `arith`;;
load_library `unwind`;;

loadf `arith-tools`;;

load_theory `Z` ? ();;
autoload_defs_and_thms `Z`;;
autoload_defs_and_thms `bool`;;

associate_restriction(`!`, `FORALL_RESTRICT`);;
associate_restriction(`?`, `EXISTS_RESTRICT`);;

%============================================================================%
% List and tuple processing routines.                                        %
%============================================================================%

ml_curried_infix `subset`;;

let s1 subset s2 = (subtract s1 s2 = []);;

let appendl l = itlist $append l [];;

%----------------------------------------------------------------------------%
% putprop (x,v) [(x1,v1);...;(xn,vn)] replaces (xi,vi) by (x,v) if x=xi,     %
% otherwise the pair (x,v) is added to the front of the list.                %
%----------------------------------------------------------------------------%

let putprop (x,v) l =
 letrec f l1 l2 =
  if null l2
  then (x,v).l
  if x=fst(hd l2)
  then (rev l1)@((x,v).(tl(l2)))
  else f(hd l2.l1)(tl l2)
 in
 f [] l;;

%----------------------------------------------------------------------------%
% []               --->  fail                                                %
% ["t1";...;"tn"]  --->  "(t1,...,tn)"                                       %
%----------------------------------------------------------------------------%

letrec mk_tuple tml =
 if null tml
  then failwith `mk_tuple`
 if null(tl tml)
  then (hd tml)
  else mk_pair(hd tml, mk_tuple(tl tml));;

%----------------------------------------------------------------------------%
% "(t1,...,tn)"   --->   ["t1";...;"tn"]                                     %
%----------------------------------------------------------------------------%

letrec dest_tuple t =
 (let t1,t2 = dest_pair t
  in
  t1.dest_tuple t2
 ) ? [t];;

%----------------------------------------------------------------------------%
% Test whether a term has the form "(v1,...,vn)".                            %
%----------------------------------------------------------------------------%

let is_var_tuple tm =
 (map (\t. is_var t => () | fail) (dest_tuple tm); true) ? false;;

%----------------------------------------------------------------------------%
% Prime a variable.                                                          %
%----------------------------------------------------------------------------%

let prime_var tm = 
 let tok,ty = (dest_var tm ? failwith `prime applied to a non-variable`)
 in
 mk_var(tok^`'`,ty);;


%============================================================================%
% Some syntax utilities for preterms.                                        %
%============================================================================%

%----------------------------------------------------------------------------%
% Convert a term to a preterm; discard types.                                %
%----------------------------------------------------------------------------%

let term_to_preterm_list = [`theta`];;

letrec term_to_preterm tm =
 (let s,() = dest_var tm
 in
 preterm_var s)
 ?
 (let s,() = dest_const tm
 in
 if mem s term_to_preterm_list
  then preterm_typed(preterm_const s, type_of tm)
  else preterm_const s)
 ?
 (let p1,p2 = dest_comb tm
  in
  preterm_comb(term_to_preterm p1, term_to_preterm p2))
 ?
 (let p1,p2 = dest_abs tm
  in
  let s,() = dest_var p1
  in
  preterm_abs(preterm_var s, term_to_preterm p2))
 ?
 failwith `term_to_preterm`;;

letrec dest_preterm_var =
 fun (preterm_var v) . v
  |  _               . failwith `dest_preterm_var`;;

letrec dest_preterm_const =
 fun (preterm_const v) . v
  |  _                 . failwith `dest_preterm_const`;;

letrec dest_preterm_comb =
 fun (preterm_comb(p1,p2)) . (p1,p2)
  |  _                     . failwith `dest_preterm_comb`;;

letrec dest_preterm_abs =
 fun (preterm_abs(p1,p2)) . (p1,p2)
  |  _                    . failwith `dest_preterm_abs`;;

letrec dest_preterm_typed =
 fun (preterm_typed(p,ty)) . (p,ty)
  |  _                     . failwith `dest_preterm_typed`;;

letrec dest_preterm_antiquot =
 fun (preterm_antiquot p) . p
  |  _                    . failwith `dest_preterm_antiquot`;;

let is_preterm_var      = can dest_preterm_var
and is_preterm_const    = can dest_preterm_const
and is_preterm_comb     = can dest_preterm_comb
and is_preterm_abs      = can dest_preterm_abs
and is_preterm_typed    = can dest_preterm_typed
and is_preterm_antiquot = can dest_preterm_antiquot;;

let preterm_rator = fst o dest_preterm_comb
and preterm_rand  = snd o dest_preterm_comb;;

let preterm_vb    = fst o dest_preterm_abs
and preterm_body  = snd o dest_preterm_abs;;

let strip_preterm_comb p =
 letrec f p =
  case p of
   (preterm_comb(p1,p2)). (let op,args = f p1 in (op,p2.args))
  |_                    . (p,[])
 in
 (I # rev)(f p);;

letrec list_preterm_comb(op,args) =
 if null args
 then op
 else list_preterm_comb(preterm_comb(op,hd args), tl args);;

let dest_preterm_pair p =
 let op,args = strip_preterm_comb p
 in
 if (op = preterm_const `,`) & (length args = 2) 
 then (hd args, hd(tl args))
 else failwith `dest_preterm_pair`;;

let is_preterm_pair = can dest_preterm_pair;;

let mk_preterm_pair(p1,p2) =
 preterm_comb((preterm_comb((preterm_const `,`), p1)), p2);;

letrec list_mk_preterm_comb(p,l) =
 if null l
 then p
 else list_mk_preterm_comb(preterm_comb(p,hd l), tl l);;

letrec dest_preterm_list p =
 if p = preterm_const `NIL`
 then []
 else
 let p1,p2 = dest_preterm_comb p
 in
 let p11,p12 = (dest_preterm_comb p1 ? failwith `dest_preterm_list`)
 in
 if not(p11 = preterm_const `CONS`)
 then failwith `dest_preterm_list`
 else p12.(dest_preterm_list p2);;

let is_preterm_list = can dest_preterm_list;;

letrec mk_preterm_list pl =
 if null pl
 then preterm_const `NIL`
 else preterm_comb
       (preterm_comb(preterm_const `CONS`, hd pl),mk_preterm_list(tl pl));;

%----------------------------------------------------------------------------%
% []               --->  fail                                                %
% ["t1";...;"tn"]  --->  "(t1,...,tn)"                                       %
%----------------------------------------------------------------------------%

letrec mk_preterm_tuple tml =
 if null tml
  then failwith `mk_preterm_tuple`
 if null(tl tml)
  then (hd tml)
  else mk_preterm_pair(hd tml, mk_preterm_tuple(tl tml));;

%----------------------------------------------------------------------------%
% "(t1,...,tn)"   --->   ["t1";...;"tn"]                                     %
%----------------------------------------------------------------------------%

letrec dest_preterm_tuple t =
 (let t1,t2 = dest_preterm_pair t
  in
  t1.dest_preterm_tuple t2
 ) ? [t];;

%----------------------------------------------------------------------------%
% Test whether a term has the form "(v1,...,vn)".                            %
%----------------------------------------------------------------------------%

let is_preterm_var_tuple tm =
 (map 
   (\t. is_preterm_var t => () | fail) 
   (dest_preterm_tuple tm); true) 
 ? false;;

%----------------------------------------------------------------------------%
% Make a preterm conjunction.                                                %
%----------------------------------------------------------------------------%

let mk_preterm_conj(p1,p2) =
 preterm_comb(preterm_comb(preterm_const `/\\`,p1),p2);;

%----------------------------------------------------------------------------%
% Split a preterm conjunction into the conjoined preterms.                   %
%----------------------------------------------------------------------------%

let dest_preterm_conj p =
 (let op,[p1;p2] = strip_preterm_comb p
  in
  if dest_preterm_const op = `/\\`
  then (p1,p2)
  else fail
 ) ? failwith `dest_preterm_conj`;;

%----------------------------------------------------------------------------%
% Preterm version of list_mk_conj.                                           %
%----------------------------------------------------------------------------%

letrec list_mk_preterm_conj l =
 if null l
 then failwith `list_mk_preterm_conj`
 if null(tl l)
 then hd l
 else
 mk_preterm_conj(hd l, list_mk_preterm_conj(tl l)) ;;

%----------------------------------------------------------------------------%
% Split a preterm into conjuncts.                                            %
%----------------------------------------------------------------------------%

letrec preterm_conjuncts p =
 (let p1,p2 = dest_preterm_conj p
  in
  (preterm_conjuncts p1 @ preterm_conjuncts p2)
 ) ? [p];;

%----------------------------------------------------------------------------%
% Make a preterm disjunction.                                                %
%----------------------------------------------------------------------------%

let mk_preterm_disj(p1,p2) =
 preterm_comb(preterm_comb(preterm_const `\\/`,p1),p2);;

%----------------------------------------------------------------------------%
% Split a preterm disjunction into the disjoined preterms.                   %
%----------------------------------------------------------------------------%

let dest_preterm_disj p =
 (let op,[p1;p2] = strip_preterm_comb p
  in
  if dest_preterm_const op = `\\/`
  then (p1,p2)
  else fail
 ) ? failwith `dest_preterm_disj`;;

%----------------------------------------------------------------------------%
% Preterm version of list_mk_disj.                                           %
%----------------------------------------------------------------------------%

letrec list_mk_preterm_disj l =
 if null l
 then failwith `list_mk_preterm_disj`
 if null(tl l)
 then hd l
 else
 mk_preterm_disj(hd l, list_mk_preterm_disj(tl l)) ;;

%----------------------------------------------------------------------------%
% Split a preterm into disjuncts.                                            %
%----------------------------------------------------------------------------%

letrec preterm_disjuncts p =
 (let p1,p2 = dest_preterm_disj p
  in
  (preterm_disjuncts p1 @ preterm_disjuncts p2)
 ) ? [p];;

%----------------------------------------------------------------------------%
% Make a preterm implication.                                                %
%----------------------------------------------------------------------------%

let mk_preterm_imp(p1,p2) =
 preterm_comb(preterm_comb(preterm_const `==>`,p1),p2);;

%----------------------------------------------------------------------------%
% Split a preterm implication into the antecedent and consequent.            %
%----------------------------------------------------------------------------%

let dest_preterm_imp p =
 (let op,[p1;p2] = strip_preterm_comb p
  in
  if dest_preterm_const op = `==>`
  then (p1,p2)
  else fail
 ) ? failwith `dest_preterm_imp`;;

%----------------------------------------------------------------------------%
% Make a preterm equality.                                                   %
%----------------------------------------------------------------------------%

let mk_preterm_eq(p1,p2) =
 preterm_comb(preterm_comb(preterm_const `=`,p1),p2);;

%----------------------------------------------------------------------------%
% Split a preterm equality into the left and right hand sides.               %
%----------------------------------------------------------------------------%

let dest_preterm_eq p =
 (let op,[p1;p2] = strip_preterm_comb p
  in
  if dest_preterm_const op = `=`
  then (p1,p2)
  else fail
 ) ? failwith `dest_preterm_eq`;;

%----------------------------------------------------------------------------%
% Syntax functions for preterm quantifiers.                                  %
%----------------------------------------------------------------------------%

let mk_preterm_forall(v,p) =
 preterm_comb(preterm_const `!`, preterm_abs(v, p));;

letrec list_mk_preterm_forall(l,p) = 
 if null l 
 then p
 else mk_preterm_forall(hd l, list_mk_preterm_forall(tl l,p));;

%< Not needed -- delete
let mk_preterm_res_forall((v,t),p) =
 preterm_comb
  ((preterm_comb((preterm_const `FORALL_RESTRICT`), t)), preterm_abs(v, p));;
>%

%----------------------------------------------------------------------------%
% ([("v1","t1");...;("vn","tn")], "p")                                       %
% --->                                                                       %
% "!v1...vn. v1::t1 /\ ... /\ vn::tn ==> p"                                  %
%----------------------------------------------------------------------------%

letrec list_mk_preterm_res_forall(l,p) =
 let vl,() = split l
 and rl    =
  map (\(v,t). preterm_comb((preterm_comb((preterm_const `::`), v)), t)) l
 in
 list_mk_preterm_forall
  (vl, 
   if null rl then p else mk_preterm_imp(list_mk_preterm_conj rl,p));;

let mk_preterm_exists(v,p) =
 preterm_comb(preterm_const `?`, preterm_abs(v, p));;

%----------------------------------------------------------------------------%
% ([("v1","t1");...;("vn","tn")], "p")                                       %
% --->                                                                       %
% "?v1...vn. v1::t1 /\ ... /\ vn::tn /\ p"                                   %
%----------------------------------------------------------------------------%

letrec list_mk_preterm_exists(l,p) =
 if null l
 then p
 else mk_preterm_exists(hd l, list_mk_preterm_exists(tl l,p));;

%< Not needed -- delete
let mk_preterm_res_exists((v,t),p) =
 preterm_comb
  ((preterm_comb((preterm_const `EXISTS_RESTRICT`), t)), preterm_abs(v, p));;
>%

%----------------------------------------------------------------------------%
% ([("v1","t1");...;("vn","tn")], "p")                                       %
% --->                                                                       %
% "?v1...vn. v1::t1 /\ ... /\ vn::tn /\ p"                                   %
%----------------------------------------------------------------------------%

letrec list_mk_preterm_res_exists(l,p) =
 let vl,() = split l
 and rl    =
  map (\(v,t). preterm_comb((preterm_comb((preterm_const `::`), v)), t)) l
 in
 list_mk_preterm_exists
  (vl, 
   if null rl then p else mk_preterm_conj(list_mk_preterm_conj rl,p));;

%----------------------------------------------------------------------------%
% preterm_frees computes the free variables in a preterm.                    %
%----------------------------------------------------------------------------%

letrec preterm_frees p =
 case p
  of (preterm_var v)       . [p]
  |  (preterm_const c)     . []
  |  (preterm_comb(p1,p2)) . union (preterm_frees p1) (preterm_frees p2)
  |  (preterm_abs(p1,p2))  . subtract (preterm_frees p2) [p1]
  |  (preterm_typed(p1,ty)). preterm_frees p1
  |  (preterm_antiquot t)  . map (preterm_var o fst o dest_var) (frees t);;

%----------------------------------------------------------------------------%
% Preterm substitution. No renaming; variable capture causes failure.        %
%----------------------------------------------------------------------------%

%----------------------------------------------------------------------------%
% var_capture l v1 v2 is true if substituting l in p2 would result in a      %
% variable capture by p1.                                                    %
%----------------------------------------------------------------------------%

let var_capture l p1 p2 =
 (map 
   (\v. if (mem p1 (preterm_frees(fst(rev_assoc v l))) ? false) then fail) 
   (preterm_frees p2);
  false
 ) ? true;;

letrec preterm_subst l p =
 case p
  of (preterm_var v)       . fst(rev_assoc p l) ? p
  |  (preterm_const c)     . p
  |  (preterm_comb(p1,p2)) . preterm_comb
                              (preterm_subst l p1, preterm_subst l p2)
  |  (preterm_abs(p1,p2))  . if var_capture l p1 p2
                             then failwith `preterm_subst: variable capture`
                             else preterm_abs(p1, preterm_subst l p2)
  |  (preterm_typed(p1,ty)). preterm_typed(preterm_subst l p1,ty)
  |  (preterm_antiquot t)  . p;;

%----------------------------------------------------------------------------%
% Prime (dash) a preterm variable.                                           %
%----------------------------------------------------------------------------%

let prime_preterm_var pm = 
 let tok = (dest_preterm_var pm ? failwith `prime applied to a non-variable`)
 in
 preterm_var(tok^`'`);;

%----------------------------------------------------------------------------%
% Test whether a preterm_var is decorated (with a dash, ? or !).             %
%----------------------------------------------------------------------------%

let is_dashed v =
 let cl = explode(dest_preterm_var v)
 in
 not(null cl) & (last cl = `'`);;

let dest_dashed v = 
 let cl = explode v
 in
 if not(null cl) & (last cl = `'`) 
 then implode(butlast cl) 
 else failwith `dest_dashed`;;

let iter_dest_dashed v =
 letrec f(n,v) = f(n+1,dest_dashed v) ? (n,v)
 in
 f(0,v);;

let is_input v =
 let cl = rev(explode(dest_preterm_var v))
 in
 not(null cl) & (hd cl = `?`);;

let is_output v =
 let cl = rev(explode(dest_preterm_var v))
 in
 not(null cl) & (hd cl = `!`);;

let is_plain v = not(is_dashed v or is_input v or is_output v);;


%============================================================================%
% Global state variables and routines.                                       %
%============================================================================%

%----------------------------------------------------------------------------%
% Global list of variables declared in schemas and their types.              %
%----------------------------------------------------------------------------%

letref schema_variables = []:(string#type)list;;

let lookup_schema_var v = 
 snd(assoc v schema_variables) 
 ? failwith `lookup_schema_var`;;

let remember_type d =
 (let v,ty1 = dest_var(rand(rator d))
  in
  let (),ty2 = assoc v schema_variables
  in
  if ty1=ty2 
  then d
  else failwith(v^` already declared with a different type`)
 ) ? (schema_variables := (dest_var(rand(rator d))).schema_variables;d);;

%----------------------------------------------------------------------------%
% Global list of schema expansions.                                          %
%----------------------------------------------------------------------------%

letref schema_expansions = [] : (term#term)list;;

%----------------------------------------------------------------------------%
% Store preterm schema sc2 as an expansion of preterm schema sc1.            %
%----------------------------------------------------------------------------%

let store_preterm_schema_pair(sc1,sc2) =
 let tm2 = preterm_to_term sc2
 in
 let tm1 = preterm_to_term(preterm_typed(sc1, type_of tm2))
 in
 if tm1 = tm2
 then ()
 else (schema_expansions := putprop (tm1, tm2) schema_expansions; ());; 

%----------------------------------------------------------------------------%
% Store schema sc2 as an expansion of schema sc1 (sc1 and sc2 both terms).   %
%----------------------------------------------------------------------------%

let store_schema_pair(sc1,sc2) =
 schema_expansions :=  putprop (sc1, sc2) schema_expansions; ();;

%----------------------------------------------------------------------------%
% Retrieve the abbreviating term for a schema; fail if no abbreviation       %
% in schema_expansions.                                                      %
%----------------------------------------------------------------------------%

let lookup_schema_abbrev tm = fst(rev_assoc tm schema_expansions);;

%----------------------------------------------------------------------------%
% Retrieve the term a schema expands to.                                     %
%----------------------------------------------------------------------------%

let lookup_schema_expansion tm = snd(assoc tm schema_expansions);;

%----------------------------------------------------------------------------%
% Global list of schema names.                                               %
%----------------------------------------------------------------------------%

letref schema_names = []:string list;;

%----------------------------------------------------------------------------%
% Store the name of a schema.                                                %
%----------------------------------------------------------------------------%

let store_schema_name name sc =
 store_schema_pair(mk_var(name,":bool"),sc);
 (if not(mem name schema_names) 
  then (schema_names := name.schema_names; ()));
 sc;;

%----------------------------------------------------------------------------%
% Retrieve the schema term associated with a name `name`.                    %
%----------------------------------------------------------------------------%

let lookup_schema_name s =
 (if mem s schema_names
  then lookup_schema_expansion(mk_var(s,":bool"))
  else fail
 ) ? failwith `lookup_schema_name`;;

%----------------------------------------------------------------------------%
% Counter used for generating axiom names.                                   %
%----------------------------------------------------------------------------%

letref axiom_count = 1;;

%----------------------------------------------------------------------------%
% List of Z construct not folded on output.                                  %
%----------------------------------------------------------------------------%

letref not_fold_list = [] : string list;;

%----------------------------------------------------------------------------%
% Check whether the head constant of a term is in not_fold_list.             %
%----------------------------------------------------------------------------%

let not_fold tm = 
 mem (fst(dest_const(fst(strip_comb tm)))) not_fold_list ? false;;

%----------------------------------------------------------------------------%
% Stop a Z construct from being folded.                                      %
%----------------------------------------------------------------------------%

let disable_folding s = (not_fold_list := union [s] not_fold_list);;

%----------------------------------------------------------------------------%
% Enable folding of a Z construct.                                           %
%----------------------------------------------------------------------------%

let enable_folding = delete not_fold_list;;

%============================================================================%
% Syntax routines for schemas.                                               %
%============================================================================%

%----------------------------------------------------------------------------%
% A schema is term of the form:                                              %
%                                                                            %
%    "SCHEMA [v1 :: S1; ... ; vn :: Sm] [B1; ... ;Bn]"                       %
%----------------------------------------------------------------------------%

%----------------------------------------------------------------------------%
% dest_dec "v :: S"  --->  ("v","S")                                         %
%----------------------------------------------------------------------------%

let dest_dec pm =
 let op,args = strip_preterm_comb pm
 in
 if is_preterm_const op &
    (dest_preterm_const op = `::`) &
    (length args = 2)                   &
    is_preterm_var(hd args)
 then (hd args, hd(tl args))
 else failwith `dest_dec`;;

let dest_input dec = 
 let v,() = dest_dec dec
 in
 if is_input v then v else fail;;

let dest_output dec = 
 let v,() = dest_dec dec
 in
 if is_output v then v else fail;;

let dest_plain dec = 
 let v,() = dest_dec dec
 in
 if is_plain v then v else fail;;

let get_dec_var = fst o dest_dec;;
let get_dec_set = snd o dest_dec;;

%----------------------------------------------------------------------------%
% is_dec pm tests whether pm has the form "v :: S"                           %
%----------------------------------------------------------------------------%

let is_dec = can dest_dec;;

%----------------------------------------------------------------------------%
% dest_decs "[v1 :: S1; ... ; vn :: Sn]"                                     %
% --->                                                                       %
% [("v1","S1");...;("vn","Sn")]                                              %
%----------------------------------------------------------------------------%

let dest_decs pm = map dest_dec (dest_preterm_list pm);;

%----------------------------------------------------------------------------%
% is_decs pm tests whether pm has the form "[v1 :: S1; ... ; vn :: Sn]"      %
%----------------------------------------------------------------------------%

let is_decs = can dest_decs;;

%----------------------------------------------------------------------------%
% ("decs", "bdy") ---> "SCHEMA decs bdy"                                     %
%                                                                            %
% and check that:                                                            %
%                                                                            %
%    1. decs is a list of declarations                                       %
%                                                                            %
%    2. free variables in bdy are declared in decs                           %
%                                                                            %
%    3. no declared variable occurs in the rhs of a declaration              %
%                                                                            %
%----------------------------------------------------------------------------%

let mk_schema(decs,bdy) =
 let decsl = dest_preterm_list decs
 in
 let dec_vars = map get_dec_var decsl
 in
 map
  (\pm. is_dec pm => () | failwith `bad declaration`)
  decsl;
 if not((preterm_frees bdy) subset dec_vars)
 then failwith `undeclared free variable in body`
 if not(intersect 
         dec_vars 
         (appendl(map (preterm_frees o get_dec_set) decsl)) = 
        [])
 then failwith `variable occurs on both lhs and rhs of declarations`
 else preterm_comb(preterm_comb(preterm_const `SCHEMA`, decs), bdy);;

%----------------------------------------------------------------------------%
% "SCHEMA decs bdy"  --->  ("decs", "bdy")                                   %
%----------------------------------------------------------------------------%

let dest_schema sc =
 (let op,[dec;bdy] = strip_preterm_comb sc
  in
  if (op = preterm_const `SCHEMA`) & 
     is_preterm_list dec           & 
     is_preterm_list bdy
  then (dec,bdy)
  else fail
 ) ? failwith `dest_schema`;;

let is_schema = can dest_schema;;

%----------------------------------------------------------------------------%
% Get conjuncts making up the declaration and predicate of a schema term.    %
%----------------------------------------------------------------------------%

let schema_dec_conjuncts sc =
 let op,[decs;bdy] = strip_comb sc
 in
 fst(dest_list decs);;

let schema_body_conjuncts sc =
 let op,[decs;bdy] = strip_comb sc
 in
 fst(dest_list bdy);;

let schema_conjuncts sc =
 let op,[decs;bdy] = strip_comb sc
 in
 fst(dest_list decs)@fst(dest_list bdy);;


%============================================================================%
% Add explicit types (from the global schema_variables) to previously        %
% declared schema variables.                                                 %
%============================================================================%

%----------------------------------------------------------------------------%
% Test whether a preterm has the form "v :: S".                              %
%----------------------------------------------------------------------------%

let is_var_dec p =
 let op,args = strip_preterm_comb p
 in
 (op = preterm_const `::`) & (length args = 2);;

%----------------------------------------------------------------------------%
% If (`v`,ty) is in schema_variables, then                                   %
%                                                                            %
%    add_type `v`  ---> (preterm_typed (preterm_var `v`) ty)                 %
%                                                                            %
% else                                                                       %
%                                                                            %
%    add_type `v`  ---> (preterm_var `v`)                                    %
%----------------------------------------------------------------------------%

let add_type v =
 preterm_typed(preterm_var v, lookup_schema_var v)
 ?
 preterm_var v;;

letrec add_types p =
 case p
  of (preterm_var v)       . (add_type v)
  |  (preterm_const c)     . p
  |  (preterm_comb(p1,p2)) . (preterm_comb(add_types p1, add_types p2))
  |  (preterm_abs(p1,p2))  . (preterm_abs(add_types p1, add_types p2))
  |  (preterm_typed(p1,ty)). (preterm_typed(add_types p1, ty))
  |  (preterm_antiquot t)  . p;;


%============================================================================%
% Preprocess applications "f x" to "f ^^ x", if "f" previously declared      %
% to have a type of the form ":(ty1#ty2)set".                                %
%============================================================================%

%----------------------------------------------------------------------------%
% is_set_fun_ty tests whether a type is of the form ":(ty1#ty2)set"          %
%----------------------------------------------------------------------------%

let is_set_fun_ty ty =
 (let op,args = dest_type ty
  in
  (op = `set`)      &
  (length args = 1) &
  (fst(dest_type(hd args)) = `prod`)
 ) ? false;;

%----------------------------------------------------------------------------%
% is_set_fun (preterm_var `f`) returns true if (`f`, ":(ty1#ty2)set") is in  %
% schema_variables, otherwise it returns false.                              %
%----------------------------------------------------------------------------%

let is_set_fun =
 fun (preterm_var v) . (is_set_fun_ty(lookup_schema_var v) ? false)
  |  _               . false;;

let mk_set_fun p1 p2 =
 preterm_comb (preterm_comb((preterm_const `^^`), p1), p2);;

%============================================================================%
% Routines for expanding schemas included in declarations.                   %
%============================================================================%

%----------------------------------------------------------------------------%
% add_import_decs                                                            %
%  "SCHEMA[u1 :: S1; ... ; um :: Sm][P1;...;Pp]"                             %
%  "[v1 :: T1; ... ; vn :: Tn]"                                              %
% --->                                                                       %
% "[u1 :: S1; ... ; um :: Sm; v1 :: T1; ... ; vn :: Tn]"                     %
%----------------------------------------------------------------------------%

let add_import_decs import decs2 =
 if not(is_schema import)
 then failwith `invalid schema import declaration`
 else
 let decs1,bdy1 = dest_schema import
 in
 let decsl1 = dest_preterm_list decs1
 and decsl2 = dest_preterm_list decs2
 in
 if not(intersect
         (map (get_dec_var) decsl1)
         (map (get_dec_var) decsl2) =
        [])
 then failwith `variable occurs in schema and in import declarations`
 else
 mk_preterm_list(decsl1 @ decsl2);;

%----------------------------------------------------------------------------%
% mk_schema_decs [imp1;...;impn] pm =                                        %
%  add_import_decs imp1 (...(add_import_decs impn pm)...)                    %
%----------------------------------------------------------------------------%

let mk_schema_decs = itlist add_import_decs;;

%----------------------------------------------------------------------------%
% add_import_body                                                            %
%  "SCHEMA[u1 :: S1; ... ; um :: Sm][P1; ... ;Pp]" "[Q1; ... ;Qq]"           %
%  --->  "P1 /\ ... /\ Pp /\ Q1 /\ ... /\ Qq"                                %
%----------------------------------------------------------------------------%

let add_import_body import bdy2 =
 if not(is_schema import)
 then failwith `invalid schema import declaration`
 else
 let decs1,bdy1 = dest_schema import
 in
 mk_preterm_list(dest_preterm_list bdy1 @ dest_preterm_list bdy2);;

%----------------------------------------------------------------------------%
% mk_schema_body [imp1;...;impn] pm =                                        %
%  add_import_body imp1 (...(add_import_body impn pm)...)                    %
%----------------------------------------------------------------------------%

let mk_schema_body = itlist add_import_body;;

%----------------------------------------------------------------------------%
% v :: S  --->  v' :: S                                                      %
%----------------------------------------------------------------------------%

let prime_dec pm = 
 let op,args = strip_preterm_comb pm
 in
 if not(is_preterm_const op            & 
        (dest_preterm_const op = `::`) & 
        (length args = 2))
 then failwith `prime_dec`
 else
 list_mk_preterm_comb(op,[prime_preterm_var(el 1 args);el 2 args]);;

%----------------------------------------------------------------------------%
% Test whether preterm_comb(p1,p2) is a conjunction.                         %
%----------------------------------------------------------------------------%

let is_schema_conj p1 p2 =
 (let p11,p12 = dest_preterm_comb p1
  in
  (dest_preterm_const p11 = `AND`)
 ) ? false;;


%============================================================================%
% Routines for `macroexpanding' schema operations.                           %
%============================================================================%

%----------------------------------------------------------------------------%
% Schema hiding:                                                             %
% hide_schema_vars                                                           %
%  "SCHEMA [u1 :: S1; ... ; um :: Sm] [B1; ... ;Bn]" ["v1";...;"vp"]         %
% --->                                                                       %
%  "SCHEMA [u1' :: S1; ... ; up' :: Sr]                                      %
%          [?v1 ... vp. B1 /\ ... /\ Bn]"                                    %
%                                                                            %
% where [u1';...;ur'] = subtract [u1;...;um] [v1;...;vp]                     %
%----------------------------------------------------------------------------%

let hide_schema_vars sc vl =
 if null vl
 then failwith `empty list of hidden variables`
 else
 let decs,bdy = dest_schema sc
 in
 let vl1 = intersect vl (preterm_frees bdy)
 in
 let decsl = dest_preterm_list decs
 in
 let decsl1 = 
  mapfilter 
   ((\(v,t). if mem v vl1 then (v,t) else fail) o dest_dec) 
   decsl
 in
 mk_schema
  (mk_preterm_list
    (filter (\d. not(mem (fst(dest_dec d)) vl)) decsl), 
   mk_preterm_list
    [list_mk_preterm_res_exists
     (decsl1,
      list_mk_preterm_conj(dest_preterm_list bdy))]);;

%----------------------------------------------------------------------------%
% Schema hiding:                                                             %
% mk_schema_hide                                                             %
%  "SCHEMA [u1 :: S1; ... ; um :: Sm] [B1; ... ;Bn]" "(v1;...;vp)"           %
% --->                                                                       %
%  "SCHEMA [u1' :: S1; ... ; up' :: Sp]                                      %
%          (?v1 ... vp. B1 /\ ... /\ Bn)"                                    %
%                                                                            %
% where [u1';...;up'] = subtract [u1;...;um] [v1;...;v9]                     %
%----------------------------------------------------------------------------%

let is_schema_hide p1 p2 =
 (let p11,p12 = dest_preterm_comb p1
  in
  (dest_preterm_const p11 = `HIDE`)
 ) ? false;;

let mk_schema_hide sc tup = 
 let sc_hide =
  hide_schema_vars sc (dest_preterm_tuple tup)
 in
 store_preterm_schema_pair
  (preterm_comb(preterm_comb(preterm_const `HIDE`,sc),tup),sc_hide);
 sc_hide;;

%----------------------------------------------------------------------------%
% mk_schema_pre "SCHEMA [u1 :: S1; ... ; um :: Sm] BL" hides all primed      %
% and output variables.                                                      %
%----------------------------------------------------------------------------%

let dest_plain_or_dashed dec = 
 let v,ty = dest_dec dec
 in
 if is_input v or is_output v then fail else v;;

%----------------------------------------------------------------------------%
% Test whether preterm_comb(p1,p2) is an application of "pre".               %
%----------------------------------------------------------------------------%

let is_schema_pre p1 p2 =
 (dest_preterm_const p1 = `pre`) ? false;;

let mk_schema_pre sc =
 let decs,bdy = dest_schema sc
 in
 let vl = map (fst o dest_dec) (dest_preterm_list decs)
 in
 let sc_pre =
  hide_schema_vars
   sc
   (filter (\v. is_dashed v or is_output v) vl)
 in
 store_preterm_schema_pair(preterm_comb(preterm_const `pre`,sc),sc_pre);
 sc_pre;;

%----------------------------------------------------------------------------%
% Compute signature of a schema.                                             %
%----------------------------------------------------------------------------%

let sig sc =
 (let op,[decs;bdy] = strip_comb sc
  in
  if op = "SCHEMA"
  then list_mk_conj(fst(dest_list decs))
  else fail)
 ? failwith `sig applied to a non-schema`;;

%----------------------------------------------------------------------------%
% Compute predicate of a schema.                                             %
%----------------------------------------------------------------------------%

let pred sc =
 (let op,[decs;bdy] = strip_comb sc
  in
  if op = "SCHEMA"
  then list_mk_conj(fst(dest_list bdy))
  else fail)
 ? failwith `pred applied to a non-schema`;;

%----------------------------------------------------------------------------%
% Store types of variables declared in a schema in schema_variables.         %
%----------------------------------------------------------------------------%

let is_schema_head p =
 (let p1,p2 = dest_preterm_comb p
  in
  ((dest_preterm_const p1 = `SCHEMA`) & is_preterm_list p2)
 ) ? false;;

let store_schema_variables decs =
 (let vdecs = filter is_dec (dest_preterm_list decs)
  in
  map (remember_type o preterm_to_term) vdecs; ()
 ) ? failwith `store_schema_variables`;;

%----------------------------------------------------------------------------%
% Expand out schemas included as declarations.                               %
%----------------------------------------------------------------------------%

%----------------------------------------------------------------------------%
% Split a preterm "[d1;...;dn]" into an ML list of the schema declarations   %
% (i.e. included schemas) and the preterm consisting of the list of          %
% the explicit variable declarations.                                        %
%                                                                            %
% Remember declared variable types in the global variable schema_variables.  %
%----------------------------------------------------------------------------%

let split_dec p =
 (let sdecs,vdecs = partition is_schema (dest_preterm_list p)
  in
  map is_schema sdecs;
  (sdecs, mk_preterm_list vdecs)
 ) ? failwith `undeclared or bad declaration in schema`;;

%----------------------------------------------------------------------------%
% "SCHEMA[schema_spec1;...;schema_specm;d1;...;dn] [B1;...;Bo]"              %
% --->                                                                       %
% (mk_schema                                                                 %
%  (mk_schema_decs [sc1;...;scm] "[d1 ; ... ;dn]",                           %
%   mk_schema_body [sc1;...;scm] "[B1; ... ; Bo]")                           %
%                                                                            %
% where d1,...,dn are the schema values denoted by                           %
% schema_spec1,...,schema_specm.                                             %
%----------------------------------------------------------------------------%

let mk_schema_construction(p,bdy) =
 let includes,dec = split_dec p
 in
 mk_schema
  (mk_schema_decs includes dec,
   mk_schema_body includes bdy);;

%----------------------------------------------------------------------------%
% Test whether preterm_comb(p1,p2) is an application of "theta".             %
%----------------------------------------------------------------------------%

let is_schema_theta p1 p2 =
 ((((is_preterm_const p1) & (dest_preterm_const p1 = `theta`)) or
   (dest_preterm_const(fst(dest_preterm_typed p1)) = `theta`)) & is_schema p2) 
 ? false;;

%----------------------------------------------------------------------------%
% theta (SCHEMA[v1' :: S1; ... ; vn' :: Sm] [B1; ... ;Bn]) =                 %
%  ((`vi1`,vi1'), ... ,(`vin`,vin'))                                         %
%                                                                            %
% where the order i1,...,in is obtained by sorting `v1`,...,`vn` with <<.    %
% The decoration may be empty, in which case:                                %
%                                                                            %
% theta (SCHEMA[v1 :: S1; ... ; vn :: Sm] [B1; ... ;Bn]) =                   %
%  ((`vi1`,vi1), ... ,(`vin`,vin))                                           %
%----------------------------------------------------------------------------% 

%----------------------------------------------------------------------------%
% `x` --> ``x``                                                              %
%----------------------------------------------------------------------------%

let add_quotes s = `\`` ^ s ^ `\``;;

let mk_theta sc =
 let decs,bdy = dest_schema sc
 in
 let l = 
  map 
   (\(v,ty). 
     (preterm_const(add_quotes(snd(iter_dest_dashed v))), 
      preterm_typed(preterm_var v,ty)))
   (map (dest_var o rand o rator o preterm_to_term) (dest_preterm_list decs))
 in
 let sc_theta = 
  mk_preterm_tuple(map mk_preterm_pair (sort (\((s1,v1),(s2,v2)). s1 << s2) l))
 in
 store_preterm_schema_pair(preterm_comb(preterm_const `theta`,sc), sc_theta);
 sc_theta;;

%----------------------------------------------------------------------------%
% Test whether preterm_comb(p1,p2) is an application of "DELTA".             %
%----------------------------------------------------------------------------%

let is_schema_delta p1 p2 =
 ((dest_preterm_const p1 = `DELTA`) & is_schema p2) ? false;;

%----------------------------------------------------------------------------%
% "S"  --->  "S AND dash S"                                                  %
%----------------------------------------------------------------------------%

set_flag(`preterm`,true);;

let preterm_handler = I;;
let delta_expansion_preterm = "sc AND (dash sc)";;
let preterm_handler = preterm_to_term;;

let delta_expansion sc =
 preterm_subst[sc, preterm_var `sc`]delta_expansion_preterm;;

%<
 preterm_comb((preterm_comb((preterm_const `AND`), sc)),
              preterm_comb((preterm_const `dash`), sc));;
>%

let mk_schema_delta sc =
 let sc_delta = delta_expansion sc
 in
 store_preterm_schema_pair(preterm_comb(preterm_const `DELTA`,sc),sc_delta);
 sc_delta;;

%----------------------------------------------------------------------------%
% Test whether preterm_comb(p1,p2) is an application of "XI".                %
%----------------------------------------------------------------------------%

let is_schema_xi p1 p2 =
 ((dest_preterm_const p1 = `XI`) & is_schema p2) ? false;;

%----------------------------------------------------------------------------%
% "S" --->  "SCHEMA [DELTA S] [theta(dash S) = theta S]"                     %
%----------------------------------------------------------------------------%

let preterm_handler = I;;
let xi_expansion_preterm = "SCHEMA [DELTA sc] [theta(dash sc) = theta sc]";;
let preterm_handler = preterm_to_term;;

%----------------------------------------------------------------------------%
% Substitute for either a variable or a constant.                            %
%----------------------------------------------------------------------------%

letrec preterm_var_or_const_subst l p =
 case p
  of (preterm_var v)       . fst(rev_assoc p l) ? p
  |  (preterm_const c)     . fst(rev_assoc p l) ? p
  |  (preterm_comb(p1,p2)) . preterm_comb
                              (preterm_var_or_const_subst l p1, 
                               preterm_var_or_const_subst l p2)
  |  (preterm_abs(p1,p2))  . if var_capture l p1 p2
                             then failwith `preterm_var_or_const_subst: variable capture`
                             else preterm_abs(p1, preterm_var_or_const_subst l p2)
  |  (preterm_typed(p1,ty)). preterm_typed(preterm_var_or_const_subst l p1,ty)
  |  (preterm_antiquot t)  . p;;

let xi_expansion sc =
 let theta_ty = ":bool -> ^(type_of(preterm_to_term(mk_theta sc)))"
 in
 preterm_var_or_const_subst
  [preterm_typed(preterm_const `theta`, theta_ty), preterm_const `theta`;
   sc,                                             preterm_var `sc`]
  xi_expansion_preterm;;

%<
 preterm_comb
  ((preterm_comb
     ((preterm_const `SCHEMA`),
      preterm_comb((preterm_comb((preterm_const `CONS`),
                                 preterm_comb((preterm_const `DELTA`), sc))),
                   preterm_const `NIL`))),
   preterm_comb
    ((preterm_comb
       ((preterm_const `CONS`),
        preterm_comb
         ((preterm_comb
            ((preterm_const `=`),
             preterm_comb((preterm_const `theta`),
                          preterm_comb((preterm_const `dash`), sc)))),
          preterm_comb((preterm_const `theta`), sc)))),
     preterm_const `NIL`));;
>%

let mk_schema_xi sc =
 let sc_xi = xi_expansion sc
 in
 store_preterm_schema_pair(preterm_comb(preterm_const `XI`,sc),sc_xi);
 sc_xi;;

%----------------------------------------------------------------------------%
% Test whether preterm_comb(p1,p2) is an application of "sig".               %
%----------------------------------------------------------------------------%

let is_schema_sig p1 p2 =
 (dest_preterm_const p1 = `sig`) ? false;;

let mk_sig sc =
 let decs,bdy = dest_schema sc
 in
 let vl = map (fst o dest_dec) (dest_preterm_list decs)
 in
 let sc_sig = list_mk_preterm_conj(dest_preterm_list decs)
 in
 store_preterm_schema_pair(preterm_comb(preterm_const `sig`,sc),sc_sig);
 sc_sig;;

%----------------------------------------------------------------------------%
% Test whether preterm_comb(p1,p2) is an application of "pred".              %
%----------------------------------------------------------------------------%

let is_schema_pred p1 p2 =
 (dest_preterm_const p1 = `pred`) ? false;;

let mk_pred sc =
 let decs,bdy = dest_schema sc
 in
 let vl = map (fst o dest_dec) (dest_preterm_list decs)
 in
 let sc_pred = list_mk_preterm_conj(dest_preterm_list bdy)
 in
 store_preterm_schema_pair(preterm_comb(preterm_const `pred`,sc),sc_pred);
 sc_pred;;

%----------------------------------------------------------------------------%
% mk_schema_dash "SCHEMA [u1 :: S1; ... um :: Sm] BL" dashes all variables   %
%----------------------------------------------------------------------------%

let is_schema_dash p1 p2 =
 (dest_preterm_const p1 = `dash`) ? false;;

let mk_schema_dash sc =
 let decs,bdy = dest_schema sc
 in
 let vl = map (fst o dest_dec) (dest_preterm_list decs)
 in
 preterm_subst(map (\v. (prime_preterm_var v, v)) vl)sc;;

%----------------------------------------------------------------------------%
% dash "SCHEMA [u1 :: S1; ... um :: Sm] BL" dashes all variables in a term   %
%----------------------------------------------------------------------------%

let dash sc =
 let (), [decs;bdy] = strip_comb sc
 in
 let vl = map (rand o rator) (fst(dest_list decs))
 in
 subst(map (\v. (prime_var v, v)) vl)sc;;

letrec iter_dash(n,sc) = if n=0 then sc else iter_dash(n-1,dash sc);;

%----------------------------------------------------------------------------%
% Expand dashed schema names.                                                %
%----------------------------------------------------------------------------%

let expand_schema_name v =
 term_to_preterm(lookup_schema_name v) 
 ? let (n,x) = iter_dest_dashed v
   in
   let tm = iter_dash(n,lookup_schema_name x)
   in
   store_schema_name v tm;
   term_to_preterm tm;;


%----------------------------------------------------------------------------%
% mk_schema_conj                                                             %
%  "SCHEMA [u1 :: S1; ... ; um :: Sm] [P1; ... ;Pp]"                         %
%  "SCHEMA [v1 :: T1; ... ; vn :: Tn] [Q1; ... ;Qq]"                         %
% --->                                                                       %
%  "SCHEMA [u1 :: S1;  ... ; um :: Sm;                                       %
%           v1':: T1'; ... ; vr':: Tr']                                      %
%          [P1; ... ;Pp; Q1; ... ;Qq]"                                       %
% where:                                                                     %
%                                                                            %
%  ["v1' :: T1'"; ... ; "vr' :: Tr'"] =                                      %
%  subtract ["v1 :: T1"; ... ;"vn :: Tn"] ["u1 :: S1"; ... ;"um :: Sm"]      %
%----------------------------------------------------------------------------%

let mk_schema_conj(sc1,sc2) =
 let decs1,bdy1 = (dest_schema sc1
                   ? failwith `first argument of AND not a schema`)
 and decs2,bdy2 = (dest_schema sc2
                   ? failwith `second argument of AND not a schema`)
 in
 let decsl1 = dest_preterm_list decs1
 and decsl2 = dest_preterm_list decs2
 in
 let sc_conj =
  mk_schema
   (mk_preterm_list(decsl1 @ subtract decsl2 decsl1), 
    mk_preterm_list(dest_preterm_list bdy1 @ dest_preterm_list bdy2))
 in
 store_preterm_schema_pair
  (preterm_comb(preterm_comb(preterm_const `AND`,sc1),sc2),sc_conj);
 sc_conj;;

%----------------------------------------------------------------------------%
% Test whether preterm_comb(p1,p2) is a disjunction.                         %
%----------------------------------------------------------------------------%

let is_schema_disj p1 p2 =
 (let p11,p12 = dest_preterm_comb p1
  in
  (dest_preterm_const p11 = `OR`)
 ) ? false;;

%----------------------------------------------------------------------------%
% mk_schema_disj                                                             %
%  "SCHEMA [u1 :: S1; ... ; um :: Sm] [P1; ... ;Pp]"                         %
%  "SCHEMA [v1 :: T1; ... ; vn :: Tn] [Q1; ... ;Qq]"                         %
% --->                                                                       %
%  "SCHEMA [u1 :: S1;  ... ; um :: Sm;                                       %
%           v1':: T1'; ... ; vr':: Tr']                                      %
%          [(P1 /\ ... /\ Pp) \/ (Q1 /\ ... /\ Qq)]"                         %
% where:                                                                     %
%                                                                            %
%  ["v1' :: T1'"; ... ; "vr' :: Tr'"] =                                      %
%  subtract ["v1 :: T1"; ... ;"vn :: Tn"] ["u1 :: S1"; ... ;"um :: Sm"]      %
%----------------------------------------------------------------------------%

let mk_schema_disj(sc1,sc2) =
 let decs1,bdy1 = (dest_schema sc1
                   ? failwith `first argument of OR not a schema`)
 and decs2,bdy2 = (dest_schema sc2
                   ? failwith `second argument of OR not a schema`)
 in
 let decsl1 = dest_preterm_list decs1
 and decsl2 = dest_preterm_list decs2
 in
 let sc_disj =
  mk_schema
   (mk_preterm_list(decsl1 @ subtract decsl2 decsl1), 
    mk_preterm_list
     [mk_preterm_disj
      (list_mk_preterm_conj(dest_preterm_list bdy1),
       list_mk_preterm_conj(dest_preterm_list bdy2))])
 in
 store_preterm_schema_pair
  (preterm_comb(preterm_comb(preterm_const `OR`,sc1),sc2),sc_disj);
 sc_disj;;

%----------------------------------------------------------------------------%
% Test whether preterm_comb(p1,p2) is an implication.                        %
%----------------------------------------------------------------------------%

let is_schema_imp p1 p2 =
 (let p11,p12 = dest_preterm_comb p1
  in
  (dest_preterm_const p11 = `IMPLIES`)
 ) ? false;;

%----------------------------------------------------------------------------%
% mk_schema_imp                                                              %
%  "SCHEMA [u1 :: S1; ... ; um :: Sm] [P1; ... ;Pp]"                         %
%  "SCHEMA [v1 :: T1; ... ; vn :: Tn] [Q1; ... ;Qq]"                         %
% --->                                                                       %
%  "SCHEMA [u1 :: S1;  ... ; um :: Sm;                                       %
%           v1':: T1'; ... ; vr':: Tr']                                      %
%          [(P1 /\  ... /\ Pp) ==> (Q1 /\ ... /\ Qq)]"                       %
% where:                                                                     %
%                                                                            %
%  ["v1' :: T1'"; ... ; "vr' :: Tr'"] =                                      %
%  subtract ["v1 :: T1"; ... ;"vn :: Tn"] ["u1 :: S1"; ... ;"um :: Sm"]      %
%----------------------------------------------------------------------------%

let mk_schema_imp(sc1,sc2) =
 let decs1,bdy1 = (dest_schema sc1
                   ? failwith `first argument of IMPLIES not a schema`)
 and decs2,bdy2 = (dest_schema sc2
                   ? failwith `second argument of IMPLIES not a schema`)
 in
 let decsl1 = dest_preterm_list decs1
 and decsl2 = dest_preterm_list decs2
 in
 let sc_imp =
  mk_schema
   (mk_preterm_list(decsl1 @ subtract decsl2 decsl1), 
    mk_preterm_list
     [mk_preterm_imp
      (list_mk_preterm_conj(dest_preterm_list bdy1),
       list_mk_preterm_conj(dest_preterm_list bdy2))])
 in
 store_preterm_schema_pair
  (preterm_comb(preterm_comb(preterm_const `IMPLIES`,sc1),sc2),sc_imp);
 sc_imp;;

%----------------------------------------------------------------------------%
% mk_schema_forall                                                           %
%  "SCHEMA [u1 :: S1; ... ; um :: Sm] [P1; ... ;Pp]"                         %
%  "SCHEMA [v1 :: T1; ... ; vn :: Tn] [Q1; ... ;Qq]"                         %
% --->                                                                       %
%  "SCHEMA [v1' :: T1; ... ; vp' :: Tr]                                      %
%          [!u1 ... um. (u1 :: S1) /\ ... /\ (um :: Sm) /\ P1 /\ ... /\ Pp   %
%                       ==> (Q1 /\ ... /\ Qq)]"                              %
%                                                                            %
% where {u1::S1, ... ,um::Sm} must be included in {v1::T1, ... ,vn::Tn}      %
% and                                                                        %
%                                                                            %
%    [v1'::T1; ... ;vp'::Tr] =                                               %
%     subtract [v1::T1; ... ;vn::Tn] [u1::S1; ... ;um::Sm]                   %
%----------------------------------------------------------------------------%

let is_schema_forall p1 p2 =
 (let p11,p12 = dest_preterm_comb p1
  in
  (dest_preterm_const p11 = `SCHEMA_FORALL`)
 ) ? false;;

let mk_schema_forall(sc1,sc2) =
 let decs1,bdy1 = dest_schema sc1
 and decs2,bdy2 = dest_schema sc2
 in
 let decsl1 = dest_preterm_list decs1
 and decsl2 = dest_preterm_list decs2
 in
 if not(decsl1 subset decsl2)
 then failwith `Universally quantified schema variable not declared in body`
 else
 let sc_forall =
  mk_schema
   (mk_preterm_list(subtract decsl2 decsl1),
    mk_preterm_list
     [list_mk_preterm_res_forall
       (map dest_dec decsl1,
        mk_preterm_imp(list_mk_preterm_conj(decsl1@[bdy1]),bdy2))])
 in
 store_preterm_schema_pair
  (preterm_comb
    (preterm_comb(preterm_const `SCHEMA_FORALL`,sc1),sc2),sc_forall);
 sc_forall;;

%----------------------------------------------------------------------------%
% mk_pred_forall                                                             %
%  "SCHEMA [u1 :: S1; ... ; um :: Sm] [P1; ... ;Pp]"                         %
%  "P"                                                                       %
% --->                                                                       %
%  "!u1 ... um. (u1 :: S1) /\ ... /\ (um :: Sm) /\ P1 /\ ... /\ Pp ==> P     % 
%                                                                            %
% mk_pred_forall                                                             %
%  "u :: S"                                                                  %
%  "P"                                                                       %
% --->                                                                       %
%  "!u. (u :: S) ==> P                                                       % 
%----------------------------------------------------------------------------%

let is_pred_forall p1 p2 =
 (let p11,p12 = dest_preterm_comb p1
  in
  (dest_preterm_const p11 = `FORALL`)
 ) ? false;;

%----------------------------------------------------------------------------%
% Quantified variable is a schema.                                           %
%----------------------------------------------------------------------------%

let mk_pred_forall1(sc,pm) =
 let decs,bdy = dest_schema sc
 in
 let decsl = dest_preterm_list decs
 in
 let sc_forall =
  list_mk_preterm_res_forall
   (map dest_dec decsl,
    mk_preterm_imp(list_mk_preterm_conj(decsl @ dest_preterm_list bdy),pm))
 in
 store_preterm_schema_pair
  (preterm_comb(preterm_comb(preterm_const `FORALL`,sc),pm),sc_forall);
 sc_forall;;

%----------------------------------------------------------------------------%
% Quantified variable is a declaration.                                      %
%----------------------------------------------------------------------------%

let mk_pred_forall2(dec,pm) =
 let v,ty = dest_dec dec
 in
 let sc_forall =
  mk_preterm_forall(v, mk_preterm_imp(dec,pm))
 in
 store_preterm_schema_pair
  (preterm_comb(preterm_comb(preterm_const `FORALL`,dec),pm),sc_forall);
 sc_forall;;

%----------------------------------------------------------------------------%
% Invoke mk_pred_forall1 or mk_pred_forall2 depending on type of argument.   %
%----------------------------------------------------------------------------%

let mk_pred_forall3 sc_dec pm =
 if is_schema sc_dec then mk_pred_forall1(sc_dec,pm)
 if is_dec sc_dec    then mk_pred_forall2(sc_dec,pm)
                     else failwith `Bad first argument to FORALL`;;

let list_mk_pred_forall(pml,pm) = 
 let sc_forall =
  itlist mk_pred_forall3 (dest_preterm_list pml) pm
 in
 store_preterm_schema_pair
  (preterm_comb(preterm_comb(preterm_const `FORALL`,pml),pm),sc_forall);
 sc_forall;;

let mk_pred_forall(pm1,pm2) =
 if is_preterm_list pm1
 then list_mk_pred_forall(pm1,pm2)
 else mk_pred_forall3 pm1 pm2;;

%----------------------------------------------------------------------------%
% mk_schema_exists                                                           %
%  "SCHEMA [u1 :: S1; ... ; um :: Sm] [P1; ... ;Pp]"                         %
%  "SCHEMA [v1 :: T1; ... ; vn :: Tn] [Q1; ... ;Qq]"                         %
% --->                                                                       %
%  "SCHEMA [v1' :: T1; ... ; vp' :: Tr]                                      %
%          [?u1 ... um. (u1 :: S1) /\ ... /\ (um :: Sm) /\                   %
%                       P1 /\ ... /\ Pp /\                                   % 
%                       Q1 /\ ... /\ Qq]"                                    %
%                                                                            %
% where {u1::S1, ... ,um::Sm} must be included in {v1::T1, ... ,vn::Tn}      %
% and                                                                        %
%                                                                            %
%    [v1'::T1; ... ;vp'::Tr] =                                               %
%     subtract [v1::T1; ... ;vn::Tn] [u1::S1; ... ;um::Sm]                   %
%----------------------------------------------------------------------------%

let is_schema_exists p1 p2 =
 (let p11,p12 = dest_preterm_comb p1
  in
  (dest_preterm_const p11 = `SCHEMA_EXISTS`)
 ) ? false;;

let mk_schema_exists(sc1,sc2) =
 let decs1,bdy1 = dest_schema sc1
 and decs2,bdy2 = dest_schema sc2
 in
 let decsl1 = dest_preterm_list decs1
 and decsl2 = dest_preterm_list decs2
 in
 if not(decsl1 subset decsl2)
 then failwith `Existentially quantified schema variable not declared in body`
 else
 let sc_exists =
 mk_schema
  (mk_preterm_list(subtract decsl2 decsl1),
   mk_preterm_list
    [list_mk_preterm_res_exists
      (map dest_dec decsl1,
       list_mk_preterm_conj
        (decsl1 @ dest_preterm_list bdy1 @ dest_preterm_list bdy2))])
 in
 store_preterm_schema_pair
  (preterm_comb
    (preterm_comb(preterm_const `SCHEMA_EXISTS`,sc1),sc2),sc_exists);
 sc_exists;;

%----------------------------------------------------------------------------%
% mk_pred_exists                                                             %
%  "SCHEMA [u1 :: S1; ... ; um :: Sm] [P1; ... ;Pp]"                         %
%  "P"                                                                       %
% --->                                                                       %
%  "?u1 ... um. (u1 :: S1) /\ ... /\ (um :: Sm) /\ P1 /\ ... /\ Pp /\ P      % 
%                                                                            %
% mk_pred_exists                                                             %
%  "u :: S"                                                                  %
%  "P"                                                                       %
% --->                                                                       %
%  "?u. (u :: S) /\ P                                                        % 
%----------------------------------------------------------------------------%

let is_pred_exists p1 p2 =
 (let p11,p12 = dest_preterm_comb p1
  in
  (dest_preterm_const p11 = `EXISTS`)
 ) ? false;;

%----------------------------------------------------------------------------%
% Quantified variable is a schema.                                           %
%----------------------------------------------------------------------------%

let mk_pred_exists1(sc,pm) =
 let decs,bdy = dest_schema sc
 in
 let decsl = dest_preterm_list decs
 in
 let sc_exists =
  list_mk_preterm_res_exists
   (map dest_dec decsl,
    list_mk_preterm_conj(decsl @ dest_preterm_list bdy @ [pm]))
 in
 store_preterm_schema_pair
  (preterm_comb(preterm_comb(preterm_const `EXISTS`,sc),pm),sc_exists);
 sc_exists;;

%----------------------------------------------------------------------------%
% Quantified variable is a declaration.                                      %
%----------------------------------------------------------------------------%

let mk_pred_exists2(dec,pm) =
 let v,ty = dest_dec dec
 in
 let sc_exists =
  mk_preterm_exists(v, mk_preterm_conj(dec,pm))
 in
 store_preterm_schema_pair
  (preterm_comb(preterm_comb(preterm_const `EXISTS`,dec),pm),sc_exists);
 sc_exists;;

%----------------------------------------------------------------------------%
% Invoke mk_pred_exists1 or mk_pred_exists2 depending on type of argument.   %
%----------------------------------------------------------------------------%

let mk_pred_exists3 sc_dec pm =
 if is_schema sc_dec then mk_pred_exists1(sc_dec,pm)
 if is_dec sc_dec    then mk_pred_exists2(sc_dec,pm)
                     else failwith `Bad first argument to EXISTS`;;

let list_mk_pred_exists(pml,pm) = 
 let sc_exists =
  itlist mk_pred_exists3 (dest_preterm_list pml) pm
 in
 store_preterm_schema_pair
  (preterm_comb(preterm_comb(preterm_const `EXISTS`,pml),pm),sc_exists);
 sc_exists;;

let mk_pred_exists(pm1,pm2) =
 if is_preterm_list pm1
 then list_mk_pred_exists(pm1,pm2)
 else mk_pred_exists3 pm1 pm2;;

%----------------------------------------------------------------------------%
% Test whether preterm_comb(p1,p2) is a sequence.                            %
%----------------------------------------------------------------------------%

let is_schema_seq p1 p2 =
 (let p11,p12 = dest_preterm_comb p1
  in
  (dest_preterm_const p11 = `SEQ`)
 ) ? false;;

% Some doodlings concerning possible formats for
  a pattern matching implementation of SEQ

let (s1,s2) = preterm_match "s1 SEQ s2" p
in
let State = extract_state_schema(s1,s2)
in
"EXISTS[State'']
       [SCHEMA_EXISTS
         [State']
         (SCHEMA[s1;State''][theta(State') = theta(State'')]) AND
        SCHEMA_EXISTS
         [State]
         (SCHEMA[s2;State''][theta(State) = theta(State'')])]"


"s1 SEQ s2" --> "EXISTS[State'']
                       [SCHEMA_EXISTS
                         [State']
                         (SCHEMA[s1;State''][theta(State') = theta(State'')]) AND
                        SCHEMA_EXISTS
                         [State]
                         (SCHEMA[s2;State''][theta(State) = theta(State'')])]"

%

%----------------------------------------------------------------------------%
% mk_schema_seq                                                              %
%  "SCHEMA [u1 :: S1; ... ; um :: Sm] [P1; ... ;Pp]"                         %
%  "SCHEMA [v1 :: T1; ... ; vn :: Tn] [Q1; ... ;Qq]"                         %
%  --->                                                                      %
%  "SCHEMA                                                                   %
%    [u1 :: S1; ... ; um :: Sm; v1 :: T1; ... ; vn :: Tn]                    %
%    (?uv1 ... uvr.                                                          %
%      P1[uv1,...,uvr/u1',...,ur'] /\ ... /\ Pp[uv1,...,uvr/u1',...,ur'] /\  %
%      Q1[uv1,...,uvr/v1,...,vr]   /\ ... /\ Qq[uv1,...,uvr/v1,...,vr])"     %
%                                                                            %
% where (following page 147 of Potter, Sinclair and Till):                   %
%                                                                            %
%    (a) The subsets of {u1 :: S1,...,um :: Sm} and                          %
%        {v1 :: T1,...,vn :: Tn} that consist of "dashed" and "plain"        %
%        variables are identical. Input and output variables are             %
%        considered neither plain nor dashed.                                %
%        uv1,...,uvp are the plain/ashed variables.                          %
%                                                                            %
%    (b) No type clashes in the input and output variables.                  %
%                                                                            %
%    (c) u1',...,ur' are the dashed variables in the first schema            %
%                                                                            %
%    (d) vi,...,vr are the plain variables in the second schema.             %
%----------------------------------------------------------------------------%

let mk_schema_seq(sc1,sc2) =
 let decs1,bdy1 = dest_schema sc1
 and decs2,bdy2 = dest_schema sc2
 in
 let decsl1 = dest_preterm_list decs1
 and decsl2 = dest_preterm_list decs2
 in
 let shvarsl1 = mapfilter dest_plain_or_dashed decsl1
 and shvarsl2 = mapfilter dest_plain_or_dashed decsl2
%< Need to add check corresponding to (b)
 and ivarsl1  = mapfilter dest_input           decsl1
 and ivarsl2  = mapfilter dest_input           decsl2
 and ovarsl1  = mapfilter dest_output          decsl1
 and ovarsl2  = mapfilter dest_output          decsl2
>%
 in
 let prime_twice = prime_preterm_var o prime_preterm_var
 in
 if not(set_equal shvarsl1 shvarsl2)
 then failwith `attempt to compose incompatible schemas`
 else
 let exist_quant_vars = mapfilter dest_plain decsl1
 and primed_exist_quant_res_vars = 
  mapfilter 
   (\p. let v,t = dest_dec p in if is_plain v then (prime_twice v,t) else fail) 
   decsl1
 in
 let sc_seq =
  mk_schema
   (mk_preterm_list(decsl1 @ subtract decsl2 decsl1), 
    mk_preterm_list
     [list_mk_preterm_res_exists
      (primed_exist_quant_res_vars,
       list_mk_preterm_conj
        (map
          (preterm_subst
           (map(\v.(prime_twice v, prime_preterm_var v))exist_quant_vars))
          (dest_preterm_list bdy1)
         @
         map
          (preterm_subst
           (map(\v.(prime_twice v, v))exist_quant_vars))
          (dest_preterm_list bdy2)))])
 in
 store_preterm_schema_pair
  (preterm_comb(preterm_comb(preterm_const `SEQ`,sc1),sc2),sc_seq);
 sc_seq;;


%============================================================================%
% Some proof utilities.                                                      %
%============================================================================%

let ASM_F_TAC = IMP_RES_TAC(DISCH_ALL(ASSUME "F"));;

let APPLY_ASMS_TAC f =
 POP_ASSUM_LIST
  (\assums. MAP_EVERY ASSUME_TAC (rev (map f assums)));;

let REWRITE_ASMS_TAC = APPLY_ASMS_TAC o REWRITE_RULE;;

let REWRITE_ALL_TAC thl = 
 REWRITE_ASMS_TAC thl THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC thl;;

let simp_thms = [SCHEMA;CONJL;FORALL_RESTRICT;EXISTS_RESTRICT];;

let SIMP_TAC =
 APPLY_ASMS_TAC (BETA_RULE o REWRITE_RULE simp_thms)
  THEN ASM_REWRITE_TAC simp_thms
  THEN BETA_TAC;;

%----------------------------------------------------------------------------%
% Remove restricted quantifications.                                         %
%----------------------------------------------------------------------------%

let REMOVE_RESTRICT_TAC =
 APPLY_ASMS_TAC (BETA_RULE o REWRITE_RULE[RES_FORALL;RES_EXISTS;FORALL_RESTRICT;EXISTS_RESTRICT])
  THEN REWRITE_TAC[RES_FORALL;RES_EXISTS;FORALL_RESTRICT;EXISTS_RESTRICT]
  THEN BETA_TAC;;

%----------------------------------------------------------------------------%
% RW_ASM_THEN ttac [f1;...;fn] f =                                           %
%  ASSUM_LIST(\thl. ttac(REWRITE_RULE[f1 thl;...;fn thl](f thl)))            %
%----------------------------------------------------------------------------%

let RW_ASM_THEN ttac fl f =
 ASSUM_LIST(\thl. ttac(REWRITE_RULE(map (\f. f thl) fl)(f thl)));;

%----------------------------------------------------------------------------%
% POP_ASSUMS n f = f[a1;...;an],                                             %
%                                                                            %
% where a1,...,an are the last n assumptions, which are popped.              %
%----------------------------------------------------------------------------%

letrec POP_ASSUMS n f =
 if n=0
 then ALL_TAC
 if n=1
 then POP_ASSUM(\th. f[th])
 else POP_ASSUM(\th. POP_ASSUMS (n-1) (\l. f (th.l)));;

letrec ITER n (tac:tactic)  = 
 if n < 0 then failwith `ITER`
 if n = 0 then ALL_TAC 
          else tac THEN ITER (n-1) tac;;

%----------------------------------------------------------------------------%
% Generalized beta-reduction (useful for reducing schema applications).      %
%----------------------------------------------------------------------------%

let GEN_BETA_TAC = CONV_TAC(DEPTH_CONV GEN_BETA_CONV);;

%----------------------------------------------------------------------------%
% Rule and Tactic for simplifying terms of the form "x IN {...|...}"         %
%----------------------------------------------------------------------------%

let SET_SPEC_RULE = CONV_RULE(DEPTH_CONV SET_SPEC_CONV)
and SET_SPEC_TAC  = CONV_TAC(DEPTH_CONV SET_SPEC_CONV);;

let simp sc =
 (let th1 = 
   (RAND_CONV(RATOR_CONV(RAND_CONV(UNWIND_AUTO_CONV THENC PRUNE_CONV))) 
     ORELSEC ALL_CONV) sc
  in
  let th2 =
   RIGHT_CONV_RULE
    (REWRITE_CONV([SCHEMA;CONJL;PAIR_EQ]) THENC REWRITE_CONV[]) 
    th1
  in
  let tyl = 
   filter 
    (\t. (fst(dest_const(rator(rator t))) = `::`) ? false)
    (conjuncts(rhs(concl th2)))
  in
  RIGHT_CONV_RULE(REWRITE_CONV(map ASSUME tyl))th2
 ) ? failwith `simp`;;

%----------------------------------------------------------------------------%
%  Resolution with filters.                                                  %
%  Code written for HOL90 by chou@cs.ucla.edu. Ported to HOL88 by MJCG.      %
%----------------------------------------------------------------------------%

let FILTER_STRIP_ASSUME_TAC (f : term -> bool) th =
  if (f (concl th)) then (STRIP_ASSUME_TAC th) else (ALL_TAC) ;;

let FILTER_IMP_RES_TAC (f : term -> bool) th g =
  IMP_RES_THEN (REPEAT_GTCL IMP_RES_THEN (FILTER_STRIP_ASSUME_TAC f)) th g
  ? ALL_TAC g ;;

let FILTER_RES_TAC (f : term -> bool) g =
  RES_THEN (REPEAT_GTCL IMP_RES_THEN (FILTER_STRIP_ASSUME_TAC f)) g
  ? ALL_TAC g ;;

let no_imp (tm) = not (free_in "==>" tm) ;;

let LITE_IMP_RES_TAC = FILTER_IMP_RES_TAC no_imp;;


%============================================================================%
% Outputting schemas.                                                        %
%============================================================================%

%----------------------------------------------------------------------------%
% Compress a term for printing by replacing schemas by their names in        %
% the global list schema_expansions.                                         %
%----------------------------------------------------------------------------%

new_flag(`fold_schemas`,true) 
? (print_newline();
   print_string `fold_schemas already declared`; 
   print_newline());;

let show_schemas b = not(set_flag(`fold_schemas`, not b));;

let bool_ty = ":bool";;

letrec fold_schemas tm =
 if (is_var tm or is_const tm)
  then tm
 if is_abs tm
  then 
  (let x,bdy = dest_abs tm
   in
   mk_abs(x, fold_schemas bdy))
  else
  (fold_schemas(lookup_schema_abbrev tm)
   ? 
   let tm1,tm2 = dest_comb tm
   in
   mk_comb(fold_schemas tm1, fold_schemas tm2));;

let print_schemas_term tm = 
 if get_flag_value `fold_schemas`
 then print_term(fold_schemas tm)
 else print_term tm;;

let print_schemas_thm th =
 if get_flag_value `fold_schemas`
 then (let asl,t = dest_thm th
       in
       print_all_thm(mk_thm(map fold_schemas asl, fold_schemas t)))
 else print_all_thm th;;

top_print print_schemas_term;;
top_print print_schemas_thm;;


%============================================================================%
% Declare sets.                                                              %
%============================================================================%

%----------------------------------------------------------------------------%
% sets `S1 S2 ... Sn` defines:                                               %
%                                                                            %
%    "S1 = (UNIV : *S1 set)"                                                 %
%    "S2 = (UNIV : *S2 set)"                                                 %
%        .                                                                   %
%        .                                                                   %
%        .                                                                   %
%    "S2 = (UNIV : *S2 set)"                                                 %
%----------------------------------------------------------------------------%

let sets str =
 let mk_ty tyname = ":^(mk_type(tyname^``,[]))set"
 in
 map 
  (\s. new_type 0 (s^``);
       new_definition
        (s, mk_eq(mk_var(s,mk_ty s), mk_const(`UNIV`,mk_ty s)));
       autoload_theory(`definition`,(current_theory()),s))
  (words str);
 ();;

%----------------------------------------------------------------------------%
% free_set `<name> = ...` expands to:                                        %
%                                                                            %
%    let <name>_Axiom = define_type `<name> = ...`;                          %
%    define "<name> = UNIV : <name> set"                                     %
%----------------------------------------------------------------------------%

letref free_set_name_buffer = ``;;

let make_new_free_set [] =
 let name = free_set_name_buffer
 and ty   = ":^(mk_type(free_set_name_buffer,[])) set"
 in
 new_definition
  (free_set_name_buffer,
   mk_eq(mk_var(name,ty), "UNIV : ^ty"));;

let free_set s =
 let name = hd(words s)
 in
 let_before(name^`_Axiom`, `make_new_structure_definition`, [name;s]);
 free_set_name_buffer := name;
 let_after(name, `make_new_free_set`, []);;


%============================================================================%
% Declare Z axioms.                                                          %
%============================================================================%

%----------------------------------------------------------------------------%
% declare_axiom "t[x1,...,xn]" delares "x1", ... , "xn" as new constants     %
% and then asserts |- t[x1,...,xn] as an axiom with name Axiom_<axiom_count> %
% and binds the axiom to this name in ML.                                    %
%----------------------------------------------------------------------------%

letref axiom_buffer = "T";;

let make_new_axiom[name] = new_axiom(name,axiom_buffer);;

let declare_axiom tm =
 (let vl = frees tm
  in
  map (new_constant o dest_var) vl;
  let pl = map (\v. (mk_const(dest_var v),v)) vl
  and ax_name = `Axiom_`^(string_of_int axiom_count)
  in
  (axiom_count := axiom_count+1;
   axiom_buffer := subst pl tm;
   let_after(ax_name, `make_new_axiom`, [ax_name]))
 ) ? failwith `declare_axiom`;;


%============================================================================%
% Declare schemas.                                                           %
%============================================================================%

%----------------------------------------------------------------------------%
% declare `name` "B"                                                         %
% parses "B", adds the name-schema pair to the global variables              %
% schema_expansions and binds `name` in ML to the expanded schema            %
%(if the flag `bind_schemas` is true (default false).                        %
%----------------------------------------------------------------------------%

new_flag(`bind_schemas`,false) ? ();;

letref schema_buffer = "T";;

let make_new_schema_declaration [] = schema_buffer;;

let declare name tm =
 store_schema_name name tm;
 if get_flag_value `bind_schemas`
 then (schema_buffer := tm;
       let_before(name, `make_new_schema_declaration`,[]);
       tm)
 else tm;;

%----------------------------------------------------------------------------%
% Macroexpand schema operations.                                             %
%----------------------------------------------------------------------------%

letrec expand_Z p =
 case p
  of (preterm_var v)       . (expand_schema_name v ? p)
  |  (preterm_const c)     . p
  |  (preterm_comb(p1,p2)) . (if is_set_fun p1
                              then mk_set_fun p1 (expand_Z p2)
                              else
                              ((if is_schema_head p1
                                then store_schema_variables(preterm_rand p1));
                               let p1e = expand_Z p1
                               and p2e = expand_Z p2
                               in
                               if is_schema p
                               then mk_schema_construction
                                     (preterm_rand p1e,p2e)
                               if is_schema_delta p1e p2e
                               then expand_Z(mk_schema_delta p2e)
                               if is_schema_xi p1e p2e
                               then expand_Z(mk_schema_xi p2e)
                               if is_schema_conj p1e p2e
                               then mk_schema_conj(preterm_rand p1e,p2e)
                               if is_schema_disj p1e p2e
                               then mk_schema_disj(preterm_rand p1e,p2e)
                               if is_schema_imp p1e p2e
                               then mk_schema_imp(preterm_rand p1e,p2e)
                               if is_schema_forall p1e p2e
                               then mk_schema_forall(preterm_rand p1e,p2e)
                               if is_pred_forall p1e p2e
                               then mk_pred_forall(preterm_rand p1e,p2e)
                               if is_schema_exists p1e p2e
                               then mk_schema_exists(preterm_rand p1e,p2e)
                               if is_pred_exists p1e p2e
                               then mk_pred_exists(preterm_rand p1e,p2e)
                               if is_schema_seq p1e p2e
                               then mk_schema_seq(preterm_rand p1e,p2e)
                               if is_schema_pre p1e p2e
                               then mk_schema_pre p2e
                               if is_schema_sig p1e p2e
                               then mk_sig p2e
                               if is_schema_theta p1e p2e
                               then mk_theta p2e
                               if is_schema_pred p1e p2e
                               then mk_pred p2e
                               if is_schema_dash p1e p2e
                               then mk_schema_dash p2e
                               if is_schema_hide p1e p2e
                               then mk_schema_hide p1e p2e
                               else preterm_comb(p1e,p2e)))
  |  (preterm_abs(p1,p2))  . (preterm_abs(p1, expand_Z p2))
  |  (preterm_typed(p1,ty)). (preterm_typed(expand_Z p1, ty))
  |  (preterm_antiquot t)  . p;;

%----------------------------------------------------------------------------%
% Setup input preprocessing.                                                 %
%----------------------------------------------------------------------------%

let preterm_handler p = 
 preterm_to_term(add_types(expand_Z p));;
