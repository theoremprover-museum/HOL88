
loadf `tools`;;
loadf `microc`;;
loadf `mut_eu`;;
loadf `mut_conv`;;

let define_mut_rec_type spec =

% Initial parse%
%%
let w = map words spec  in
let names = map hd w in
let old_rests = map (tl o tl) w in
let old_case_list = map (\x.strip_cases x []) old_rests  in
let const_list = map hd (flat old_case_list)  in
let subst_list = const_list com (map ($^ `SUM_`) const_list)  in
let rests = map (map (\x. snd((find (\y. fst y = x) subst_list)?
                              (``,x)))) old_rests  in
let case_list = map (\x.strip_cases x []) rests  in

% Generate composite type: (S=SUM_OF_A_B_C)%
%   `SUM_OF_A_B_C = A1 | A2 S S | B1 | B2 S | B3 S | C1 | C2 | C3 S S S`%
%%
let sum_type_name = `SUM_OF` ^ (foldl1 $^ (map ($^ `_`) names)) in

% Generate TAG type:%
%   `TAG_TYPE_SUM_OF_A_B_C = TAG_UNDEF_SUM_OF_A_B_C | TAG_A | TAG_B | TAG_C`    %
%%
let tag_type_name = `TAG_TYPE_`^sum_type_name  in
let tag_undef_name = `TAG_UNDEF_`^sum_type_name  in

% Define the types (may take a while)%
%%
let sum_type = 
  let sum_type_body = map (\x.if mem x names then sum_type_name else x)
                        (tl (flat (map (curry $. `|`) rests))) in
  let sum_type_spec = sum_type_name^(foldl1 $^ (map ($^ ` `)
                                                    (`=`.sum_type_body))) in
  define_type sum_type_name sum_type_spec  in

let tag_type =
  let tag_type_body = tag_undef_name.(map ($^ ` | TAG_`) names) in
  let tag_type_spec = tag_type_name^` = `^
                      implode(flat(map explode tag_type_body)) in
  define_type tag_type_name tag_type_spec  in

% Assign useful terms to variables %
let sum_type_term = mk_type(sum_type_name, [])  in
let tag_type_term = mk_type(tag_type_name, [])  in

let TAG_x_terms =
  let make_TAG_term x = mk_const(`TAG_`^x, tag_type_term) in
  map make_TAG_term names in


% Define TagOf_A_B_C%
%%
% First construct a list of pairs specifying the appropriate tags on elements%
%   of the sum type ie.%
% named_case_list = [(`TAG_A`, [[`A1`]; [`A2`; `B`; `C`]]);                     %
%                    (`TAG_B`, [[`B1`]; [`B2`; `B`]; [`B3`; `A`]]);             %
%                    (`TAG_C`, [[`C1`]; [`C2`]; [`C3`; `A`; `B`; `C`]])]        %

let named_case_list = (map ($^ `TAG_`) names) com case_list  in
%                                                                           %
% Now generate a predicate that selects subtypes from the sum type according%
%    to their tag.%
%                                                                          %
let TagOf_name = `TagOf_`^sum_type_name  in
%                                                                          %
% Most of the following is syntactic term creation and manipulation, which %
%   defines a predicate.                                                   %
%                                                                          %
let make_pred tag l =
  let TagOf_type_term = mk_type(`fun`, [sum_type_term; tag_type_term]) in
  let TagOf_term = mk_var(TagOf_name, TagOf_type_term) in

  if (length l) = 1 then 
    let lhs = mk_comb(TagOf_term, mk_const((hd l), sum_type_term)) in
    mk_eq (lhs, mk_const(tag, mk_type(tag_type_name, [])))
                          
  else
    let vars = genvars ((length l)-1) in
    let typed_vars = (tl l) com vars  in
    let todo = filter (\x. mem (snd x) names) (vars com (tl l)) in
    let make_inner_pred (x,name) = 
      let var = mk_var(x, sum_type_term) in
      let tag = mk_const(`TAG_`^name, tag_type_term) in
      let lhs = mk_comb(TagOf_term, var) in
      mk_eq(lhs, tag) in
    let inner_pred_list = map make_inner_pred todo in
%  This is just a little hack !!                                          %
    let inner_pred = if (null inner_pred_list)
                     then "T"
                     else list_mk_conj inner_pred_list in
    let vars_term = map (\(name,x). mk_var(x, (if (mem name names)
                                               then sum_type_term
                                               else mk_type(name, [])))) 
                        typed_vars in
    let lhs = mk_comb(TagOf_term,
                           list_mk_comb (string2term (hd l), vars_term)) in
    mk_eq(lhs,(mk_cond(inner_pred,
                       string2term tag,
                       string2term tag_undef_name))) in
%%
%                %                
let make_sub_conjuncts tag list =
  let pred_list = map (make_pred tag) list in
  list_mk_conj pred_list in

let conjunct_list = map (uncurry make_sub_conjuncts) named_case_list in
let conjunct = list_mk_conj conjunct_list in  
let sum_theorem = new_recursive_definition false sum_type TagOf_name conjunct in

% The glorious result :      %          
% |- (!v2 v1.%
%      TagOf_SUM_OF_A_B_C(A1 v2 v1) =%
%      (((TagOf_SUM_OF_A_B_C v2 = TAG_B) /\%
%        (TagOf_SUM_OF_A_B_C v1 = TAG_C)) => %
%       TAG_A | %
%       TAG_UNDEF_SUM_OF_A_B_C)) /\%
%    (TagOf_SUM_OF_A_B_C B1 = TAG_B) /\%
%    (!v1.%
%      TagOf_SUM_OF_A_B_C(B2 v1) =%
%      ((TagOf_SUM_OF_A_B_C v1 = TAG_B) => TAG_B | TAG_UNDEF_SUM_OF_A_B_C)) /\%
%    (!v1.%
%      TagOf_SUM_OF_A_B_C(B3 v1) =%
%      ((TagOf_SUM_OF_A_B_C v1 = TAG_C) => TAG_B | TAG_UNDEF_SUM_OF_A_B_C)) /\%
%    (!v3 v2 v1.%
%      TagOf_SUM_OF_A_B_C(C1 v3 v2 v1) =%
%      (((TagOf_SUM_OF_A_B_C v3 = TAG_A) /\%
%        (TagOf_SUM_OF_A_B_C v2 = TAG_B) /\%
%        (TagOf_SUM_OF_A_B_C v1 = TAG_C)) => %
%       TAG_C | %
%       TAG_UNDEF_SUM_OF_A_B_C)) /\%
%    (!v1.%
%      TagOf_SUM_OF_A_B_C(C2 v1) =%
%      ((TagOf_SUM_OF_A_B_C v1 = TAG_B) => TAG_C | TAG_UNDEF_SUM_OF_A_B_C))%
%%


% Now generate a function that takes a tag as an argument, and returns %
% a subtype-selecting predicate %
%%
let IsIt_name = `IsIt_`^sum_type_name in
let IsIt_type_term = make_fun tag_type_term (make_fun sum_type_term ":bool") in
let IsIt_name_term = mk_var(IsIt_name, IsIt_type_term) in
let tag_var = mk_var(`tag`, tag_type_term) in
let arg_var = mk_var(`IsIt_arg`, sum_type_term) in 

% IsIt_definition = 
  "IsIt_SUM_OF_nexp_bexp tag IsIt_arg =
     (TagOf_SUM_OF_nexp_bexp IsIt_arg = tag)"
%

let IsIt =
  let IsIt_definition =
    let lhs = list_mk_comb(IsIt_name_term, [tag_var; arg_var]) in
    let rhs = mk_eq(mk_comb(string2term TagOf_name, arg_var), tag_var) in
    mk_eq(lhs,rhs) in
  new_definition(IsIt_name, IsIt_definition) in

% Now we have the predicate:%
% |- !tag IsIt_arg. %
%     IsIt_SUM_OF_A_B_C_D_E tag IsIt_arg = %
%     (TagOf_SUM_OF_A_B_C_D_E IsIt_arg = tag) %

let dep_list = map (\(name,cases). (map (\c. ((name,c),tl c)) cases))
                   (names com case_list) in
letrec sort_dep_list = (\depl sdepl.
   let filter_pred = (\(_,dep). forall (\z. (not(mem z names)) or 
                                            (exists (\r. (fst r) = z) sdepl))
                                       dep) in
   let filtered_list = map (filter filter_pred) depl in
   let clean = filter ($not o null) in
   let types_found = map (fst o hd) (clean filtered_list) in
   let filtered_dep_list = filter (\x. not(exists (\y. (fst y) =
                                                       ((fst o fst o hd) x))
                                                  types_found))
                                  depl in
       if   ((null types_found) or (null filtered_dep_list))
       then sdepl @ types_found
       else sort_dep_list filtered_dep_list (sdepl @ types_found))  in
let sorted_dep_list = sort_dep_list dep_list []  in
% JUBIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIII !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!%

let IsIt_term = mk_const(IsIt_name, IsIt_type_term) in

% !!!!!!!!!!!!!!!!!!!!!! %
% ! Should be possible ! %
% ! to remove BETA_TAC ! %
% ! below...           ! %
% !!!!!!!!!!!!!!!!!!!!!! %

let def_type (name, arg_list) defined_types existence_thms =
  let tag_term = string2term (`TAG_`^name) in
  let x_term = mk_var(`x`, sum_type_term) in
    
 % "@x:SUM_TYPE.IsIt TAG_? x" %
 % "@x:?.T" %
    
  let mk_hilbert t =
    if (mem t names)
    then mk_select(x_term,
               list_mk_comb(IsIt_term, [string2term (`TAG_`^t); x_term]))
    else mk_select(mk_var(`x`,  mk_type(t, [])), "T") in
  let hilberts = map mk_hilbert (tl arg_list) in
  let constructed_hilberts =
                     list_mk_comb(string2term (hd arg_list), hilberts) in
  let exists_term = mk_exists(x_term,
                           list_mk_comb(IsIt_term, [tag_term; x_term])) in
  let simple_TAC = (EXISTS_TAC constructed_hilberts) THEN
                   (PURE_REWRITE_TAC [IsIt]) THEN
                   BETA_TAC THEN
                   (REWRITE_TAC [sum_theorem]) in

  let our_TAC = (PURE_REWRITE_TAC [EXISTS_DEF]) THEN
                BETA_TAC THEN
                (PURE_REWRITE_TAC [IsIt]) THEN
                BETA_TAC THEN
                DISCH_TAC THEN
                (ASM_REWRITE_TAC []) in
  let existence_thms =
    existence_thms@
    [TAC_PROOF(([], exists_term),
        ((simple_TAC THEN
% split conditional into cases %
         COND_CASES_TAC) THENL [
% rewrite to solve trivial case ie. x=x %
           REFL_TAC
         ;
% other case .. %
           (EVERY_ASSUM (UNDISCH_TAC o concl)) THEN
           (EVERY (map ASSUME_TAC existence_thms)) THEN
% for 3rd case need to iterate from here %
           (EVERY (map (\x. x THEN our_TAC)
                       (map (UNDISCH_TAC o concl) existence_thms)))
         ]   % end of tactic list, THENL %
         ORELSE (simple_TAC))) ]    in
    let pred = mk_comb(IsIt_term, tag_term) in
    let defined_types = defined_types@
                [new_type_definition(name, pred, hd (rev existence_thms))] in
    (defined_types, existence_thms) in

% end of def_type  %

letrec list_def_types sp_list ty_list th_list =
  if (null sp_list)
  then ty_list
  else let (defined_types,existence_thms) =
                               def_type (hd sp_list) ty_list th_list in
       list_def_types (tl sp_list) defined_types existence_thms in
 
letrec sort_back templ l =
  if null templ
  then []
  else let (this.rest) = templ in
       let (item,rest') = partition (\(n,_). n = this) l in
       if null item then failwith (`sort_back: Couldn't find item `^this) else
       if (length item) > 1 then failwith (`sort_back: Too many match `^this)
       else
         (hd item).(sort_back rest rest') in

let our_very_own_defined_types =
  let unsorted = list_def_types sorted_dep_list [] [] in
  let unsorted_names = map fst sorted_dep_list in
  let sorted = sort_back names (unsorted_names com unsorted) in
  map snd sorted in

let expanded_defs = map EXPAND_TY_DEF our_very_own_defined_types  in
let type_isomorphisms = map define_new_type_isomorphisms expanded_defs  in


% -------------------------------------- %
% | Conversion to remove lambdas has   | %
% | progressed to about here           | %
% -------------------------------------- %

letrec list_make_fun_type t l =
  letrec inner_mk_type l =
    if (null l)
    then mk_type(t,[])
    else make_fun (mk_type(hd l,[])) (inner_mk_type (tl l)) in
  inner_mk_type l in

let our_very_own_constants =
  let define_it x (name.l) =
    let types = map (\x. mk_type(x,[])) l in
    let var_terms = (make_vars `v` `` types) com l in
    let parm_list = map (\(t,n). if (mem n names)
                                 then mk_comb(string2term(`REP_`^n), t)
                                 else t)
                        var_terms in
    let rhs = mk_comb(string2term (`ABS_`^x),
                      list_mk_comb(string2term (`SUM_`^name), parm_list)) in
    let lhs = list_mk_comb(mk_var(name, list_make_fun_type x l),
                           map fst var_terms) in
    new_definition(name, mk_eq(lhs, rhs)) in
  flat (map (\x. map (define_it (fst x)) (snd x)) (names com old_case_list)) in
    
                  
% our_very_own_constants =  %
% [|- C = (\v1. ABS_nexp(tmp_C v1)); %
%  |- PLUS = (\v2 v1. ABS_nexp(tmp_PLUS(REP_nexp v2)(REP_nexp v1))); %
%  |- HVIS = %
%     (\v3 v2 v1. %
%       ABS_nexp(tmp_HVIS(REP_bexp v3)(REP_nexp v2)(REP_nexp v1))); %
%  |- TRUE = ABS_bexp tmp_TRUE; %
%  |- FALSE = ABS_bexp tmp_FALSE; %
%  |- NAND = (\v2 v1. ABS_bexp(tmp_NAND(REP_bexp v2)(REP_bexp v1))); %
%  |- LEQ = (\v2 v1. ABS_bexp(tmp_LEQ(REP_nexp v2)(REP_nexp v1)))] %
% : thm list %
% %

%
#sum_type in
|- !f0 f1 f2 e0 e1 f3 f4.
    ?! fn.
     (!n. fn(tmp_C n) = f0 n) /\
     (!S' S''. fn(tmp_PLUS S' S'') = f1(fn S')(fn S'')S' S'') /\
     (!S' S'' S'''.
       fn(tmp_HVIS S' S'' S''') = f2(fn S')(fn S'')(fn S''')S' S'' S''') /\
     (fn tmp_TRUE = e0) /\
     (fn tmp_FALSE = e1) /\
     (!S' S''. fn(tmp_NAND S' S'') = f3(fn S')(fn S'')S' S'') /\
     (!S' S''. fn(tmp_LEQ S' S'') = f4(fn S')(fn S'')S' S'')
     
%

% ":*nexp+*bexp+one" %
let star_sumtype_types =
  map (\x. mk_vartype (`*`^x)) names in

% For debugging TAC_PROOF's %
% let m s t g = print_string (s^`...`); print_goal g; let r=t g in message `done`; r  in %

let PRINT_TAC s1 s2 g =
  print_string s1; print_newline();
  ([g], (\x. print_string s2; print_newline(); hd x)) in

% let NL = `` in %


let constructors = map string2term const_list in

let sum_constructors = map (string2term o (\x.`SUM_`^x)) const_list in
        
let type_terms = map (\x.mk_type(x,[])) names in

let star_sumtype_type =
  foldr (\x.\y. mk_type(`sum`, [x;y])) ":one" star_sumtype_types in
  

% OUTR^n p %
letrec make_outr n p =
  if n=0
  then (p,type_of p)
  else 
    let (inner,t1) = make_outr (n-1) p in
    let (_,[_;t2])=dest_type t1 in
    (mk_comb(mk_const(`OUTR`,make_fun t1 t2),inner), t2) in

%
ISL p
ISR p /\ ISL(OUTR p)
ISR p /\ ISR(OUTR p) /\ ISL(OUTR(OUTR p))
...
%
%
let make_is_star_term n p =
  let (t1.terms) = map (\x. make_outr x p) (numbers n) in
  let conjuncts =
    (mk_comb(mk_const(`ISL`, make_fun (snd t1) ":bool"),fst t1)).
    (map (\(te,ty). mk_comb(mk_const(`ISR`, make_fun ty ":bool"),te)) terms) in
  list_mk_conj (rev conjuncts) in
%

let make_is_star_term n p =
  let (terms,t1) = chop_last(map (\x. make_outr x p) (upto 0 n)) in
  let conjuncts =
    (mk_comb(mk_const(`ISL`, make_fun (snd t1) ":bool"),fst t1)).
    (map (\(te,ty). mk_comb(mk_const(`ISR`, make_fun ty ":bool"),te)) terms) in
  list_mk_conj conjuncts in

let is_star_x =
  let is_star_names = map ($^ `is_star_`) names in
  let p = mk_var(`p`, star_sumtype_type) in
  let lhss =
    map (\x. mk_comb( mk_var(x, make_fun star_sumtype_type ":bool"), p))
        is_star_names in
  let rhss =
    map (\x. make_is_star_term x p)
        (upto 0 ((length names)-1)) in
  let bodys = map2 mk_eq (lhss, rhss) in
  map2 new_definition (is_star_names, bodys) in

%
OUTL(p)
OUTL(OUTR(p))
OUTL(OUTR(OUTR(p)))
%
let star_sum2x =
  let star_sum2x_names = map ($^ `star_sum2`) names in
  let p = mk_var(`p`, star_sumtype_type) in
  let lhss =
    map (\(x,t). mk_comb(mk_var(x, make_fun star_sumtype_type t), p))
        (star_sum2x_names com star_sumtype_types) in
  let rhss =
    map (\x. 
         (\(e,t).
          let (_,[t1;_]) = dest_type t in
          (mk_comb(mk_const(`OUTL`, make_fun t t1),e)))
         (make_outr x p)
        )
        (upto 0 ((length names)-1)) in
  let bodys = map2 mk_eq (lhss, rhss) in
  map2 new_definition (star_sum2x_names, bodys) in

letrec make_inls psl =
  if null psl
  then ([],":one")
  else
    let ((p,t1).psl1) = psl in
    let (inls,t) = make_inls psl1 in
    let t2 = mk_type(`sum`, [t1; t]) in
    (((mk_comb(mk_const(`INL`, make_fun t1 t2), p)).
     (map (\x. mk_comb(mk_const(`INR`, make_fun t t2), x)) inls)), t2) in

%
INL p             : *a -> *a+*b+*c+one 
INR(INL p)        : *b -> *b+*c+one
INR(INR(INL p)))  : *c -> *c+one
%
let star_x2sum =
  let star_x2sum_names = map (\x. `star_`^x^`2sum`) names in
  let ps = map (\t. mk_var(`p`, t)) star_sumtype_types in
  let lhss =
    map (\((x,t),p). mk_comb(mk_var(x, make_fun t star_sumtype_type), p))
        (star_x2sum_names com star_sumtype_types com ps) in
  let rhss = fst (make_inls (ps com star_sumtype_types)) in
  let bodys = map2 mk_eq (lhss, rhss) in
  map2 new_definition (star_x2sum_names, bodys) in

letrec make_inr p l =
  if null l
  then (p,type_of p)
  else 
    let (inner,t) = make_inr p (tl l) in
    let t1 = mk_type(`sum`, [hd l;t]) in
    (mk_comb(mk_const(`INR`,make_fun t t1),inner), t1) in

%
INR^n one
%
let star_junk = 
  let lhs = mk_var(`star_junk`, star_sumtype_type) in
  let rhs = fst (make_inr "one" star_sumtype_types) in
  let body = mk_eq(lhs, rhs) in
  new_definition (`star_junk`, body) in


% ---------------------------------------- %

%
is_a p = IsIt TAG_a p
is_b p = IsIt TAG_b p
is_c p = IsIt TAG_c p
%

let is_x =
  let make_body (x,tag) = 
    let is_x = mk_var(`is_`^x, make_fun sum_type_term ":bool") in
    let p = mk_var(`p`, sum_type_term) in
    let lhs = mk_comb(is_x, p) in
    let rhs = list_mk_comb(IsIt_term, [tag;p]) in
    mk_eq(lhs,rhs) in
  let bodys = map make_body (names com TAG_x_terms) in
  map new_definition (names com bodys) in

let is_x_terms =
  map (\x. mk_const(`is_`^x, make_fun sum_type_term ":bool")) names in

let x_types =
  map (\x. mk_type(x, [])) names in

let sum2x =
  let make_body (x,t) = 
    let t1 = make_fun sum_type_term t in
    let name = `sum2`^x in
    let lhs = mk_var(name, t1) in
    let rhs = mk_const(`ABS_`^x, t1) in
    name, mk_eq(lhs,rhs) in
  let bodys = map make_body (names com x_types) in
  map new_definition bodys in

let x2sum =
  let make_body (x,t) = 
    let t1 = make_fun t sum_type_term in
    let name = x^`2sum` in
    let lhs = mk_var(name, t1) in
    let rhs = mk_const(`REP_`^x, t1) in
    name, mk_eq(lhs,rhs) in
  let bodys = map make_body (names com x_types) in
  map new_definition bodys in

% ------------------------------- %

%
c = ... | C a num b | ... ->
*_C_2_sum_*_C (f:num->*a->*b->a->b->c)
              (c1:num) (x1:*s) (x2:*s) (y1:s) (y2:s) =
  (is_*a x1 /\ is_*b x2 /\ is_a y1 /\ is_b y2) =>
   *_c2sum(f c1 (*_sum2a x1) (*_sum2b x2) (sum2a y1) (sum2b y2))
  | star_junk
%

%
Givet en constructor c:
 find parametertyper og resultattype
 sorter pr{definerede typer fra
 lav *parametertyper
 f:pr{definerede->*parametertyper->parametertyper->resultattype
 lav c'er med pr{definerede typer
 lav x'er med *parametertyper
 lav y'er med parametertyper
 lav pr{dikater for x'er og y'er
 lav conjunct af disse
 lav afbildninger for x'er og y'er
 lav *_(resultat)2sum(f c'er (afb. x'er) (afb. y'er))
 lav body
 definer
%

let def_constructor constructor =
  let (name, typ) = dest_const constructor in
  let l = strip_fun_type typ in
  let (parm_types, res_type) = chop_last l in
  let (parm_types', pre_types) = partition (\x. mem x x_types) parm_types in
  let tnames = map (fst o dest_type) parm_types' in
  let star_types = map make_star parm_types' in
  let f_type = foldr (\x.\y. make_fun x y)
                     (make_star res_type)
                     (star_types@pre_types@parm_types') in
  let f_term = mk_var(`f`, f_type) in
  let cs = make_vars `c` `` pre_types in
  let xs_types = replicate star_sumtype_type (length parm_types') in
  let xs = make_vars `x` `` xs_types in
  let cys_types = map (\x. if (mem x x_types) then sum_type_term else x)
                      parm_types in
  let cys = make_vars `y` `` cys_types in
  let ys_types = replicate sum_type_term (length parm_types') in
  let ys = make_vars `y` `` ys_types in
  let mk_predicate ((x,y),s) =
    let predx = mk_comb(mk_const(`is_star_`^s,
                                 make_fun star_sumtype_type ":bool"), x) in
    let predy = mk_comb(mk_const(`is_`^s,
                                 make_fun sum_type_term ":bool"), y) in
    predx,predy in
  let predicates = map mk_predicate (xs com ys com tnames) in
  let conj = 
    if null predicates
    then "T"
    else list_mk_conj ($@ (split predicates)) in
  let mk_map ((x,y),s) =
    let mapx = mk_comb(mk_const(`star_sum2`^s,
                                make_fun star_sumtype_type
                                         (mk_vartype(`*`^s))), x) in
    let mapy = mk_comb(mk_const(`sum2`^s,
                                make_fun sum_type_term (mk_type(s,[]))), y) in
    mapx, mapy in
  let maps = map mk_map (xs com ys com tnames) in
  let f_app = list_mk_comb (f_term, (\x,y.x@cs@y) (split maps)) in
  let res_type_name = fst(dest_type res_type) in
  let f_app_mapped = mk_comb(mk_const(`star_`^res_type_name^`2sum`,
                                      make_fun (mk_vartype(`*`^res_type_name))
                                               star_sumtype_type),
                             f_app) in
  let def_name = `star_`^name^`_to_sum_star_`^name in
  let lhs = list_mk_comb (mk_var(def_name,
                                 (foldr (\x.\y. make_fun x y)
                                        star_sumtype_type
                                        (f_type.(map type_of (xs@cs@ys))))),
                          (f_term.(xs@cs@ys))) in
  let rhs =
    if conj="T"
    then f_app_mapped
    else mk_cond (conj, f_app_mapped, mk_const(`star_junk`,
                                               star_sumtype_type)) in
  let body=mk_eq(lhs, rhs) in
  new_definition (def_name,body) in        

let star_x_to_sum_star_x = map def_constructor constructors in
  
let ost = GEN_ALL(CONJUNCT1 ((CONV_RULE EXISTS_UNIQUE_CONV) (SPEC_ALL sum_type))) in
let brie = EA_CONV (concl ost) in

let fn_def =
  let fn_name = `fn_`^sum_type_name in
  new_specification fn_name [(`constant`,fn_name)] (EQ_MP brie ost) in

let fn_rewrites = map GEN_ALL (CONJUNCTS(SPEC_ALL fn_def)) in




% Construct ... %
let (fn_constructor, fn_constr_term) =
  let types = map (\x. mk_type(x,[])) names in
  let typ_list = map (uncurry make_fun) (types com star_sumtype_types) in
  let hs = map (\(i,t). mk_var(`h`^(tok_of_int i), t))
               (counted typ_list) in
  let x = mk_var(`x`, sum_type_term) in
  let fn_cons_type = foldr make_fun star_sumtype_type
                                              (typ_list@[sum_type_term]) in
  let fn_cons_term = mk_var(`fn_constructor`, fn_cons_type) in
  let lhs = foldl (curry mk_comb) fn_cons_term (hs@[x]) in
  letrec make_cond l =
    if null l
    then mk_const(`star_junk`, star_sumtype_type) else
    let (h.rest) = l in
    let [t1;t2] = snd(dest_type(type_of h)) in
    let name = fst(dest_type t1) in
    let cond = mk_comb(mk_const(`is_`^name, make_fun sum_type_term ":bool"),
                       x) in
    let term =
      let star_x2sum = mk_const(`star_`^name^`2sum`,
                                make_fun t2 star_sumtype_type) in
      let sum2x = mk_const(`sum2`^name,make_fun sum_type_term t1) in
      foldr (curry mk_comb) x [star_x2sum;h;sum2x] in
    mk_cond(cond, term, (make_cond rest)) in
  let rhs = make_cond hs in
  let body = mk_eq(lhs,rhs) in
  new_definition(`fn_constructor`, body),
  mk_const(`fn_constructor`, fn_cons_type) in
  
  
% A utility function %
                
let simple_x_lemma =
  let make_body x =
    let x_type = mk_type(x,[]) in
    let a = mk_var(`a`,x_type) and
        n = mk_var(`n`,x_type) in
    let REP_x = mk_const(`REP_`^x, make_fun x_type sum_type_term) in
    n,mk_exists(a,mk_eq(mk_comb(REP_x,n),mk_comb(REP_x,a))) in
  let prove x =
    let (n,body) = make_body x in
    TAC_PROOF(([],body),(EXISTS_TAC n) THEN REFL_TAC) in
  map prove names in

let is_x_x2sum = 
  let make_body x =
    let x_type = mk_type(x,[]) in
    let x_term = mk_var(`x`, x_type) in
    let is_x = mk_const(`is_`^x, make_fun sum_type_term ":bool") in
    let x2sum = mk_const(x^`2sum`, make_fun x_type sum_type_term) in
    mk_forall(x_term, foldr1 (curry mk_comb) [is_x;x2sum;x_term]) in
  let prove (i,x) =
    TAC_PROOF(([],make_body x),
              GEN_TAC THEN
              (PURE_ONCE_REWRITE_TAC is_x) THEN
              (PURE_ONCE_REWRITE_TAC x2sum) THEN
              (PURE_ONCE_REWRITE_TAC (map (pick 2) type_isomorphisms)) THEN
              (FIRST (map MATCH_ACCEPT_TAC simple_x_lemma))) in
  map prove (counted names) in


let id_x =
  let make_body x =
    let x_type = mk_type(x,[]) in
    let x_term = mk_var(`x`, x_type) in
    let sum2x = mk_const(`sum2`^x, mk_type(`fun`,[sum_type_term;x_type])) in
    let x2sum = mk_const(x^`2sum`, mk_type(`fun`,[x_type;sum_type_term])) in
    mk_forall(x_term, mk_eq(foldr1 (curry mk_comb) [sum2x;x2sum;x_term],
                            x_term)) in
  let prove (i,x) =
    TAC_PROOF(([],make_body x),
              (REWRITE_TAC [pick i sum2x; pick i x2sum;
                            pick 5 (pick i type_isomorphisms)])) in
  map prove (counted names) in


let rep_tmp_eq_x =
  let make_body constructor =
    let (cname,ctyp) = dest_const constructor in
    let (types,dtype) = chop_last(strip_fun_type ctyp) in
    let name t = fst(dest_type t) in
    let x2sum_term = mk_const((name dtype)^`2sum`, make_fun dtype sum_type_term) in
    let vars = make_vars `x` `` types in
    let lhs = mk_comb(x2sum_term,list_mk_comb(constructor,vars)) in
    let make_term var =
      let typ = type_of var in
      if mem typ type_terms           % Predefined types %
      then let x2sum_term = mk_const((name typ)^`2sum`, make_fun typ sum_type_term) in
            mk_comb(x2sum_term,var)
      else var in
    let terms = map make_term vars in
    let SUM_types = map (\x.if (mem x type_terms)
                                 then sum_type_term else x) types in
    let SUM_c = mk_const(`SUM_`^cname,foldr make_fun sum_type_term SUM_types) in
    let rhs = list_mk_comb(SUM_c,terms) in
    ((pos dtype type_terms),cname),list_mk_forall(vars,mk_eq(lhs,rhs)) in
  let prove (i,constructor) =
    let ((typn,cname),body) = make_body constructor in
    TAC_PROOF(([],body),
              (REPEAT GEN_TAC) THEN
              (PURE_ONCE_REWRITE_TAC x2sum) THEN
              (PURE_ONCE_REWRITE_TAC [definition `-` cname]) THEN
              (PURE_ONCE_REWRITE_TAC [(GEN_ALL o SYM o SPEC_ALL)
                                (pick 6 (pick typn type_isomorphisms))]) THEN
              (PURE_ONCE_REWRITE_TAC [IsIt]) THEN
              (PURE_ONCE_REWRITE_TAC [pick_CONJ i sum_theorem]) THEN
              (PURE_ONCE_REWRITE_TAC (map ((PURE_ONCE_REWRITE_RULE [IsIt]) o
                                           (pick 2))
                                          type_isomorphisms)) THEN
              (PURE_ONCE_REWRITE_TAC simple_x_lemma) THEN
              (PURE_REWRITE_TAC [AND_CLAUSES]) THEN
              (PURE_ONCE_REWRITE_TAC [COND_CLAUSES]) THEN
              REFL_TAC) in
  map prove (counted constructors) in


let star_id_x =
  let make_body x =
    let typ = mk_vartype(`*`^x) in
    let x_term = mk_var(`x`, typ) in
    let star_sum2x_term = mk_const(`star_sum2`^x, make_fun star_sumtype_type typ) in
    let star_x2sum_term = mk_const(`star_`^x^`2sum`, make_fun typ star_sumtype_type) in
    let lhs = foldr1 (curry mk_comb) [star_sum2x_term;star_x2sum_term;x_term] in
    mk_forall(x_term,mk_eq(lhs,x_term)) in
  let prove (i,x) =
    TAC_PROOF(([],make_body x),
          (REWRITE_TAC [(pick i star_sum2x);
                        (pick i star_x2sum);
                        OUTL;OUTR])) in
  map prove (counted names) in

let tags_distinct = prove_constructors_distinct tag_type in

let lemma_star_x =
  let make_body x =
    let typ = mk_vartype(`*`^x) in
    let x_term = mk_var(`x`,typ) in
    let is_star_x = mk_const(`is_star_`^x,make_fun star_sumtype_type ":bool") in
    let star_x2sum = mk_const(`star_`^x^`2sum`,make_fun typ star_sumtype_type) in
    mk_forall(x_term, foldr1 (curry mk_comb) [is_star_x;star_x2sum;x_term]) in
  let prove (i,x) =
    TAC_PROOF(([],make_body x),
                  GEN_TAC THEN
                  (REWRITE_TAC [(pick i is_star_x);
                                (pick i star_x2sum);
                                ISL;ISR;OUTL;OUTR])) in
  map prove (counted names) in


let nice_pick_6_x =
  let make_body x =
    let typ = mk_type(x,[]) in
    let x_term = mk_var(`x`,sum_type_term) in
    let is_x = mk_const(`is_`^x,make_fun sum_type_term ":bool") in
    let lhs = mk_comb(is_x,x_term) in
    let x2sum = mk_const(x^`2sum`,make_fun typ sum_type_term) in
    let sum2x = mk_const(`sum2`^x,make_fun sum_type_term typ) in
    let rhs = mk_eq(foldr1 (curry mk_comb) [x2sum;sum2x;x_term], x_term) in
    mk_forall(x_term,mk_eq(lhs,rhs)) in
  let prove (i,x) =
    TAC_PROOF(([],make_body x),
                 (PURE_REWRITE_TAC [(pick i is_x);
                                    (pick i x2sum);
                                    (pick i sum2x)]) THEN
                 (ACCEPT_TAC (pick 6 (pick i type_isomorphisms)))) in
  map prove (counted names) in


let tags_distinct_sym =
  let conjs = CONJUNCTS tags_distinct in
  let RAND_SYM = CONV_RULE (RAND_CONV SYM_CONV) in
  let syms = map RAND_SYM conjs in
  conjs @ syms in

let x_lemmas =
  let make_body x (c,constr) =
    let (cname,ctype) = dest_const constr in
    let (types,dtype) = chop_last(strip_fun_type ctype) in
    let (cn,ct) = dest_const c in
    print_string `x_lemmas: `;
    print_string cn;
    print_string `, `;
    print_string x;
    print_newline();
    let (cts,cdt) = chop_last(strip_fun_type ct) in
    let name t = fst(dest_type t) in
    let vars = make_vars `x` `` types in
    let is_x_type = make_fun sum_type_term ":bool" in
    let is_x_term = mk_const(`is_`^x, is_x_type) in
    let lhs = mk_comb(is_x_term,list_mk_comb(constr,vars)) in
    let make_term (t,v) =
      let is_x_term = mk_const(`is_`^(name t),is_x_type) in
      mk_comb(is_x_term,v) in
    let filtered = filter (\(t,v). mem t type_terms) (cts com vars) in
    let rhs = if not ((name cdt) = x) then "F" else
              if null filtered then "T" else
              list_mk_conj (map make_term filtered) in
    list_mk_forall(vars,mk_eq(lhs,rhs)) in
  let prove x (c,constr) =
    TAC_PROOF(([], make_body x (c,constr)),
              (REPEAT GEN_TAC) THEN
              (PURE_ONCE_REWRITE_TAC is_x) THEN
              (PURE_ONCE_REWRITE_TAC [IsIt]) THEN
              (PURE_ONCE_REWRITE_TAC [sum_theorem]) THEN
              ((COND_CASES_TAC THENL [
                 (PURE_REWRITE_TAC (REFL_CLAUSE.tags_distinct_sym));
                 (PURE_REWRITE_TAC (REFL_CLAUSE.tags_distinct_sym))
              ]) ORELSE
              (PURE_REWRITE_TAC ([COND_CLAUSES;REFL_CLAUSE]@
                                 tags_distinct_sym)))) in
  map (\x. map (prove x) (constructors com sum_constructors)) names in



let sum_type_induction = prove_induction_thm sum_type in

let x_isn_y =
  let tags_thms = CONJUNCTS tags_distinct in
  let syms = map (CONV_RULE (RAND_CONV SYM_CONV)) tags_thms in
  let make_thm a b =
    let body =
      let x_term = mk_var(`x`, sum_type_term) in
      let make_is_x name =
        let is_x_term = mk_const(`is_`^name, make_fun sum_type_term ":bool") in
        mk_comb(is_x_term, x_term) in
      let lhs = mk_eq(make_is_x b, "T") in
      let rhs = mk_eq(make_is_x a, "F") in
      mk_forall(x_term, mk_imp(lhs, rhs)) in
    TAC_PROOF(([], body),
      GEN_TAC THEN
      (PURE_ONCE_REWRITE_TAC is_x) THEN
      (PURE_ONCE_REWRITE_TAC [IsIt]) THEN
      (PURE_ONCE_REWRITE_TAC [EQ_CLAUSES]) THEN
      (DISCH_THEN SUBST1_TAC) THEN
      (FIRST (map ACCEPT_TAC (tags_thms@syms)))) in
  letrec make_thms l =
    if null l
    then []
    else (map (make_thm (hd l)) (tl l))@(make_thms (tl l)) in
  make_thms names in



% Given a thm "A |- is_x a = T", return
     "A |- is_x a = T", "A |- is_x' a = F", ..." where
  the x' 's are all "lesser" types. Used when rewriting terms of the form:
  "is_x1 a => t1 | is_x2 a => t2 | ... | tn".
%

let make_rewrite_thms thm =
  let var = snd(dest_comb(fst(dest_eq(concl thm)))) in
  let thms = mapfilter (\x. MP (SPEC var x) thm) x_isn_y in
  thm.thms in

let is_x_x2sum_full = flat (map (make_rewrite_thms o EQT_INTRO o SPEC_ALL)
                                is_x_x2sum) in

let f_types =
  let make_type t =
    let (types,dtype) = chop_last(strip_fun_type t) in
    let (typs,pre) = partition (\x. mem x type_terms) types in
    let star_typs = map make_star typs in
    foldr (\x.\y. make_fun x y)
          (make_star dtype)
          (star_typs@pre@typs) in
  map (make_type o type_of) constructors in

let f_vars = make_vars `f` `` f_types in

let cond_equivalence_lemma =
  let (proof_help, body) =
    let h_vars = 
      let types = map (\t. make_fun t (make_star t)) type_terms in
      make_vars `h` `` types in
    let (proof_help1, lhs) =
      let make_term (constr,x) =
        let find_h typ = snd (find (\(t,h).t=typ) (type_terms com h_vars)) in
        let (cname,ctype) = dest_const constr in
        let (types,dtype) = chop_last(strip_fun_type ctype) in
        let vars = make_vars `x` `` types in
        let proof_help = map (fst o dest_type) types in
        let h = find_h dtype in
        let lhs = mk_comb(h,(list_mk_comb(constr,vars))) in
        let (filtered,pre) = partition (\x. mem (type_of x) type_terms) vars in
        let make_comb x = mk_comb(find_h (type_of x), x) in
        let rhs = list_mk_comb(x, (map make_comb filtered)@pre@filtered) in
        proof_help, list_mk_forall(vars,mk_eq(lhs,rhs)) in
      let (proof_help, terms) = split (map make_term (constructors com
                                                      f_vars)) in
      proof_help, list_mk_conj terms in
    let fn_constr = list_mk_comb(fn_constr_term, h_vars) in
    let (proof_help2, rhs) =
      let make_term (c,(constr,x)) =
        let (name,_) = dest_const c in
        print_string `rhs: `;
        print_string name;
        print_newline();
        let (cname,ctype) = dest_const constr in
        let (types,dtype) = chop_last(strip_fun_type ctype) in
        let vars = make_vars `x` `` types in
        let lhs = mk_comb(fn_constr, list_mk_comb(constr, vars)) in
        let star_x = string2term (`star_`^name^`_to_sum_star_`^name) in
        let (filtered,predefined) = partition ((curry $= sum_type_term) o
                                               type_of)
                                              vars in
        let rhs = list_mk_comb(star_x,
                          x.(map (curry mk_comb fn_constr) filtered)@predefined@filtered) in
        vars, list_mk_forall(vars, mk_eq(lhs,rhs)) in
      let l = (map make_term (constructors com
                              (sum_constructors com f_vars))) in
      let (proof_help, terms) = split l in
      proof_help, list_mk_conj terms in
    let proof_help = map2 combine (proof_help2,proof_help1) in
    proof_help, list_mk_forall(f_vars,
                               list_mk_forall(h_vars, mk_imp(lhs,rhs))) in

% For the proof: %

  let make_proof_part (i,l) =
    print_string `make_proof_part: Doing index `;
    print_int i;
    print_newline();
    let n = length l in
    let prefix = (REPEAT GEN_TAC) THEN
                 (PRINT_TAC ((tok_of_int i)^` Entering.`)
                            ((tok_of_int i)^` Done.`)) THEN
                 (PURE_REWRITE_TAC ([fn_constructor;
                                     (pick i star_x_to_sum_star_x)]@
                                    (map (pick i) x_lemmas))) in
    let inner =
      print_string `Doing inner`;
      print_newline();
      let tac1 = (PURE_REWRITE_TAC ([AND_CLAUSES;COND_CLAUSES]@
                                    star_id_x@lemma_star_x)) THEN
                 (((make_repeated_tactic (POP_ASSUM MP_TAC) n) THEN
                   (PURE_ONCE_REWRITE_TAC [EQ_CLAUSES]) THEN
                   (make_repeated_tactic DISCH_TAC n))
                                              ? ALL_TAC) in
      let make_imp_res_tac (x,thm) =
        let x_term = mk_var(`x`, sum_type_term) in
        let is_x = mk_const(`is_`^x, make_fun sum_type_term ":bool") in
        let is_x_x = mk_comb(is_x, x_term) in
        (IMP_RES_TAC (DISCH_ALL (SYM(EQ_MP (SPEC x_term thm)
                                           (ASSUME is_x_x))))) in
      let tac_list = map make_imp_res_tac (names com nice_pick_6_x) in
      let tac2 = foldl1 ($THEN) tac_list in
      let tac3 = (((PURE_ONCE_ASM_REWRITE_TAC []) THEN
                   (make_repeated_tactic (POP_ASSUM MP_TAC) n) THEN
                   (make_repeated_tactic (DISCH_THEN(ASSUME_TAC o SYM)) n))
                                                   ? ALL_TAC) THEN
                 (PURE_REWRITE_TAC
                   ([GEN_ALL(SYM(SPEC_ALL(pick i rep_tmp_eq_x)))]@id_x)) THEN
                 (PURE_ONCE_ASM_REWRITE_TAC []) THEN
                 REFL_TAC in
      tac1 THEN tac2 THEN tac3 in
    let postfix = (PURE_REWRITE_TAC [AND_CLAUSES;COND_CLAUSES]) THEN
                  REFL_TAC in
    letrec make_tac l =
      print_string `make_tac`;
      print_newline();
      if null l then inner else
      let (var,x).l1 = l in
      let inner_tac = make_tac l1 in
      let is_x_term =
        let is_x = mk_const(`is_`^x, make_fun sum_type_term ":bool") in
        mk_comb(is_x, var) in
      (DISJ_CASES_THEN (\x. SUBST_TAC(make_rewrite_thms x) THEN ASSUME_TAC x)
                       (SPEC is_x_term BOOL_CASES_AX)) THENL
      [inner_tac; postfix] in
    prefix THEN (make_tac l) in
  let tacs = map make_proof_part
            (counted (map (filter (\(v,x). mem x names)) proof_help)) in
  TAC_PROOF(([],body), (REPEAT STRIP_TAC) THENL tacs) in


let star_x_to_sum_star_x_f_terms = 
  let make_star_x_to_sum_star_x_term (name,f) =
    let types = strip_fun_type (type_of f) in
    let make_type t =
      if is_vartype t then star_sumtype_type else
      if mem (fst(dest_type t)) names then sum_type_term else
      t in
    let typs = map make_type types in
    let dtyp = foldr1 make_fun typs in
    let typ = make_fun (type_of f) dtyp in
    let term = mk_const(`star_`^name^`_to_sum_star_`^name, typ) in
    mk_comb(term, f) in
  let c_names = map (fst o dest_const) constructors in
  map make_star_x_to_sum_star_x_term (c_names com f_vars) in

let fn_term_without_exp = 
  let d_type = make_fun sum_type_term star_sumtype_type in
  let typs = map type_of star_x_to_sum_star_x_f_terms in
  let fn_SUM_type = foldr make_fun d_type typs in
  let fn_SUM_term = mk_const(`fn_`^sum_type_name, fn_SUM_type) in
  list_mk_comb(fn_SUM_term, star_x_to_sum_star_x_f_terms) in

let fn_term =
  let exp_term = mk_var(`exp`,sum_type_term) in
  mk_comb(fn_term_without_exp, exp_term) in

let FN =
  let exp_term = mk_var(`exp`,sum_type_term) in
  let d_type = make_fun sum_type_term star_sumtype_type in
  let FN_type = foldr make_fun d_type f_types in
  let FN_term = mk_var(`FN`, FN_type) in
  let lhs = list_mk_comb(FN_term, f_vars@[exp_term]) in
  let body = mk_eq(lhs,fn_term) in
  new_definition(`FN`, body) in

let FN_term = string2term `FN` in
let FN_fvars_term = list_mk_comb(FN_term,f_vars) in

let FN_rewrite_lemma = GEN_ALL(SYM(SPEC_ALL FN)) in


let lemma_that_Peter_says_will_solve_all_our_problems =
  let body =
    let x_term = mk_var(`x`, sum_type_term) in
    let make_conj xx =
      let is_x = mk_const(`is_`^xx, make_fun sum_type_term ":bool") in
      let lhs = mk_comb(is_x, x_term) in
      let is_star_x = mk_const(`is_star_`^xx, make_fun star_sumtype_type ":bool") in
      let fn_term = mk_comb(FN_fvars_term,x_term) in
      let rhs = mk_comb(is_star_x,fn_term) in
      mk_imp(lhs,rhs) in
    let conjs = map make_conj names in
    list_mk_forall(f_vars@[x_term],list_mk_conj conjs) in
  let do_vars_tac =
    (POP_ASSUM (\x. EVERY (map (ASSUME_TAC) (CONJUNCTS x)))) THEN
    (RES_THEN (SUBST1_TAC o EQT_INTRO)) THEN
    (REPEAT (POP_ASSUM (SUBST1_TAC o EQT_INTRO))) THEN
    (PURE_REWRITE_TAC [AND_CLAUSES]) THEN
    (PURE_ONCE_REWRITE_TAC [COND_CLAUSES]) in
  let inner_tac (fn_r,star_x) (a.asl,g) =
    (if a="F" then (UNDISCH_TAC a) THEN
                   (PURE_ONCE_REWRITE_TAC [IMP_CLAUSE2])
              else (PURE_ONCE_REWRITE_TAC [FN]) THEN
                   (PURE_ONCE_REWRITE_TAC [fn_r]) THEN
                   (PURE_ONCE_REWRITE_TAC [FN_rewrite_lemma]) THEN
                   (PURE_ONCE_REWRITE_TAC [star_x]) THEN
                   (if a="T" then ALL_TAC else do_vars_tac) THEN
                   (PURE_ONCE_REWRITE_TAC lemma_star_x))
    (a.asl,g) in
  let l = (transpose x_lemmas) com (fn_rewrites com star_x_to_sum_star_x) in
  let outer_tac (x_ls,ts) =
    (PRINT_TAC `Down` `Up`) THEN
    (REPEAT STRIP_TAC) THEN
    (POP_ASSUM (ASSUME_TAC o (PURE_ONCE_REWRITE_RULE x_ls))) THEN
    (inner_tac ts) in
  TAC_PROOF(([],body),
    (foldl1 ($THEN) (replicate GEN_TAC (length f_vars))) THEN
    (INDUCT_THEN sum_type_induction ASSUME_TAC) THENL
    (map outer_tac l)) in


let is_star_x_FN_x2sum =
  let make_body typ =
    let name = fst(dest_type typ) in
    let x_term = mk_var(`x`,typ) in
    let x2sum_term = mk_const(name^`2sum`, make_fun typ sum_type_term) in
    let is_term = mk_const(`is_star_`^name, make_fun star_sumtype_type ":bool") in
    let inner = mk_comb(is_term, mk_comb(FN_fvars_term,
                                         mk_comb(x2sum_term,x_term))) in
    x_term, list_mk_forall(f_vars@[x_term], inner) in
  let prove (is_x,typ) =
    let (x_term,body) = make_body typ in
    TAC_PROOF(([],body),
      (REPEAT GEN_TAC) THEN
      (MP_TAC (SPEC x_term is_x)) THEN
      (PURE_ONCE_REWRITE_TAC
            [lemma_that_Peter_says_will_solve_all_our_problems])) in
  map prove (is_x_x2sum com type_terms) in

let sum2x_preserves_uniqueness =
  let make_body name =
    let typ = mk_type(name,[]) in
    let styp = mk_vartype(`*`^name) in
    let ftyp = make_fun typ styp in
    let [h1;h2] = make_vars `h` `` [ftyp;ftyp] in
    let sum2x_type = make_fun sum_type_term typ in
    let sum2x = mk_const(`sum2`^name, sum2x_type) in
    let lhs =
      let o_typ = make_fun ftyp (make_fun sum2x_type (make_fun sum_type_term styp)) in
      let o_term = mk_const(`o`,o_typ) in
      let lhs = list_mk_comb(o_term,[h1;sum2x]) in
      let rhs = list_mk_comb(o_term,[h2;sum2x]) in
      mk_eq(lhs,rhs) in
    let rhs = mk_eq(h1,h2) in
    list_mk_forall([h1;h2], mk_imp(lhs,rhs)) in
  let prove name =
    print_string (`sum2x_preserves_uniqueness: `^name);
    print_newline();
    let body = make_body name in
    let tac (asl,g) =
      let (var,body) = dest_forall g in
      let x2sum_term = mk_const(name^`2sum`,
                                make_fun (mk_type(name,[])) sum_type_term) in
      let x2sum_x = mk_comb(x2sum_term, var) in
      (GEN_TAC THEN (POP_ASSUM (MP_TAC o (\x. AP_THM x x2sum_x)))) (asl,g) in
    TAC_PROOF(([], body),
      (REPEAT GEN_TAC) THEN 
      DISCH_TAC THEN
      (CONV_TAC FUN_EQ_CONV) THEN
      tac THEN
      (PURE_ONCE_REWRITE_TAC [o_DEF]) THEN
      BETA_TAC THEN
      (PURE_ONCE_REWRITE_TAC id_x) THEN
      (PURE_ONCE_REWRITE_TAC [IMP_CLAUSES])) in
  map prove names in

let star_x2sum_preserves_uniqueness =
  let make_body name =
    let var_type = make_fun (mk_type(name,[])) (mk_vartype(`*`^ name)) in
    let vars = make_vars `h` `` [var_type;var_type] in
    let x_term = mk_var(`x`, mk_type(name,[])) in
    let star_x2sum_term = mk_const(`star_`^name^`2sum`, make_fun (mk_vartype(`*`^ name)) star_sumtype_type) in
    let make_term v = mk_comb(star_x2sum_term, mk_comb(v,x_term)) in
    let [t1;t2] = map make_term vars in
    let lhs = mk_eq(t1,t2) in
    let make_term' v = mk_comb(v,x_term) in
    let [t1';t2'] = map make_term' vars in
    let rhs = mk_eq(t1',t2') in
    list_mk_forall(vars@[x_term], mk_imp(lhs,rhs)) in
  let prove name =
    let star_sum2x_term = mk_const(`star_sum2`^name, make_fun star_sumtype_type (mk_vartype(`*`^ name))) in
    TAC_PROOF(([],make_body name),
      (REPEAT GEN_TAC) THEN
      (DISCH_THEN (ACCEPT_TAC o
                   (PURE_ONCE_REWRITE_RULE star_id_x) o
                   (AP_TERM star_sum2x_term)))) in
  map prove names in


let fn_constructor_preserves_uniqueness = 
  let body =
    let make_types name =
      let t = make_fun (mk_type(name,[])) (mk_vartype(`*`^name)) in
      [t;t] in
    let vars = map (\(i,n).make_vars (`h`^(tok_of_int i)) `` (make_types n)) (counted names) in
    let make_fn_term vs = list_mk_comb(fn_constr_term,vs) in
    let [t1;t2] = map make_fn_term (transpose vars) in
    let lhs = mk_eq(t1,t2) in
    let ts = map (\[x;y].mk_eq(x,y)) vars in
    let rhs = list_mk_conj ts in
    list_mk_forall((flat vars),mk_imp(lhs,rhs)) in
  let my_tac (asl,g) =
    let (v,_) = dest_forall g in
    let (nam,typ) = dest_var v in
    let (tnam,_) = dest_type typ in
    let x2sum_term = mk_const(tnam^`2sum`, make_fun typ sum_type_term) in
    let spec_term = mk_comb(x2sum_term, v) in
    (GEN_TAC THEN
     (POP_ASSUM (MP_TAC o (SPEC spec_term)))) (asl,g) in
  TAC_PROOF(([],body),
    (REPEAT GEN_TAC) THEN
    (DISCH_THEN (MP_TAC o (CONV_RULE FUN_EQ_CONV))) THEN
    (PURE_ONCE_REWRITE_TAC [fn_constructor]) THEN
    DISCH_TAC THEN
    (REPEAT CONJ_TAC) THEN
    ((CONV_TAC FUN_EQ_CONV) THEN
     my_tac THEN
     (PURE_ONCE_REWRITE_TAC is_x_x2sum_full) THEN
     (PURE_REWRITE_TAC [COND_CLAUSES]) THEN
     (PURE_ONCE_REWRITE_TAC id_x) THEN
     (PURE_ONCE_REWRITE_TAC star_x2sum_preserves_uniqueness))) in

let spec_rule t =
  EQT_ELIM o
  (CONV_RULE ((dir_CONV `fa` BETA_CONV) THENC (dir_CONV `a` BETA_CONV))) o
  (\x. AP_THM (INST_TYPE [star_sumtype_type,":*"] x) t) o
  (CONV_RULE BETA_CONV) o
  (CONV_RULE (RATOR_CONV (pure_once_rewrite_CONV [FORALL_DEF]))) in
  
letrec specl_rule l thm = 
  if (null l)
  then thm 
  else specl_rule (tl l) (spec_rule (hd l) thm) in


let main_theorem =
  let body =
    let h_vars = 
      let types = map (\t. make_fun t (make_star t)) type_terms in
      make_vars `h` `` types in
    let inner =
      let make_term (constr,x) =
        let find_h typ = snd (find (\(t,h).t=typ) (type_terms com h_vars)) in
        let (_,ctype) = dest_const constr in
        let (types,dtype) = chop_last(strip_fun_type ctype) in
        let vars = make_vars `z` `` types in
        let h = find_h dtype in
        let lhs = mk_comb(h,(list_mk_comb(constr,vars))) in
        let (filtered,predefined) = partition (\x. mem (type_of x) type_terms)
                                              vars in
        let make_comb x = mk_comb(find_h (type_of x), x) in
        let rhs = list_mk_comb(x, (map make_comb filtered) @ predefined@filtered) in
        list_mk_forall(vars,mk_eq(lhs,rhs)) in
      let terms = map make_term (constructors com f_vars) in
      list_mk_conj terms in
    list_mk_forall(f_vars, list_mk_eu(h_vars, inner)) in
  let make_term name =
    let x2sum_term = mk_const(name^`2sum`, make_fun (mk_type(name,[])) sum_type_term) in
    let x_term = mk_var(`x`,mk_type(name,[])) in
    let x2sum_x = mk_comb(x2sum_term,x_term) in
    let FN_x2sum_x = mk_comb(FN_fvars_term, x2sum_x) in
    let star_sum2x = mk_const(`star_sum2`^name,
                              make_fun star_sumtype_type (mk_vartype(`*`^name))) in
    let inner = mk_comb(star_sum2x, FN_x2sum_x) in
    mk_abs(x_term, inner) in
  let make_TAC (th1,th2) =
    let tac1 = 
      ((PURE_ONCE_REWRITE_TAC [FN]) THEN
       (CONV_TAC (RATOR_CONV                    % Rewrite on LEFT side only %
                  (RAND_CONV
                   (ONCE_DEPTH_CONV
                    (REWRITES_CONV (mk_conv_net [fn_def])))))) THEN 
       (PURE_ONCE_REWRITE_TAC [FN_rewrite_lemma])) in
    let tac2 = 
      ((PURE_ONCE_REWRITE_TAC is_x_x2sum) THEN
       (PURE_ONCE_REWRITE_TAC is_star_x_FN_x2sum) THEN
       (PURE_REWRITE_TAC [AND_CLAUSES]) THEN
       (PURE_ONCE_REWRITE_TAC [COND_CLAUSES]) THEN
       (PURE_ONCE_REWRITE_TAC star_id_x) THEN
       (PURE_ONCE_REWRITE_TAC id_x) THEN
       REFL_TAC) in
    ((PRINT_TAC `Main, Existence: Entering case`
                `Main, Existence: Finishing case`) THEN
     (PURE_ONCE_REWRITE_TAC [th1]) THEN
     tac1 THEN
     (PURE_ONCE_REWRITE_TAC [th2]) THEN
     tac2) in
  let tactics = map make_TAC (rep_tmp_eq_x com star_x_to_sum_star_x) in
  let (x_vars, y_vars) =
    let make_type name =
      let t1 = mk_type(name,[]) in
      let t2 = mk_vartype(`*`^name) in
      make_fun t1 t2 in
    (make_vars `x` `` (map make_type names),
     make_vars `y` `` (map make_type names)) in
  TAC_PROOF(([],body),
    (REPEAT GEN_TAC) THEN
    (OUR_EXISTS_UNIQUE_TAC (length names)) THEN
    CONJ_TAC THENL [        % 2 subgoals, Existence %
      (foldl1 $THEN (map (EXISTS_TAC o make_term) names)) THEN
      (BETA_TAC THEN BETA_TAC) THEN % Yes, TWO times %
      ((REPEAT STRIP_TAC) THENL tactics)
    ;
      (REPEAT GEN_TAC) THEN             % Uniqueness %
      BETA_TAC THEN
      (DISCH_THEN ((uncurry (THEN:tactic->tactic->tactic)) o
                   (MP_TAC#MP_TAC) o
                   (CONJUNCT1#CONJUNCT2 o
                   (\x.x,x)))) THEN
      (DISCH_THEN (ASSUME_TAC o (MP (SPECL (f_vars@y_vars)
                                           cond_equivalence_lemma)))) THEN
      (DISCH_THEN (ASSUME_TAC o (MP (SPECL (f_vars@x_vars)
                                           cond_equivalence_lemma)))) THEN

      (MP_TAC ((CONV_RULE ((dir_CONV `fafa` BETA_CONV) THENC
                           (dir_CONV `faa` BETA_CONV)))
               (spec_rule (list_mk_comb(fn_constr_term, y_vars))
                 (spec_rule (list_mk_comb(fn_constr_term, x_vars))
                   (CONJUNCT2
                     (CONV_RULE EXISTS_UNIQUE_CONV
                                (specl_rule star_x_to_sum_star_x_f_terms
                                            sum_type))))))) THEN
      (PURE_ONCE_ASM_REWRITE_TAC []) THEN
      (REPEAT (POP_ASSUM (\x.ALL_TAC))) THEN
      (PURE_ONCE_REWRITE_TAC [REFL_CLAUSE]) THEN
      (PURE_REWRITE_TAC [FORALL_SIMP;AND_CLAUSES]) THEN
      (PURE_ONCE_REWRITE_TAC [IMP_CLAUSES]) THEN
      (MATCH_ACCEPT_TAC fn_constructor_preserves_uniqueness)
    ]) in

% Return the result %
main_theorem;;
