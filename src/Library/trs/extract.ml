% extract.ml                                            (c) R.J.Boulton 1990 %
%----------------------------------------------------------------------------%


% Function to take a term and return a triple:     %
% (<constants>,<free variables>,<bound variables>) %

% Set union and set difference are used to avoid generating repetitions in   %
% the lists derived. For function applications, the lists from the rator and %
% the rand can simply be joined by set union. For abstractions, the bound    %
% variable is removed from the free-variable list of the body, and is added  %
% to the bound-variable list of the body.                                    %

letrec get_ids t =

   % : (term -> (term list # term list # term list)) %

   if (is_const t) then ([t],[],[])
   if (is_var t)   then ([],[t],[])
   if (is_abs t)   then
     (let (bv,body) = dest_abs t
      in  let (cl,fvl,bvl) = get_ids body
          in  (cl,(subtract fvl [bv]),(union bvl [bv]))
     )
   if (is_comb t)  then
     (let (a,b) = dest_comb t
      in  let (cla,fvla,bvla) = get_ids a
          and (clb,fvlb,bvlb) = get_ids b
          in  (union cla clb,union fvla fvlb,union bvla bvlb)
     )
   else fail;;


% Functions to extract components from the get_ids triple %

let get_consts t = (fst o get_ids) t;;

   % : (term -> term list) %


let get_freevars t = (fst o snd o get_ids) t;;

   % : (term -> term list) %


let get_boundvars t = (snd o snd o get_ids) t;;

   % : (term -> term list) %


% Function to obtain a list of the types which occur in a term %

% The lists of constants, free-variables and bound-variables are        %
% concatenated. The resulting identifiers are converted to their types, %
% and then any repetitions are removed.                                 %

let get_types t =

   % : (term -> type list) %

   let (cl,fvl,bvl) = get_ids t
   and get_typ t = snd (dest_const t ? dest_var t)
   in  remove_rep (map get_typ (cl @ fvl @ bvl));;


%--------------------------------------------------------------------------%


% Function which applied to a HOL type returns true if the type is of the %
% form ":*..." or ":op", otherwise false is returned.                     %

let is_primtype typ = (null (snd (dest_type typ))) ? true;;

   % : (type -> bool) %


% Function which applied to a HOL type returns a list containing simply %
% the type itself if it is `primitive' or the types from which it is    %
% constructed otherwise.                                                %

let subtypes typ =

   % : (type -> type list) %

   if (is_primtype typ)
   then [typ]
   else (snd (dest_type typ));;


% Function to break-up a type into its `primitive' types %

% The function uses the predicate is_primtype, defined above. If the     %
% type is not `primitive', a list of the component types is obtained, to %
% which the function is applied recursively. The resulting list of lists %
% is then `flattened' to give a list of `primitive' types, from which    %
% any repetitions are removed.                                           %

letrec prim_subtypes typ =

   % : (type -> type list) %

   if (is_primtype typ)
   then [typ]
   else (remove_rep o flat o (map prim_subtypes) o subtypes) typ;;


% Function to obtain a list of the `primitive' types occurring in a term %

% A list of the types occurring in the term is obtained. Each of these %
% types is converted to a list of its `primitive' types. The resulting %
% list of lists is then `flattened', and any repetitions are removed.  %

let get_primtypes t =

   % : (term -> type list) %

   (remove_rep o flat o (map prim_subtypes) o get_types) t;;


% Function to obtain a list of the `primitive' polymorphic types in a term %

let get_primvartypes t = filter is_vartype (get_primtypes t);;

   % : (term -> type list) %


%----------------------------------------------------------------------------%
