%****************************************************************************%
% FILE          : arith_cons.ml                                              %
% DESCRIPTION   : Constructor, destructor and discriminator functions for    %
%                 arithmetic terms.                                          %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 4th March 1991                                             %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 22nd June 1992                                             %
%****************************************************************************%

%============================================================================%
% Constructors, destructors and discriminators for +,-,*                     %
%============================================================================%

%----------------------------------------------------------------------------%
% mk_plus, mk_minus, mk_mult                                                 %
%----------------------------------------------------------------------------%

let mk_arith_op tok ftok =
 let num_ty = mk_type(`num`,[])
 in  let fun_ty = mk_type(`fun`,[num_ty;mk_type(`fun`,[num_ty;num_ty])])
 in  \(t1,t2). (mk_comb(mk_comb(mk_const(tok,fun_ty),t1),t2)
                ? failwith ftok);;

let mk_plus  = mk_arith_op `+` `mk_plus`
and mk_minus = mk_arith_op `-` `mk_minus`
and mk_mult  = mk_arith_op `*` `mk_mult`;;

%----------------------------------------------------------------------------%
% dest_plus, dest_minus, dest_mult                                           %
%----------------------------------------------------------------------------%

let dest_arith_op tok ftok =
 let num_ty = mk_type(`num`,[])
 in  let fun_ty = mk_type(`fun`,[num_ty;mk_type(`fun`,[num_ty;num_ty])])
 in  let check = assert (\c. dest_const c = (tok,fun_ty))
 in  \tm. (let ((_,c1),c2) = (((check # I) o dest_comb) # I) (dest_comb tm)
           in  (c1,c2)
           ? failwith ftok);;

let dest_plus  = dest_arith_op `+` `dest_plus`
and dest_minus = dest_arith_op `-` `dest_minus`
and dest_mult  = dest_arith_op `*` `dest_mult`;;

%----------------------------------------------------------------------------%
% is_plus, is_minus, is_mult, is_arith_op                                    %
%----------------------------------------------------------------------------%

let is_plus  = can dest_plus
and is_minus = can dest_minus
and is_mult  = can dest_mult;;

let is_arith_op =
 let num_ty = mk_type(`num`,[])
 in  let fun_ty = mk_type(`fun`,[num_ty;mk_type(`fun`,[num_ty;num_ty])])
 in  \tm. (type_of (rator (rator tm)) = fun_ty ? false);;

%============================================================================%
% Constructors, destructors and discriminators for <,<=,>,>=                 %
%============================================================================%

%----------------------------------------------------------------------------%
% mk_less, mk_leq, mk_great, mk_geq                                          %
%----------------------------------------------------------------------------%

let mk_num_reln tok ftok =
 let num_ty = mk_type(`num`,[])
 in  let fun_ty = mk_type(`fun`,[num_ty;mk_type(`fun`,[num_ty;bool_ty])])
 in  \(t1,t2). (mk_comb(mk_comb(mk_const(tok,fun_ty),t1),t2)
                ? failwith ftok);;

let mk_less  = mk_num_reln `<` `mk_less`
and mk_leq   = mk_num_reln `<=` `mk_leq`
and mk_great = mk_num_reln `>` `mk_great`
and mk_geq   = mk_num_reln `>=` `mk_geq`;;

%----------------------------------------------------------------------------%
% dest_less, dest_leq, dest_great, dest_geq                                  %
%----------------------------------------------------------------------------%

let dest_num_reln tok ftok =
 let num_ty = mk_type(`num`,[])
 in  let fun_ty = mk_type(`fun`,[num_ty;mk_type(`fun`,[num_ty;bool_ty])])
 in  let check = assert (\c. dest_const c = (tok,fun_ty))
 in  \tm. (let ((_,c1),c2) = (((check # I) o dest_comb) # I) (dest_comb tm)
           in  (c1,c2)
           ? failwith ftok);;

let dest_less  = dest_num_reln `<` `dest_less`
and dest_leq   = dest_num_reln `<=` `dest_leq`
and dest_great = dest_num_reln `>` `dest_great`
and dest_geq   = dest_num_reln `>=` `dest_geq`;;

%----------------------------------------------------------------------------%
% is_less, is_leq, is_great, is_geq, is_num_reln                             %
%----------------------------------------------------------------------------%

let is_less  = can dest_less
and is_leq   = can dest_leq
and is_great = can dest_great
and is_geq   = can dest_geq;;

let is_num_reln =
 let num_ty = mk_type(`num`,[])
 in  let fun_ty = mk_type(`fun`,[num_ty;mk_type(`fun`,[num_ty;bool_ty])])
 in  \tm. (type_of (rator (rator tm)) = fun_ty ? false);;

%============================================================================%
% Constructor, destructor and discriminator for SUC                          %
%============================================================================%

let mk_suc =
 let num_ty = mk_type(`num`,[])
 in  let fun_ty = mk_type(`fun`,[num_ty;num_ty])
 in  \t. (mk_comb(mk_const(`SUC`,fun_ty),t) ? failwith `mk_suc`);;

let dest_suc =
 let num_ty = mk_type(`num`,[])
 in  let fun_ty = mk_type(`fun`,[num_ty;num_ty])
 in  let check = assert (\c. dest_const c = (`SUC`,fun_ty))
 in  \tm. (let (_,c) = (check # I) (dest_comb tm) in c ? failwith `dest_suc`);;

let is_suc = can dest_suc;;

%============================================================================%
% Discriminators for numbers                                                 %
%============================================================================%

let is_num_const tm =
 dest_type (snd (dest_const tm)) = (`num`,[]) ? false;;

let is_zero tm = fst (dest_const tm) = `0` ? false;;

%============================================================================%
% Conversions between ML integers and numeric constant terms                 %
%============================================================================%

let int_of_term tm =
 (int_of_string (fst (dest_const tm))) ? failwith `int_of_term`;;

let term_of_int =
 let num_ty = mk_type(`num`,[])
 in  \n. (mk_const(string_of_int n,num_ty) ? failwith `term_of_int`);;

%============================================================================%
% Generation of a numeric variable from a name                               %
%============================================================================%

let mk_num_var =
 let num_ty = mk_type(`num`,[])
 in  \s. (mk_var(s,num_ty) ? failwith `mk_num_var`);;

%============================================================================%
% Functions to extract the arguments from an application of a binary op.     %
%============================================================================%

let arg1 = rand o rator
and arg2 = rand;;
