% ===================================================================== %
% FILE		: compat.ml						%
% DESCRIPTION   : Compatability file for HOL version 2.0.  Loading this	%
% 		  file will make the examples in this directory work in	%
%		  version 2.0.						%
%									%
% AUTHOR	: Tom Melham						%
% DATE		: 01.09.92						%
% ===================================================================== %

let GSYM = CONV_RULE(ONCE_DEPTH_CONV SYM_CONV);;

let REWR_CONV = REWRITE_CONV;;

let load_library st =
    if (st = `ind_defs`) then loadf `ind-defs` else load_library st;;

let GEN_REWRITE_CONV =
    let RW_CONV net = \tm. FIRST_CONV (lookup_term net tm) tm in
    \(rewrite_fun:conv->conv) built_in_rewrites.
      let basic_net = mk_conv_net built_in_rewrites in
      \thl. rewrite_fun
                (RW_CONV (merge_term_nets (mk_conv_net thl) basic_net));;

let PURE_REWRITE_CONV = GEN_REWRITE_CONV TOP_DEPTH_CONV []
and REWRITE_CONV = GEN_REWRITE_CONV TOP_DEPTH_CONV basic_rewrites
and PURE_ONCE_REWRITE_CONV = GEN_REWRITE_CONV ONCE_DEPTH_CONV []
and ONCE_REWRITE_CONV = GEN_REWRITE_CONV ONCE_DEPTH_CONV basic_rewrites;;
