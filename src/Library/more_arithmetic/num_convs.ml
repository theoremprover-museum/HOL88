
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   FILE:         list_imec_tactics.ml                                       %
%   EDITOR:       Paul Curzon                                                %
%   DATE:         July 1991                                                  %
%   DESCRIPTION:  Some tactics and conversion for rewriting equalities and   %
%                 inequalities of naturals                                   %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   File:         list_imec_tactics.ml                                       %
%                                                                            %
%   Author:       Wim Ploegaerts                                             %
%                                                                            %
%   Organization: Imec vzw.                                                  %
%                 Kapeldreef 75                                              %
%                 3030 Leuven, Belgium                                       %
%                                                                            %
%   Date:         14-6-1990                                                  %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

                   %< several "translation" conversions >%
                        %< The same as for integers >%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%







let (NUM_LESS_EQ_PLUS_CONV, NUM_EQ_PLUS_CONV, NUM_LESS_PLUS_CONV) =

letrec PROTECT_GSPEC tml th =
    let wl,w = dest_thm th in
    if is_forall w then
	let tm = fst(dest_forall w) in
	let tm' = (mem tm tml) => (genvar (type_of tm)) | tm in
	PROTECT_GSPEC tml (SPEC tm' th)
    else th


in let PROTECT_PART_MATCH tml  partfn th =
    let pth = PROTECT_GSPEC tml (GEN_ALL th)  in
    let pat = partfn(concl pth) in
    let matchfn = match pat in
    \tm. INST_TY_TERM (matchfn tm) pth

in let PROTECT_REWRITE_CONV tml =
  set_fail_prefix `PROTECT_REWRITE_CONV`
     (PROTECT_PART_MATCH tml (fst o dest_eq))

in let NUM_TRANSLATION_LEQ_EQ = 
          ((GENL ["p:num";"m:num";"n:num"])
                    o SYM o SPEC_ALL) LESS_EQ_MONO_ADD_EQ

in let NUM_TRANSLATION_LESS_EQ = 
          ((GENL ["p:num";"m:num";"n:num"])
                   o SYM o SPEC_ALL) LESS_MONO_ADD_EQ

in let NUM_TRANSLATION_EQ_EQ = 
          ((GENL ["p:num";"m:num";"n:num"])
                   o SYM o SPEC_ALL) EQ_MONO_ADD_EQ

in

 ((\t. PROTECT_REWRITE_CONV [] 
			(SPEC t NUM_TRANSLATION_LEQ_EQ)),
  (\t. PROTECT_REWRITE_CONV [] 
			(SPEC t NUM_TRANSLATION_EQ_EQ)),
  (\t. PROTECT_REWRITE_CONV [] 
			(SPEC t NUM_TRANSLATION_LESS_EQ)));;






