%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        numconv.ml                                            %
%                                                                             %
%     DESCRIPTION:      Define the axiom scheme for numerals                  %
%                                                                             %
%     AUTHOR:           T. F. Melham (87.08.23)                               %
%                                                                             %
%     USES FILES:       assumes num.th as parent                              %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        University of Edinburgh                               %
%     COPYRIGHT:        University of Cambridge                               %
%     COPYRIGHT:        INRIA                                                 %
%                                                                             %
%     REVISION HISTORY: 90.05.06                                              %
%=============================================================================%

% --------------------------------------------------------------------- %
% num_CONV: axiom scheme for numerals					%
% --------------------------------------------------------------------- %

let num_CONV =
    let num = ":num" and SUC = "SUC" in
    \tm. let n = int_of_string(fst(dest_const tm)) ?
	         failwith `num_CONV: argument not a numeral` in
         if n<1 then failwith `num_CONV: argument less than 1` else
         let pre_n = mk_const(string_of_int (n-1),num) in
            fst(mk_thm([], mk_eq (tm,(mk_comb(SUC,pre_n)))),
    	    	RecordStep(NumConvStep tm));;


