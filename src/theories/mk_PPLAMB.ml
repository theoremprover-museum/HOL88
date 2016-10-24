%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        mk_PPLAMB.ml                                          %
%                                                                             %
%     DESCRIPTION:      Set up stripped down PPLAMBDA theory for HOL.. This   %
%                       must be made using hol-lcf so that HOL versions of    %
%                       new_predicate etc. are not used.                      %
%                                                                             %
%     WRITES FILES:     PPLAMB.th                                             %
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
%     REVISION HISTORY: (none)                                                %
%=============================================================================%

new_theory `PPLAMB`;;

paired_new_type(2, `fun`);;

close_theory();;

quit();;
