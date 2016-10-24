%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        mk_ind.ml                                             %
%                                                                             %
%     DESCRIPTION:      Sets up the type individuals and the Axiom of Infinity%
%                                                                             %
%     PARENTS:          bool.th                                               %
%     WRITES FILES:     ind.th                                                %
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

% Load into hol-lcf %

new_theory `ind`;;

new_parent `bool`;;

paired_new_type(0, `ind`);;

loadt (concat ml_dir_pathname `hol-in-out`);;

new_axiom(`INFINITY_AX`, "?f:ind->ind. ONE_ONE f /\ ~(ONTO f)");;

close_theory();;

quit();;
