
%----------------------------------------------------------------------------%
% startSW.ml :  Load this file from HOL using                                %
%    #loadf`startSW`;;                                                       %
% to re-set up a theory for sliding window protocols when you have been      %
% working on the theory and want to recover the work so far.                 %
% last changed: 22/3/91 by rco                                               %
%----------------------------------------------------------------------------%

extend_theory `SWnew`;;
load_definitions`SWnew`;;
load_theorems`SWnew`;;

load_theorems`myarith`;;
load_definitions`hdi_tli`;;
load_theorems`hdi_tli`;;
load_definitions`plusm_subm`;;
load_theorems`plusm_subm`;;

loadf`tydefsSW`;;

loadf`tacticsSW`;;
