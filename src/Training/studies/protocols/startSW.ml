
%----------------------------------------------------------------------------%
% startSW.ml :  Load this file from HOL using                                %
%    #loadf`startSW`;;                                                       %
% to set up a new theory for sliding window protocols, SWnew.                %
% last changed: 20/3/91 by rco                                               %
%----------------------------------------------------------------------------%

new_theory `SWnew`;;


new_parent`myarith`;;
new_parent`hdi_tli`;;
new_parent`plusm_subm`;; 

load_theorems`myarith`;;
load_definitions`hdi_tli`;;
load_theorems`hdi_tli`;;
load_definitions`plusm_subm`;;
load_theorems`plusm_subm`;;
