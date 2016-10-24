%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        hol-net.ml                                            %
%                                                                             %
%     DESCRIPTION:      HOL version of the ML interface to Lisp-coded ol net- %
%                       work functions.  These provide the ability to store   %
%                       data indexed by terms, particularly for simplifica-   %
%                       tion.                                                 %
%                                                                             %
%                       Since "dml" cannot define objects of abstract types,  %
%                       they are defined with type "* list" instead of        %
%                       "* term_net".  This abstract type definition intro-   %
%                       duces the correct types.  Polymorphism works because  %
%                       "* list" involves a type variable.  This is a hack but%
%                       there seems to be no ideal solution.                  %
%                                                                             %
%     USES FILES:       basci-hol lisp files, bool.th, genfns.ml, hol-syn.ml  %
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

% Must be compiled in the presence of the hol parser/pretty printer	%
% This loads genfns.ml and hol-syn.ml too.				%

if compiling then  (loadf `ml/hol-in-out`);;

abstype * term_net = * list
with nil_term_net = 
     abs_term_net []
and  enter_term (tm,data) tnet = 
     abs_term_net (enter_term_rep (data,tm, rep_term_net tnet))
and  lookup_term tnet tm = 
     lookup_term_rep (rep_term_net tnet, tm)
and  merge_term_nets tnet1 tnet2 =
     abs_term_net (merge_nets_rep (rep_term_net tnet1, rep_term_net tnet2))
;;

