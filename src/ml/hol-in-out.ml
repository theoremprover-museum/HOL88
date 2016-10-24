%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        hol-in-out.ml                                         %
%                                                                             %
%     DESCRIPTION:      Loads in the HOL parser and printer                   %
%                                                                             %
%     USES FILES:       basic-hol lisp files                                  %
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
%     REVISION HISTORY: pathnames -- J. Joyce (April 1987)                    %
%=============================================================================%

% Modification J.Joyce Apr 87 %
% lisp `(setdebug t)`;; %

lisp (concat (concat `(load "` lisp_dir_pathname) `genfns")`);;
lisp (concat (concat `(load "` lisp_dir_pathname) `gnt")`);;
lisp (concat (concat `(load "` lisp_dir_pathname) `hol-pars")`);;
lisp (concat (concat `(load "` lisp_dir_pathname) `parslist")`);;
lisp (concat (concat `(load "` lisp_dir_pathname) `parslet")`);;
lisp (concat (concat `(load "` lisp_dir_pathname) `constp")`);;
lisp (concat (concat `(load "` lisp_dir_pathname) `hol-writ")`);;
lisp (concat (concat `(load "` lisp_dir_pathname) `mk_pp_thm")`);;

loadf (concat ml_dir_pathname `genfns`);;    %general purpose functions%
loadf (concat ml_dir_pathname `hol-syn`);;   %basic syntax functions for HOL%
