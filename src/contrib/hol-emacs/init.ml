%----------------------------------------------------------------

   File: init.ml
   Author: PJWindley (UCDavis)

   Purpose: initialize HOL88 for running under emacs.

----------------------------------------------------------------%

%----------------------------------------------------------------
Since this file is only called if I'm running HOL from within
Emacs, I want to turn my prompt off.
----------------------------------------------------------------%
set_flag (`prompt`,false);;


%----------------------------------------------------------------
Search the system directories first.  Note that the trailing '/' 
has to be on each path component for this to work.
----------------------------------------------------------------%
set_search_path (search_path() @ [`~windley/hwv/hol/tactics/`; 
                                  `~windley/hwv/hol/ml/`;
                                 ]);;

