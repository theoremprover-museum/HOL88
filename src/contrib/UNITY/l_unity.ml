% -*- Emacs Mode: fundamental -*- %

%-----------------------------------------------------------------------------%
%
   File:         l_unity.ml

   Description:  The loading of this file gives access to the defined UNITY
                 theory.

   Author:       (c) Copyright by Flemming Andersen
   Date:         January 7, 1990
%
%-----------------------------------------------------------------------------%

loadf`aux_definitions`;;

autoload_defs_and_thms `state_logic`;;
autoload_defs_and_thms `unless`;;
autoload_defs_and_thms `ensures`;;
autoload_defs_and_thms `gen_induct`;;
autoload_defs_and_thms `leadsto`;;
autoload_defs_and_thms `comp_unity`;;

loadf`leadsto_induct0`;;
