% ===================================================================== %
% FILE		: load_fixpoints.ml					%
% DESCRIPTION   : creates a function that loads the contents of the	%
%		  library "fixpoints" into hol.				%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 91.01.24						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% define the function load_fixpoints.					%
% --------------------------------------------------------------------- %

let load_fixpoints (v:void) =
    if (mem `fixpoints` (ancestry())) then
       (print_string `Loading contents of fixpoints...`; print_newline();
        map autoload_theory
         [`definition`, `fixpoints`, `LESS_DEF`;
          `definition`, `fixpoints`, `FIX`;
          `definition`, `fixpoints`, `ITER`;
          `definition`, `fixpoints`, `LUB`;
          `definition`, `fixpoints`, `BOT`;
          `definition`, `fixpoints`, `LIM_ITER`;
          `definition`, `fixpoints`, `CHAIN`;
          `definition`, `fixpoints`, `TRIV_CHAIN`;
          `definition`, `fixpoints`, `MONO`;
          `definition`, `fixpoints`, `CONTINUOUS`;
          `definition`, `fixpoints`, `ADMITS_INDUCTION`;
        
          `theorem`, `fixpoints`, `TRIV_CHAIN_LEMMA`;
          `theorem`, `fixpoints`, `CHAIN_ITER`;
          `theorem`, `fixpoints`, `LUB_CHAIN_LEMMA`;
          `theorem`, `fixpoints`, `LAMB_TRIV_CHAIN`;
          `theorem`, `fixpoints`, `CONT_MONO`;
          `theorem`, `fixpoints`, `FIX_LEMMA`;
          `theorem`, `fixpoints`, `LEAST_FIX_LEMMA`;
          `theorem`, `fixpoints`, `LEAST_FIX_THM`;
          `theorem`, `fixpoints`, `LIM_ITER_THM`;
          `theorem`, `fixpoints`, `FIX_EXISTS`;
          `theorem`, `fixpoints`, `FIX_THM`;
          `theorem`, `fixpoints`, `ANTISYM_LEMMA`;
          `theorem`, `fixpoints`, `FIX_LIM_ITER_THM`;
          `theorem`, `fixpoints`, `HOARE_ADMITS_LEMMA`;
          `theorem`, `fixpoints`, `SCOTT_INDUCTION_LEMMA`;
          `theorem`, `fixpoints`, `SCOTT_INDUCTION_THM`]; ()) else
    failwith `theory fixpoints not an ancestor of the current theory`;;

