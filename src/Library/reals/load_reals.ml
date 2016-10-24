%============================================================================%
% Creates a function that loads the contents of the library "reals" into HOL %
%============================================================================%

let load_reals (():void) =
    if (mem `TRANSC` (ancestry())) then
       loadt `autoload_reals`
    else failwith `theory REAL not an ancestor of the current theory`;;
