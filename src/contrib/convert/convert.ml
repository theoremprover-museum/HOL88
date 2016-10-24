% ===================================================================== %
% FILE		: convert.ml						%
% DESCRIPTION   : loads the library "convert" into hol.			%
%									%
% AUTHOR	: D Shepherd						%
% REVISED	: 90.12.01 (TFM).					%
% ===================================================================== %

%< =====================================================================
   convert library
   
   contents:
   		conv_package.ml:	conversion package
   		unfold.ml:		unfolding rules
   		unwind.ml:		unwinding rules
   		prune.ml:		pruning rules
   		more_conv.ml:		some extra conversions
   
   The unfolding and unwinding comes from original HOL sources.
   The pruning conversions have been rewritten to be tidier and
   more theoretically sound (i.e. no mk_thms)
   
   conv_package was inspired by interface to occam transformation system
   and allows detailed term hacking in a (semi-)controlled environemnt.
   
   more_conv contains some extra conversions and conversionals.
   
  
   david shepherd <des@inmos.co.uk>
===================================================================== >%

% --------------------------------------------------------------------- %
% Load the compiled code into ml.					%
% --------------------------------------------------------------------- %

let path st = library_pathname() ^ `/convert/` ^ st in
    load(path `conv_package`, get_flag_value `print_lib`);
    load(path `unfold`, get_flag_value `print_lib`);
    load(path `unwind`, get_flag_value `print_lib`);
    load(path `prune`, get_flag_value `print_lib`);
    load(path `more_conv`, get_flag_value `print_lib`);;
