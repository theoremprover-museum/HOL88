% Must be compiled when other ml sources are compiled %

let concat tok1 tok2 = implode( explode tok1 @ explode tok2);;

let ml_dir_pathname = `ml\\`;;
let lisp_dir_pathname = `lisp\\\\`;;

% No longer needed.		  [TFM 91.02.24] %
% let theories_dir_pathname = `theories\\`;;      %
