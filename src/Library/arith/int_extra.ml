%****************************************************************************%
% FILE          : int_extra.ml                                               %
% DESCRIPTION   : Additional functions for integer arithmetic in ML.         %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 4th March 1991                                             %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 12th April 1991                                            %
%****************************************************************************%

%----------------------------------------------------------------------------%
% Absolute value of an integer                                               %
%----------------------------------------------------------------------------%

let abs i = if (i < 0) then (-i) else i;;

%----------------------------------------------------------------------------%
% Function to compute the remainder of an integer division                   %
%----------------------------------------------------------------------------%

ml_curried_infix `mod`;;

let n mod m =
   let r = n - ((n / m) * m)
   in  if (r < 0) then (r + m) else r;;

%----------------------------------------------------------------------------%
% Function to compute the Greatest Common Divisor of two integers.           %
%----------------------------------------------------------------------------%

let gcd (i,j) =
   letrec gcd' (i,j) =
      let rem = i mod j
      in  if (rem = 0)
          then j
          else gcd' (j,rem)
   in (if ((i < 0) or (j < 0))
       then fail
       else if (i < j) then gcd' (j,i) else gcd' (i,j)
      ) ? failwith `gcd`;;

%----------------------------------------------------------------------------%
% Function to compute the Lowest Common Multiple of two integers.            %
%----------------------------------------------------------------------------%

let lcm (i,j) = (i * j) / (gcd (i,j)) ? failwith `lcm`;;
