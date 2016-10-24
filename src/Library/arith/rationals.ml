%****************************************************************************%
% FILE          : rationals.ml                                               %
% DESCRIPTION   : Abstract datatype and functions for rational arithmetic    %
%                 in ML.                                                     %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 4th March 1991                                             %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 2nd July 1992                                              %
%****************************************************************************%

%============================================================================%
% Rational arithmetic                                                        %
%============================================================================%

%----------------------------------------------------------------------------%
% Abstract datatype for rational numbers and arithmetic                      %
%                                                                            %
% Rat         : (int # int) -> rat                                           %
% Numerator   : rat -> int                                                   %
% Denominator : rat -> int                                                   %
% rat_inv     : rat -> rat                                                   %
% rat_plus    : rat -> rat -> rat                                            %
% rat_minus   : rat -> rat -> rat                                            %
% rat_mult    : rat -> rat -> rat                                            %
% rat_div     : rat -> rat -> rat                                            %
% print_rat   : rat -> void                                                  %
%----------------------------------------------------------------------------%

abstype rat = int # int
   with Rat (i,j) =
      (if (i = 0) then abs_rat (0,1)
       else let g = gcd (abs i,abs j)
            in  let i' = i / g
                and j' = j / g
            in  if (j' < 0)
                then abs_rat ((-i'),(-j'))
                else abs_rat (i',j')
      ) ? failwith `Rat`
   and Numerator r = fst (rep_rat r)
   and Denominator r = snd (rep_rat r)
   and rat_inv r =
      let (i,j) = rep_rat r
      in  if (i < 0) then abs_rat ((-j),(-i))
          if (i > 0) then abs_rat (j,i)
          else failwith `rat_inv`
   and rat_plus r1 r2 =
      let (i1,j1) = rep_rat r1
      and (i2,j2) = rep_rat r2
      in  let g = gcd (j1,j2)
      in  let d1 = j1 / g
          and d2 = j2 / g
      in  let (i,j) = ((i1 * d2) + (i2 * d1),(j1 * d2))
      in  if (i = 0) then abs_rat (0,1) else abs_rat (i,j)
   and rat_minus r1 r2 =
      let (i1,j1) = rep_rat r1
      and (i2,j2) = rep_rat r2
      in  let g = gcd (j1,j2)
      in  let d1 = j1 / g
          and d2 = j2 / g
      in  let (i,j) = ((i1 * d2) - (i2 * d1),(j1 * d2))
      in  if (i = 0) then abs_rat (0,1) else abs_rat (i,j)
   and rat_mult r1 r2 =
      let (i1,j1) = rep_rat r1
      and (i2,j2) = rep_rat r2
      in  if ((i1 = 0) or (i2 = 0))
          then abs_rat (0,1)
          else let g = gcd (abs i1,j2)
               and h = gcd (abs i2,j1)
               in  let i = (i1 / g) * (i2 / h)
                   and j = (j1 / h) * (j2 / g)
               in  abs_rat (i,j)
   and rat_div r1 r2 =
      let (i1,j1) = rep_rat r1
      and (i2,j2) = rep_rat r2
      in  if (i2 = 0) then failwith `rat_div`
          if (i1 = 0) then abs_rat (0,1)
          else let g = gcd (abs i1,abs i2)
               and h = gcd (j1,j2)
               in  let i = (i1 / g) * (j2 / h)
                   and j = (j1 / h) * (i2 / g)
               in  if (j < 0) then abs_rat ((-i),(-j)) else abs_rat (i,j)
   and print_rat r =
      let (i,j) = rep_rat r
      in  if (j = 1)
          then print_int i
          else do (print_int i; print_string `/`; print_int j);;

top_print print_rat;;

%----------------------------------------------------------------------------%
% rat_of_int : int -> rat                                                    %
%                                                                            %
% Conversion from integers to rationals                                      %
%----------------------------------------------------------------------------%

let rat_of_int i = Rat (i,1);;

%----------------------------------------------------------------------------%
% lower_int_of_rat : rat -> int                                              %
%                                                                            %
% Conversion from rationals to integers                                      %
%                                                                            %
% Computes the largest integer less than or equal to the rational.           %
%----------------------------------------------------------------------------%

let lower_int_of_rat r =
   let n = Numerator r
   and d = Denominator r
   in  if (n < 0)
       then let p = (n * d) in (((n - p) / d) + n)
       else (n / d);;

%----------------------------------------------------------------------------%
% upper_int_of_rat : rat -> int                                              %
%                                                                            %
% Conversion from rationals to integers                                      %
%                                                                            %
% Computes the smallest integer greater than or equal to the rational.       %
%----------------------------------------------------------------------------%

let upper_int_of_rat r =
   let n = Numerator r
   and d = Denominator r
   in  if (n > 0)
       then let p = (n * d) in (((n - p) / d) + n)
       else (n / d);;

%----------------------------------------------------------------------------%
% The rational number zero                                                   %
%----------------------------------------------------------------------------%

let rat_zero = rat_of_int 0;;

%----------------------------------------------------------------------------%
% The rational number one                                                    %
%----------------------------------------------------------------------------%

let rat_one = rat_of_int 1;;

%----------------------------------------------------------------------------%
% rat_less : rat -> rat -> bool                                              %
%                                                                            %
% Less-than for rationals                                                    %
%----------------------------------------------------------------------------%

let rat_less r1 r2 = Numerator (rat_minus r1 r2) < 0;;
