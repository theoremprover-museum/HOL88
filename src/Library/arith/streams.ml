%****************************************************************************%
% FILE          : streams.ml                                                 %
% DESCRIPTION   : Datatype and functions for streams (lazy lists).           %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 20th April 1991                                            %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 22nd April 1991                                            %
%****************************************************************************%

%----------------------------------------------------------------------------%
% Datatype for lazy lists                                                    %
%----------------------------------------------------------------------------%

rectype * stream = Stream of * # (void -> * stream);;

%----------------------------------------------------------------------------%
% stream_map : (* -> **) -> (void -> * stream) -> (void -> ** stream)        %
%----------------------------------------------------------------------------%

letrec stream_map f s () =
   case s ()
   of (Stream (x,s')) . (Stream (f x,stream_map f s'));;

%----------------------------------------------------------------------------%
% stream_append : (void -> * stream) ->                                      %
%                 (void -> * stream) ->                                      %
%                 (void -> * stream)                                         %
%----------------------------------------------------------------------------%

letrec stream_append s1 s2 () =
   (case s1 ()
    of (Stream (x,s1')) . (Stream (x,stream_append s1' s2)))
   ? s2 ();;

%----------------------------------------------------------------------------%
% stream_flat : (void -> (void -> * stream) stream) -> void -> * stream      %
%----------------------------------------------------------------------------%

letrec stream_flat ss () =
   case ss ()
   of (Stream (s,ss')) . (stream_append s (stream_flat ss') ());;

%----------------------------------------------------------------------------%
% permutations : * list -> void -> * list stream                             %
%----------------------------------------------------------------------------%

letrec permutations l () =
   letrec remove_el n l =
      if ((null l) or (n < 1))
      then failwith `remove_el`
      else if (n = 1)
           then (hd l,tl l)
           else let (x,l') = remove_el (n - 1) (tl l)
                in  (x,(hd l).l')
   in
   let one_smaller_subsets l =
      letrec one_smaller_subsets' l n () =
         if (null l)
         then fail
         else Stream (remove_el n l,one_smaller_subsets' l (n + 1))
      in one_smaller_subsets' l 1
   in
   if (null l) then fail
   if (null (tl l)) then Stream ([hd l],\(). fail)
   else let oss = one_smaller_subsets l
        in  let subperms = stream_map (I # permutations) oss
        in  stream_flat
              (stream_map (\(x,sofl). stream_map (\l. x.l) sofl) subperms) ();;
