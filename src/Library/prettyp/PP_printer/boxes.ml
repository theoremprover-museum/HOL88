% boxes.ml                                                                    %
%-----------------------------------------------------------------------------%


%  Datatype for boxes of text.  %

%  A box looks like this:                                                     %
%                                                                             %
%         <-io-->@__________________                                          %
%          ______|                  |   |                                     %
%         |                         | height                                  %
%         |                _________|   |                                     %
%         |_______________|             |                                     %
%         <------fo------->                                                   %
%         <----------width---------->                                         %
%                                                                             %

%  `N_box' (null box) is a box with dimensions of length zero.                %
%  `A_box ((width,s),_)' (atomic box) is a box of height 1, width the length  %
%     of the string s (so width is redundant, but useful for efficiency),     %
%     io = 0 and fo = width.                                                  %
%  `L_box ((width,separation,pb1,pb2),_)' (linear box) is a box of height 1,  %
%     io = 0 and fo = width. separation is the number of spaces between the   %
%     back of pb1 and the front of pb2. A linear box is a special case of a   %
%     compound box. The advantage of using a linear box when possible is      %
%     that it takes up less memory.                                           %
%  `C_box (((io,width,fo),height,(x,y),pb1,pb2),_)' (compound box) is a box   %
%     made from two other boxes, pb1 and pb2. The dimensions of the compound  %
%     box are included. (x,y) are the horizontal (to the right) and vertical  %
%     (downwards) offset of pb2 within the compound box. The offsets are      %
%     measured between the origins of the boxes (labelled by @ in the         %
%     diagram). The offsets of pb1 are (0,0).                                 %

rectype * print_box = N_box
                    | A_box of (nat # string) # *
                    | L_box of (nat # nat # * print_box # * print_box) # *
                    | C_box of ((nat # nat # nat) # nat # (int # nat) #
                                   * print_box # * print_box) # *;;


%  Functions to extract the dimensions of a box.  %

let print_box_io pb =

   % : (* print_box -> int) %

   case pb
   of N_box . 0
    | (A_box _) . 0
    | (L_box _) . 0
    | (C_box (((io,_,_),_),_)) . (Int io);;


let print_box_width pb =

   % : (* print_box -> int) %

   case pb
   of N_box . 0
    | (A_box ((width,_),_)) . (Int width)
    | (L_box ((width,_),_)) . (Int width)
    | (C_box (((_,width,_),_),_)) . (Int width);;


let print_box_fo pb =

   % : (* print_box -> int) %

   case pb
   of N_box . 0
    | (A_box ((width,_),_)) . (Int width)
    | (L_box ((width,_),_)) . (Int width)
    | (C_box (((_,_,fo),_),_)) . (Int fo);;


let print_box_height pb =

   % : (* print_box -> int) %

   case pb
   of N_box . 0
    | (A_box _) . 1
    | (L_box _) . 1
    | (C_box ((_,height,_),_)) . (Int height);;


let print_box_sizes pb =

   % : (* print_box -> (int # int # int) # int) %

   case pb
   of N_box . ((0,0,0),0)
    | (A_box ((w,_),_)) . (let w' = Int w in ((0,w',w'),1))
    | (L_box ((w,_),_)) . (let w' = Int w in ((0,w',w'),1))
    | (C_box (((io,w,fo),h,_),_)) . ((Int io,Int w,Int fo),Int h);;


%  Function for changing the `label' of a print_box.  %

let replace_box_label v pb =

   % : (* -> * print_box -> * print_box) %

   case pb
   of N_box . pb
    | (A_box (x,_)) . (A_box (x,v))
    | (L_box (x,_)) . (L_box (x,v))
    | (C_box (x,_)) . (C_box (x,v));;


%  Datatype for indentation values.  %

%  `Abs' is absolute indentation (relative to first sub-box).        %
%  `Inc' is incremental indentation (relative to previous sub-box).  %

type print_indent = Abs of int
                  | Inc of int;;


%  Datatype for boxes ready to be built.  %

%  The boxes are just waiting to be told what horizontal space is available  %
%  to them before taking on their final form.                                %

%  The sub-boxes can be composed horizontally (H), vertically (V),           %
%  horizontal/vertically (HV), or horizontal-or-vertically (HoV).            %

%  Each sub-box is represented by an object of type                          %
%  (int -> int -> * print_box). This is a function which when given the      %
%  current output width and the current indentation from the left margin,    %
%  yields a box.                                                             %

%  The first sub-box is fixed. All the others carry offset information with  %
%  them.                                                                     %

type * unbuilt_box = UB_H of (int -> int -> * print_box) #
                             (nat # (int -> int -> * print_box)) list
                   | UB_V of (int -> int -> * print_box) #
                             ((print_indent # nat) #
                                 (int -> int -> * print_box)) list
                   | UB_HV of (int -> int -> * print_box) #
                              ((nat # print_indent # nat) #
                                  (int -> int -> * print_box)) list
                   | UB_HoV of (int -> int -> * print_box) #
                               ((nat # print_indent # nat) #
                                   (int -> int -> * print_box)) list;;

begin_section boxes;;

%  Function for joining two boxes together.  %

%  `x' and `y' have rather strange definitions which allow the one function   %
%  to be used for joining boxes both horizontally and vertically. Note that   %
%  `join_boxes' does not work properly with boxes of zero height.             %

%  The intermediate values `lo' and `ro' are illustrated (both with positive  %
%  values) in the diagram below:                                              %
%                                                                             %
%                          _______ <-ro->                                     %
%                     ____|  _____|_____                                      %
%                    |______|_|      ___|                                     %
%                        |__________|                                         %
%                    <lo>                                                     %
%                                                                             %
%  The composition of the two boxes looks like this:                          %
%                                                                             %
%                          _____________                                      %
%                     ____|             |                                     %
%                    |               ___|                                     %
%                    |______________|                                         %
%                                                                             %

let join_boxes x y pb1 pb2 v =

   % : (int -> int -> * print_box -> * print_box -> * -> * print_box) %

   let ((io1,w1,fo1),h1) = print_box_sizes pb1
   and ((io2,w2,fo2),h2) = print_box_sizes pb2
   in  let lo = x - io2
       and ro = (w2 - io2) - (w1 - x)
   in  let io = if (lo < 0) then (io1 - lo) else io1
       and w  = if (lo < 0)
                then if (ro < 0) then (w1 - lo) else w2
                else if (ro < 0) then w1 else (w2 + lo)
       and fo = if (lo < 0) then fo2 else (fo2 + lo)
       and h  = h1 + h2 + y
       and x2 = x - io1
       and y2 = h1 + y
   in  if (h = 1)
       then L_box ((Nat w,Nat (x2 - w1),pb1,pb2),v)
       else C_box (((Nat io,Nat w,Nat fo),Nat h,(x2,Nat y2),pb1,pb2),v);;


%  Function to join boxes horizontally with separation `dx'.  %

%  Composition with an `N_box' leaves the other box unchanged.                %

%  Composing two boxes horizontally:                                          %
%                                                                             %
%                           |dx|                                              %
%                          _______                                            %
%                     ____|  _____|_____                                      %
%                    |______|__|     ___|   | -y                              %
%                        |__________|                                         %
%                    <----x---->                                              %
%                                                                             %

let join_H_boxes dx pb1 pb2 v =

   % : (nat -> * print_box -> * print_box -> * -> * print_box) %

   case (pb1,pb2)
   of (N_box,_) . pb2
    | (_,N_box) . pb1
    | (_) . (join_boxes ((print_box_fo pb1) + (Int dx)) (-1) pb1 pb2 v);;


%  Function to join boxes vertically with separation `dh'  %
%  and indentation `di'.                                   %

%  Composition with an `N_box' leaves the other box unchanged.                %

%  Composing two boxes vertically:                                            %
%                                                                             %
%                          _______                                            %
%                     ____|     __|                                           %
%                    |_________|                                              %
%                         <di>_______    | y = dh                             %
%                       _____|     __|                                        %
%                      |__________|                                           %
%                    <---x--->                                                %
%                                                                             %

let join_V_boxes di dh pb1 pb2 v =

   % : (int -> nat -> * print_box -> * print_box -> * -> * print_box) %

   case (pb1,pb2)
   of (N_box,_) . pb2
    | (_,N_box) . pb1
    | (_) . (join_boxes ((print_box_io pb1) + di) (Int dh) pb1 pb2 v);;


%  Function to build a horizontal (H) box.  %

%  The sub-function `gaps' is used to compute the total separation between    %
%  the sub-boxes. To this is added the number of sub-boxes (less the first).  %
%  The available width (m) is then reduced by this total to give the new      %
%  available width (m'). This is an attempt to guess how much space to leave  %
%  on the line for the remainder of the sub-boxes. The effective width of     %
%  each sub-box is assumed to be one. In fact it could be any value, even     %
%  negative. The heuristic seems to work well in practice though, probably    %
%  because most horizontal boxes that are large enough to spread over more    %
%  than one line are of the form parenthesis - large block - parenthesis, or  %
%  in place of the parentheses, some other single character.                  %

%  As each sub-box is built, the gap between it and the previous sub-box      %
%  plus one is added back on to the available width, and the indentation      %
%  from the left margin is changed by the genuine amount. In fact, the        %
%  indentation is computed each time from the original indentation, the       %
%  effective width of the box built so far, and the effective width of the    %
%  latest sub-box.                                                            %

let build_H_box m i v box boxl =

   % : (int -> int -> * -> (int -> int -> * print_box) ->           %
   %       (nat # (int -> int -> * print_box)) list -> * print_box) %

   letrec f pb m' boxl' =

      % : (* print_box -> int ->                                       %
      %       (nat # (int -> int -> * print_box)) list -> * print_box) %

      if (null boxl')
      then pb
      else let (dx,pbfn) = hd boxl'
           in  let m'' = m' + 1 + (Int dx)
               and i' = i + ((print_box_fo pb) - (print_box_io pb)) + (Int dx)
               in  f (join_H_boxes dx pb (pbfn m'' i') v) m'' (tl boxl')

   and gaps boxl' =

      % : ((nat # (int -> int -> * print_box)) list -> int) %

      itlist (\x n. (Int (fst x)) + n) boxl' 0

   in let m' = m - ((gaps boxl) + (length boxl))
      in  f (box m' i) m' boxl;;


%  Function to build a vertical (V) box.  %

%  The sub-boxes are composed vertically. The indentation from the left  %
%  margin is modified as each sub-box is added.                          %

let build_V_box (m:int) i v box boxl =

   % : (int -> int -> * -> (int -> int -> * print_box) ->            %
   %    ((print_indent # nat) # (int -> int -> * print_box)) list -> %
   %    * print_box)                                                 %

   letrec f pb i' boxl' =

      % : (* print_box -> int ->                                        %
      %    ((print_indent # nat) # (int -> int -> * print_box)) list -> %
      %    * print_box)                                                 %

      if (null boxl')
      then pb
      else let ((pi,dh),pbfn) = hd boxl'
           in  let di = case pi
                        of (Abs n) . n
                         | (Inc n) . (n + i' - i)
               in  f (join_V_boxes di dh pb (pbfn m (i + di)) v)
                                                (i + di) (tl boxl')

   in f (box m i) i boxl;;


%  Function to build a horizontal/vertical (HV) box.  %

%  The sub-function `fH' generates a list of boxes to be composed vertically  %
%  where each box has been made up by composing one or more of the original   %
%  sub-boxes horizontally. The list generated is in reverse order and the     %
%  indentations for the vertical composition are offsets from the first       %
%  box. Note that the function used with `itlist' reverses its arguments.     %
%  Consideration of the call to `itlist' should reveal the rather delicate    %
%  nature of the composition occurring. The order in which the composition    %
%  is done is crucially linked with whether the indentations are absolute or  %
%  relative.                                                                  %

%  The sub-function builds horizontal boxes until they are too big, and then  %
%  adds them to a list of boxes built so far. When trying to add a sub-box    %
%  to the current horizontal box, the function evaluates by how much the      %
%  offset from the left margin (i') will be increased if a line-break is not  %
%  used. If this is less than or equal to the increase that will occur with   %
%  a line-break, the sub-box is added to the horizontal box regardless.       %

%  The function uses two criteria for determining when to break. If the new   %
%  box is wider than the available space, a break must occur. There must      %
%  also be a break if the right-hand edge of the box exceeds the right-hand   %
%  margin. The two criteria are not necessarily the same because the          %
%  indentation may force the box further to the right. Since the indentation  %
%  can also be negative, it could pull the box to the left, giving a false    %
%  result. For this reason negative indentations are taken to be zero.        %

%  The vertical composition parameters of the first sub-box of a horizontal   %
%  box are remembered when it is started, so that they become the parameters  %
%  for the composite horizontal box.                                          %

let build_HV_box m i v box boxl =

   % : (int -> int -> * -> (int -> int -> * print_box) ->                  %
   %    ((nat # print_indent # nat) # (int -> int -> * print_box)) list -> %
   %    * print_box)                                                       %

   letrec fH newboxl newbox i' boxl' =

      % : ((int # nat # * print_box) list ->                                  %
      %    (int # nat # * print_box) -> int ->                                %
      %    ((nat # print_indent # nat) # (int -> int -> * print_box)) list -> %
      %    (int # nat # * print_box) list)                                    %

      if (null boxl')
      then newbox.newboxl
      else let ((dx,pi,dh),pbfn) = hd boxl'
           and (newdi,newdh,pb) = newbox
           in  let di = case pi
                        of (Abs n) . n
                         | (Inc n) . (n + i' - i)
               and no_break_indent =
                      (Int dx) + (print_box_fo pb) - (print_box_io pb)
               in  if ((di - (i' - i)) < no_break_indent)
                   then let newb = pbfn m (i + di)
                        in  let newhb = join_H_boxes dx pb newb v
                            in  if (((print_box_width newhb) > m) or
                                    ((print_box_width newhb) -
                                             (print_box_io newhb)
                                        > (m - max [i';0])))
                                then fH (newbox.newboxl) (di,dh,newb)
                                                          (i + di) (tl boxl')
                                else fH newboxl (newdi,newdh,newhb) i'
                                                                   (tl boxl')
                   else let newhb = join_H_boxes dx pb
                                       (pbfn m (i' + no_break_indent)) v
                        in  fH newboxl (newdi,newdh,newhb) i' (tl boxl')

   in let newboxl = fH [] (0,Nat 0,box m i) i boxl
      in  itlist (\(di,dh,pb2) pb1. join_V_boxes di dh pb1 pb2 v) newboxl
                                                                     N_box;;


%  Function to build a horizontal-or-vertical (HoV) box.  %

%  The sub-function `f' computes the indentations for each box and builds     %
%  the sub-boxes under the assumption that each will go on a new line.        %

%  The body of the main function composes the boxes horizontally. If the      %
%  resulting box is too big (see comments for `build_HV_box'), the boxes are  %
%  composed vertically. The narrower of the two compositions is then used.    %
%  See comments for `build_HV_box' regarding use of `itlist' for composing.   %

let build_HoV_box m i v box boxl =

   % : (int -> int -> * -> (int -> int -> * print_box) ->                  %
   %    ((nat # print_indent # nat) # (int -> int -> * print_box)) list -> %
   %    * print_box)                                                       %

   letrec f newboxl i' boxl' =

      % : ((nat # int # nat # * print_box) list -> int ->                     %
      %    ((nat # print_indent # nat) # (int -> int -> * print_box)) list -> %
      %    (nat # int # nat # * print_box) list)                              %

      if (null boxl')
      then newboxl
      else let ((dx,pi,dh),pbfn) = hd boxl'
           in  let di = case pi
                        of (Abs n) . n
                         | (Inc n) . (n + i' - i)
               in  f ((dx,di,dh,pbfn m (i + di)).newboxl) (i + di) (tl boxl')

   in let newb = box m i
      and newboxl = f [] i boxl
      in  let newhb = itlist (\(dx,di,dh,pb2) pb1. join_H_boxes dx pb1 pb2 v)
                                                                  newboxl newb
          in  let hw = print_box_width newhb
              and hio = print_box_io newhb
              in  if ((hw > m) or (hw - hio > (m - max [i;0])))
                  then let newvb =
                          itlist
                           (\(dx,di,dh,pb2) pb1. join_V_boxes di dh pb1 pb2 v)
                                                                   newboxl newb
                       in  let vw = print_box_width newvb
                           and vio = print_box_io newvb
                           in  if ((hw > vw) or (hw - hio > vw - vio))
                               then newvb
                               else newhb
                  else newhb;;


%  Function for building a box.  %

%  The value v is used as the `label' for all sub-boxes constructed.  %

let build_print_box m i v unbox =

   % : (int -> int -> * -> * unbuilt_box -> * print_box) %

   case unbox
   of (UB_H (box,boxl))   . (build_H_box m i v box boxl)
    | (UB_V (box,boxl))   . (build_V_box m i v box boxl)
    | (UB_HV (box,boxl))  . (build_HV_box m i v box boxl)
    | (UB_HoV (box,boxl)) . (build_HoV_box m i v box boxl);;

build_print_box;;
end_section boxes;;
let build_print_box = it;;


%-----------------------------------------------------------------------------%
