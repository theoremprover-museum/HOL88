%----------------------------------------------------------------------------%
% Load these type definitions each time you enter HOL to build or modify     %
% the sliding window protocol theory.  Use, loadf`tydefsSW`;;                %
%----------------------------------------------------------------------------%

let  time = ":num"
and  data = ":*"
and  sequence = ":num"
and  non_packet = ":one" ;; 

let  packet = ":(^sequence # ^data) + ^non_packet" ;;
let  channel = ":^time -> ^packet" ;;

let  seqtime = ":^time->^sequence" ;;
let  datatime = ":^time->^data list" ;;
