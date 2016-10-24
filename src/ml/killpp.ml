%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        killpp.ml                                             %
%                                                                             %
%     DESCRIPTION:      Removes traces of PPLAMBDA                            %
%                                                                             %
%     USES FILES:       hol-lcf lisp files, ml-curry.ml, ml-gen.ml, ml-lis.ml,%
%                       ml-site.ml                                            %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        University of Edinburgh                               %
%     COPYRIGHT:        University of Cambridge                               %
%     COPYRIGHT:        INRIA                                                 %
%                                                                             %
%     REVISION HISTORY: (none)                                                %
%=============================================================================%

lisp`(remprop 'UU   'const)`;;
lisp`(remprop 'TT   'const)`;;
lisp`(remprop 'FF   'const)`;;
lisp`(remprop 'FST  'const)`;;
lisp`(remprop 'SND  'const)`;;
lisp`(remprop 'FIX  'const)`;;
lisp`(remprop 'COND 'const)`;;
lisp`(remprop 'PAIR 'const)`;;

lisp`(remprop '|<<|  'ollp)`;;
lisp`(remprop '|<<|  'ol2)`;;

lisp`(remprop '|==|  'ollp)`;;
lisp`(remprop '|==|  'ol2)`;;
