;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        parse_as_binder.l                                   ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      This fragment of lisp originally appeared in        ;;;
;;;                     hol-syn.ml as an argument to the ML function "lisp".;;;
;;;                     Vertical bars were needed where they appear below,  ;;;
;;;                     but when the ML source was compiled, disaster res-  ;;;
;;;                     ulted because the lisp expression below is compiled ;;;
;;;                     into a lisp symbol inside vertical bars, ie. res-   ;;;
;;;                     ulting in nested vertical bars which doesn't work.  ;;;
;;;                     Note that the ML could be evaluated but couldn't be ;;;
;;;                     compiled.  Instead, the compiled version of this    ;;;
;;;                     lisp source is loaded at run-time by hol-syn.ml.    ;;;
;;;                                                                         ;;;
;;;   USES FILES:                                                           ;;;
;;;                                                                         ;;;
;;;                     University of Cambridge                             ;;;
;;;                     Hardware Verification Group                         ;;;
;;;                     Computer Laboratory                                 ;;;
;;;                     New Museums Site                                    ;;;
;;;                     Pembroke Street                                     ;;;
;;;                     Cambridge  CB2 3QG                                  ;;;
;;;                     England                                             ;;;
;;;                                                                         ;;;
;;;   COPYRIGHT:        University of Edinburgh                             ;;;
;;;   COPYRIGHT:        University of Cambridge                             ;;;
;;;   COPYRIGHT:        INRIA                                               ;;;
;;;                                                                         ;;;
;;;   REVISION HISTORY: April 1987 (J.Joyce)                                ;;;
;;;                     October 1 1992 : parse_as_binder removed and put    ;;;
;;;                     into hol-syn.l just after binder-rtn.  This file    ;;;
;;;                     removed from build sequence [TFM for HOL88 2.01]    ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   (include "lisp/f-macro"))

(dml |parse_as_binder| 1 binder-rtn (|tok| -> |tok|))

