;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        mk_pp_thm.l                                         ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Hack to get PPLAMBDA started.                       ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-franz.l (or f-cl.l), f-macro.l, f-ol-rec.l,       ;;;
;;;                     genmacs.l                                           ;;;
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
;;;   REVISION HISTORY: (none)                                              ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-macro")
   (include "lisp/f-ol-rec")
   (include "lisp/genmacs")
   (special %thm-count))


(defun set-thm-count (x) (prog1 %thm-count (setq %thm-count x)))

(dml |set_thm_count| 1 set-thm-count (|int| |->| |int|))

(defun identity-function (x) (incf %thm-count) x)

(dml |mk_pp_thm| 1 identity-function
   (((|form| |list|) |#| |form|) |->| |thm|))
