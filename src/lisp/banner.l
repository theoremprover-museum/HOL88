;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.1                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        banner.l                                            ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      HOL system banner                                   ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-franz.l (or f-cl.l)                               ;;;
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
;;;   REVISION HISTORY: "Classic HOL" banner added by MJCG on 31 March 1992 ;;;
;;;                     ========== banner installed by MJCG on 27 June 1992 ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (special %build-date %version))


;;;(setq HOL-sym
;;;  `|_  _         __        _         
;;;!__!        !  !       !
;;;!  ! IGHER  !__! RDER  !__ OGIC
;;;===============================
;;;|)

;;;(defconstant HOL-sym
;;;"          _  _    __    _      __    __
;;;   |___   |__|   |  |   |     |__|  |__|
;;;   |      |  |   |__|   |__   |__|  |__|
;;;   
;;;")

;;;(defconstant HOL-sym
;;;"           __  _     _    __   __  _   __     _  _   __   _
;;;   |___   |    |    /_\\  |__  |__  |  |       |__|  |  |  |
;;;   |      |__  |__ /   \\  __|  __| |  |__     |  |  |__|  |__
;;;
;;;")

(defconstant eqline
"
===============================================================================
")

(setq %build-date (date))

;;; Version: set in Makefile
(setq %version '"<version number>")

(defun banner ()
   (terpri)
   (princ eqline)
   (princ "         HOL88 Version ") (princ %version) 
   (princ '", built on ") (princ %build-date)
   (princ eqline)
   )


;;;(defun banner ()
;;;   (terpri)
;;;   (princ HOL-sym)
;;;   (princ "          HOL88 Version ") (princ %version) 
;;;   (princ '", built on ") (princ %build-date)
;;;   (terpri)
;;;   )

;;;(defun banner ()
;;;       (terpri)
;;;       (princ '|Higher Order Logic|) (terpri)
;;;       (princ '|==================|) (terpri)
;;;       (princ `|[Based on Cambridge LCF, version |)
;;;       (princ %version)
;;;       (princ '|  created |) (princ %ctime) (princ '|]|) (terpri)
;;;       (cond (experimental (princ '|Experimental system!|) (terpri)))
;;; )
