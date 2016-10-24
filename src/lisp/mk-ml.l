;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        mk-ml.l                                             ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Loads compiled lisp files to create an ML system    ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-cl.l                                              ;;;
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

;;; The franz feature is used for distinguishing between CL and
;;; Franz lisp. Remove it from features if it appears in a common
;;; lisp implementation. [Grotty way to tell that in franz lisp
;;; - *features* is unbound).

(eval-when (compile load eval)
   (cond
      ((boundp '*features*)
         (setq *features* (remove :franz *features*)))))


(eval-when (load)
   (setq |%theory_pp-flag| nil)
   (setq %debug nil)
   (setq experimental nil)
   (setq eof '$eof$)
   (setq %mlprindepth 3)
   (setq initial%load t))   ; allow modules to initialize themselves


;;; Dummy definition for special - franz lisp interpreter does not
;;; seem to know about it. Called when loading files declaring constants
;;; (implemented as specials in franz).

#+franz (defun special fexpr (x) nil)


;;; If %directory is bound, then prepend it to filename. If not unix
;;; then make directory separator : rather than /.

;;; f-obj.l deleted from the load sequence [TFM 90.09.09] 

;;; f-help.l added to the load sequence

(eval-when (load)
   (mapc
      #'(lambda (file)
           (cond
              ((and (boundp '%directory) (eval '%directory))
                 (setq file
                    #+franz (concat (eval '%directory) file)
                    #-franz
                    (concatenate 'string (eval '%directory)
                       #+unix file
                       #-unix
                       ;; Franz cannot parse #\:
                       (substitute (schar ":" 0) (schar "/" 0) file)))))
            (load file))
      '(#+franz "lisp/f-franz" #-franz "lisp/f-cl"
         "lisp/f-system" "lisp/f-constants" "lisp/f-site"
         "lisp/f-gp" "lisp/f-parser" "lisp/f-parsml" "lisp/f-mlprin"
         "lisp/f-typeml" "lisp/f-dml" "lisp/f-format" "lisp/f-tran"
         "lisp/f-iox-stand" "lisp/f-writml" "lisp/f-tml"
         "lisp/f-lis" "lisp/f-ol-rec" "lisp/f-help")))


;;; End of file
