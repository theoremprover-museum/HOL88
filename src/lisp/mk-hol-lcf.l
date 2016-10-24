;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        mk-hol-lcf.l                                        ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Loads files into ML to get an LCF suitable for HOL  ;;;
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

;;; If %directory is bound, then prepend it to filename. If not unix
;;; then make directory separator : rather than /.

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
      '("lisp/f-parsol" "lisp/f-typeol" "lisp/f-help" "lisp/f-format"
         "lisp/f-writol" "lisp/f-thyfns" 
         #-franz "lisp/f-freadth" "lisp/f-ol-syntax" "lisp/f-subst"
         "lisp/f-inst" "lisp/f-simpl" "lisp/f-ol-net")))


;;; End of file
