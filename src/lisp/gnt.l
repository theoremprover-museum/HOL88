;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        gnt.l                                               ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Get next token                                      ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-franz.l (or f-cl.l), f-constants.l, f-macro.l,    ;;;
;;;                     f-ol-rec.l                                          ;;;
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

;;; gnt (get next token) changed so numbers returned in both ML and OL

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (include "lisp/f-ol-rec")
   (*lexpr concat)
   (special token tokchs toktyp cflag ptoken ptokchs ptoktyp pchar
      parsedepth arg1 lang1 atom-rtn langlp juxtlevel juxt-rtn lang2 msg1
      msg2 nulltyptok tokbearer toklbearer olinprec zeros-count))


(defun gnt ()
   (setq cflag (spacep hol-char))                     ;for vartypes (berk)
   (setq ptoken token)
   (setq ptokchs tokchs)
   (setq ptoktyp toktyp)
   (setq pchar hol-char)
   (while (spacep hol-char)(setq pchar (setq hol-char (gnc)))) ;remove spacing
   (setq toktyp 1)
   (cond ((letterp hol-char) (setq tokchs (list hol-char))     ;ident
         (ident))
      ((digitp hol-char) (setq tokchs (list hol-char))     ;number (ML and OL)
         (numb)) 
      ((= hol-char tokqt) (setq tokchs nil) (tcn))
      (t (setq toktyp 2)
         (setq hol-char (gnc))
         (setq token (ascii pchar))
         (if (and (eq token scolon-sym) (= hol-char lf))
            (setq hol-char (gnc)))
         (while (memq hol-char (get token 'double)) 
            (setq token (concat token (ascii hol-char)))
            (setq hol-char (gnc)))))
   token    
   )  ;gnt

;;; scan a number and return its numeric value
;;; number of leading zeros stored in zeros-count
;;; In the function numb below zeros-flag is t whilst counting leading zeros.
;;; As soon as a non-zero digit is reached it goes to nil.

(defun numb ()
   (let ((accu (difference hol-char #/0))(zeros-flag t))
      (setq zeros-flag (if (zerop accu) t nil))
      (setq zeros-count (if (zerop accu) 1 0))
      (while (digitp (setq hol-char (nextcn)))
         (if (= hol-char #/0)
            (if zeros-flag (setq zeros-count (add1 zeros-count)))
            (setq zeros-flag nil))
         (setq accu (add (times accu 10)(difference hol-char #/0))))
      (setq token accu)))
