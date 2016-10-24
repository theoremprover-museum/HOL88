;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        constp.l                                            ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Functions that test for constants                   ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-cl.l (no need for f-franz.l in Franz Lisp)        ;;;
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

;;; MJCG 8/11/88 for HOL88
;;; local declaration commented out (tokconstp used in hol-pars.l now)
;;; #+franz (declare (localf tokconstp))

;;; There must be a better way of doing the stuff below ...
;;; # is mapped to (35) by exploden
;;; ` is mapped to (96)
;;; |0123456789| is mapped to (48 49 50 51 52 53 54 55 56 57) by exploden

(defun tokconstp (tok)
   (let ((l (exploden tok)))
      (and (= (car l) 96)   
         (= (car (last l)) 96))))

(defun numconstp (tok)
   (test-list-els (exploden tok) '(48 49 50 51 52 53 54 55 56 57)))

#-franz (proclaim '(notinline numconstp))  ; since it gets redefined later


(defun wordconstp (tok)
   (let ((l (exploden tok)))
      (and (= (car l) 35)   
         (test-list-els (cdr l) '(48 49)))))

(defun test-list-els (l els)
   (or (null l)
      (and (memq (car l) els)
         (test-list-els (cdr l) els))))


;;; Modified TFM 88.04.04  :string instead of :tok
;;; MJCG 7/1/88 for HOL88
;;; check for hidden constants

(defun constp (tok)
   (cond ((tokconstp tok)
         '(|string|))
      ((numconstp tok) 
         '(|num|))
      ((wordconstp tok) 
         (list
            (imploden
               (append 
                  '(#/w #/o #/r #/d) 
                  (exploden (length (cdr (exploden tok))))))))
      (t (or (get tok 'const)
            (and (get tok 'hidden-const)
               (cdr (assq 'const (get tok 'hidden-const))))))))


