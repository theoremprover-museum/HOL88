;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        genfns.l                                            ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      General-purpose lisp functions                      ;;;
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
;;;   REVISION HISTORY: (none)                                              ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-macro"))


#+franz (declare (localf truncate-list))


;;;(truncate-list i (x1 ... xn)) gives (x1 ... xi). Must have i<n+1.

(defun truncate-list (i l)
   (cond ((zerop i) nil) (t (cons (car l) (truncate-list (sub1 i) (cdr l))))))

(defun seg (p l)
   (let ((m (car p))
         (n (cadr p)))
      (cond ((or (lessp m 0) (lessp n m))
            (failwith '|seg|))
         ((zerop m) (truncate-list (add1 (difference n m)) l))
         (t (seg (list (sub1 m) (sub1 n)) (cdr l))))))

(defun word-seg (p l) (reverse (seg p (reverse l))))

(defun word-el (n l) (nth n (reverse l)))
