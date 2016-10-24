;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        genmacs.l                                           ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      General-purpose macros                              ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-franz.l (or f-cl.l), f-macro.l, f-ol-rec.l        ;;;
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
   (macros t)
   (special %show-types %empty-set))


(defmacro get-term-list (tm) `(cadr ,tm))

(defmacro make-prep-term (class term-list type)
   `(cons ,class (cons ,term-list ,type)))


(defmacro atom-to-num (a)
   ;; (atom-to-num |n1n2...|) gives the number n1n2...
   #+franz `(readlist (explodec ,a))
   #-franz `(parse-integer (string ,a) :junk-allowed t))


(defmacro is-num-atom (a)
   ;; is-num-atom tests whether an atom is an atomified number
   `(numberp (atom-to-num ,a)))


(defmacro null-ol-list (tm)
   `(and (is-const ,tm) (eq (get-const-name ,tm) 'NIL)))

(defmacro hd-ol-list (tm)
   `(get-rand (get-rator ,tm)))

(defmacro tl-ol-list (tm)
   `(get-rand ,tm))

(defmacro get-ol-list-type (tm)
   `(first (get-type-args (get-type ,tm))))

(defmacro null-ol-set (tm)
   `(and (is-const ,tm) (eq (get-const-name ,tm) %empty-set)))

(defmacro hd-ol-set (tm)
   `(get-rand (get-rator ,tm)))

(defmacro tl-ol-set (tm)
   `(get-rand ,tm))

(defmacro get-ol-set-type (tm)
   `(first (get-type-args (get-type ,tm))))

(defmacro is-pair (tm)
   `(and (is-comb ,tm)
      (is-comb (get-rator ,tm))
      (is-const (get-rator (get-rator ,tm)))
      (eq (get-const-name (get-rator (get-rator ,tm))) '|,|)))

(defmacro is-triple (tm) `(and (is-pair ,tm) (is-pair (get-snd ,tm))))

(defmacro get-fst (tm) `(get-rand (get-rator ,tm)))

(defmacro get-snd (tm) `(get-rand ,tm))

(defmacro get-thrd (tm) `(get-snd (get-snd ,tm)))
