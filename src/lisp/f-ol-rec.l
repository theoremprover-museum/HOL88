;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-ol-rec.l                                          ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Definition of object language data structures       ;;;
;;;   AUTHOR:           Larry Paulson (October 1982)                        ;;;
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
;;;   REVISION HISTORY: (none)                                              ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile) (macros t))


(defmacro make-thm (asl w) `(cons ,asl ,w))
(defmacro get-hyp (th) `(car ,th))
(defmacro get-concl (th) `(cdr ,th))

(defmacro make-conn-form (conn left right)
   `(cons ,conn (cons ,left ,right)))
(defmacro get-conn (fm) `(car ,fm))
(defmacro get-left-form (fm) `(cadr ,fm))
(defmacro get-right-form (fm) `(cddr ,fm))

(defmacro make-quant-form (quant var body)
   `(cons ,quant (cons ,var ,body)))
(defmacro get-quant (fm) `(car ,fm))
(defmacro get-quant-var (fm) `(cadr ,fm))
(defmacro get-quant-body (fm) `(cddr ,fm))

(defmacro make-pred-form (pred tm)
   `(cons 'pred (cons ,pred ,tm)))
(defmacro get-pred-sym (fm) `(cadr ,fm))
(defmacro get-pred-arg (fm) `(cddr ,fm))

(defmacro form-class (fm) `(car ,fm))

;;; Terms -- each class of term stores the type in the same place

(defmacro make-var (name ty) `(cons 'var (cons ,name ,ty)))
(defmacro is-var (tm) `(eq (car ,tm) 'var))
(defmacro get-var-name (tm) `(cadr ,tm))

(defmacro make-const (name ty) `(cons 'const (cons ,name ,ty)))
(defmacro is-const (tm) `(eq (car ,tm) 'const))
(defmacro get-const-name (tm) `(cadr ,tm))

(defmacro make-abs (var body ty)
   `(cons 'abs (cons (cons ,var ,body) ,ty)))
(defmacro is-abs (tm) `(eq (car ,tm) 'abs))
(defmacro get-abs-var (tm) `(caadr ,tm))
(defmacro get-abs-body (tm) `(cdadr ,tm))

(defmacro make-comb (rator rand ty)
   `(cons 'comb (cons (cons ,rator ,rand) ,ty)))
(defmacro is-comb (tm) `(eq (car ,tm) 'comb))
(defmacro get-rator (tm) `(caadr ,tm))
(defmacro get-rand (tm) `(cdadr ,tm))

(defmacro get-type (tm) `(cddr ,tm))
(defmacro put-type (tm ty)
   ;; used in F-thyfns
   `(rplacd (cdr ,tm) ,ty))

(defmacro term-class (tm) `(car ,tm))

;;; Types

(defmacro make-type (tyop tyargs) `(cons ,tyop ,tyargs))
(defmacro get-type-op (ty) `(car ,ty))
(defmacro get-type-args (ty) `(cdr ,ty))

(defmacro make-vartype (name) `(cons '%VARTYPE ,name))
(defmacro is-vartype (ty) `(eq (car ,ty) '%VARTYPE))
(defmacro get-vartype-name (ty) `(cdr ,ty))

(defmacro is-linktype (ty) `(eq (car ,ty) '%LINK))

(defmacro type-class (ty) `(car ,ty))

(defmacro is-antiquot (ob) `(eq (car ,ob) '%ANTIQUOT))
