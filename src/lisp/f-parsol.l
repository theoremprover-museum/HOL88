;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-parsol.l                                          ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Functions for parsing OL                            ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-franz.l (or f-cl.l), f-constants.l, f-macro.l     ;;;
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
;;;   REVISION HISTORY: Original code: parsol (lisp 1.6) part of Edinburgh  ;;;
;;;                     LCF by M. Gordon, R. Milner and C. Wadsworth (1978) ;;;
;;;                     Transported by G. Huet in Maclisp on Multics, Fall  ;;;
;;;                     1981                                                ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; When changing precedences you must update every call to parse-level.
;;; There are many interactions among the precedences of the operators.

;;; note that the "optr" arg of term-rtn and form-rtn is not used.
;;; thus syntax error messages do not mention the specific operator or
;;; connective being parsed.  Earlier code consed up error message that
;;; usually were not needed, wasting storage.  A better way to make
;;; specific error messages would be to make term-check and form-check
;;; take args msg1, msg2, and msg3 -- which would be concatenated only
;;; if an error actually occurred.  
;;;  - LP

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro"))

#+franz (declare (localf form-check))


;;; Parse an OL quotation (for ML)
(defun parse-ol ()
   (let ((lang1 'ol1) (lang2 'ol2) (langlp 'ollp) (atom-rtn '(ol-atomr))
         (juxtlevel 120)        ; precedence of application
         (%mk=antiquot 'MK=ANTIQUOT)
         (juxt-rtn '(oljuxt arg1)) (ibase 10) (parsedepth 0))
      (parse-level 0)
      ; this check catches dangling predicate symbols
      (if (or (memq (car arg1) term-constrs)
            (memq (car arg1) form-constrs))
         arg1
         (parse-failed "syntax error in quotation"))
      ))  ;parse-ol

;;; declare a user-defined OL infix
;;; called from theory package
(defun olinfix (x typ)
   (let ((lang1 'ol1)(lang2 'ol2)(langlp 'ollp))
      (putprop x typ 'olinfix)
      (binop x (+ olinprec 5)     ; right-associative
         (list (if (eq typ 'paired) 'olinf-rtn 'olcinf-rtn) (list 'quote x)))
      ))  ;olinfix

;;; parse paired OL infix
(defun olinf-rtn (x)
   (list 'MK=COMB
      (mk-ol-atom x)
      (list 'MK=PAIR
         (term-check arg1 "arg1 of infix must be a term")
         (term-check (parse-level olinprec) "arg2 of infix must be a term")))
   )  ;olinf-rtn

;;; parse curried OL infix
(defun olcinf-rtn (x)
   (list 'MK=COMB
      (list 'MK=COMB
         (mk-ol-atom x)
         (term-check arg1 "arg1 of infix must be a term"))
      (term-check (parse-level olinprec)
         "arg2 of infix must be a term")))  ;olcinf-rtn

;;; Added by MJCG on 31.01.94 for HOL88.2.02
;;; declare a user-defined OL infixed variable
;;; dml-ed in f-dml.l

(setq hol-var-binops nil)

(defun olvarinfix (x)
   (let ((lang1 'ol1)(lang2 'ol2)(langlp 'ollp))
      (if (not(memq x hol-var-binops))
          (setq hol-var-binops (cons x hol-var-binops)))
      (binop x (+ olinprec 5)     ; right-associative
         (list 'olcinf-rtn (list 'quote x)))
      nil
      ))  ;olvarinfix

;;; handle parentheses, also special token ()
(defun lpar-rtn ()
   (cond ((eq token rparen-sym) (gnt) '(MK=CONST |()|))
      (t (check rparen-sym (parse-level 0) "bad paren balance")))
   )  ;lpar-rtn

;;; logical connectives
(defun form-rtn (optr constr a b)
   optr                                        ;not used
   (list constr
      (form-check a "arg1 of connective must be a formula")
      (form-check b "arg2 of connective must be a formula")))  ;form-rtn

;;; check that an object is a form, print msg if not
(defun form-check (ob msg)
   (if (memq (car ob) form-constrs) ob (parse-failed msg)))  ;form-check

;;; routine for OL atoms, linked to atom-rtn
(defun ol-atomr () (mk-ol-atom ptoken))  ;ol-atomr

;;; determine the use of an OL atom : constant or variable
;;; for OL, numbers are scanned as symbols
(defun mk-ol-atom (x)
   (cond ((memq x spec-toks)  (parse-failed (catenate x " cannot be a term")))
      ((constp x)  (list 'MK=CONST x))
      ((predicatep x)  (list 'MK=PREDSYM x))
      (t (list 'MK=VAR x))))  ;mk-ol-atom

;;; routine for juxtaposed OL objects, linked to juxt-rtn
;;; handles predicates and combinations
(defun oljuxt (x)
   (if (eq (car x) 'MK=PREDSYM)
      (list 'MK=PREDICATE (cadr x)
         (term-check (parse-level juxtlevel)
            "argument of predicate must be a term"))
      (list 'MK=COMB
         (term-check x "formula terminated by junk")
         (term-check (parse-level juxtlevel)
            "term juxtaposed with formula")))
   )  ;oljuxt

;;; Parse lambda or quantifier
(defun lamq-rtn (constr chk n msg)
   (let ((x (cond ((eq token anticnr-tok) (gnt) (metacall))
               ((not (= toktyp 1))
                  (parse-failed (catenate token " in a prefix")))
               (t (gnt) (mk-ol-atom ptoken)))))
      (while (eq token colon-sym) (gnt) (setq x (list 'MK=TYPED x (olt))))
      (list constr x
         (cond ((eq token period-sym) (gnt) (funcall chk (parse-level n) msg))
            (t (lamq-rtn constr chk n msg))))
      ))  ;lamq-rtn

(defun lam-rtn ()
   (lamq-rtn 'MK=ABS (function term-check) 70
      "lambda body must be a term"))  ;lam-rtn

(defun quant-rtn (constr)
   (lamq-rtn constr (function form-check) 5
      "can only quantify a formula"))  ;quant-rtn

;;; negation -- extends over predicates only
(defun neg-rtn ()
   (list 'MK=NEG
      (form-check (parse-level 59) "can only negate a formula"))) ; neg-rtn


;;; infix operators on terms (comma, ==, <<)
(defun term-rtn (optr constr a b)
   optr                                         ;not used
   (list constr
      (term-check a "arg1 of operator must be a term")
      (term-check b "arg2 of operator must be a term"))) ;term-rtn

;;; check that an object is a term, fail if not
(defun term-check (ob msg)
   (if (memq (car ob) term-constrs) ob (parse-failed msg)))  ;term-check

(defun condl-rtn (p)
   (list 'MK=COND
      (term-check p "condition of conditional not term")
      (term-check (check else-tok (parse-level 80)
            "need 2 nd branch to conditional")
         "1 st branch of conditional not term")
      (term-check (parse-level 80) "2 nd branch of conditional not term")
      ))  ;condl-rtn


;;; antiquotation of terms/forms (MK=ANTIQUOT) or types (MK=TYPE=ANTIQUOT)
(defun metacall ()
   (list %mk=antiquot
      (progn (gnt)
         (cond ((eq ptoken lparen-sym)
               (check rparen-sym (parseml metaprec) "bad antiquotation"))
            ((= ptoktyp 1) (mlatomr))
            ((parse-failed "junk in antiquotation"))))))  ;metacall

;;; type constraint on term
(defun oltyp-rtn ()
   (list 'MK=TYPED
      (term-check arg1 "only a term can have a type")
      (olt)))  ;oltyp-rtn


;;; free-standing type quotation
;;; this is presumably a separate recursive descent parser
(defun olt ()
   (let ((%mk=antiquot 'MK=TYPE=ANTIQUOT))
      (olt1 (olt2 (olt3 (olt4))))))  ;olt

(defun olt1 (x)
   (cond ((eq token arrow-tok) (gnt) (list 'MK=TYPE '|fun| x (olt)))
      (t x)))  ;olt1

;;; PPLAMBDA does not have any built-in "sum" type, but user may define it
(defun olt2 (x)
   (cond ((eq token sum-tok) (gnt)
         (list 'MK=TYPE '|sum| x (olt2 (olt3 (olt4)))))
      (t x)))  ;olt2

(defun olt3 (x)
   (cond ((eq token prod-tok) (gnt) (list 'MK=TYPE '|prod| x (olt3 (olt4))))
      (t x)))  ;olt3

(defun olt4 ()
   (prog (x)
      (gnt)
      (when (eq ptoken lparen-sym)
         (setq x (cond ((eq token rparen-sym) (gnt) nil) (t (olt5))))
         (go l))
      (setq x (list
            (cond ((eq ptoken anticnr-tok) (metacall))
               ((eq ptoken mul-sym)
                  (list 'MK=VARTYPE (vartype-rtn)))
               ((not (= ptoktyp 1))
                  (parse-failed
                     (catenate ptoken " is not allowed in a type")))
               (t (list 'MK=TYPE ptoken)))))
      l  (cond ((= toktyp 1) (gnt))
         ((and x (null (cdr x))) (return (car x)))
         (t (parse-failed "missing type constructor")))
      (setq x (list (cons 'MK=TYPE (cons ptoken x))))
      (go l)))  ;olt4

(defun olt5 ()
   (prog (x)
      (setq x (list (olt)))
      loop (cond ((eq token rparen-sym) (gnt) (return x))
         ((eq token comma-sym) (gnt) (setq x (append x (list (olt))))
            (go loop))
         (t (parse-failed "missing separator or terminator in type")))
      ))  ;olt5


;;; set up OL symbols and precedences

(eval-when (load)
   (let ((lang1 'ol1) (lang2 'ol2) (langlp 'ollp))
      
(putprop endcnrtok 0 'ollp)
(putprop rparen-sym 0 'ollp)
(unop lparen-sym '(lpar-rtn))
(unop forall-tok '(quant-rtn 'MK=FORALL))
(unop exists-tok '(quant-rtn 'MK=EXISTS))
(unop neg-tok '(neg-rtn))

;; in OL, all infixes associate to RIGHT
;; however == and << do not associate at all

;; the first arg of form-rtn should be a string (for error messages)
;; however it is currently unused

;;; iff-tok deleted [TFM 90.01.20]
;;; (binop iff-tok 25
;;;  '(form-rtn 'if-and-only-if 'MK=IFF arg1 (parse-level 20)))
(binop imp-tok 35
   '(form-rtn 'implication 'MK=IMP arg1 (parse-level 30)))
(binop disj-tok 45
   '(form-rtn 'disjunction 'MK=DISJ arg1 (parse-level 40)))
(binop conj-tok 55
   '(form-rtn 'conjunction 'MK=CONJ arg1 (parse-level 50)))
(binop eq-tok 60
   '(term-rtn 'equality 'MK=EQUIV arg1 (parse-level 60)))
(binop ineq-tok 60
   '(term-rtn 'inequality 'MK=INEQUIV arg1 (parse-level 60)))
(binop condl-tok 85 '(condl-rtn arg1))
(binop comma-sym 95
   '(term-rtn 'tupling 'MK=PAIR arg1 (parse-level 90)))
(unop lambda-tok '(lam-rtn))

(putprop else-tok 10 'ollp)    ; the value of the number seems irrelevant

(binop colon-sym 105 '(oltyp-rtn))
(unop anticnr-tok '(metacall))
(unop exfix-sym '(progn (gnt) (mk-ol-atom ptoken)))
))


(setq olinprec 100)


(setq term-constrs '(MK=ANTIQUOT MK=CONST MK=VAR MK=COMB MK=PAIR MK=ABS
      MK=COND MK=TYPED))


;;; MK=IFF deleted [TFM 90.01.20]
(setq form-constrs '(MK=ANTIQUOT MK=PREDICATE
      MK=EQUIV MK=INEQUIV MK=NEG MK=CONJ MK=DISJ
      MK=IMP MK=FORALL MK=EXISTS))


