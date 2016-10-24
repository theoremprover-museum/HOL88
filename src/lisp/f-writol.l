;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-writol.l                                          ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Functions for pretty printing OL                    ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-franz.l (or f-cl.l), f-constants.l, f-macro.l,    ;;;
;;;                     f-ol-rec.l, genmacs.l                               ;;;
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
;;;   REVISION HISTORY: Original code: writol (lisp 1.6) part of Edinburgh  ;;;
;;;                     LCF by M. Gordon, R. Milner and C. Wadsworth (1978) ;;;
;;;                     Transported by G. Huet in Maclisp on Multics, Fall  ;;;
;;;                     1981.                                               ;;;
;;;                                                                         ;;;
;;;                     V2.2: exit instead of err                           ;;;
;;;                                                                         ;;;
;;;                     to do:  right-associative infixes                   ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (include "lisp/f-ol-rec")
   (include "lisp/genmacs"))

#+franz
(declare
   (localf prep-pair
      prep-cond
      prep-curr
      prep-pred-form
      prep-conn-form
      print-abs
      print-pair
      print-conn-form
      print-neg-form
      print-infix-pred
      print-quant-form
      print-named-type))


;;; %printtypes changed to |%show_types-flag| for HOL88 (30/11/88)
(setq |%show_types-flag| nil)

;;; Changed to return old value of flag for HOL88 (30/11/88)
(dml |show_types| 1 ml-show_types (|bool| -> |bool|))
(defun ml-show_types (b)
   (prog1 |%show_types-flag| (setq |%show_types-flag| b)))  ;ml-show_types

(dml |print_term| 1 ml-print_term (|term| -> |void|))

(defun ml-print_term (tm)
   (ptoken |"|)
   (print-tm (prep-tm tm) t t)
   (ptoken |"|)
   )  ;ml-print_term

;;; No formulas in HOL: print_form deleted	[TFM 90.04.20]
;;; (dml |print_form| 1 ml-print_form (|form| -> |void|))

(defun ml-print_form (w)
   (ptoken |"|)
   (print-fm (prep-fm w) t)
   (ptoken |"|)
   )  ;ml-print_form


(dml |print_thm| 1 ml-print_thm (|thm| -> |void|))

(defun ml-print_thm (th)
   (mapc #'(lambda (x) x (ptoken |.|)) (car th))
   (ptoken "|-") 
      (ml-print_form (cdr th))
      )  ;ml-print_thm
   

(dml |print_type| 1 ml-print_type (|type| -> |void|))

(defun ml-print_type (ty)
   (ptoken |":|)
   (print-ty ty t)
   (ptoken |"|)
   )  ;ml-print_type


;;; RJB 1.7.92
;;; Function to print a type without quotes and without the leading colon
(dml |print_unquoted_type| 1 ml-print_unquoted_type (|type| -> |void|))

(defun ml-print_unquoted_type (ty)
   (print-ty ty t)
   )  ;ml-print_unquoted_type


;;; precedence information for when to print brackets
;;; the left symbol binds more tightly than the right symbols
;;; associativity logic is not stored here, but included in printing functions
;;; the symbols include those introduced by prep-tm/fm

(eval-when (load)
   (mapc #'(lambda (x) (putprop (car x) (cdr x) 'closes))
      '((neg . (forall exists conj disj imp)) ; iff deleted [TFM 90.01.20]
         (conj . (forall exists conj disj imp)) ; iff deleted [TFM 90.01.20]
         (disj . (forall exists disj imp)) ; iff deleted [TFM 90.01.20]
         (imp . (forall exists imp)) ; iff deleted [TFM 90.01.20]
;;;      (iff . (forall exists iff)) ; iff deleted [TFM 90.01.20]
         (pair . (abs pair))
         (then . (then))
         (else . (abs then pair))
         (listcomb . (abs listcomb infixcomb then pair typed))
         (infixcomb . (abs listcomb infixcomb then pair typed))
         (typed . (infixcomb))
         (|fun| . (|fun|))
         (|sum| . (|sum| |fun|))
         (|prod| . (|prod| |sum| |fun|))
         )))


;;; are parens needed around "X op2 Y" if a neighboring infix is op1?
(defun closes (op1 op2) (memq op2 (get op1 'closes)))  ;closes


;;; prepare pairs for printing
;;; put the combination ((PAIR X) Y) into a special format
(defun prep-pair (rator rand ty)
   (if (and (is-comb rator)
         (eq (get-const-name (get-rator rator)) 'PAIR))
      (make-prep-term 'pair 
         (list (prep-tm (get-rand rator)) (prep-tm rand))
         ty))
   )  ;prep-pair


;;; prepare conditional for printing
;;; put the combination (((COND P) X) Y) into a special format
(defun prep-cond (rator rand ty)
   (if (is-comb rator)
      (let ((ratrat (get-rator rator)))
         (if (is-comb ratrat)
            (let ((ratratrat (get-rator ratrat)))
               (if (and (is-const ratratrat)
                     (eq (get-const-name ratratrat) 'COND))
                  (make-prep-term 'cond
                     (list (prep-tm (get-rand ratrat))
                        (prep-tm (get-rand rator))
                        (prep-tm rand))
                     ty)))))))          ; prep-cond


;;; detect infixes and long combinations
(defun prep-comb (rator rand ty)
   (let ((prator (prep-tm rator))(prand (prep-tm rand)))
      (cond
         ((and (is-const prator)
               (eq (get (get-const-name prator) 'olinfix) 'paired)
               (eq (term-class prand) 'pair))
            (make-prep-term 'infixcomb (cons prator (get-term-list prand)) ty))
         ((eq (term-class prator) 'listcomb)
            (prep-curr (get-term-list prator) prand ty))
         ((make-prep-term 'listcomb (list prator prand) ty)))
      ))  ;prep-comb


;;; see if ((tm1 tm2 ...) y) is the curried infix "tm2 <tm1> y"
;;; otherwise return (tm1 tm2 ... y)
(defun prep-curr (tml y ty)
   (let ((tm1 (car tml)) (tm2 (cadr tml)) (tmtail (cddr tml)))
      (if (and (null tmtail) (is-const tm1)
            (eq (get (get-const-name tm1) 'olinfix) 'curried))
         (make-prep-term 'infixcomb (list tm1 tm2 y) ty)
         (make-prep-term 'listcomb (append tml (list y)) ty)
         )))                                 ;prep-curr

;;; preprocess a term for easier printing
;;; locate all conditionals, pairs, infixes, and long combinations
(defun prep-tm (tm)
   (case (term-class tm)
      ((var const) tm)
      (abs (make-abs (get-abs-var tm)(prep-tm (get-abs-body tm))
            (get-type tm)))
      (comb (let ((rator (get-rator tm))
               (rand (get-rand tm))
               (ty (get-type tm)))
            (or (prep-pair rator rand ty)
               (prep-cond rator rand ty)
               (prep-comb rator rand ty))))
      (t (lcferror 'prep-tm)))
   )  ;prep-tm


;;; preprocess a formula
(defun prep-fm (fm)
   (case (form-class fm)
      (pred (prep-pred-form (get-pred-sym fm) (prep-tm (get-pred-arg fm))))
      ((conj disj imp) ; iff deleted [TFM 90.01.20]
         (prep-conn-form (get-conn fm)
            (prep-fm(get-left-form fm)) (prep-fm(get-right-form fm))))
      ((forall exists)
         (make-quant-form (get-quant fm)
            (get-quant-var fm) (prep-fm(get-quant-body fm))))
      (t (lcferror 'prep-fm))
      ))  ;prep-fm


;;; re-build a predicate, changing equiv(x,y) to x==y, likewise for inequiv
(defun prep-pred-form (sym arg)
   (if (and (memq sym '(|equiv| |inequiv|))
         (eq 'pair (term-class arg)))
      (cons 'infixpred (cons sym (get-term-list arg)))
      (make-pred-form sym arg))
   )   ; prep-pred-form


;;; re-build a connective formula, changing A ==> FALSITY()  to  ~A
(defun prep-conn-form (conn left right)
   (if (and (eq 'imp conn)
         (eq 'pred (form-class right))
         (eq 'FALSITY (get-pred-sym right)))
      (list 'neg left)
      (make-conn-form conn left right)
      ))  ; prep-conn-form


;;; is the OL type polymorphic?
(defun opoly (ty)
   (or (is-vartype ty) (exists 'opoly (get-type-args ty))))  ;opoly


;;; print a term
;;; op1 is the operator that will be printed before or after
;;;     for deciding whether to print disambiguating parentheses
;;; needty tells print-tm to print enough type information to deduce the
;;;    type of this term, perhaps from the types of its subterms
;;; method for minimizing types that are printed:
;;;    for long combinations whose rator is a polymorphic constant,
;;;    print types of result and operands, but not type of constant
;;; Without optimization, redundant types would cause an exponential amount
;;;    of printing.
(defun print-tm (tm op1 needty)
   (let ((op2 (term-class tm))
         (tml (get-term-list tm))
         (ty (get-type tm)))
      (let ((pcrator                ; is rator a polymorphic constant?
               (and |%show_types-flag|
                  (memq op2 '(listcomb infixcomb))
                  (let ((r (first tml)))    ; find innermost operator
                     (if (eq (term-class r) 'infixcomb)
                        (setq r (first (get-term-list r))))
                     (and (is-const r) (opoly (constp (get-const-name r))))))))
         (let ((tyflag               ; print type of this particular term?
                  (and needty |%show_types-flag|
                     (case op2
                        (var t)
                        (const (opoly (constp (get-const-name tm))))
                        ((listcomb infixcomb) pcrator)
                        (t nil)))))
            ; possibly one pair of parens for precedence, another for typing
            (let ((cl1 (closes op1 (if tyflag 'typed op2)))
                  (cl2 (and tyflag (closes 'typed op2))))
               (if cl1 (ptoken |(|))
               (if cl2 (ptoken |(|))
               (pbegin 0)
               (case op2
                  (var (pstring (get-var-name tm)))
                  (const (print-const (get-const-name tm)))
                  (abs (print-abs tm needty))
                  (cond (print-cond tml needty))
                  (pair  (print-pair tm needty))
                  (listcomb (print-listcomb tml pcrator))
                  (infixcomb (print-infixcomb tml pcrator))
                  (t (lcferror 'print-tm)))
               (cond (tyflag            ; print type
                     (if cl2 (ptoken |)|)
                        (ifn (memq op2 '(var const)) (ptoken | |)))
                     (pbreak 0 0)
                     (ptoken |:|) (print-ty ty t)))
               (if cl1 (ptoken |)|))
               (pend))))))  ;print-tm


;;; print a constant (may be infix standing alone)
(defun print-const (name)
   (if (get name 'olinfix) (ptoken |$|))
   (pstring name))             ; print-const


;;; print an abstraction
(defun print-abs (tm needty)
   (ptoken \\)         ; i.e. lambda
   (print-tm (get-abs-var tm) 'abs nil)
   (ptoken |.|)
   (pbreak 0 0)
   (print-tm (get-abs-body tm) 'abs needty))   ; print-abs


;;; print a conditional
(defun print-cond (tml needty)
   (ptoken |(|)
   (print-tm (first tml) 'then nil)
   (ptoken | => |)
   (pbreak 0 1)
   (print-tm (second tml) 'else nil)
   (ptoken " | ")             ; vertical bar
   (pbreak 0 1)
   (print-tm (third tml) 'else needty)
   (ptoken |)|))              ; print-cond
   

;;; print a pair or n-tuple, suppressing parentheses using associativity
(defun print-pair (tm needty)
   (while (eq 'pair (term-class tm))
      (print-tm (first (get-term-list tm)) 'pair needty)
      (ptoken |,|) (pbreak 0 0)
      (setq tm (second (get-term-list tm))))
   (print-tm tm 'pair needty)) ; print-pair


;;; print a long combination (f x1 ... xn)
(defun print-listcomb (tml pcrator)
   (let ((y (pop tml)) (prev nil))
      (print-tm y 'listcomb (not pcrator))
      (while tml
         (setq prev y) (setq y (pop tml))
         (if (and(memq (term-class prev) '(var const))
               (memq (term-class y)    '(var const)))
            (ptoken | |))  ; space between two identifiers
         (pbreak 0 0)
         (print-tm y 'listcomb pcrator)
         )))                   ; print-listcomb


;;; print a user-defined infix operator
(defun print-infixcomb (tml pcrator)
   (print-tm (second tml) 'infixcomb pcrator)
   (ptoken | |)
   (pstring (get-const-name (first tml)))
   (pbreak 1 0)
   (print-tm (third tml) 'infixcomb pcrator))  ; print-infixcomb


;;; print a formula
(defun print-fm (fm op1)
   (let ((op2 (form-class fm)))
      (let ((cl (closes op1 op2)))
         (if cl (ptoken |(|))
         (pbegin 0)
         (case op2
            ((conj disj imp) (print-conn-form fm)) ; iff deleted [TFM 90.01.20]
            (neg (print-neg-form fm))
            (pred (print-pred-form fm))
            (infixpred (print-infix-pred fm))
            ((forall exists) (print-quant-form fm))
            (t (lcferror 'print-fm)))
         (pend)
         (if cl (ptoken |)|))
         )))  ;print-fm


;;; print a formula built from a connective
;;; suppress parentheses using right-associativity
(defun print-conn-form (fm)
   (let ((conn (get-conn fm)))
      (while (eq conn (get-conn fm))
         (print-fm (get-left-form fm) conn)
         (case (get-conn fm)
            (conj (ptoken \ \ /\\))  ; = |  /\|
            (disj (ptoken \ \ \\/))  ; = |  \/|
            (imp  (ptoken |  ==>|)))
;;;         (iff  (ptoken |  <=>|))) ; iff deleted [TFM 90.01.20]
         (pbreak 2 0)
         (setq fm (get-right-form fm)))
      (print-fm fm conn)))  ; print-conn-form
   

;;; print negation
(defun print-neg-form (fm)
   (ptoken |~ |)
   (print-fm (second fm) 'neg))        ; print-neg-form



;;; print an infix predicate
(defun print-infix-pred (fm)
   (let ((sym (cadr fm)) (arg1 (caddr fm)) (arg2 (cadddr fm)))
      (print-tm arg1 nil nil)
      (case sym
         (|equiv| (ptoken | ==|))
         (|inequiv| (ptoken | <<|))
         (t (ptoken | |) (pstring sym)))
      (pbreak 1 0)
      (print-tm arg2 nil t)))                 ; print-infix-pred

;;; print a predicate formula
(defun print-pred-form (fm)
   (pstring (get-pred-sym fm))
   (pbreak 1 0)
   (print-tm (get-pred-arg fm) t t))   ; print-pred-form


;;; print !x y z.w  instead of !x. !y. !z. w
;;; this makes a big difference if the formula is broken over several lines
(defun print-quant-form (fm)
   (let ((quant (get-quant fm)))
      (pbegin 1)
      (if (eq quant 'forall) (ptoken |!|) (ptoken |?|))
      (print-tm (get-quant-var fm) quant t)
      (let ((body (get-quant-body fm)))
         (while (eq (form-class body) quant)
            (pbreak 1 0)
            (print-tm (get-quant-var body) quant t)
            (setq body (get-quant-body body)))
         (ptoken |.|)
         (pend)
         (pbreak 1 1)
         (print-fm body quant))))  ;prquant

;;; print a type
(defun print-ty (ty op1)
   (let ((op2 (type-class ty)))
      (case op2
         (%VARTYPE (pstring(get-vartype-name ty)))
         ((|prod| |sum| |fun|)
            (let ((cl (closes op1 op2)) (tyargs (get-type-args ty)))
               (if cl (ptoken |(|))
               (pbegin 0)
               (print-ty (first tyargs) op2)
               (case op2
                  (|prod| (ptoken | #|))
                  (|sum| (ptoken | +|))
                  (|fun| (ptoken | ->|))
                  (t (lcferror "bad type - print-ty")))
               (pbreak 1 0)
               (print-ty (second tyargs) op2)
               (pend)
               (if cl (ptoken |)|))))
         (t (print-named-type ty)))))  ;print-ty


;;; Print named type, with its type arguments
(defun print-named-type (ty)
   (let ((tyname (get-type-op ty))  (tyargs (get-type-args ty)))
      (cond ((null tyargs) (pstring tyname))
         (t (pbegin 0)
            (pbegin 1)
            (ptoken |(|)
            (print-ty (first tyargs) nil)  ; nil added V3.2
            (mapc #'(lambda (ty) (ptoken |,|) (pbreak 0 0) (print-ty ty nil))
               (cdr tyargs))
            (pend)
            (ptoken |)|)
            (pbreak 0 0)
            (pstring tyname)
            (pend)))))  ;print-named-type


;;; These functions in this file get redefined later

#-franz
(proclaim
   '(notinline prep-tm print-tm print-const print-cond print-infixcomb
      print-pred-form ml-print_thm prep-comb prep-curr))


