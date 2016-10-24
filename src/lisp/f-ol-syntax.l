;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-ol-syntax.l                                       ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Object language abstract syntax                     ;;;
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
;;;   REVISION HISTORY: Original code: ol0 (lisp 1.6) part of Edinburgh LCF ;;;
;;;                     by M. Gordon, R. Milner and C. Wadsworth   (1978)   ;;;
;;;                     Transported by G. Huet in Maclisp on Multics, Fall  ;;;
;;;                     1981                                                ;;;
;;;                                                                         ;;;
;;;                     V2.2 : new-exit instead of err                      ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (include "lisp/f-ol-rec")
   (special %vtyl %link-names %linkcount |%type_error-flag| %thm-count))


#+franz
(declare (localf new-var-type q-free-var q-typeof strip-antiquot
      print-mk_comb-error prep-ty-for-print 
      get-type-links get-term-links make-link-names prep-term-fn
      prep-ty-fn prep-term-ty add-term-links
      add-type-links))


;;; for writing destructor functions

(eval-when (compile)
   (defmacro destruct (tag x msg)
      `(cond
         ((#+franz eq #-franz eql (car ,x) (quote ,tag))
            (cdr ,x))
         (t
            (throw-from evaluation ,msg)))))  ;destruct

;;; antiquotation

(defun q-mk_antiquot (ob) (cons '%ANTIQUOT ob)) ; q-mk_antiquot

;;; predicates

(defun q-mk_pred (tok tm)
   (if (unify (omutant (predicatep tok)) (q-typeof tm))
      (make-pred-form tok tm)
      (failwith '|mk_pred|)))   ; q-mk_pred

(dml |mk_pred| 2 q-mk_pred ((|string| |#| |term|) -> |form|))

(defun ml-is_pred (fm) (eq (form-class fm) 'pred))  ;ml-is_pred
(dml |is_pred| 1 ml-is_pred (|form| -> |bool|))

(defun ml-dest_pred (fm) (destruct pred fm '|dest_pred|))  ;ml-dest_pred
(dml |dest_pred| 1 ml-dest_pred (|form| -> (|string| |#| |term|)))

;;; conjunction

(defun q-mk_conj (fm1 fm2) (make-conn-form 'conj fm1 fm2))  ;q-mk_conj

(dml |mk_conj| 2 q-mk_conj ((|form| |#| |form|) -> |form|))

(defun ml-is_conj (fm) (eq (form-class fm) 'conj))  ;ml-is_conj
(dml |is_conj| 1 ml-is_conj (|form| -> |bool|))

(defun ml-dest_conj (fm) (destruct conj fm '|dest_conj|))  ;ml-dest_conj
(dml |dest_conj| 1 ml-dest_conj (|form| -> (|form| |#| |form|)) )


;;; disjunction

(defun q-mk_disj (fm1 fm2) (make-conn-form 'disj fm1 fm2))  ;q-mk_disj
(dml |mk_disj| 2 q-mk_disj ((|form| |#| |form|) -> |form|) )

(defun ml-is_disj (fm) (eq (form-class fm) 'disj))  ;ml-is_disj
(dml |is_disj| 1 ml-is_disj (|form| -> |bool|))

(defun ml-dest_disj (fm) (destruct disj fm '|dest_disj|))  ;ml-dest_disj
(dml |dest_disj| 1 ml-dest_disj (|form| -> (|form| |#| |form|)) )



;;; implication

(defun q-mk_imp (fm1 fm2) (make-conn-form 'imp fm1 fm2))  ;q-mk_imp
(dml |mk_imp| 2 q-mk_imp ((|form| |#| |form|) -> |form|) )

(defun ml-is_imp (fm)  (eq (form-class fm) 'imp))  ;ml-is_imp
(dml |is_imp| 1 ml-is_imp (|form| -> |bool|))

(defun ml-dest_imp (fm)  (destruct imp fm '|dest_imp|))  ;ml-dest_imp
(dml |dest_imp| 1 ml-dest_imp (|form| -> (|form| |#| |form|)) )



;;; if-and-only-if
;;; all deleted [TFM 90.01.20]

;;;(defun q-mk_iff (fm1 fm2) (make-conn-form 'iff fm1 fm2))  ;q-mk_iff
;;;(dml |mk_iff| 2 q-mk_iff ((|form| |#| |form|) -> |form|) )

;;;(defun ml-is_iff (fm) (eq (form-class fm) 'iff))  ;ml-is_iff
;;;(dml |is_iff| 1 ml-is_iff (|form| -> |bool|))

;;;(defun ml-dest_iff (fm)  (destruct iff fm '|dest_iff|))  ;ml-dest_iff
;;;(dml |dest_iff| 1 ml-dest_iff (|form| -> (|form| |#| |form|)) )

;;; negation is a special case of implication, thus no destructors, etc.

(defun q-mk_neg (fm) (make-conn-form 'imp fm %falsity))  ;q-mk_neg

;;; universal quantifier

(defun q-mk_forall (v fm)
   (let ((v (strip-antiquot v)))
      (q-free-var v)
      (ml-mk_forall v fm))
   )  ;q-mk_forall

(defun ml-mk_forall (v fm)
   (if (is-var v) (make-quant-form 'forall v fm)
      (failwith '|mk_forall|)))  ;ml-mk_forall

(dml |mk_forall| 2 ml-mk_forall ((|term| |#| |form|) -> |form|))

(defun ml-is_forall (fm)  (eq (form-class fm) 'forall))  ;ml-is_forall
(dml |is_forall| 1 ml-is_forall (|form| -> |bool|))

(defun ml-dest_forall (fm)  (destruct forall fm '|dest_forall|)) ;ml-dest_forall
(dml |dest_forall| 1 ml-dest_forall (|form| -> (|term| |#| |form|)) )



;;; existential quantifier


(defun q-mk_exists (v fm)
   (let ((v (strip-antiquot v)))
      (q-free-var v)
      (ml-mk_exists v fm))
   )  ;q-mk_exists

(defun ml-mk_exists (v fm)
   (if (is-var v) (make-quant-form 'exists v fm)
      (failwith '|mk_exists|)))  ;ml-mk_exists

(dml |mk_exists| 2 ml-mk_exists ((|term| |#| |form|) -> |form|))

(defun ml-is_exists (fm)  (eq (form-class fm) 'exists))  ;ml-is_exists
(dml |is_exists| 1 ml-is_exists (|form| -> |bool|))

(defun ml-dest_exists (fm)  (destruct exists fm '|dest_exists|))  ;ml-dest_exists
(dml |dest_exists| 1 ml-dest_exists (|form| -> (|term| |#| |form|)) )


;;; equivalence and inequivalence are special cases of predicates
;;; thus no destructors, etc.

(defun q-mk_equiv (tm1 tm2)
   (failtrap #'(lambda (tok) (failwith '|mk_equiv|))
      (q-mk_pred '|equiv| (q-mk_pair tm1 tm2))))   ; q-mk_equiv

(defun q-mk_inequiv (tm1 tm2)
   (failtrap #'(lambda (tok) (failwith '|mk_inequiv|))
      (q-mk_pred '|inequiv| (q-mk_pair tm1 tm2))))   ; q-mk_ienequ

;;; variables

;;; In a quotation, all variables with the same name are identical --
;;; the alist %vtyl makes sure of that.
(defun q-mk_var (tok)
   (make-var tok
      (or (assoc1 tok %vtyl)
         (new-var-type tok)))
   )  ;q-mk_var


;;; create a new type variable and put it on %vtyl
(defun new-var-type (tok)
   (let ((newty (genlink)))
      (push (cons tok newty) %vtyl)
      newty))                  ; new-var-type


;;; allows bound variables of the same name to be independent
(defun q-free-var (v)
   (if (is-var v) (new-var-type (get-var-name v)))
   )                               ; q-free-var



;;; variable names must be identifiers
;;; thus genvars will be distinct from any other variables
;;; MJCG 30/11/88 for HOL88
;;; removed check that variables are constants or allowable identifiers
;;; Old code:
;;;(defun ml-mk_var (tok ty)
;;; (if (or (constp tok) (not (idenp tok))) (failwith '|mk_var|)
;;;     (mk_realvar tok ty)))  ;ml-mk_var

;;; set up sharing so equivalent variables are "eq"
(defun mk_realvar (tok ty)
   (or (assoc1 ty (get tok '|mk_var|))
      (cdr (consprop tok (cons ty (make-var tok ty)) '|mk_var|))))
; mk_realvar
;;; MJCG 30/11/88 for HOL88
;;; ml-mk_var replaced by mk_realvar
(dml |mk_var| 2 mk_realvar ((|string| |#| |type|) -> |term|))

;;; Generate a variable, with name that can't conflict with any other
;;; (presuming that genvars cannot be read from theory files)
;;;  the name is interned by uniquesym (to avoid weird consequences)
(defun ml-genvar  (ty) (mk_realvar (uniquesym 'gen 'var) ty))  ;ml-genvar

(defun ml-is_var (term)  (eq (term-class term) 'var))  ;ml-is_var
(dml |is_var| 1 ml-is_var (|term| -> |bool|))

(defun ml-dest_var (tm) (destruct var tm '|dest_var|))  ;ml-dest_var
(dml |dest_var| 1 ml-dest_var (|term| -> (|string| |#| |type|)))



;;; constants

(defun q-mk_const (tok) (make-const tok (omutant (constp tok))))  ;q-mk_const

;;; includes code to share constants of identical types
;;; (this wastes storage...does it do any good?)
;;; MJCG 1/12/88 for HOL88
;;; Informative failure messages added
(defun ml-mk_const (tok ty)
   (cond
      ((assoc1 ty (get tok '|mk_const|)))
      ((and (constp tok) (unify ty (omutant(constp tok))))
         (cdr (consprop tok (cons ty (make-const tok ty)) '|mk_const|)))
      ((not(constp tok))
         (failwith (concat "mk_const: " tok " not a constant")))
      ((not(unify ty (omutant(constp tok))))
         (failwith (concat "mk_const: wrong type for " tok " supplied")))
      (t (failwith "mk_const: mystery failure;  please report")))
   )  ;ml-mk_const

(dml |mk_const| 2 ml-mk_const ((|string| |#| |type|) -> |term|))

(defun ml-is_const (term)  (eq (term-class term) 'const))  ;ml-is_const
(dml |is_const| 1 ml-is_const (|term| -> |bool|))

(defun ml-dest_const (tm) (destruct const tm '|dest_const|))  ;ml-dest_const
(dml |dest_const| 1 ml-dest_const (|term| -> (|string| |#| |type|)))



;;; abstractions

(defun q-mk_abs (v tm)
   (let ((v (strip-antiquot v)))
      (q-free-var v)
      (ml-mk_abs v tm))
   )  ;q-mk_abs

(dml |mk_abs| 2 ml-mk_abs ((|term| |#| |term|) -> |term|))

(defun ml-mk_abs (v tm)
   (if (is-var v)
      (make-abs v tm (make-type '|fun| (list (q-typeof v) (q-typeof tm))))
      (failwith '|mk_abs|)))  ;ml-mk_abs

(dml |is_abs| 1 ml-is_abs (|term| -> |bool|))
(defun ml-is_abs (term)  (eq (term-class term) 'abs))  ;ml-is_abs

;;; different from other destructors -- throws away the type
(defun ml-dest_abs (tm) (car (destruct abs tm '|dest_abs|)))  ;ml-dest_abs
(dml |dest_abs| 1 ml-dest_abs (|term| -> (|term| |#| |term|)))


;;; MJCG 2/12/88 for HOL88
;;; The code that follows is to generate nice error messages
;;; from mk_comb and indeterminate types in quotations.
;;; The code is pretty inefficient (it does multiple passes), 
;;; but since it is only invoked on errors this should not be a problem.

;;; MJCG 13/11/88 for HOL88
;;; Function for making a partially evaluated term printable
;;; (remove antiquotations etc)
(defun prep-term-fn (tm)
   (case (term-class tm)
      (var (make-var (get-var-name tm) (prep-ty-fn(get-type tm))))
      (const (make-const (get-const-name tm) (prep-ty-fn(get-type tm))))
      (comb (make-comb (prep-term-fn(get-rator tm))
            (prep-term-fn(get-rand tm))
            (prep-ty-fn(get-type tm))))
      (abs (make-abs (prep-term-fn(get-abs-var tm))
            (prep-term-fn(get-abs-body tm))
            (prep-ty-fn(get-type tm))))
      (%ANTIQUOT (prep-term-fn(cdr tm)))
      (t  (failwith 
            "Error in Lisp function prep-term-fn -- please report"))))

(defun prep-term-for-print (tm)
   (let ((tm1 (add-term-links tm)))
      (let ((%link-names (make-link-names(get-term-links tm1))))
         (prep-term-fn tm1))))

;;; MJCG 2/12/88 for HOL88
;;; Replace (%LINK) by (%LINK . N) in a term
;;; side effects %linkcount
(defun add-term-links (tm)
   (case (term-class tm)
      (var (make-var(get-var-name tm) (add-type-links(get-type tm))))
      (const (make-const(get-const-name tm) (add-type-links(get-type tm))))
      (comb (make-comb (add-term-links(get-rator tm))
            (add-term-links(get-rand tm))
            (add-type-links(get-type tm))))
      (abs  (make-abs (add-term-links(get-abs-var tm))
            (add-term-links(get-abs-body tm))
            (add-type-links(get-type tm))))
      (%ANTIQUOT (add-term-links(cdr tm)))
      (t  (failwith 
            "Error in Lisp function add-term-links -- please report"))))

;;; MJCG 2/12/88 for HOL88
;;; Replace (%LINK) by (%LINK . N) in a type
;;; side effects %linkcount
(defun add-type-links (ty)
   (case (type-class ty)
      (%ANTIQUOT (cdr ty))
      (%VARTYPE ty)
      (%LINK (cond ((numberp (cdr ty)) ty)
            ((null (cdr ty))
               (cons '%LINK (incf %linkcount)))
            (t (add-type-links(cdr ty)))))
      (t (make-type 
            (get-type-op ty)
            (mapcar (function add-type-links) (get-type-args ty))))))

;;; MJCG 2/12/88 for HOL88
;;; Function for extracting %LINKs from a type
(defun get-type-links (ty)
   (case (type-class ty)
      ((%ANTIQUOT %VARTYPE) nil)
      (%LINK (if (numberp (cdr ty)) 
            (list (cdr ty))
            (get-type-links(cdr ty))))
      (t (apply (function append)
            (mapcar (function get-type-links) (get-type-args ty))))))

;;; MJCG 25/11/88 for HOL88
;;; Function for extracting %LINKs from a term
(defun get-term-links (tm)
   (case (term-class tm)
      (var (get-type-links(get-type tm)))
      (const (get-type-links(get-type tm)))
      (comb (append (get-term-links(get-rator tm))
            (get-term-links(get-rand tm))))
      (abs (append  (get-term-links(get-abs-var tm))
            (get-term-links(get-abs-body tm))))
      (%ANTIQUOT (get-term-links(cdr tm)))
      (t  (failwith 
            "Error in Lisp function get-term-links -- please report"))))

;;; MJCG 25/11/88 for HOL88
;;; Make a map from %LINK numbers to print names ?, ?1, ?2 ...
(defun make-link-names (l)
   (prog (ll link-names n)
      (cond ((null l)          (return (list nil)))
         ((= (length l) 1) (return (list(cons (car l) '|?|)))))
      (setq n 1)
      (setq ll l)
      (setq link-names nil)
      loop (cond ((null ll) (return link-names))
         ((assoc-equal (car ll) link-names))
         (t
            (setq link-names 
               (cons (cons (car ll) (concat '|?| n)) link-names))
            (setq n (add1 n))))
      (setq ll (cdr ll))
      (go loop)))

;;; MJCG 13/11/88 for HOL88
;;; Function for making a partially typechecked type printable
;;; (remove antiquotations, %LINK, %VARTYPE etc)
;;; MJCG 25/11/88 for HOL88
;;; Code for ?, ?1, ?2, ?3 ... added

(defun prep-ty-fn (ty)
   (case (type-class ty)
      (%ANTIQUOT (cdr ty))
      (%VARTYPE ty)
      (%LINK (if (numberp (cdr ty)) 
            (make-vartype (cdr (assoc-equal (cdr ty) %link-names)))
            (prep-ty-fn(cdr ty))))
      (t (make-type (get-type-op ty) 
            (mapcar (function prep-ty-fn) 
               (get-type-args ty))))))

(defun prep-ty-for-print (ty)
   (let ((ty1 (add-type-links ty)))
      (let ((%link-names (make-link-names(get-type-links ty1))))
         (prep-ty-fn ty1))))

;;; MJCG 13/11/88 for HOL88
;;; Get type (stripping off %ANTIQUOT if necessary)
(defun prep-term-ty (tm)
   (if (eq (car tm) '%ANTIQUOT) (get-type(cdr tm)) (get-type tm)))

;;; MJCG 13/11/88 for HOL88
;;; Function for printing mk_comb failure error messages
(defun print-mk_comb-error (tm1 tm2)
   (progn (ptoken "Badly typed application of:")
      (pbreak 2 4)
      (ml-print_term(prep-term-for-print tm1))
      (pnewline)
      (ptoken "   which has type:         ")
      (pbreak 2 4)
      (ml-print_type(prep-ty-for-print(prep-term-ty tm1)))
      (pnewline)
      (ptoken "to the argument term:      ")
      (pbreak 2 4)
      (ml-print_term(prep-term-for-print tm2))
      (pnewline)
      (ptoken "   which has type:         ")
      (pbreak 2 4)
      (ml-print_type(prep-ty-for-print(prep-term-ty tm2)))
      (pnewline)
      (pnewline)))

;;; MJCG 13/11/88 for HOL88
;;; Flag to control printing of type errors
(setq |%type_error-flag| t)

;;; MJCG 10/11/88 for HOL88
;;; add error message printing
;;; combinations

(defun q-mk_comb (tm1 tm2)
   (let ((ty (genlink)))
      (if (unify (q-typeof tm1) (make-type '|fun| (list (q-typeof tm2) ty)))
         (make-comb tm1 tm2 ty)
         (prog2 (if |%type_error-flag| (print-mk_comb-error tm1 tm2))
            (failwith '|mk_comb|)))))  ;q-mk_comb


;;; q-mk_comb tries to unify types while ml-mk_comb expects an exact match
;;;    and returns a type free of links.
(defun ml-mk_comb (tm1 tm2)
   (let* ((constyoptyargs
            (failtrap #'(lambda (tok) (failwith '|mk_comb|))
               (ml-dest_type (get-type tm1))))
         (tyop (car constyoptyargs))
         (tyargs (cdr constyoptyargs)))
      (if (and (eq tyop '|fun|) (equal (first tyargs)(get-type tm2)))
         (make-comb tm1 tm2 (second tyargs))
         ;;;        (prog2 (if |%type_error-flag| (print-mk_comb-error tm1 tm2))
         ;;;                 (failwith '|mk_comb|))))
         (failwith '|mk_comb|)))
   )  ;ml-mk_comb

(dml |mk_comb| 2 ml-mk_comb ((|term| |#| |term|) -> |term|))

(defun ml-is_comb (term)  (eq (term-class term) 'comb))  ;ml-is_comb
(dml |is_comb| 1 ml-is_comb (|term| -> |bool|))

(defun ml-dest_comb (tm) (car (destruct comb tm '|dest_comb|)))  ;ml-dest_comb
(dml |dest_comb| 1 ml-dest_comb (|term| -> (|term| |#| |term|)))



;;; other terms

;;; put a type constraint onto a term
;;; the type is antiquoted for efficiency
;;;    to prevent canon-ty from traversing it
(defun q-mk_typed (tm ty)
   (if (unify (q-typeof tm) (q-mk_antiquot ty)) tm
      (failwith '|types|))
   )  ;q-mk_typed


(defun q-mk_pair (tm1 tm2) (q-mk_comb (q-mk_comb (q-mk_const 'PAIR) tm1) tm2))  ;q-mk_pair

(defun q-mk_cond (tm1 tm2 tm3)
   (q-mk_comb (q-mk_comb (q-mk_comb (q-mk_const 'COND) tm1) tm2) tm3)
   )  ;q-mk_cond




;;; vartypes

;;; create a vartype, maintaining sharing so equivalent vartypes are "eq"
(defun q-mk_vartype (tok)
   (cond
      ((get tok '|mk_vartype|))
      ((= (first (exploden tok)) #/*)
         (putprop tok (make-vartype tok) '|mk_vartype|))
      ((failwith '|mk_vartype|))
      ))  ;q-mk_vartype

(dml |mk_vartype| 1 q-mk_vartype (|string| -> |type|))

(defun ml-is_vartype (ty)  (eq (type-class ty) '%VARTYPE))  ;ml-is_vartype
(dml |is_vartype| 1 ml-is_vartype (|type| -> |bool|))

(defun ml-dest_vartype (ty)
   (if (is-vartype ty) (get-vartype-name ty)
      (failwith '|dest_vartype|)))  ;ml-dest_vartype

(dml |dest_vartype| 1 ml-dest_vartype (|type| -> |string|))



;;; compound types

;;; make a compound type ... check number of arguments
(defun q-mk_type (op tylist)
   (cond
      ((not (equal (get op 'olarity) (length tylist)))
         (failwith '|mk_type|))
      ((null tylist) (get op 'canon))
      (t (make-type op tylist))))
;q-mk_type

(dml |mk_type| 2 q-mk_type ((|string| |#| (|type| |list|)) -> |type|))


;;; no discriminator -- use (not is_vartype)


(defun ml-dest_type (ty)
   (if (is-vartype ty) (failwith '|dest_type|) ty))  ;ml-dest_type

(dml |dest_type| 1 ml-dest_type (|type| -> (|string| |#| (|type| |list|))))

;;; type of any term

(defun ml-type_of (tm)  (get-type tm))  ;ml-type_of
(dml |type_of| 1 ml-type_of (|term| -> |type|))


;;; type of a term in a quotation
(defun q-typeof (tm) (get-type (strip-antiquot tm)))  ;q-typeof


;;; Skip over ANTIQUOT nodes
(defun strip-antiquot (ob) (while (is-antiquot ob) (setq ob (cdr ob))) ob)  ; strip-antiquot


(setq %thm-count 0)             ; count theorems inferred in session


(defun ml-thm_count () %thm-count) ;ml-thm_count
(dml |thm_count| 0 ml-thm_count (|void| -> |int|))


(defun ml-mk_thm (sq)  (incf %thm-count)  sq)  ;ml-mk_thm
(dml |mk_thm| 1 ml-mk_thm (((|form| |list|) |#| |form|) -> |thm|))


(defun ml-dest_thm (sq)  sq)  ;ml-dest_thm
(dml |dest_thm| 1 ml-dest_thm (|thm| -> ((|form| |list|) |#| |form|)))


;;; the following function definitions depend on the Lisp representation
;;; of theorems, terms, and formulas.

(dml |hyp| 1 car (|thm| -> (|form| |list|)))

(dml |concl| 1 cdr (|thm| -> |form|))

;;; if tok is a predicate symbol, then return its type, else nil
(defun predicatep (tok) (get tok 'predicate))  ; predicatep

;;; if tok is a constant symbol, then return its type, else nil
(defun constp (tok) (get tok 'const))  ;constp

;;; the predicate FALSITY()
(setq %empty (make-const '|()| (make-type '|void| nil)))
(setq %falsity (make-pred-form 'FALSITY %empty))

;;; term_class used nowhere in HOL88: deleted	[TFM 90.06.05] 
;;; (dml |term_class| 1 car (|term| -> |string|))

;;; Deleted: formulas not used in HOL  [TFM 90.06.27]
;;; (dml |form_class| 1 car (|form| -> |string|))


(dml |genvar| 1 ml-genvar (|type| -> |term|))


;;; This function defined in this file gets redefined later

#-franz (proclaim '(notinline constp))

