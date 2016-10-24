;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-inst.l                                            ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Object language type instantiation                  ;;;
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
;;;   REVISION HISTORY: Original code: ol3 (lisp 1.6) part of Edinburgh LCF ;;;
;;;                     by M. Gordon, R. Milner and C. Wadsworth   (1978)   ;;;
;;;                     Transported by G. Huet in Maclisp on Multics, Fall  ;;;
;;;                     1981                                                ;;;
;;; Hol version 2.02:   Bug in INST_TYPE fixed :        [MJCG 25.01.94]     ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Sharing relationships in types must be detected -- dumb algorithms that
;;; expand type DAGs into trees will consume exponential time and space!
;;; This particularly holds for algorithms that traverse all types of a term,
;;; for note the duplication of types in combinations:
;;;             ((F : ty1 -> ty2)  (X : ty1))  : ty2

;;; The instantiation of terms and formulas is now implemented in Lisp,
;;; as the ML versions were exponential.

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (include "lisp/f-ol-rec")
   (special %clash-danger-vars))


#+franz
(declare
   (localf tyvars-type instin-type instin-var rename-var forget-var
           typel-in-tm strip-primes-aux strip-primes))


;;; *********************************************


(dml |type_in_type| 2 ml-type_in_type ((|type| |#| |type|) -> |bool|))
(dml |type_in| 2 ml-type_in_term ((|type| |#| |term|) -> |bool|))

;;; No formulas in HOL: paired_type_in_form deleted	[TFM 90.04.19]
;;; (dml |paired_type_in_form| 2 ml-type_in_form ((|type| |#| |form|) -> |bool|))


(defun ml-type_in_type (%ty ty)
   (let ((%oldtys nil)) (type-in-type ty)))


;;; does %ty occur anywhere inside ty?
;;; record compound types already seen to avoid re-traversal
(defun type-in-type (ty)
   (cond ((memq ty %oldtys) nil)
      ((equal ty %ty) t)
      ((not (is-vartype ty))
         (prog1 (exists 'type-in-type (cdr (ml-dest_type ty)))
            (push ty %oldtys)))
      ))  ;type-in-type


;;; No formulas in HOL: deleted	[TFM 90.04.19]
;;;(defun ml-type_in_form (%ty ob)
;;;   (let ((%oldtys nil)) (type-in-fm ob)))


(defun ml-type_in_term (%ty ob)
   (let ((%oldtys nil)) (type-in-tm ob)))


;;; does %ty appear in the formula?
(defun type-in-fm (fm)
   (case (form-class fm)
      ((conj disj imp) ; iff deleted [TFM 90.01.20]
         (or (type-in-fm (get-left-form fm)) (type-in-fm (get-right-form fm))))
      ((forall exists)
         (or (type-in-tm (get-quant-var fm)) (type-in-fm (get-quant-body fm))))
      (pred (type-in-tm (get-pred-arg fm)))
      (t (lcferror (cons fm '|type-in-fm|))))
   )    ; type-in-fm


;;; does %ty appear in the term?
(defun type-in-tm (tm)
   (case (term-class tm)
      ((var const) (type-in-type (get-type tm)))
      (abs (or (type-in-tm (get-abs-var tm)) (type-in-tm (get-abs-body tm))))
      (comb (or (type-in-tm (get-rator tm)) (type-in-tm (get-rand tm))))
      (t (lcferror '|type-in-tm|)))
   )    ; type-in-tm


;;; *********************************************

(dml |type_tyvars| 1 ml-type-tyvars (|type| -> (|type| |list|)))


;;; term_tyvars renamed to be tyvars [TFM 90.06.04]
;;; (dml |term_tyvars| 1 ml-term_tyvars (|term| -> (|type| |list|)))

(dml |tyvars| 1 ml-term_tyvars (|term| -> (|type| |list|)))

;;; Deleted: formulas not used in HOL  [TFM 90.06.27]
;;; (dml |form_tyvars| 1 ml-form_tyvars (|form| -> (|type| |list|)))


(defun ml-type-tyvars  (ty)
   (let ((%tyvl nil) (%oldtys nil))
      (tyvars-type ty)
      (nreverse %tyvl)))          ; ml-type-tyvars




;;; find all type variables in a type
;;;
;;; [DES] 17feb92 member-equal for memq; again exponentiality.
;;; Looks as if my big tuples have gone over the limit where things
;;; start showing up. Found another problem as equivalent types
;;; are not necessarily "eql". This shows itself up in
;;; tyvars-type. Basically %oldtys was getting over 4000 things
;;; stuck on it. When using member-equal only 170 were there 
;;; (i.e. 3800-odd members were equiavalent types with a
;;; different top level cons cell).
;;;
;;; (defun tyvars-type (ty)
;;;   (cond ((memq ty %oldtys))
;;;      ((is-vartype ty) (setq %tyvl (inq ty %tyvl)))
;;;      (t (mapc #'tyvars-type (cdr (ml-dest_type ty)))
;;;         (push ty %oldtys))    
;;;      ))   ; tyvars

(defun tyvars-type (ty)
   (cond ((member-equal ty %oldtys))
      ((is-vartype ty) (setq %tyvl (inq ty %tyvl)))
      (t (mapc #'tyvars-type (cdr (ml-dest_type ty)))
         (push ty %oldtys))
      ))   ; tyvars

;;; Deleted: formulas not used in HOL  [TFM 90.06.27]
;;; (defun ml-form_tyvars(ob)
;;;   (let ((%tyvl nil) (%oldtys nil))
;;;      (tyvars-fm ob)
;;;      (nreverse %tyvl)))


(defun ml-term_tyvars(ob)
   (let ((%tyvl nil) (%oldtys nil))
      (tyvars-tm ob)
      (nreverse %tyvl)))


;;; find all type variables in a formula
(defun tyvars-fm (fm)
   (case (form-class fm)
	 ((conj disj imp) ; iff deleted [TFM 90.01.20]
         (tyvars-fm (get-left-form fm)) (tyvars-fm (get-right-form fm)))
      ((forall exists)
         (tyvars-tm (get-quant-var fm)) (tyvars-fm (get-quant-body fm)))
      (pred (tyvars-tm (get-pred-arg fm)))
      (t (lcferror (cons fm '|tyvars-fm|))))
   )                                             ; tyvars-fm


;;; find all type variables in a term
(defun tyvars-tm (tm)
   (case (term-class tm)
      ((var const) (tyvars-type (get-type tm)))
      (abs (tyvars-tm (get-abs-var tm)) (tyvars-tm (get-abs-body tm)))
      (comb (tyvars-tm (get-rator tm)) (tyvars-tm (get-rand tm)))
      (t (lcferror '|tyvars-tm|)))
   )    ; tyvars-tm


;;; *********************************************

;;; type instantiation

;;; Renames variables to ensure that no distinct variables become identical
;;; after instantiation -- makes variants of all (and ONLY) those
;;; variables whose types change and whose names match.
;;; The first argument of inst_term and inst_form is
;;; a list of variables whose names must not be used.
;;; This handles free variables in the assumption list for the rule INST_TYPE.

;;; Original code does not detect capture of free variables when a type
;;; instantiation causes a variable to become identical to a lambda-bound
;;; variable whose scope it is in. This is fixed by a patch at the end
;;; of the file and in the ML code for INST_TYPE (MJCG 15/10/1989). 
;;; Problem detected by Roger Jones' group at ICL Defence Systems.


(dml |inst_type| 2 ml-inst_type
   ((((|type| |#| |type|) |list|) |#| |type|) -> |type|))

(dml |inst| 3 ml-inst_term
   (((|term| |list|) |#| (((|type| |#| |type|) |list|) |#| |term|)) -> |term|))

;;; No formulas in HOL: paired_inst_form deleted	[TFM 90.04.19]
;;;(dml |paired_inst_form| 3 ml-inst_form
;;;   (((|term| |list|) |#| (((|type| |#| |type|) |list|) |#| |form|)) -> |form|))


(defun ml-inst_type (%insttyl ty)
   (if %insttyl (instin-type ty) ty))  ;ml-instintype


;;; No formulas in HOL: ml-inst_form deleted	[TFM 90.04.19]
;;;(defun ml-inst_form (used-vars %insttyl ob)
;;;   (if %insttyl
;;;      (let ((%renames nil)
;;;            (%changed-types (mapcar #'cdr %insttyl))
;;;            (%used-varnames (var-name-list used-vars 'inst))) 
;;;         (instin-fm ob))
;;;      ob))                     ; ml-inst-in-fm

;;; GH:duplicated code of ml-inst-in for forms and terms
(defun ml-inst_term (used-vars %insttyl ob)
   (if %insttyl
      (let ((%renames nil)
            (%changed-types (mapcar #'cdr %insttyl))
            (%used-varnames (var-name-list used-vars 'inst))) 
         (instin-tm ob))
      ob))                     ; ml-inst-in-tm


;;; instantiate types in a type
;;; record values of compound types to save re-traversal
(defun instin-type (ty)
   (cond
      ((revassoc1 ty %insttyl))
      ((is-vartype ty) ty)
      ((let* ((constyoptyargs (ml-dest_type ty))
               (tyop (car constyoptyargs))
               (tyargs (cdr constyoptyargs)))
            (let ((newty (make-type tyop (mapcar #'instin-type tyargs))))
               (push (cons newty ty) %insttyl)
               newty))
         )))  ;instin-type

;;; instantiate types in a formula
(defun instin-fm (fm)
   (case (form-class fm)
      ((conj disj imp) ; iff deleted [TFM 90.01.20]
         (make-conn-form (get-conn fm)
            (instin-fm (get-left-form fm))
            (instin-fm (get-right-form fm))))
      ((forall exists)
         (make-quant-form (get-quant fm)
            (instin-tm (get-quant-var fm))
            (instin-fm (get-quant-body fm))))
      (pred (make-pred-form (get-pred-sym fm)
            (instin-tm (get-pred-arg fm))))
      (t (lcferror 'instin-fm)))
   )    ; instin-fm



;;; instantiate types in a term
(defun instin-tm (tm)
   (case (term-class tm)
      (var (instin-var tm))
      (const (ml-mk_const (get-const-name tm)
            (instin-type (get-type tm))))
      (abs (ml-mk_abs (instin-tm (get-abs-var tm))
            (instin-tm (get-abs-body tm))))
      (comb (let ((rator (instin-tm (get-rator tm)))
               (rand  (instin-tm (get-rand tm))))
            (let ((tyargs (cdr (ml-dest_type (get-type rator)))))
               (make-comb rator rand (second tyargs)))))
      (t (lcferror 'instin-tm)))
   )    ; instin-tm



;;; prime tok until it is not one of the tokl
;;; TFM for Version 1.12 [90.11.25]
;;; replaces a call to "variant-name" in instin-var below.
(defun variant-name2 (tokl tok)
   (while (memq tok tokl) (setq tok (concat tok '|'|)))
   tok)  ; variant-name2


;;; instantiate types in a variable
;;; renames variables whose type may change
;;; the new name differs from all previous names
;;; call to "variant-name" replaced by call to variant-name2
;;; [TFM 90.11.25]
(defun instin-var (tm)
   (let ((name (get-var-name tm)) (ty (get-type tm)))
      (cond ((assq1 tm %renames))
         ((exists #'(lambda (cty) (ml-type_in_type cty ty))
               %changed-types)
            (let ((newname (variant-name2 %used-varnames name)))
               (let ((newv (mk_realvar newname (instin-type ty))))
                  (push newname %used-varnames)
                  (push (cons tm newv) %renames)
                  newv)))
         (t (push (cons tm tm) %renames) tm))
      ))   ; instin-var



;;; variable renaming - primarily for storing axioms and theorems
;;; forces all variable names in a scope to be distinct
;;; creates new names (identifiers) for all genvars

;;; We don't allow genvars on theory files because
;;; calling genvar should always make a variable not already present
;;; in the current LCF session (in particular, not read from a theory file).

;;; the implementation of scopes should be changed to use an environment,
;;; without side-effects, rather than the hack of forget-var

;;; rename_term used nowhere in HOL 88: deleted		[TFM 90.06.01]
;;; (dml |rename_term| 1 ml-rename_term (|term| -> |term|))

;;; Not used: deleted					[TFM 90.06.01] 
;;; (defun ml-rename_term (ob)
;;;   (let ((%renames nil)  (%used-varnames nil))
;;;      (rename-vars-tm ob)))

;;; No formulas in HOL: rename_form deleted		[TFM 90.04.19]
;;;(dml |rename_form| 1 ml-rename_form (|form| -> |form|))

(defun ml-rename_form (ob)
   (let ((%renames nil)  (%used-varnames nil))
      (rename-vars-fm ob)))



;;; rename variables in a formula

(defun rename-vars-fm (fm)
   (case (form-class fm)
       ((conj disj imp) ; iff deleted [TFM 90.01.20]
         (make-conn-form (get-conn fm)
            (rename-vars-fm (get-left-form fm))
            (rename-vars-fm (get-right-form fm))))
      ((forall exists)
         (let ((quant (get-quant fm))
               (bv (rename-vars-tm (get-quant-var fm)))
               (body (rename-vars-fm (get-quant-body fm))))
            (forget-var (get-quant-var fm))
            (make-quant-form quant bv body)))
      (pred (make-pred-form (get-pred-sym fm)
            (rename-vars-tm (get-pred-arg fm))))
      (t (lcferror 'rename-vars-fm )))
   )    ; rename-vars-fm



;;; rename variables in a term
(defun rename-vars-tm (tm)
   (case (term-class tm)
      (var (rename-var tm))
      (const tm)
      (abs (let ((bv (rename-vars-tm (get-abs-var tm)))
               (body (rename-vars-tm (get-abs-body tm))))
            (forget-var (get-abs-var tm))
            (ml-mk_abs bv body)))
      (comb (ml-mk_comb (rename-vars-tm (get-rator tm))
            (rename-vars-tm (get-rand tm))))
      (t (lcferror 'rename-vars-tm)))
   )    ; rename-vars-tm


;;; rename a variable
;;; primes each variable to differ from all previous names
;;; renames all genvars
(defun rename-var (v)
   (let ((name (get-var-name v)) (ty (get-type v)))
      (cond ((assq1 v %renames))
         (t (let ((newname (variant-name %used-varnames 
                        (if (idenp name) name (gensym-interned)))))
               (let ((newv (mk_realvar newname ty)))
                  (push newname %used-varnames)
                  (push (cons v newv) %renames)
                  newv))))
      ))   ; rename-var


;;; forget about a variable once leaving its scope
;;; to allow (\x.x), (\x.x) without priming the second x 
;;; change needed by Mike Gordon (this is a mystery to me: MJCG 15/10/89!)
(defun forget-var (v)
   (let ((v2 (assq1 v %renames)))
      (setq %used-varnames (delq (get-var-name v2) %used-varnames))
      (push (cons v nil) %renames))
   )                               ; forget-var


;;; Code below added on 15/10/89 by MJCG to correct a variable capture bug 
;;; found by ICL Defence Systems.

;;; Returns list of variables "x:ty2" in a term where there is a preceding
;;; "x:ty1" in the term with ty1 is not equal to ty2.
;;; (It is possible that the old code could be debugged to avoid this
;;; inefficient second pass, MJCG could not see how and installed this patch
;;; as a temporary fix.)
;;; Patched 25/01/94 by MJCG to return list of variables "x2:ty2" in a term 
;;; where there is a preceding "x1:ty1" in the term 
;;; with x1 equal to x2 up to priming and ty1 is not equal to ty2.
;;; Fixes a bug found by Joakim Von Wright

(defun strip-primes (tok) (strip-primes-aux(reverse(exploden tok))))

(defun strip-primes-aux (tokl)
 (cond ((eq (car tokl) 39) (strip-primes-aux(cdr tokl)))
       (t (imploden(reverse tokl)))))

(defun get-inst-rename-list (tm)
  (case (term-class tm)
        (var (let ((p (assq (strip-primes(get-var-name tm))
                            %clash-danger-vars)))
              (cond (p (and (not (eq (get-type tm) (cdr p))) (list tm)))
                    (t (push (cons (strip-primes(cadr tm)) (cddr tm))
                             %clash-danger-vars) nil))))
        (const nil)
        (abs (append (get-inst-rename-list (get-abs-var tm))
                     (get-inst-rename-list (get-abs-body tm))))
        (comb (append (get-inst-rename-list (get-rator tm))
                      (get-inst-rename-list (get-rand tm))))
        (t (lcferror 'get-inst-rename-list))))

(defun inst-renames (tm) 
 (setq %clash-danger-vars nil)
 (get-inst-rename-list tm))

(dml |inst_rename_list| 1 inst-renames (|term| -> (|term| |list|)))

;;; Checks whether any type in tyl occurs in term tm
;;; Added 15/10/89 by MJCG as an optimization of INST_TYPE.
(defun typel-in-tm (tyl tm)
  (and tyl (or (ml-type_in_term (car tyl) tm)
               (typel-in-tm (cdr tyl) tm))))

;;; Checks (i) that the second component of every pair in inst_tylist
;;; is a type variable, and (ii) that none of these type variables occur
;;; in any of the terms in asl. Returns the free variables in asl.
;;; Added 15/10/89 by MJCG as an optimization of INST_TYPE.
(defun ml-inst_check (inst_tylist asl)
 (prog (tyvars vars)
       (setq tyvars nil)
       (setq vars nil)
  l1   (cond ((null inst_tylist) (go l2))
             ((is-vartype(cdar inst_tylist))
              (setq tyvars (cons (cdar inst_tylist) tyvars))
              (setq inst_tylist (cdr inst_tylist))
              (go l1))
             (t (failwith '|INST_TYPE: attempt to instantiate non-tyvar|)))
  l2   (cond ((null asl) (return vars))
             ((typel-in-tm tyvars (car asl)) 
              (failwith
                '|INST_TYPE: type variable free in assumptions|)))
       (setq vars (nconc (freevars (car asl)) vars))
       (setq asl (cdr asl))
       (go l2)))


(dml 
 |inst_check| 
 2 
 ml-inst_check
 ((((|type| |#| |type|) |list|) |#| (|term| |list|)) |->| (|term| |list|)))
