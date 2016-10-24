;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-typeol.l                                          ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Checks types in quotations, and puts them into      ;;;
;;;                     canonical form                                      ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-franz (or f-cl.l), f-constants.l, f-macro.l,      ;;;
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
;;;   REVISION HISTORY: Original code: typeol (lisp 1.6) part of Edinburgh  ;;;
;;;                     LCF by M. Gordon, R. Milner and C. Wadsworth (1978) ;;;
;;;                     Transported by G. Huet in Maclisp on Multics, Fall  ;;;
;;;                     1981                                                ;;;
;;;                                                                         ;;;
;;;                     V2.2 : quotch and tyquotch rewritten using tag      ;;;
;;;                                                                         ;;;
;;;                     V4 : quotations redone, eliminating fexprs          ;;;
;;;                                                                         ;;;
;;;                     April 1987: all instances of "trunc" replaced by    ;;;
;;;                       "hol-trunc" to prevent problems with redefining   ;;;
;;;                       the system "trunc" -- J. Joyce                    ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (include "lisp/f-ol-rec")
   (special %term %sticky-types %linkcount %stickylist |%show_types-flag|
      %canonlist |%type_error-flag| %tyvars |%sticky-flag|))

#+franz
(declare
   (localf unifyb hol-trunc occb set-sticky use-sticky canon-quot-fm
      canon-ty omutant1))

(setq %linkcount 0)

;;; generate a type link, an internal type variable for matching
;;; explicit type variables such as * are not matched
(defun genlink () (cons '%LINK (incf %linkcount)))  ;genlink

;;; Unify two OL types for checking types in quotations
(defun unify (ty1 ty2) (unifyb (hol-trunc ty1) (hol-trunc ty2)))  ;unify

;;; Unify "base types" -- no intervening %LINK nodes
(defun unifyb (bty1 bty2)
   (and bty1
      bty2     
      (cond
         ((eq bty1 bty2))
         ((is-linktype bty1) (if (occb bty1 bty2) nil (rplacd bty1 bty2)))
         ((is-linktype bty2) (if (occb bty2 bty1) nil (rplacd bty2 bty1)))
         ((is-vartype bty1) nil)                ; since vartypes are eq
         ((is-vartype bty2) nil)
         ((and (eq (get-type-op bty1) (get-type-op bty2)) 
               (forall 'unify (get-type-args bty1) (get-type-args bty2))))))
   )                                             ;unifyb

;;; skip past antiquotes and resolved links in a type
(defun hol-trunc (ty)
   (cond ((and (is-linktype ty) (not (atom (cdr ty))))  (hol-trunc (cdr ty)))
      ((is-antiquot ty) (hol-trunc (cdr ty)))
      (ty)))                                  ;hol-trunc

;;; For unification : see if type variable v occurs in ty
(defun occ (v ty) (occb v (hol-trunc ty)))  ;occ

(defun occb (v bty)
   (or (eq v bty)
      (case (type-class bty)
         ((%LINK %VARTYPE %ANTIQUOT) nil)
         (t (exists #'(lambda (ty) (occ v ty)) (get-type-args bty))))))   ; occb

;;; set sticky types -- called after successful evaluation of a quotation
;;; Sets sticky types of all variables to their most recent type
;;; MJCG 13/11/88 for HOL88
;;; Record sticktypes in %sticky-types

(defun set-sticky (styl)
   (mapc 
      #'(lambda (vty)
         (let ((sty (q-mk_antiquot (cdr vty))))
            (putprop (car vty) sty 'stickytype)
            #+franz (putprop %sticky-types sty (car vty))
            #-franz (setf (getf %sticky-types (car vty)) sty)))
      styl))                    ; set-sticky

;;; Apply sticky types to those variables whose type is still undefined
;;; In previous LCF, the sticky type was always used, requiring a hack
;;; in MK=TYPED to override it.
(defun use-sticky ()
   (mapc #'(lambda (vty)
         (let ((v (car vty)) (ty (hol-trunc (cdr vty))))
            (if (eq (car ty) '%LINK)
               (rplacd ty (get v 'stickytype)))))
      %vtyl))                ; use-sticky

;;; Map canon-ty over all types of a formula (or term).
;;; Nodes from antiquotations are already in proper form.
;;; Retain sticky types of variables (but don't set yet)
(defun canon-quot-fm (fm)
   (case (form-class fm)
      (%ANTIQUOT (cdr fm))
      (pred (make-pred-form (get-pred-sym fm) (canon-quot-tm (get-pred-arg fm))))
      ((conj disj imp) ; iff deleted [TFM 90.01.20]
         (make-conn-form (get-conn fm)
            (canon-quot-fm (get-left-form fm))
            (canon-quot-fm (get-right-form fm))))
      ((forall exists)
         (make-quant-form (get-quant fm)
            (canon-quot-tm (get-quant-var fm))
            (canon-quot-fm (get-quant-body fm))))
      (t (canon-quot-tm fm))
      ))  ;canon-quot-fm

;;; MJCG 2/12/88 for HOL88
;;; Make %term a special variable useable for error messages.
;;; for terms only.
(defun canon-quot-tm (%term)
   (case (term-class %term)
      (%ANTIQUOT (cdr %term))
      (comb
         (make-comb (canon-quot-tm (get-rator %term)) 
            (canon-quot-tm (get-rand %term))
            (canon-ty (get-type %term))))
      (abs
         (make-abs (canon-quot-tm (get-abs-var %term))
            (canon-quot-tm (get-abs-body %term))
            (canon-ty (get-type %term))))
      (var (let ((tok (get-var-name %term)) (ty (canon-ty(get-type %term))))
            (push (cons tok ty) %stickylist) (mk_realvar tok ty)))
      (const (ml-mk_const (get-const-name %term) (canon-ty(get-type %term))))
      (t (lcferror 'canon-quot-tm))
      ))  ;canon-quot-tm


;;; MJCG 1/12/88 for HOL88
;;; Function for printing types indeterminate error messages
(defun print-indeterminate-error (tm)
   (prog  (save-flag)
      (setq save-flag |%show_types-flag|)
      (setq |%show_types-flag| t)
      (ptoken "Indeterminate types:")
      (pbreak 2 4)
      (ml-print_term(prep-term-for-print tm))
      (pnewline)
      (pnewline)
      (setq |%show_types-flag| save-flag)))

;;; Strip all links from a type, complain if any are still undefined.
;;; To prevent expanding the DAG of links into a tree (which is exponential),
;;; retain before/after pairs of types in %canonlist
;;; Types beginning with %ANTIQUOT are already in canonical form.
;;; MJCG 1/12/88 for HOL88
;;; Printer of error message added
;;; (defun canon-ty (ty)
;;;   (cond ((assq1 ty %canonlist))
;;;      ((case (type-class ty)
;;;            (%ANTIQUOT (cdr ty))
;;;            (%LINK (if (atom (cdr ty))
;;;                  (prog2 (if |%type_error-flag| 
;;;                        (print-indeterminate-error %term))
;;;                     (throw-from evaluation "types indeterminate"))
;;;                  (canon-ty (cdr ty))))
;;;            (%VARTYPE ty)
;;;            (t (let ((cty (make-type (get-type-op ty)
;;;                           (mapcar #'canon-ty (get-type-args ty)))))
;;;                  (if (get-type-args ty) (push (cons ty cty) %canonlist))
;;;                  cty)))))
;;;   )              ; canon-ty

;;; Optimized version from David Shepherd
;;; (optimization only works for Common Lisp)
;;; [DES] 9may91
;;; for lists push sticks 1 element on %canonlist for *each* list
;;; element even though all are identical which causes problems with
;;; list search funs like assq1 later!
;;; pushnew with equality test fast-list-equal only puts distinct
;;; elements on the list !
;;;
;;; (defun canon-ty (ty)
;;;    (cond ((assq1 ty %canonlist))
;;;       ((case (type-class ty)
;;;             (%ANTIQUOT (cdr ty))
;;;             (%LINK (if (atom (cdr ty))
;;;                   (prog2 (if |%type_error-flag| 
;;;                         (print-indeterminate-error %term))
;;;                      (throw-from evaluation "types indeterminate"))
;;;                   (canon-ty (cdr ty))))
;;;             (%VARTYPE ty)
;;;             (t (let ((cty (make-type (get-type-op ty)
;;;                            (mapcar #'canon-ty (get-type-args ty)))))
;;;                   (if (get-type-args ty) 
;;; 	      #+franz (push (cons ty cty) %canonlist)
;;; 	      #-franz (pushnew (cons ty cty) %canonlist :test 'fast-list-equal)
;;;                   )
;;;                   cty)))))
;;;    )              ; canon-ty

;;; Another optimized version from David Shepherd 
;;;
;;; the problem is that %canonlist introduces more complexity than it
;;; reduces. without it canon-izing a given type takes o(n) where n is the
;;; number of nodes in the type. if we save this in %canonlist then we also
;;; potentially have we have o(n) comparisons on each element of %canonlust
;;; to see if its there already and if it isn't something similar to put it
;;; into the list.
;;; 
;;; i.e. the benefit (in number of calls) of not recursing down a type and
;;; getting the result out of %canonlist is similar to the number of extra
;;; calls used in checking the type against the keys in %canonlist in
;;; assq1. Since canon-ty does very little on each node then this call
;;; count is equivalent to speed.
;;;
;;; hence replace canon-ty with following code.
;;;
;;; on the term i was infuriated with it has reduced its retrieval from
;;; 120s to 3s and the maximum call count to 280,000 :-)
;;; the original version (before my mod of 9may91) took 350s and had a
;;; maximum call count of 120 million calls to EQL !
;;; naturally this fix will apply to all versions of lisp.
;;;
;;; [Installed by TFM, Feb 8 1992 for version 2.01]

(defun canon-ty (ty)
        (case (type-class ty)
            (%ANTIQUOT (cdr ty))
            (%LINK (if (atom (cdr ty))
                  (prog2 (if |%type_error-flag|
                        (print-indeterminate-error %term))
                     (throw-from evaluation "types indeterminate"))
                  (canon-ty (cdr ty))))
            (%VARTYPE ty)
            (t (make-type (get-type-op ty)
                          (mapcar #'canon-ty (get-type-args ty))))
        )
   ) ; canon-ty


;;; Convert all type variables to type links
(defun omutant (ty) (let ((%tyvars nil)) (omutant1 ty)))  ;omutant

(defun omutant1 (ty)
   (if (is-vartype ty)
      (or (assq1 ty %tyvars)
         (let ((newty (genlink))) (push (cons ty newty) %tyvars) newty))
      (make-type (get-type-op ty)
         (mapcar #'omutant1 (get-type-args ty)))
      ))  ;omutant1

;;; Functions called in ML object code

;;; Report errors found during evaluation of a quotation
;;; x is either a failure token or a list containing the quotation
(defun qtrap (x)
   (if (atom x)
      (throw-from evaluation (catenate x " in quotation")) (car x))
   )  ;qtrap

;;; clean up a quotation
;;; if quotation is OK then sets sticky types and returns a singleton list.
;;; MJCG 13/11/88 for HOL88
;;; stop sticktypes from being set if |%sticky-flag| is nil
;;; %sticky-types is a disembodied property list holding the sticky types
;;; of variables
(setq |%sticky-flag| nil)
(setq %sticky-types #+franz '(sticky-types) #-franz nil)
(defun quotation (qob)
   (use-sticky)
   (let ((%stickylist nil) (%canonlist nil))
      (prog1 (list (canon-quot-fm qob))  
         (if |%sticky-flag| (set-sticky %stickylist))
         ))
   )    ; quotation


;;; MJCG 13/11/88 for HOL88
;;; ML functions for setting and removing sticky types
(defun ml-set_sticky_type (var ty)
   (let ((sty (q-mk_antiquot ty)))
      (putprop var sty 'stickytype)
      #+franz (putprop %sticky-types sty var)
      #-franz (setf (getf %sticky-types var) sty)
      nil))
(dml |set_sticky_type| 
   2 
   ml-set_sticky_type 
   ((|string| |#| |type|) |->| |void|))

(defun ml-remove_sticky_type (var)
   (let ((ty (get var 'stickytype)))
      (if ty 
         (prog1 (cdr ty) (remprop var 'stickytype)
            #+franz (remprop %sticky-types var)
            #-franz (remf %sticky-types var))
         (failwith '|remove_sticky_type|))))
(dml |remove_sticky_type| 
   1
   ml-remove_sticky_type 
   (|string| |->| |type|))

;;; Get list of sticky-types
(defun ml-sticky_list ()
   (prog (temp res)
      (setq temp
         #+franz (cdr %sticky-types) #-franz %sticky-types)
      (setq res nil)
      loop (if (null temp) (return res))
      (setq res (cons (cons (car temp) (cdadr temp)) res))
      (setq temp (cddr temp))
      (go loop)))
(dml |sticky_list| 
   0
   ml-sticky_list
   (|void| -> ((|string| |#| |type|) |list|)))

;;; Switch old stickytypes on
;;;(defun ml-sticky_types (x)
;;; (prog1 |%sticky-flag| (setq |%sticky-flag| x)))
;;;(dml |sticky_types| 
;;;     1 
;;;     ml-sticky_types
;;;     (|bool| -> |bool|))

;;; Convert a preterm to a term

(defun eval-preterm (pt)
 (case (car pt)
       (|preterm_var| (q-mk_var (cdr pt)))
       (|preterm_const| (q-mk_const (cdr pt)))
       (|preterm_comb|
        (q-mk_comb
         (eval-preterm(cadr pt))
         (eval-preterm(cddr pt))))
       (|preterm_abs|
        (q-mk_abs
         (eval-preterm(cadr pt))
         (eval-preterm(cddr pt))))
       (|preterm_typed|
        (q-mk_typed
         (eval-preterm(cadr pt))
         (cddr pt)))
       (|preterm_antiquot|
        (q-mk_antiquot
         (cdr pt)))
       (t (failwith '|preterm_to_term|))))

(defun ml-preterm_to_term (pt)
  (let ((%vtyl nil)(%sharetypes nil))
       (car (quotation (eval-preterm pt)))))

(dml |preterm_to_term| 1 ml-preterm_to_term (|preterm| |->| |term|))
