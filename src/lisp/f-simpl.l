;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-simpl.l                                           ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Matching functions                                  ;;;
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

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (include "lisp/f-ol-rec"))


#+franz (declare (localf var-match prepare-substl prepare-insttyl))

;;; unlike the F-simpl written by Chris Wadsworth, these matching functions
;;; do not preprocess the patterns for faster matching.  They are simpler
;;; to use, their implementation is much cleaner, and they are almost as
;;; efficient as their predecessors.  For fast matching, the OL network
;;; functions can be used.

;;; term_match and form_match now match types as well as terms.

;;; match a pattern pat to an object ob
;;;   returns nil to indicate failure
;;;   records match in specials %substl and %insttyl

;;; ---------------------------------------------------------------------
;;; form-match, ml-form_match, and paired_form_match used nowhere in HOL.
;;; So, commented out here.   [TFM 90.04.19]
;;; ---------------------------------------------------------------------
;(defun form-match (pat ob)
;   (and (eq (form-class pat) (form-class ob))
;      (case (form-class pat)
;         ((conj disj imp iff)
;            (and (form-match (get-left-form pat) (get-left-form ob))
;               (form-match (get-right-form pat) (get-right-form ob))))
;         ((forall exists)
;            (let ((pbv (get-quant-var pat))  (obv (get-quant-var ob)))
;               (and (type-match (get-type pbv) (get-type obv))
;                  (let ((%bv-pairs (cons (cons pbv obv) %bv-pairs)))
;                    (form-match (get-quant-body pat) (get-quant-body ob))))))
;         (pred (and (eq (get-pred-sym pat) (get-pred-sym ob))
;               (term-match (get-pred-arg pat) (get-pred-arg ob))))
;         (t (lcferror 'form-match)))))          ; form-match


(defun term-match (pat ob)
   (case (term-class pat)
      (const (and (is-const ob)
            (eq (get-const-name pat) (get-const-name ob))
            (type-match (get-type pat) (get-type ob))))
      (var  (var-match pat ob))
      (comb (and (is-comb ob)
            (term-match (get-rator pat) (get-rator ob))
            (term-match (get-rand pat) (get-rand ob))))
      (abs (and (is-abs ob)
            (let ((pbv (get-abs-var pat)) (obv (get-abs-var ob)))
               (type-match (get-type pbv) (get-type obv))
               (let ((%bv-pairs (cons (cons pbv obv) %bv-pairs)))
                  (term-match (get-abs-body pat) (get-abs-body ob))))))
      (t (lcferror 'term-match))))                ;term-match

;;; match a variable to an object
(defun var-match (var ob)
   (let ((pbind (assq var %bv-pairs)) (obind (revassq ob %bv-pairs)))
      (cond ((or pbind obind)
            (#+franz eq #-franz eql pbind obind))   ; corresponding bound vars
         ((not (exists #'(lambda (vv) (freein-tm (cdr vv) ob)) %bv-pairs))
            ; ob is free in entire object
            (let ((prev (revassq1 var %substl))) ; keep consistent
               (cond (prev (alphaconv ob prev))   ; with prev match
                  ((type-match (get-type var) (get-type ob))
                     (push (cons ob var) %substl)))))))) ; var-match

;;; match a pattern type with an object type, return nil if failure
;;; records types that are known to match, to prevent exponential blow-up
;;; (defun type-match (pty ty)
;;;    (if (is-vartype pty)
;;;       (let ((ty2 (revassq1 pty %insttyl)))
;;;          (if ty2 (equal ty ty2)       ; consistent with previous match
;;;             (push (cons ty pty) %insttyl)))
;;;       (let ((pty-tys (assq pty %type-matches)))
;;;          (or (memq ty (cdr pty-tys))
;;;             (cond ((is-vartype ty) (failwith '|type-match|))
;;;                ((and (eq (get-type-op pty) (get-type-op ty))
;;;                      (forall 'type-match
;;;                         (get-type-args pty)
;;;                         (get-type-args ty)))
;;;                   ; record matching pair of types
;;;                   (if pty-tys
;;;                      (rplacd pty-tys (cons ty (cdr pty-tys)))
;;;                      (push (cons pty (list ty)) %type-matches))
;;;                   t))))))                      ;type-match



;;; match a pattern type with an object type, return nil if failure
;;; records types that are known to match, to prevent exponential blow-up
;;; [DES] 11feb92 - stop if types are equal as (ty.ty) is dropped later
(defun type-match (pty ty)
 (if (#+franz equal #-franz fast-list-equal pty ty) t  ; [DES] 11feb92
   (if (is-vartype pty)
      (let ((ty2 (revassq1 pty %insttyl)))
         (if ty2 (equal ty ty2)           ; consistent with previous match
            (push (cons ty pty) %insttyl)))
      (let ((pty-tys (assq pty %type-matches)))
         (or (memq ty (cdr pty-tys))
            (cond ((is-vartype ty) (failwith '|type-match|))
               ((and (eq (get-type-op pty) (get-type-op ty))
                     (forall 'type-match
                        (get-type-args pty)
                        (get-type-args ty)))
                  ; record matching pair of types
                  (if pty-tys
                     (rplacd pty-tys (cons ty (cdr pty-tys)))
                     (push (cons pty (list ty)) %type-matches))
                  t)))))))                      ;type-match

;;; instantiate types in variables
;;; and strip out null matches of the form (v . v)
;;; to minimize the variables that must be instantiated
;;; (null matches must first be recorded
;;;    to prevent v from matching something else)
(defun prepare-substl (substl)
   (if substl
      (let ((tm (caar substl)) (var (cdar substl)) (tail (cdr substl)))
         (let ((var2 (mk_realvar (get-var-name var) (get-type tm))))
            (if (eq tm var2) (prepare-substl tail)
               (cons (cons tm var2) (prepare-substl tail))))))) ; prepare-substl

;;; prepare the type instantiation list
;;; by stripping out redundant pairs (* . *)
(defun prepare-insttyl (insttyl)
   (if insttyl
      (let ((head (car insttyl)) (tail (cdr insttyl)))
         (if (eq (car head) (cdr head)) (prepare-insttyl tail)
            (cons head (prepare-insttyl tail))))))      ; prepare-insttyl

;;; Error changed from term_match to match [JRH 94.01.08]

(defun ml-term_match (pat ob)
   (let ((%substl nil) (%insttyl nil) (%bv-pairs nil) (%type-matches nil))
      (ifn (term-match pat ob) (throw-from evaluation 'match))
      (cons (prepare-substl %substl) (prepare-insttyl %insttyl))))        ; ml-term_match

;;; ---------------------------------------------------------------------
;;; form-match, ml-form_match, and paired_form_match used nowhere in HOL.
;;; So, commented out here.   [TFM 90.04.19]
;;; ---------------------------------------------------------------------

;(defun ml-form_match (pat ob)
;   (let ((%substl nil) (%insttyl nil) (%bv-pairs nil) (%type-matches nil))
;      (ifn (form-match pat ob) (throw-from evaluation 'form_match))
;      (cons (prepare-substl %substl) (prepare-insttyl %insttyl))))
                                                             ; ml-form_match


;;; ---------------------------------------------------------------
;;; This paired function later gets REDEFINED to be a curried
;;; function (in ml/ml-hol-syn.ml)
;;; Used to be called "paired_term_match".
;;;  --------------------------------------------------------------

(dml |match| 2 ml-term_match
   ((|term| |#| |term|) ->
      (((|term| |#| |term|) |list|) |#| ((|type| |#| |type|) |list|))))

;;; ---------------------------------------------------------------------
;;; form-match, ml-form_match, and paired_form_match used nowhere in HOL.
;;; So, commented out here.   [TFM 90.04.19]
;;; ---------------------------------------------------------------------

;(dml |paired_form_match| 2 ml-form_match
;   ((form |#| form) ->
;      (((|term| |#| |term|) |list|) |#| ((|type| |#| |type|) |list|))))
