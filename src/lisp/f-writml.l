;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-writml.l                                          ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Functions for pretty printing ML types              ;;;
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
;;;   REVISION HISTORY: Original code: writml (lisp 1.6) part of Edinburgh  ;;;
;;;                     LCF by M. Gordon, R. Milner and C. Wadsworth (1978) ;;;
;;;                     Transported by G. Huet in Maclisp on Multics, Fall  ;;;
;;;                     1981                                                ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (special %top-print))

#+franz
(declare
   (localf isconctype print_list print_sum print_prod print_conc))

;;; Print new top-level definitions
;;; MJCG 11 May 1992. Eliminated third argument (ty) of prlet.
;;; This fixes a bug discovered by JG.
;;; prlet is called in f-tml.l
(defun prlet (s x)
   (cond
      ((memq s (list nill empty)))
      ((atom s)
         (unless (eq s '%con)
            (pstring s) (ptoken | = |) (pbreak 0 0)
            ;; tidy added so start from one * for each binding
            ;; tidy changed into tidy1 GH 2/2/82 because tenv unbound
            (prvalty x (tidy1 (assoc1 s (cdr %thisdec))))))
      (t (prlet (car s) (car x))
         (prlet (cdr s) (cdr x))
         )))                                    ;prlet

;;; Print value, type of top-level expression
(defun prvalty (x ty)
   (prinml x ty nil)
   (pbreak 1 0)
   (ptoken |: |)
   (printmty ty)
   (pnewline))                                 ;prvalty

;;; Print result of "lettype"
(defun prdefty (idtyl)
   (ptoken |type |)
   (mapc #'(lambda (idty) (pstring (car idty)) (pbreak 1 0)) idtyl)
   (ptoken |defined|) (pnewline))              ;prdefty


;;; Print result of type or rectype
(defun prconstrs (idtyl)
   (pnewline)
   (ptoken |New constructors declared:|)
   (pnewline)
   (mapc
      #'(lambda (idty) (pstring (car idty)) 
         (ptoken | : |)
         (printmty (tidy1 (cdr idty)))
         (pnewline))
      idtyl))                               ; prconstrs

(dml |print_int| 1 ml-print_int (|int| -> |.|))

(defun ml-print_int (n) (pstring n))            ; ml-print_int

(dml |print_tok| 1 ml-print_tok (|string| -> |.|))

(defun ml-print_tok (tok) (ptoken |`|) (pstring tok) (ptoken |`|))      ;ml-print_tok

(dml |print_string| 1 pstring (|string| -> |.|))

(dml |print_bool| 1 ml-print_bool (|bool| -> |.|))

(defun ml-print_bool (b) (if b (ptoken |true|) (ptoken |false|)))       ;ml-print_bool

(dml |print_void| 1 ml-print_void (|.| -> |.|) )

(defun ml-print_void (ignore) (ptoken |()| ))   ;ml-print_void

;;; MJCG 30/1/89 for HOL88
;;; Alist of type/prin-function pairs
(setq %top-print nil)

;;; MJCG 30/1/89 for HOL88
;;; Kludge function to grab argument and type and ad to %top-print
(defun ml-top_print (x)
   (setq %top-print (cons (cons (cadr %ty) (car x)) %top-print))
   x)

;;; MJCG 30/1/89 for HOL88
;;; ML function to grab argument and type
;;; only works at top-level
(dml |top_print| 1 ml-top_print ((* -> **) -> (* -> **)))

;;; the parameter "cl" requests surrounding parentheses
;;; MJCG 25 Jan 1989 for HOL88
;;; Separated out and improved printing of concrete types.
;;; Fixed for HOL88 to look up type in %top-print.
(defun prinml (x ty cl)
   (let ((prfn (assoc-equal ty %top-print)))
      (if
         prfn
         (funcall (cdr prfn) (list x))
         (case (if (isconctype ty) 'conctype (car ty))
            (mk-nulltyp (ml-print_void x))
            (mk-inttyp (ml-print_int x))
            (mk-toktyp (ml-print_tok x))
            (mk-booltyp (ml-print_bool x))
            (mk-termtyp (ml-print_term x))
            (mk-formtyp (ml-print_form x))
            (mk-typetyp (ml-print_type x))
            (mk-thmtyp (ml-print_thm x))
            (mk-listyp (print_list x (cadr ty)))
            (mk-sumtyp (print_sum x ty cl))
            (mk-prodtyp (print_prod x ty cl))
            (conctype  (print_conc x ty cl))
            (t (if cl (ptoken |(-)|) (ptoken |-|)))))))        ;printml

(defun isconctype (ty) (eq (car (explode-word (car ty))) 'CONC))

;;; Print a list x whose ELEMENTS have type ty
(defun print_list (x ty)
   (pbegin 1)
   (ptoken |[|)
   (cond (x
         (prinml(car x) ty nil)
         (mapc #'(lambda (y) (ptoken |;|) (pbreak 1 0) (prinml y ty nil))
            (cdr x))))
   (ptoken |]|)
   (pend))                                     ; print_list

;;; Print value x of sum type ty
(defun print_sum (x ty cl)
   (if cl (ptoken |(|))
   (cond
      ((car x) (ptoken |inl |) (prinml (cdr x) (cadr ty) t))
      (t (ptoken |inr |) (prinml (cdr x) (caddr ty) t)))
   (if cl (ptoken |)|)))

;;; Print value x of product type ty
;;; MJCG 25/1/89 for HOL88 improved printing of tuples
;;; tuples now always enclosed in brackets
(defun print_prod (x ty cl)
   (prog ()
      (pbegin 1)
      (ptoken |(|)
      loop (if (atom x) (go exit))
      (prinml (car x) (cadr ty) t)
      (ptoken |,|) 
      (pbreak 1 0) 
      (setq x (cdr x))
      (setq ty (caddr ty))
      (if (eq (car ty) 'mk-prodtyp) (go loop) (go exit))
      exit (prinml x ty nil)
      (ptoken |)|)
      (pend)))

;;; MJCG 25 jan 1989 for HOL88
;;; Function for printing concrete types
;;; code moved out of writml (same action as before, but works
;;; better due to improved tuple printing)       
;;; MJCG 29.10.90: extra space printed after constructor with atomic arg

(defun print_conc (x ty cl)
   (if (atom x) 
      (ifn cl (pstring x) (ptoken |(|) (pstring x) (ptoken |)|))
      (progn
         (when cl (ptoken |(|))
         (pstring (car x))
         (if (atom (cdr x)) (ptoken | |))
         (prinml (cdr x) (cadr (get (car x) 'mltype)) t)
         (when cl (ptoken |)|)))))
