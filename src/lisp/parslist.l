;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        parslist.l                                          ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Parsing of OL lists and sets                        ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-franz.l (or f-cl.l), f-constants.l, f-macro.l,    ;;;
;;;                     f-ol-rec.l genmacs.l                                ;;;
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
;;;   REVISION HISTORY: %hol-list-depth added by MJCG on 9/2/93             ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (include "lisp/f-ol-rec")
   (include "lisp/genmacs")
   (special lbrace-sym rbrace-sym pair-tok %set-depth %print_set-flag
            %empty-set %finite-set-constructor %set-abstraction-constructor))

#+franz (declare (localf mk-ol-list mk-finite-set get-frees-in-pt 
                         mk-var-tuple-pt mk-tuple-pt))

(eval-when (load)
   (let ((lang1 'ol1)(lang2 'ol2)(langlp 'ollp))
      (unop lbrkt-sym '(ol-list-rtn))
      (putprop scolon-sym 20 'ollp)
      (putprop rbrkt-sym  0  'ollp)
      ))

;;; The current empty set and finite set constructor are held in the globals
;;; %empty-set, %finite-set-constructor.
;;; The current set abstraction constructor is held in the global
;;; %set-abstraction-constructor

(setq %empty-set nil)
(setq %finite-set-constructor nil)
(setq %set-abstraction-constructor nil)

;;; Added by MJCG 27/6/92
;;; Added by MJCG 9/2/93 to fix a bug (see below)
;;; Depth of nesting inside "[...]"
(setq %hol-list-depth 0)
(defun hol-scolonsetup () 
  (putprop scolon-sym 20 'ollp) 
  (setq %hol-list-depth 0))


;;; MJCG 27/6/1992
;;; Bug introduced on 31/5/92 fixed
;;; MJCG 9/2/93
;;; Bug with nexted "[...]" fixed using %hol-list-depth hack
(defun ol-list-rtn ()
   (prog (l)
         (incf %hol-list-depth)
         (putprop scolon-sym 0 'ollp)
    loop (cond ((eq token rbrkt-sym) 
                (gnt) 
                (decf %hol-list-depth)
                (if (zerop %hol-list-depth) (putprop scolon-sym 20 'ollp))
                (return(mk-ol-list(reverse l)))))
         (setq l (cons (parse-level 10) l))
         (cond ((eq token rbrkt-sym)
                (go loop))
               (t (check scolon-sym nil '|bad list separator|)
                  (go loop)))))

(defun mk-ol-list (l)
   (cond ((null l) '(MK=CONST NIL))
      (t `(MK=COMB (MK=COMB (MK=CONST CONS) ,(car l))
            ,(mk-ol-list (cdr l))))))


;;; ================ Code for parsing set abstractions ================
;;; ---------------- MJCG, August 2, 1990 for HOL.1.12 ----------------

(setq lbrace-sym '|{|)
(setq rbrace-sym '|}|)

;;; Make } a terminator
(putprop rbrace-sym 0 'ollp)

;;; Restore normal precedence of comma

(defun hol-commasetup () 
 (let ((lang1 'ol1) (lang2 'ol2) (langlp 'ollp))
      (binop comma-sym 95 (term-rtn pair-tok 'arg1 '(parse-level 90)))))

;;; ================= Finite set notation =================

(defun ml-define_finite_set_syntax (emty con)
 (let ((lang1 'ol1)
       (lang2 'ol2)
       (langlp 'ollp) 
       (set-prop (get lbrace-sym 'ol1)))
      (if (not(ml-is_constant emty)) 
          (failwith (concat emty " is not a constant")))
      (if (not(ml-is_constant con)) 
          (failwith (concat con " is not a constant")))
      (setq %empty-set emty)
      (setq %finite-set-constructor con)
      (setq |%print_set-flag| t)
      (unop lbrace-sym `(ol-set-rtn))))

(dml |define_finite_set_syntax| 
     2
     ml-define_finite_set_syntax
     ((|string| |#| |string|) |->| |void|))


;;; ================= Set abstraction notation =================

(defun ml-define_set_abstraction_syntax (con)
 (let ((lang1 'ol1)
       (lang2 'ol2)
       (langlp 'ollp) 
       (set-prop (get lbrace-sym 'ol1)))
      (if (not(ml-is_constant con)) 
          (failwith (concat con " is not a constant")))
      (setq %set-abstraction-constructor con)
      (setq |%print_set-flag| t)
      (unop lbrace-sym `(ol-set-rtn))))      

(dml |define_set_abstraction_syntax| 
     1
     ml-define_set_abstraction_syntax
     (|string| |->| |void|))


;;; ================ Parsing code ================

;;; ("t1" "t2" ... "tn") --> "t1,t2,...,tn"

(defun mk-tuple-pt (l)
 (if (null(cdr l)) 
     (car l)
     `(MK=COMB (MK=COMB (MK=CONST |,|) ,(car l)) ,(mk-tuple-pt (cdr l)))))

(defun mk-finite-set (l emty con)
   (cond ((null l) `(MK=CONST ,emty))
         (t `(MK=COMB (MK=COMB (MK=CONST ,con) ,(car l))
              ,(mk-finite-set (cdr l) emty con)))))

;;; Compute the names of free variables in a parse tree that are not in vars

(defun get-frees-in-pt (vars pt)
 (cond ((atom pt) nil)
       ((eq (car pt) '|MK=ABS|) 
        (get-frees-in-pt (cons (cadadr pt) vars) (caddr pt)))
       ((and (eq (car pt) '|MK=VAR|)
             (not (memq (cadr pt) vars)))
        (list (cadr pt)))
       (t (union 
            (get-frees-in-pt vars (car pt))
            (get-frees-in-pt vars (cdr pt))))))
     
;;; (x1 x2 ... xn) --> parse tree of "x1,x2,...,xn"
;;; MJCG 12/11/90: redundant code commented out
(defun mk-var-tuple-pt (vars)
  (cond ;;; ((null vars) ;;; This should never happen!
        ;;; '(MK=TYPED (MK=VAR |%dummy|) (MK=VARTYPE |*|)))
        ((null (cdr vars)) 
         `(MK=VAR ,(car vars)))
        (t 
         `(MK=COMB 
           (MK=COMB (MK=CONST |,|) (MK=VAR ,(car vars)))
           ,(mk-var-tuple-pt (cdr vars))))))

(defun redefine-comma ()
 (let ((lang1 'ol1) (lang2 'ol2) (langlp 'ollp))
      (binop comma-sym 20 (term-rtn pair-tok 'arg1 '(parse-level 15)))))

;;; Added by MJCG 30.10.90
(defun intersect (x y)
  (cond ((null x) nil)
        ((member (car x) y) (cons (car x) (intersect (cdr x) y)))
        (t (intersect (cdr x) y))))

;;; MJCG 23.3.91
(setq %set-depth 0)

;;; Binding of intersection of variables added by MJCG 30.10.90
;;; Check that intersection is non-empty added by MJCG 12.11.90
;;; (This makes some code in mk-var-tuple-pt redundant)
;;; MJCG 28.1.91 extra pred argument to build-lam-struc
;;; MJCG 28.3.91 code to handle precedence of commas in nested sets added
(defun ol-set-rtn ()
   (prog (tms tm body)
         (incf %set-depth)
         (redefine-comma)
    loop (cond ((eq token rbrace-sym)
                (gnt)
                (decf %set-depth)
                (if (eq %set-depth 0) (hol-commasetup))
                (if (or (null %empty-set) (null %finite-set-constructor))
                    (parse-failed "finite set constructors not specified"))
                (return 
                 (mk-finite-set
                  (reverse tms) 
                  %empty-set 
                  %finite-set-constructor))))
         (setq tms (cons (parse-level 30) tms))
         (cond ((eq token rbrace-sym) (go loop))
               ((eq token comma-sym) (gnt) (go loop)))
         (check else-sym nil '|missing comma or \| in set notation|)
         (hol-commasetup)
         (if (null %set-abstraction-constructor)
             (parse-failed "set abstraction constructor not specified"))
         (setq tm (mk-tuple-pt(reverse tms)))
         (setq body (parse-level 10))
         (check rbrace-sym nil `|missing } in set abstraction|)
         (setq 
           tms 
           (intersect (get-frees-in-pt nil tm) (get-frees-in-pt nil body)))
         (cond ((null tms)
                (parse-failed "no variable is bound by the set abstraction"))
               (t
                (decf %set-depth)
                (if (> %set-depth 0) (redefine-comma))
                (return
                 (build-lam-struc 
                   %set-abstraction-constructor
                   nil
                   (mk-var-tuple-pt tms)
                   `(MK=COMB (MK=COMB (MK=CONST |,|) ,tm) ,body)))))))


