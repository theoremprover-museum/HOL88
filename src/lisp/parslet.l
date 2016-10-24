;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        parslet.l                                           ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Parsing of "let" expressions                        ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-franz.l (or f-cl.l), f-constants.l f-macro.l      ;;;
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
;;;   REVISION HISTORY: MJCG 28/02/94 Fixed MN's "in" bug                   ;;;
;;;                   : MJCG 04/04/94 Fixed "and" bug like MN's "in" bug    ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; MJCG 3/2/89 for HOL88
;;; ol-let-rtn parses "let ... " as follows
;;; 
;;;   "let f v1 ... vn = t1 in t2"
;;;          --> "LET (\f.t2) (\v1 ... vn.t1)"
;;; 
;;;   "let (x1,...,xn) = t1 in t2"
;;;        --> "LET (\(x1,...,xn).t2) t1"
;;; 
;;;   "let x1=t1 and x2=t2 ... and xn=tn in t" 
;;;          --> "LET ( ... (LET(LET (\x1...xn.t) t1)t2) ... ) tn" 

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (include "lisp/f-ol-rec")
   (*lexpr concat))


#+franz (declare (localf hol-bnd-rtn))

(eval-when (load)
   (let ((lang1 'ol1) (lang2 'ol2) (langlp 'ollp))
      (unop '|let| '(ol-let-rtn))))


;;;(defun let-lhs-rtn (msg)
;;;   (prog (x)
;;;         (setq
;;;          x
;;;          (cond ((eq token anticnr-tok) (gnt) (metacall))
;;;                ((not(= toktyp 1)) (parse-failed msg))
;;;                (t (gnt) (mk-ol-atom ptoken))))
;;;         (while (eq token colon-sym) (gnt) (setq x (list 'MK=TYPED x (olt))))
;;;         (return x)))

;;; MJCG 31/1/89 for HOL88
;;; Function to test for a parse tree of a (possibly typed) variable
;;; or antiquotation

(defun is-var-pt (x)
   (or (eq (car x) 'MK=VAR)
      (and (eq (car x) 'MK=TYPED)
         (is-var-pt (cadr x)))
      (eq (car x) 'MK=ANTIQUOT)))

;;; MJCG 31/1/89 for HOL88
;;; Function to test for a parse tree of a (possibly typed) tuple of
;;; variables (or antiquotation)

(defun is-var-tuple-pt (x)
   (or (eq (car x) 'MK=VAR)
      (and (eq (car x) 'MK=TYPED)
         (is-var-tuple-pt (cadr x)))
      (and (eq (car x) 'MK=COMB)
         (eq (caadr x) 'MK=COMB)
         (equal (cadadr x) '(MK=CONST |,|))
         (is-var-tuple-pt (caddadr x))
         (is-var-tuple-pt (caddr x)))
      (eq (car x) 'MK=ANTIQUOT)))


;;; MJCG 31/1/89 for HOL88
;;; Function to test for a parse tree of a (possibly typed) varstruct
;;; (i.e. formal application of tuples of variables (or antiquotations)

(defun is-varstruct-pt (x)
   (or (eq (car x) 'MK=VAR)
      (and (eq (car x) 'MK=TYPED)
         (is-varstruct-pt (cadr x)))
      (and (eq (car x) 'MK=COMB)
         (eq (caadr x) 'MK=COMB)
         (equal (cadadr x) '(MK=CONST |,|))
         (is-varstruct-pt (caddadr x))
         (is-varstruct-pt (caddr x)))
      (and (eq (car x) 'MK=COMB)
         (is-varstruct-pt (cadr x))
         (is-varstruct-pt (caddr x)))
      (eq (car x) 'MK=ANTIQUOT)))



;;; MJCG 27/1/89 for HOL88
;;; used to reset |=| on parse failure (see lisp/f-parser.l)
(defun hol-eqsetup () (putprop eq-sym 15 'ollp))

;;; If [t] denotes the result of parsing t, then hol-bnd-rtn does:
;;; "f1 v11 ...vm1 = t1 and ... and fn = vn1 ... vnm"
;;;  --> (([f1] . [\v11 ... vm1.t1]) ... ([fn] . [\vn1 ... vnm.tn]))
;;; MJCG 28.1.91 extra pred argument to build-lam-struc

(defun hol-bnd-rtn ()
   (prog (bindings name vars rhs)
      (setq bindings nil)
      (putprop eq-sym 0 'ollp)
      loop (setq 
         name 
         (term-check
            (parse-level 1000)
            "syntax error immediately after `let`"))
      (while (eq token colon-sym) 
         (gnt) 
         (setq name (list 'MK=TYPED name (olt))))
      (cond ((eq token eq-sym)
            (ifn (is-var-tuple-pt name)
               (parse-failed "bad lhs after `let`"))
            (gnt)
            (hol-eqsetup)
            (push-in-and-ollp)
            (setq 
               rhs 
               (term-check (parse-level 10) "bad term after `=` in `let`"))
            (setq bindings (cons (cons name rhs) bindings))
            (go and)))
      (ifn (is-var-pt name)
         (parse-failed "bad function name after `let`"))
      (setq vars (parse-level 20))
      (ifn (is-varstruct-pt vars)
         (parse-failed "bad args to function definition after `let`"))
      (check eq-sym nil '|missing = after let|)
      (hol-eqsetup)
      (push-in-and-ollp)
      (setq rhs (term-check (parse-level 10) "bad term after `=` in `let`"))
      (setq 
         bindings 
         (cons (cons name (build-lam-struc lam-sym nil vars rhs)) bindings))
      and  (cond ((eq token '|and|) (gnt) (pop-in-and-ollp) (go loop)))
      (check '|in| nil "missing `in` or `and` after `let`")
      (pop-in-and-ollp)
      (return (reverse bindings))))

;;; MJCG 30/1/89 for HOL88
;;; If [t] denotes the result of parsing t, then hol-and-rtn does:
;;; (([x1] . [t1]) ([x2] . [t2]) ... ([xn] . [tn])), [t]
;;; --> [LET ( ... (LET (LET (\x1...xn. t) t1)t2) ... ) tn]
;;; MJCG 28.1.91 extra pred argument to build-lam-struc

(defun hol-and-rtn (bindings body)
   (prog (lamb tms)
      (setq lamb body)
      (setq tms nil)
      (mapc 
         (function
            (lambda (p) 
               (setq lamb (build-lam-struc lam-sym nil (car p) lamb))
               (setq tms  (cons (cdr p) tms))))
         (reverse bindings))
      (mapc 
         (function 
            (lambda (x) 
               (setq lamb `(MK=COMB (MK=COMB (MK=CONST LET) ,lamb) ,x))))
         tms)
      (return lamb)))

;;; Recoded on 30/1/89 by MJCG for HOL88
(defun ol-let-rtn ()
   (hol-and-rtn 
      (hol-bnd-rtn)
      (term-check (parse-level 80) '|bad term after in|)))

;;; used to reset |in| on parse failure (see lisp/f-parser.l)
;;; MJCG 28/02/94: Grotesque fix for Malcolm Newey's "in" bug
(defun hol-insetup () 
 (if (eq (get '|in| 'ollp) 0)                        ;inside "let ... in ..."
     (putprop '|in|  (get '|in|  'ollp-save) 'ollp)));reset in's ollp


;;; MJCG 27/1/89 for HOL88
;;; used to reset |and| on parse failure (see lisp/f-parser.l)
;;; MJCG 28/02/94: Grotesque fix for "and" bug similar to MN's "in" bug
(defun hol-andsetup () 
 (if (eq (get '|and| 'ollp) 0)                         ;inside "let ... in ..."
     (putprop '|and|  (get '|and|  'ollp-save) 'ollp)));reset and's ollp

;;; MJCG 26/1/89 for HOL88
;;; Hack to make nested lets work
(defun push-in-and-ollp ()
   (putprop '|in|  (get '|in|  'ollp) 'ollp-save)
   (putprop '|and| (get '|and| 'ollp) 'ollp-save)
   (putprop '|in|  0 'ollp)
   (putprop '|and| 0 'ollp))

(defun pop-in-and-ollp ()
   (putprop '|in|  (get '|in|  'ollp-save) 'ollp)
   (putprop '|and| (get '|and| 'ollp-save) 'ollp))
