; FILE	       : print_hacks.l (modified version of lisp/hol-writ.l)
; DESCRIPTION  : Pretty printer hacks to support programming language
;									
; AUTHOR       : M. Gordon						
; DATE	       : 30 March 1989

(eval-when (compile)
   #+franz (include "f-franz")
   (include "f-constants")
   (include "f-macro")
   (include "f-ol-rec")
   (include "genmacs")
   (special |%show_types-flag| ol-lam-sym hol-unops hol-binops binders
            |%interface_print-flag| %turnstile |%print_top_types-flag|
            |%print_list-flag| |%print_cond-flag| |%print_quant-flag| 
            |%print_let-flag| |%print_uncurry-flag| |%print_infix-flag|
            |%print_top_val-flag| %deftypes
; =============== Added to support programming language ===============
            |%print_lang-flag| rator %flags
; =====================================================================
))

; =============== Added to support programming language ===============
(eval-when (load)
   (setq %flags (cons '|%print_lang-flag| %flags))
   (setq |%print_lang-flag| t))
; =====================================================================

#+franz
(declare
 (localf prep-ol-let
         print-ol-let
         pre-prep-ol-list
         prep-ol-list
         print-ol-list
         prep-ol-cond
         is-special-comb
         prep-ol-quant
         prep-ol-unop
         prep-ol-binop
         print-ol-unop
         prep-ol-uncurry
         print-eq
         print-ol-binop
         print-neg
         print-ol-quant))

; If T1 is a 'closes property of T2 then brackets will be put around
; T1 when it is printed in the context of T2
 
(mapc '(lambda (x) (putprop (car x) (cdr x) 'closes))
      '((|~| . (quant /\\ \\/ |==>| |<=>| |,| |=|))
        (/\\ . (quant /\\ \\/ |==>| |<=>| |,| |=|))
	(\\/ . (quant \\/ |==>| |<=>| |,| |=|))
	(|==>| . (quant |==>| |<=>| |,| |=|))
	(|<=>| . (quant |<=>| |,| |=|))
	(|,| . (quant |,| /\\ \\/ |==>| |<=>| ol-let |=|))
        (|=| . (quant ol-let |=|))
	(then . (quant then |=| /\\ \\/ |~| |==>| |<=>|))
	(else . (quant then |,| |=| /\\ \\/ |==>| |<=>|))
	(listcomb . (quant listcomb infixcomb then |,| typed ol-let |=| /\\))
	(infixcomb . (quant listcomb infixcomb then |,| typed ol-let |=| /\\))
        (varstruct . (|,|))
        (let-rhs . (|=|))
	(typed . (infixcomb))
	(fun . (fun))
	(sum . (sum fun))
	(prod . (prod sum fun))
        (quant . (|,| typed))
        (eqn-rhs . (quant listcomb infixcomb then |,| typed))
; =============== Added to support programming language ===============
(listcomb . 
    (quant listcomb infixcomb then |,| typed ol-let |=| /\\ while ite))
(infixcomb . 
    (quant listcomb infixcomb then |,| typed ol-let |=| /\\ while ite))
	(typed . (infixcomb))
	(fun . (fun))
        (do . (while ite))
        (Then . (while ite))
        (Else . (while ite))
	(sum . (sum fun))
	(prod . (prod sum fun))
        (eqn-rhs . (quant listcomb infixcomb then |,| typed))
; =====================================================================
))


; MJCG 17/1/89 for HOL88
; Code change from Davis Shepherd for changing lambda symbol
; (ol-lam-sym for lam-sym)
; MJCG 31/1/89 for HOL88
; Modified to support print_ flags

(mapc
 (function(lambda (x) (set x t)))
 '(|%print_list-flag|  |%print_cond-flag| |%print_quant-flag| 
   |%print_infix-flag| |%print_let-flag|  |%print_comb-flag|))

(defun prep-tm (tm)
  (case (term-class tm)
     (var tm)
     (const (if (and |%print_list-flag| (eq (get-const-name tm) 'NIL))
                `(ol-list . (nil . ,(get-ol-list-type tm)))
                tm))
     (abs (list 'quant ol-lam-sym (get-abs-var tm) (prep-tm (get-abs-body tm))))
     (comb (let ((rator (get-rator tm))
		 (rand (get-rand tm))
		 (ty (get-type tm)))
	     (or (and |%print_list-flag|    (prep-ol-list tm))
		 (and |%print_cond-flag|    (prep-ol-cond rator rand ty))
; =============== Added to support programming language ===============
		 (prep-ol-assign rator rand ty)
		 (prep-ol-it rator rand ty)
		 (prep-ol-ite rator rand ty)
		 (prep-ol-seq rator rand ty)
		 (prep-ol-while rator rand ty)
		 (prep-ol-assert rator rand ty)
		 (prep-ol-invariant rator rand ty)
		 (prep-ol-variant rator rand ty)
		 (prep-ol-spec rator rand ty)
		 (prep-ol-t-spec rator rand ty)
; =====================================================================
                 (and |%print_quant-flag|   (prep-ol-quant rator rand ty))
                 (and |%print_let-flag|     (prep-ol-let tm))
                 (and |%print_infix-flag|   (prep-ol-binop rator rand ty))
                 (and |%print_infix-flag|   (prep-ol-unop rator rand ty))
                 (and |%print_uncurry-flag| (prep-ol-uncurry tm))
		 (prep-comb rator rand ty))))
     (t (lcferror "prep-tm"))))


(defun print-tm (tm op1 needty)
 (let ((op2 (term-class tm))
       (tml (get-term-list tm))
       (ty (get-type tm)))
  (let ((pcrator 		; is rator a polymorphic constant?
	  (and |%show_types-flag|
	       (memq op2 '(listcomb infixcomb))
	       (let ((r (first tml)))	 ; find innermost operator 
		 (if (eq (term-class r) 'infixcomb)
		     (setq r (first (get-term-list r))))
	         (and (is-const r) (opoly (constp (get-const-name r))))))))
    (let ((tyflag 		; print type of this particular term?
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
	(cond (print-cond tml needty))
; =============== Added to support programming language ===============
	(assign (print-assign tml needty))
	(it (print-it tml needty))
	(ite (print-ite tml needty))
	(seq (print-seq tml needty))
        (while (print-while tml needty))
        (assert (print-assert tml needty))
        (invariant (print-invariant tml needty))
        (variant (print-variant tml needty))
        (spec (print-spec tml needty))
        (t-spec (print-t-spec tml needty))
; =====================================================================
	(listcomb (print-listcomb tml pcrator))
	(infixcomb (print-infixcomb tml pcrator))
        (quant (print-ol-quant tm))
        (|~| (print-ol-unop tm))
        ((|=| /\\ \\/ |==>| |<=>| |,|) (print-ol-binop tm))
        (ol-let (print-ol-let tm))
        (ol-list (print-ol-list tm))
	(t (lcferror "print-tm")))
       (cond (tyflag		; print type
	    (if cl2 (ptoken |)|)
		    (ifn (memq op2 '(var const)) (ptoken | |)))
	    (pbreak 0 0)
	    (ptoken |:|) (print-ty ty t)))
       (if cl1 (ptoken |)|))
       (pend)))))) 

; MJCG 20/10/88 for HOL88
; string printing function that inverts interface
(defun pistring (str)
 (pstring (or (and |%interface_print-flag| (get str 'interface-print))
              str)))

; MJCG 19/10/88 for HOL88
; print a constant (may be a prefix, infix or binder standing alone)
; modified to invert interface-map
(defun print-const (name)
 (cond ((or (get name 'olinfix)
            (get name 'prefix)
            (get name 'binder))
        (ptoken |$|)))
 (pistring name))

; MJCG 3/2/89 for HOL88
; Function for stripping of the varstructs of a function
; "\v1 v2 ... vn. t"  --> ((v1 v2 ... vn) . t)
; "t"                 --> (nil . t)  -- t not a function
; (vi either a variable or a varstruct)

(defun strip-abs (tm)
 (or (and (is-abs tm)
          (let ((p (strip-abs(get-abs-body tm))))
           (cons (cons (get-abs-var tm) (car p)) (cdr p))))
     (and (is-special-comb tm '(UNCURRY))
          (let* ((p (dest-uncurry tm))
                 (q (strip-abs (cdr p))))
           (cons (cons (car p) (car q)) (cdr q))))
     (cons nil tm)))

; MJCG 3/2/89 for HOL88
; Function for exploding an application
; "LET ( ... (LET t1 t2) ... ) tn"  --> (t1 t2 ... tn)
; "t"                 --> (t)  -- t not of this form

(defun strip-let (tm)
 (or (and (is-comb tm)
          (is-special-comb (get-rator tm) '(LET))
          (let ((args (strip-let(get-rand(get-rator tm)))))
           (append1 args (get-rand tm))))
     (list tm)))

; code for printing "let ... in ... "
; MJCG 3/2/89 for HOL88
; Extended to deal with fancier let constructs
; 
; "let x=u in tm"
; 
;    "LET (\x. tm) u" --> (ol-let (((x) . u)) tm)
; 
; "let f v1 ... vn = u in tm"
; 
;    "LET (\f. tm) (\v1 ... vn. u)" --> (ol-let (((f v1 ... vn) . u)) tm)
; 
; "let x1=u1 and ... and xn=un in tm"
; 
;    "LET ( ... (LET (\x1 ... xn. tm) u1) ... ) un"
;    --> 
;    (ol-let ((x1 . u2) ... (xn .un)) tm)
; 

(defun prep-ol-let (tm)
 (and (is-comb tm)
      (is-special-comb (get-rator tm) `(LET))
      (let* ((tms    (strip-let tm))
             (args   (cdr tms))			; (u1 ... un) 
             (p      (strip-abs(car tms)))
             (params (car p))			; (x1 ... xn)
             (body   (cdr p)))			; tm
       (and (eq (length params) (length args))
            (list 
              'ol-let
              (mapcar
               (function
                (lambda (x u)
                 (let ((q (strip-abs u)))
                  (cons
                    (cons (prep-tm x) (mapcar (function prep-tm) (car q)))
                    (prep-tm(cdr q))))))
               params
               args)
              (prep-tm body))))))

; Old code:
;(defun print-ol-let (tm)
;  (let ((bnd (cadr tm))
;        (body (caddr tm)))
;       (pbegin 0)
;       (ptoken |let |)
;       (print-tm x t nil)
;       (ptoken | = |)
;       (print-tm t1 t nil)
;       (pbreak 1 0)
;       (ptoken |in|)
;       (pbreak 1 0)
;       (print-tm t2 t nil)
;       (pend)))

; MJCG 3/2/89 for HOL88
; Printing of let bindings
;    ((x) . u) --> x = u
; 
;    ((f v1 ... vn) . u) --> f v1 ... vn = u

(defun print-ol-bnd (b)
 (pibegin 0)
 (print-tm (caar b) t nil)
 (pbreak 0 0)
 (mapc 
  (function
   (lambda (y) (ptoken | |) (pbreak 0 1) (print-tm y 'varstruct nil)))
  (cdar b))
 (ptoken | = |)
 (pbreak 0 2)
 (print-tm (cdr b) 'let-rhs nil)
 (pend))

; MJCG 3/2/89 for HOL88
; Modified printing of let-terms
(defun print-ol-let (tm)
  (let ((bnd (cadr tm))
        (body (caddr tm)))
       (pbegin 0)
       (ptoken |let |)
       (print-ol-bnd (car bnd))
       (mapc 
        #'(lambda (y) (pbreak 1 0 ) (ptoken |and |) (print-ol-bnd y))
        (cdr bnd))
       (pbreak 1 0)
       (ptoken |in|)
       (pbreak 1 1)
       (print-tm body t nil)
       (pend)))

; MJCG 2/2/89 for HOL88
; code for printing "\(v1,v2,...,vn).t"

; MJCG 2/2/89 for HOL88
; function for making pairs: ("t1" "t2") --> "(t1,t2)"

(defun make-pair (t1 t2)
 (let* ((ty1    (get-type t1))
        (ty2    (get-type t2))
        (prodty (make-type 'prod (list ty1 ty2)))
        (fun1ty (make-type 'fun (list ty2 prodty)))
        (fun2ty (make-type 'fun (list ty1 fun1ty))))
   (make-comb 
    (make-comb (make-const comma-sym fun2ty) t1 fun1ty)
    t2
    prodty)))


; dest-uncurry is defined by the rules:
; 
;    ------------------------------------
;    "UNCURRY(\x.\y. t)" --> ("x,y" . t)
; 
;          "(UNCURRY t)" --> ("p" . t1)
;    -----------------------------------------
;    "UNCURRY(\x. UNCURRY t)" --> ("x,p" . t1)
; 
;       "(UNCURRY t)" --> ("p" . "\x.t1")
;    -------------------------------------
;    "UNCURRY(UNCURRY t)" --> ("p,x" . t1)
;
;       "(UNCURRY t)" --> ("p" . "\q.t1")
;    -------------------------------------  ("q" a tuple)
;    "UNCURRY(UNCURRY t)" --> ("p,q" . t1)
; 
; If none of these apply, then nil is returned
; The Lisp code below shows why Prolog is such a nice language!

(defun dest-uncurry (tm)
 (let ((t1 (get-rand tm)))
  (or (and (is-abs t1)
           (is-abs (get-abs-body t1))
            (cons
             (make-pair (get-abs-var t1) (get-abs-var(get-abs-body t1)))
             (get-abs-body(get-abs-body t1))))
      (and (is-abs t1)
           (is-special-comb (get-abs-body t1) '(UNCURRY))
           (let ((p (dest-uncurry (get-abs-body t1))))
             (and p
                  (cons (make-pair (get-abs-var t1) (car p))
                        (cdr p)))))
      (and (is-special-comb t1 '(UNCURRY))
           (let ((p (dest-uncurry t1)))
             (and p
                  (or
                   (and (is-abs (cdr p))
                        (cons (make-pair (car p) (get-abs-var (cdr p)))
                              (get-abs-body(cdr p))))
                   (and (is-special-comb (cdr p) '(UNCURRY))
                        (let ((q (dest-uncurry(cdr p))))
                          (and q
                               (cons (make-pair (car p) (car q)) 
                                     (cdr q))))))))))))
                                  
                   

; (prep-ol-uncurry "\(v1,v2,...,vn).t") --> (quant |\| "v1,...,vn" t)

(defun prep-ol-uncurry (tm)
  (and (is-special-comb tm '(UNCURRY))
       (let ((p (dest-uncurry tm)))
         (and p (list 'quant ol-lam-sym (prep-tm(car p)) (prep-tm(cdr p)))))))

; code for printing "[t1; ... ;tn]"

;is-ol-list tests whether tm is of the form: 
;       CONS t1 (CONS t2 ... (CONS tn nil) ... )

(defun is-ol-cons (tm)
   (and (is-comb tm)
        (let ((rator (get-rator tm)))
             (and (is-comb rator)
                  (is-const (get-rator rator))
                  (eq (get-const-name(get-rator rator)) 'CONS)))))

(defun is-ol-list (tm)
   (or (null-ol-list tm)
       (and (is-ol-cons tm)
            (is-ol-list(tl-ol-list tm)))))

;pre-prep-ol-list gets a list of the elements of an OL value representing
;a list - e.g CONS 1(CONS 2(CONS 3 NIL)) -> (1 2 3)

(defun pre-prep-ol-list (tm)
   (cond ((null-ol-list tm) nil)
         (t (cons (prep-tm (hd-ol-list tm)) 
                  (pre-prep-ol-list (tl-ol-list tm))))))

(defun prep-ol-list (tm)
   (if (is-ol-list tm) 
       (make-prep-term 'ol-list 
                       (pre-prep-ol-list tm)
                       (get-ol-list-type tm))))

(defun print-ol-list (tm)
   (let ((termlist (get-term-list tm)))
    (pibegin 1)
    (ptoken |[|)
    (cond (termlist
	    (print-tm (car termlist) t nil)
	    (mapc 
              #'(lambda (y) (ptoken |;|) (pbreak 0 0) (print-tm y t nil))
              (cdr termlist))))
    (ptoken |]|)
    (pend)))

; prepare conditional for printing
; put the combination (((COND P) X) Y)  into a special format

(defun prep-ol-cond (rator rand ty)
 (if (is-comb rator)
   (let ((ratrat (get-rator rator)))
     (if (is-comb ratrat)
       (let ((ratratrat (get-rator ratrat)))
	 (if (and (is-const ratratrat)
		  (eq (get-const-name ratratrat) 'COND))
	   (make-prep-term
             'cond
 	     (list (prep-tm (get-rand ratrat))
		   (prep-tm (get-rand rator))
		   (prep-tm rand))
	     ty)))))))

; print conditionals

(defun print-cond (tml needty)
     (ptoken |(|)
     (print-tm (first tml) 'then nil)
     (ptoken | => |)
     (pbreak 0 1)
     (print-tm (second tml) 'else nil)
     (ptoken " | ")		; vertical bar
     (pbreak 0 1)
     (print-tm (third tml) 'else needty)
     (ptoken |)|))

; (is-special-comb tm '(tok1 tok2 ...)) checks that tm has the form "F t"
; where "F" is a constant.

(defun is-special-comb (tm tokl)
   (and (is-comb tm)
        (let ((rator (get-rator tm)))
             (and (is-const rator)
                  (memq (get-const-name rator) tokl)))))


; MJCG 27/10/88 for HOL88
; replace a name by its interface-print property (if it exists)
(defmacro get-print-name (name) 
 `(or (get ,name 'interface-print) ,name))

; MJCG 27/10/88 for HOL88
; (prep-ol-quant "Q" "\x.t" ty) --> (quant "Q" "x" "t")
; Modified to use get-print-name
; MJCG 3/2/88 for HOL88
; Modified to handle uncurried functions

(defun prep-ol-quant (t1 t2 ty)
  (and (is-const t1) 
       (get (get-print-name(get-const-name t1)) 'binder)
       (or (and (is-abs t2)
                (list 
                 'quant
                 (get-const-name t1)
                 (prep-tm(get-abs-var t2))
                 (prep-tm(get-abs-body t2))))
           (and (is-special-comb t2 '(UNCURRY))
                (let ((p (dest-uncurry t2)))
                  (and p
                       (list
                        'quant
                         (get-const-name t1)
                         (prep-tm (car p))
                         (prep-tm (cdr p)))))))))

(setq hol-unops  '(|~|))
(setq hol-binops '(/\\ \\/ |==>| |=| |<=>| |,|))
(setq binders    '(\\ |!| |?| |@|))

; (prep-ol-unop "F" "t" ty) --> (F t) 
; where F is an atom and t is a term

(defun prep-ol-unop (t1 t2 ty)
 (if (and (is-const t1) (memq (get-const-name t1) hol-unops))
     (list (get-const-name t1)
           (prep-tm t2))))

; (prep-ol-binop "F t1" "t2" ty) --> (F t1 t2) 
; where F is an atom and t1,t2 are terms

(defun prep-ol-binop (t1 t2 ty)
 (if (is-special-comb t1 hol-binops)
     (list (get-const-name(get-rator t1))
           (prep-tm(get-rand t1))
           (prep-tm t2))))

; print a formula built from a unary operator

(defun print-ol-unop (fm)
 (case (first fm)
  (|~| (print-neg fm))))

; print a formula built from a binary operator
; suppress parentheses using right-associativity (except for =)
; print tuples as an inconsistent block

; first an ad-hoc function for printing equations
; MJCG 20/10/88 for HOL88
; modified to use pistring

(defun print-eq (fm)
  (print-tm (second fm) '|=| nil)
;  (ptoken | =|) 		; old code
  (ptoken | |)(pistring '|=|)
  (pbreak 1 0)
  (print-tm (third fm) '|=| nil))
 
; MJCG 19/10/88 for HOL88
; print a user-defined infix operator
; modified to invert interface-map
(defun print-infixcomb (tml pcrator)
    (print-tm (second tml) 'infixcomb pcrator)
    (ptoken | |)
    (pistring (get-const-name (first tml)))
    (pbreak 1 0)
    (print-tm (third tml) 'infixcomb pcrator)) 	; print-infixcomb

; MJCG 19/10/88 for HOL88
; print a binary operator
; modified to invert interface-map

(defun print-ol-binop (fm)
  (let ((op (first fm)))
   (case op
    (|=| (print-eq fm))
    (t   (case op
          (|,| (pibegin 0))
          (t   (pbegin 0)))
         (while (eq op (first fm))
          (print-tm (second fm) op nil)
          (case (first fm)
;           (|,|   (ptoken |,|)    (pbreak 0 0))
;           (|=|   (ptoken | =|)   (pbreak 1 0))
;           (/\\  (ptoken | /\|)  (pbreak 1 0))
;           (\\/  (ptoken | \/|)  (pbreak 1 0))
;           (|==>| (ptoken | ==>|) (pbreak 1 0))
;           (|<=>| (ptoken | <=>|) (pbreak 1 0)))
           (|,| (cond 
                 ((and |%interface_print-flag| 
                       (get '|,| 'interface-print))
                  (ptoken | |)(pistring '|,|) (pbreak 1 0))
                 (t (ptoken |,|) (pbreak 0 0))))
           (|=|   (ptoken | |)(pistring '|=|)   (pbreak 1 0))
           (/\\  (ptoken | |)(pistring '/\\)  (pbreak 1 0))
           (\\/  (ptoken | |)(pistring '\\/)  (pbreak 1 0))
           (|==>| (ptoken | |)(pistring '|==>|) (pbreak 1 0))
           (|<=>| (ptoken | |)(pistring '|<=>|) (pbreak 1 0)))
          (setq fm (third fm)))
         (print-tm fm op nil)
         (pend)))))

; MJCG 20/10/88 for HOL88
; modified to use pistring
; print a negation

(defun print-neg (fm) (pistring '|~|) (print-tm (second fm) (first fm) t))

; print Qx y z.w  instead of Qx. Qy. Qz. (where Q is a binder)
; this makes a big difference if the formula is broken over several lines
; "\" is treated as a quantifier for printing purposes

(putprop lam-sym t 'binder)


; MJCG 19/10/88 for HOL88
; print a quantifier
; modified to invert interface-map

(setq |%print_uncurry-flag| t)

(defun print-ol-quant (fm)
  (let ((quant (second fm))
        (vars (third fm))
        (body (fourth fm)))
    (pbegin 1)
    (pistring quant)
    (if (not(memq quant binders)) (ptoken | |))
    (pibegin 0)
    (print-tm vars 'quant t)
    (while (and (eq (first body) 'quant) (eq (second body) quant))
           (pbreak 1 0)
	   (print-tm (third body) 'quant t)
	   (setq body (fourth body)))
    (pend)
    (ptoken |.|)
    (pend)
    (pbreak 1 1)
    (print-tm body 'quant t)))

; Change printing of predicate formulae to suppress HOL_ASSERT

(defun print-pred-form (fm)
    (cond ((not(eq(get-pred-sym fm)'HOL_ASSERT))
           (pstring (get-pred-sym fm))
           (pbreak 1 0)))
    (print-tm (get-pred-arg fm) t t))

; Changes top-level printing of theorems to suppress quotes

(defun ml-print_thm (th)
  (cond ((not(null(car th)))
         (mapc #'(lambda (x) (ptoken |.|)) (car th))
         (ptoken | |)))
  (pstring %turnstile) 
  (print-fm (prep-fm(cdr th)) t)
  ) 

; Printing a theorem and all its assumptions

(defun ml-print_all_thm (th)
  (pibegin 0)
  (cond ((not(null(car th)))
         (print-fm(prep-fm(caar th))t)
         (mapc 
          #'(lambda (x) (ptoken |, |) (pbreak 0 0) (print-fm(prep-fm x)t))
          (cdar th))
         (ptoken | |)
         (pbreak 0 0)))
  (pstring %turnstile) 
  (print-fm (prep-fm(cdr th)) t)
  (pend)
  ) 

(dml |print_all_thm| 1 ml-print_all_thm (thm -> void))

; Print value, type of top-level expression
; HOL: modified not to print ": thm" after theorems
; MJCG 31/1/89 for HOL88
; Added test for |%print_top_types-flag|
; MJCG 7/2/89 for HOL88
; Added test for |%print_top_val-flag|
(setq |%print_top_types-flag| t)
(setq |%print_top_val-flag| t)
(defun prvalty (x ty)
  (cond
   (|%print_top_val-flag| 
    (prinml x ty nil)
    (cond ((not(eq (car ty) 'mk-thmtyp))
           (pbreak 1 0)
           (cond (|%print_top_types-flag|
                  (ptoken |: |)
                  (printmty ty)))))
    (pnewline))))

; MJCG 27/10/88 for HOL88
; detect infixes and long combinations
; modified to invert interface-map
(defun prep-comb (rator rand ty)
  (let ((prator (prep-tm rator))(prand (prep-tm rand)))
     (cond
     ((and (is-const prator)
           |%print_infix-flag|
	   (eq (get (get-print-name(get-const-name prator)) 'olinfix) 'paired)
	   (eq (term-class prand) 'pair))
      (make-prep-term 'infixcomb (cons prator (get-term-list prand)) ty))
     ((eq (term-class prator) 'listcomb)
      (prep-curr (get-term-list prator) prand ty))
     ((make-prep-term 'listcomb (list prator prand) ty)))
     ))  ;prep-comb


; MJCG 27/10/88 for HOL88
; detect infixes and long combinations
; see if ((tm1 tm2 ...) y) is the curried infix "tm2 <tm1> y"
; otherwise return (tm1 tm2 ... y)
; modified to invert interface-map
(defun prep-curr (tml y ty)
; Modification J.Joyce Apr 87 - fix non-standard zetalisp
      (let ((tm1 (car tml)) (tm2 (cadr tml)) (tmtail (cddr tml)))
	(if (and (null tmtail) (is-const tm1) |%print_infix-flag|
		 (eq (get (get-print-name(get-const-name tm1)) 'olinfix) 'curried))
	    (make-prep-term 'infixcomb (list tm1 tm2 y) ty)
	    (make-prep-term 'listcomb (append tml (list y)) ty)
	    )))					;prep-curr


; MJCG 7/2/89 for HOL88
; Function to print currently defined types
(defun prdeftypes ()
 (pbegin 1)
 (pbreak 0 1)
 (mapc
  (function
   (lambda (p)
    (cond ((atom (cdr p)) 
           (pstring (car p)) 
           (ptoken | -- an abstract type|)
           (pbreak 0 1))
          (t (pstring (car p))
             (ptoken | = |)
             (printmty (cdr p))
             (pbreak 0 1)))))
   (reverse %deftypes))
  (pend)
  (pnewline))

(dml |print_defined_types| 0 prdeftypes (|void| -> |void|))



; =============== Added to support programming language ===============

; Printing hacks for programming language

; |`X`|  -->  |X|

(defun strip-primes (x)
  (imploden(reverse(cdr(reverse(cdr(exploden x)))))))

(defun strip-primes-from-const (tm)
  (if (is-const tm)
      (make-const (strip-primes(get-const-name tm)) (get-type tm))
      tm))

;  "\s. ... s`X` ..."  -->  "... X ..."

(defun delambda (tm)
 (if (is-abs tm)
     (delambda-fun (get-var-name(get-abs-var tm)) (get-abs-body tm))
     tm))

(defun delambda-fun (s tm)
 (cond ((and (is-comb tm)
             (is-var (get-rator tm))
             (eq (get-var-name(get-rator tm)) s)
             (is-const (get-rand tm)))
        (make-var (strip-primes(get-const-name(get-rand tm)))
                  (get-type(get-rand tm))))
       ((is-comb tm)
        (make-comb 
         (delambda-fun s (get-rator tm))
         (delambda-fun s (get-rand tm))
         (get-type tm)))
       ((and (is-abs tm)
             (eq (get-var-name(get-abs-var tm)) s))
        tm)
       ((is-abs tm)
        (make-abs 
         (get-abs-var tm)
         (delambda-fun s (get-abs-body tm))
         (get-type tm)))
       (t tm)))


; =====================================================================
; prepare assignment for printing

(defun prep-ol-assign (rator rand ty)
 (and |%print_lang-flag|
      (is-const rator)
      (eq (get-const-name rator) 'MK_ASSIGN)
      (make-prep-term
        'assign
        (list (prep-tm (get-fst rand))
              (prep-tm (delambda(get-snd rand))))
        ty)))
       
; print assignment ******

(defun print-assign (tml needty)
     (pbegin 0)
     (print-tm (strip-primes-from-const(first tml)) 'assign-left nil)
     (ptoken | := |)
     (pbreak 0 1)
     (print-tm (second tml) 'assign-right needty)
     (pend)
       )

; =====================================================================
; prepare if-then for printing

(defun prep-ol-it (rator rand ty)
 (and |%print_lang-flag|
      (is-const rator)
      (eq (get-const-name rator) 'MK_IF1)
      (make-prep-term
        'it
        (list (prep-tm (delambda(get-fst rand)))
              (prep-tm (get-snd rand)))
        ty)))
       
; print if-then ******

(defun print-it (tml needty)
     (pbegin 0)
     (ptoken |if |)
     (print-tm (first tml) 'if nil)
     (ptoken | then |)
     (pbreak 0 1)
     (print-tm (second tml) 'Then needty)
     (pend)
       )

; =====================================================================
; prepare if-then-else for printing

(defun prep-ol-ite (rator rand ty)
 (and |%print_lang-flag|
      (is-const rator)
      (eq (get-const-name rator) 'MK_IF2)
      (make-prep-term
        'ite
        (list (prep-tm (delambda(get-fst rand)))
              (prep-tm (get-fst(get-snd rand)))
              (prep-tm (get-snd(get-snd rand))))
        ty)))
       
; print if-then-else ******

(defun print-ite (tml needty)
     (pbegin 0)
     (ptoken |if |)
     (print-tm (first tml) 'if nil)
     (ptoken | then |)
     (pbreak 0 1)
     (print-tm (second tml) 'Then nil)
     (ptoken | else |)		
     (pbreak 0 1)
     (print-tm (third tml) 'Else needty)
     (pend)
       )

; =====================================================================
; prepare sequence for printing

(defun flatten-seq (tm)
 (if (and (is-const tm)
          (eq (get-const-name rator) 'MK_SEQ))
     (append (flatten-seq (get-fst (get-rand tm)))
             (flatten-seq (get-snd (get-rand tm))))
     (list tm)))

(defun prep-ol-seq (rator rand ty)
 (and |%print_lang-flag|
      (is-const rator)
      (eq (get-const-name rator) 'MK_SEQ)
      (make-prep-term
        'seq
        (list (mapcar 
               (function prep-tm) 
               (append (flatten-seq (get-fst rand))
                       (flatten-seq (get-snd rand)))))
        ty)))

; print seq ******

(defun print-seq (tml needty)
 (let ((l (car tml)))
      (pbegin 0)
      (cond (l
	      (print-tm (car l) t nil)
	      (mapc 
                #'(lambda (y) (ptoken |; |) (pbreak 0 0) (print-tm y t nil))
                (cdr l))))
      (pend)
 ))


; prepare while for printing

(defun prep-ol-while (rator rand ty)
 (and |%print_lang-flag|
      (is-const rator)
      (eq (get-const-name rator) 'MK_WHILE)
      (make-prep-term
        'while
 	(list (prep-tm (delambda(get-fst rand)))
              (prep-tm (get-snd rand)))
        ty)))

; print while ******

(defun print-while (tml needty)
     (pbegin 0)
     (ptoken |while |)
     (print-tm (first tml) 'while nil)
     (ptoken | do |)
     (pbreak 0 1)
     (print-tm (second tml) 'do nil)
     (pend))

; prepare assertion for printing

(defun prep-ol-assert (rator rand ty)
 (and |%print_lang-flag|
      (is-const rator)
      (eq (get-const-name rator) 'MK_ASSERT)
      (make-prep-term
        'assert
 	(list (prep-tm (delambda rand)))
        ty)))

; print assert ******

(defun print-assert (tml needty)
     (pbegin 0)
     (ptoken |assert{|)
     (print-tm (first tml) 'assert nil)
     (ptoken |}|)
     (pend))

; prepare invariant for printing

(defun prep-ol-invariant (rator rand ty)
 (and |%print_lang-flag|
      (is-const rator)
      (eq (get-const-name rator) 'MK_INVARIANT)
      (make-prep-term
        'invariant
 	(list (prep-tm (delambda rand)))
        ty)))

; print invariant ******

(defun print-invariant (tml needty)
     (pbegin 0)
     (ptoken |invariant{|)
     (print-tm (first tml) 'invariant nil)
     (ptoken |}|)
     (pend))

; prepare variant for printing

(defun prep-ol-variant (rator rand ty)
 (and |%print_lang-flag|
      (is-const rator)
      (eq (get-const-name rator) 'MK_VARIANT)
      (make-prep-term
        'variant
 	(list (prep-tm (delambda rand)))
        ty)))

; print variant ******

(defun print-variant (tml needty)
     (pbegin 0)
     (ptoken |variant{|)
     (print-tm (first tml) 'variant nil)
     (ptoken |}|)
     (pend))


; prepare spec for printing

(defun prep-ol-spec (rator rand ty)
 (and |%print_lang-flag|
      (is-const rator)
      (eq (get-const-name rator) 'MK_SPEC)
      (make-prep-term
        'spec
 	(list (prep-tm (delambda(get-fst rand)))
              (prep-tm (get-fst(get-snd rand)))
              (prep-tm (delambda(get-snd(get-snd rand)))))
        ty)))

; print spec ******

(defun print-spec (tml needty)
     (pbegin 0)
     (ptoken |{|)
     (print-tm (first tml) 'spec-left nil)
     (ptoken |}|)
     (pbreak 0 1)
     (print-tm (second tml) t nil)
     (pbreak 0 0)
     (ptoken |{|)
     (print-tm (third tml) 'spec-right nil)
     (ptoken |}|)
     (pend))

(defun prep-ol-t-spec (rator rand ty)
 (and |%print_lang-flag|
      (is-const rator)
      (eq (get-const-name rator) 'T_SPEC)
      (make-prep-term
        't-spec
 	(list (prep-tm (delambda(get-fst rand)))
              (prep-tm (get-fst(get-snd rand)))
              (prep-tm (delambda(get-snd(get-snd rand)))))
        ty)))

; print t-spec ******

(defun print-t-spec (tml needty)
     (pbegin 0)
     (ptoken |[|)
     (print-tm (first tml) 't-spec-left nil)
     (ptoken |]|)
     (pbreak 0 1)
     (print-tm (second tml) t nil)
     (pbreak 0 0)
     (ptoken |[|)
     (print-tm (third tml) 't-spec-right nil)
     (ptoken |]|)
     (pend))

; =====================================================================
