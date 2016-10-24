;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        hol-writ.l                                          ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Lisp functions for printing HOL terms               ;;;
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
;;;   REVISION HISTORY: (none)                                              ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; RJB 16.11.92 - All occurrences of <=> deleted.

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (include "lisp/f-ol-rec")
   (include "lisp/genmacs")
   (special ol-lam-sym hol-unops hol-binops binders |%show_types-flag|
      |%interface_print-flag| %turnstile |%print_top_types-flag|
      |%print_list-flag| |%print_cond-flag|
      |%print_quant-flag| |%print_restrict-flag|
      |%print_let-flag| |%print_uncurry-flag| |%print_infix-flag|
      |%print_lettypes-flag| |%print_top_val-flag|  |%print_set-flag|
      |%empty-set| |%finite-set-constructor| |%set-abstraction-constructor|
      |%pp_sexpr-flag| |%print_sexpr-flag| %pt1 |%print_parse_trees-flag|))

#+franz
(declare
   (localf subtract is-subset nargtys polytys uninferred-poly-remnant
      prep-ol-let
      print-ol-bnd
      print-ol-let
      prep-ol-uncurry
      is-ol-cons
      is-ol-list
      pre-prep-ol-list
      prep-ol-list
      print-ol-list
      is-ol-set-cons
      is-ol-finite-set
      pre-prep-ol-finite-set
      prep-ol-finite-set
      print-ol-finite-set
      prep-ol-set-abstraction
      print-ol-set-abstraction
      prep-ol-cond
      is-special-comb
      prep-ol-quant
      prep-ol-restrict
      prep-ol-unop
      prep-ol-binop
      print-ol-unop
      print-eq
      print-ol-binop
      print-neg
      print-ol-quant
      print-ol-restrict))

;;; If T1 is a 'closes property of T2 then brackets will be put around
;;; T1 when it is printed in the context of T2

(eval-when (load)
   (mapc
      #'(lambda (x) (putprop (car x) (cdr x) 'closes))
      '((|~| . (quant restrict /\\ \\/ |==>| |,| |=|))
         (/\\ . (quant restrict /\\ \\/ |==>| |,| |=|))
         (\\/ . (quant restrict \\/ |==>| |,| |=|))
         (|==>| . (quant restrict |==>| |,| |=|))
         (|,| . (quant restrict |,| /\\ \\/ |==>| ol-let |=|))
         (|=| . (quant restrict ol-let |=|))
         (then . (quant restrict then |=| /\\ \\/ |~| |==>|))
         (else . (quant restrict then |,| |=| /\\ \\/ |==>|))
         (listcomb . (quant restrict listcomb ratorofcomb infixcomb then
                      |,| typed ol-let |=| /\\ \\/ ==> ))
         (ratorofcomb . (quant restrict listcomb ratorofcomb infixcomb then
                         |,| typed ol-let |=| /\\ \\/ ==> ))
         (infixcomb . (quant restrict listcomb ratorofcomb infixcomb then
                       |,| typed ol-let |=| /\\ \\/ ==> |~|))
         (varstruct . (|,| typed))
         (varstructrator . (|,| typed))
         (let-rhs . (|=| |,| typed))
         (let-body . (quant restrict  |=| /\\ \\/ |~| |==>|))
         (typed . (infixcomb))
         (fun . (fun))
         (sum . (sum fun))
         (prod . (prod sum fun))
         (quant . (|,| typed))
         (restrict . (|,| typed))
         (fin-set . (|,|))
         (set-abs1 . (|,|))
         (eqn-rhs . (quant restrict listcomb ratorofcomb infixcomb then
                     |,| typed)))))


;;; MJCG 17/1/89 for HOL88
;;; Code change from Davis Shepherd for changing lambda symbol
;;; (ol-lam-sym for lam-sym)
;;; MJCG 31/1/89 for HOL88
;;; Modified to support print_flags
;;; MJCG 5/8/90 for HOL88.1.12
;;; |%print_set-flag| added

(eval-when (load)
   (mapc
      (function (lambda (x) (set x t)))
      '(|%print_list-flag| |%print_cond-flag| |%print_restrict-flag|
        |%print_quant-flag| |%print_infix-flag| |%print_let-flag|
        |%print_comb-flag|))
   (setq |%print_set-flag| nil))

;;; MJCG 5/8/90 for HOL88.1.12
;;; Modified to print sets

(defun prep-tm (tm)
   (case (term-class tm)
      (var tm)
      (const (cond ((and |%print_set-flag| (eq (get-const-name tm) %empty-set))
                    `(ol-finite-set . (nil . ,(get-ol-set-type tm))))
                   ((and |%print_list-flag| (eq (get-const-name tm) 'NIL))
                    `(ol-list . (nil . ,(get-ol-list-type tm))))
                   (t tm)))
      (abs (list 'quant ol-lam-sym (get-abs-var tm) (prep-tm (get-abs-body tm))))
      (comb (let ((rator (get-rator tm))
               (rand (get-rand tm))
               (ty (get-type tm)))
            (or (and |%print_set-flag|     (prep-ol-finite-set tm))
                (and |%print_set-flag|     (prep-ol-set-abstraction rator rand ty))
                (and |%print_list-flag|    (prep-ol-list tm))
                (and |%print_cond-flag|    (prep-ol-cond rator rand ty))
                (and |%print_restrict-flag|(prep-ol-restrict rator rand ty))
                (and |%print_quant-flag|   (prep-ol-quant rator rand ty))
                (and |%print_let-flag|     (prep-ol-let tm))
                (and |%print_infix-flag|   (prep-ol-binop rator rand ty))
                (and |%print_infix-flag|   (prep-ol-unop rator rand ty))
                (and |%print_uncurry-flag| (prep-ol-uncurry tm))
                (prep-comb rator rand ty))))
      (t (lcferror "prep-tm"))))


;;; Added by RJB 16.11.92
;;; Set difference

(defun subtract (l1 l2)
   (if (null l1) nil
      (if (member (car l1) l2) (subtract (cdr l1) l2)
         (cons (car l1) (subtract (cdr l1) l2)))))

;;; Added by RJB 16.11.92

(defun is-subset (l1 l2)
   (if (null l1) t (and (member (car l1) l2) (is-subset (cdr l1) l2))))

;;; Added by RJB 16.11.92
;;; Given a type and a number n this function returns a cons cell whose car is
;;; a list of the first n argument types and the cdr is the remainder of the
;;; type. If the number of arguments is less than n, the function stops pulling
;;; off argument types when they are exhausted.

(defun nargtys (ty n)
   (if (or (< n 1) (not (eq (get-type-op ty) '|fun|))) (cons nil ty)
      (let ((tyargs (get-type-args ty)))
      (let ((argty (car tyargs)) (restty (cadr tyargs)))
      (let ((result (nargtys restty (- n 1))))
         (cons (cons argty (car result)) (cdr result)))))))

;;; Added by RJB 16.11.92
;;; Obtains a list of the type variables present in a type.

(defun polytys (ty)
   (if (is-vartype ty) (list ty)
      (itlist 'union (cons nil (mapcar 'polytys (get-type-args ty))) nil)))

;;; Added by RJB 16.11.92
;;; This function takes a name of an object language constant and a number.
;;; Suppose the constant has been applied to that number of arguments and the
;;; types of those arguments are known. Then, this function returns non-nil if
;;; it is still not possible to infer the type of the application.
;;; It does this by testing the remnant of the most general type of the
;;; constant to see if it contains a type variable that does not appear in the
;;; types of the arguments.

(defun uninferred-poly-remnant (cname num-of-args)
   (let ((cty (constp cname)))
   (let ((splitty (nargtys cty num-of-args)))
   (let ((argtys (car splitty)) (resty (cdr splitty)))
      (not (is-subset (polytys resty)
              (itlist 'union (cons nil (mapcar 'polytys argtys)) nil)))))))

;;; RJB 16.11.92: Pretty-printing with `show_types' true re-implemented.
;;;
;;; The basic idea is:
;;; (1) Type the bound variables of abstractions. Note that this ensures that
;;;     terms such as "@(x:*). T" are printed with enough type information.
;;; (2) Type each free variable exactly once.
;;; (3) Type polymorphic constants (including NIL) if they are not the operator
;;;     of an application.
;;; (4) Type an application (combination) if its operator is a constant whose
;;;     most general type contains a type variable which cannot be inferred
;;;     from the arguments (see uninferred-poly-remnant).
;;; This is achieved by passing around a list of variables (actually name/type
;;; pairs) that have already been adorned with type information during the
;;; term traversal. The only tricky bit is dealing with bound variables.
;;; As a binding is entered the bound variables are added to the list of typed
;;; variables coming down the term tree (The bound variables are typed at the
;;; binding so don't need to be done in the body.). As the traversal comes
;;; back up through the binding, the new variables added to the list (that is
;;; those variables that were adorned with type information inside the body)
;;; are extracted and added to the original list of typed variables. This
;;; allows the bound variables to be removed from the list so that free
;;; variables of the same name will still be typed, but without removing such
;;; variables from the list if they had already been typed.
;;;
;;; An additional optimisation is performed: A term is not printed with type
;;; information if it is a direct subterm of ~, /\, \/, or ==>. However, if
;;; the term is a variable it *is* added to the typed-variable list since we
;;; know its type can be inferred.
;;;
;;; This scheme certainly doesn't keep type information to a minimum but I
;;; don't think the amount will be excessive, and I think it will provide
;;; enough information for the type of the term to be inferred which was not
;;; the case for the old version.
;;;
;;; - RJB
;;;
;;; Printing of $ before infixed variables added
;;; MJCG 01.02.94

(defun print-tm (tm op1 typedvars)
   (let ((op2 (term-class tm))
         (tml (get-term-list tm))
         (ty (get-type tm)))
      (let ((tyflag               ; print type of this particular term?
               (and |%show_types-flag|
                  (case op2
                     (var (not (member (cdr tm) typedvars)))
                     (const (and (not (eq op1 'ratorofcomb))
                                 (opoly (constp (get-const-name tm)))))
                     ((listcomb infixcomb)
                        (let ((r (first tml))    ; find innermost operator
                              (n (- (length tml) 1)))
                           (if (eq (term-class r) 'infixcomb)
                              (setq n (+ n (- (length (get-term-list r)) 1))
                                    r (first (get-term-list r))))
                           (and (is-const r)
                              (uninferred-poly-remnant (get-const-name r) n))))
                     ((ol-list ol-finite-set) (eq tml nil))
                     (t nil))))
            (knownty (memq op1 '(|~| /\\ \\/ |==>| varstructrator))))
         (let ((printty (and tyflag (not knownty))))
         ; possibly one pair of parens for precedence, another for typing
         (let ((cl1 (closes op1 (if printty 'typed op2)))
               (cl2 (and printty (closes 'typed op2))))
            (if cl1 (ptoken |(|))
            (if cl2 (ptoken |(|))
            (pbegin 0)
            (setq typedvars
               (case op2
                  (var (progn (if (memq (get-var-name tm) hol-var-binops)
                                        (ptoken |$|))
                              (pstring (get-var-name tm))
                              (if tyflag (cons (cdr tm) typedvars) typedvars)))
                  (const (progn (print-const (get-const-name tm)) typedvars))
                  (cond (print-cond tml typedvars))
                  (listcomb (print-listcomb tml typedvars))
                  (infixcomb (print-infixcomb tml typedvars))
                  (restrict (print-ol-restrict tm typedvars))
                  (quant (print-ol-quant tm typedvars))
                  (|~| (print-ol-unop tm typedvars))
                  ((|=| /\\ \\/ |==>| |,|) (print-ol-binop tm typedvars))
                  (ol-let (print-ol-let tm typedvars))
                  (ol-list (print-ol-list tm typedvars))
                  (ol-finite-set (print-ol-finite-set tm typedvars))
                  (ol-set-abstraction (print-ol-set-abstraction tml typedvars))
                  (t (lcferror "print-tm"))))
            (cond (printty            ; print type
                  (if cl2 (ptoken |)|)
                     (ifn (memq op2 '(var const ol-list ol-finite-set))
                        (ptoken | |)))
                  (pbreak 0 0)
                  (ptoken |:|)
                  (print-ty (case op2 (ol-list (list '|list| ty))
                                      (ol-finite-set (list '|set| ty))
                                      (t ty)) t)))
            (if cl1 (ptoken |)|))
            (pend))
            typedvars))))

;;; MJCG 20/10/88 for HOL88
;;; string printing function that inverts interface
(defun pistring (str)
   (pstring (or (and |%interface_print-flag| (get str 'interface-print))
         str)))

;;; MJCG 19/10/88 for HOL88
;;; print a constant (may be a prefix, infix or binder standing alone)
;;; modified to invert interface-map
(defun print-const (name)
   (cond ((or (get name 'olinfix)
            (get name 'prefix)
            (get name 'binder))
         (ptoken |$|)))
   (pistring name))

;;; MJCG 3/2/89 for HOL88
;;; Function for stripping of the varstructs of a function
;;; "\v1 v2 ... vn. t"  --> ((v1 v2 ... vn) . t)
;;; "t"                 --> (nil . t)  -- t not a function
;;; (vi either a variable or a varstruct)
;;; MJCG 27/6/92
;;; Strip off at most n lambdas if n is a number and all lambdas otherwise
;;; (strip-abs ("\x1 ... xm ... xn. e" m)) = ((x1 ... xm) "\x(m+1) ... xn. e")
(defun strip-abs (tm n)
 (or (and (numberp n) (eq n 0) (cons nil tm))
     (and (is-abs tm)
          (let* ((v (get-abs-var tm))
                 (b (get-abs-body tm))
                 (p (strip-abs b (if (numberp n) (sub1 n) n))))
            (cons (cons v (car p)) (cdr p))))
     (and (is-special-comb tm '(UNCURRY))
          (let* ((p (dest-uncurry tm))
                 (q (strip-abs (cdr p) (if (numberp n) (sub1 n) n))))
            (cons (cons (car p) (car q)) (cdr q))))
     (cons nil tm)))


;;; MJCG 3/2/89 for HOL88
;;; Function for exploding an application
;;; "LET ( ... (LET t1 t2) ... ) tn"  --> (t1 t2 ... tn)
;;; "t"                 --> (t)  -- t not of this form

(defun strip-let (tm)
   (or (and (is-comb tm)
         (is-special-comb (get-rator tm) '(LET))
         (let ((args (strip-let(get-rand(get-rator tm)))))
            (append args (list (get-rand tm)))))
      (list tm)))

;;; code for printing "let ... in ... "
;;; MJCG 3/2/89 for HOL88
;;; Extended to deal with fancier let constructs
;;;
;;; "let x=u in tm"
;;;
;;;    "LET (\x. tm) u" --> (ol-let (((x) . u)) tm)
;;;
;;; "let f v1 ... vn = u in tm"
;;;
;;;    "LET (\f. tm) (\v1 ... vn. u)" --> (ol-let (((f v1 ... vn) . u)) tm)
;;;
;;; "let x1=u1 and ... and xn=un in tm"
;;;
;;;    "LET ( ... (LET (\x1 ... xn. tm) u1) ... ) un"
;;;    -->
;;;    (ol-let ((x1 . u2) ... (xn .un)) tm)
;;;
;;; Modified by MJCG 27/6/92 to use new strip-abs with second argument

(defun prep-ol-let (tm)
   (and (is-comb tm)
      (is-special-comb (get-rator tm) `(LET))
      (let* ((tms    (strip-let tm))
            (args   (cdr tms))                            ; (u1 ... un)
            (p      (strip-abs (car tms) (length args)))
            (params (car p))                              ; (x1 ... xn)
            (body   (cdr p)))                             ; tm
         (and (= (length params) (length args))
            (list
               'ol-let
               (mapcar
                (function
                 (lambda (x u)
                  (let ((q (strip-abs u nil)))
                   (cons
                    (cons (prep-tm x) (mapcar (function prep-tm) (car q)))
                          (prep-tm(cdr q))))))
                params
                args)
               (prep-tm body))))))

;;; MJCG 3/2/89 for HOL88
;;; Printing of let bindings
;;;    ((x) . u) --> x = u
;;;
;;;    ((f v1 ... vn) . u) --> f v1 ... vn = u
;;;
;;; Modified by RJB 16.11.92
;;;
;;; The variable being declared by the let binding is not printed with type
;;; information, but any occurrence of it within the body (as a recursive call)
;;; is printed with type information otherwise it may not be possible to infer
;;; the type of the body. If a structure is being declared (e.g. "(x,y)") all
;;; the variables in it *are* given types. This is because the `varstructrator'
;;; context gets lost once the structure is entered and I don't want to
;;; complicate the code with a more sophisticated technique.
;;;
;;; Note that the result returned by this function is not the usual list of
;;; variables that have already been typed but a cons of the variables declared
;;; by the let binding and that list.

(defun print-ol-bnd (b typedvars)
   (pibegin 0)
   (let ((letvars (print-tm (caar b) 'varstructrator nil))
         (boundvars nil))
      (pbreak 0 0)
      (mapc
         (function
            (lambda (y) (ptoken | |) (pbreak 0 1)
               (setq boundvars
                  (append (print-tm y 'varstruct nil) boundvars))))
         (cdar b))
      (ptoken | = |)
      (pbreak 0 2)
      (let ((bodyvars (append boundvars typedvars)))
         (let ((newlytypedvars (ldiff (print-tm (cdr b) 'let-rhs bodyvars)
                                  bodyvars)))
            (pend)
            (cons letvars
               (append (subtract newlytypedvars letvars) typedvars))))))

;;; MJCG 3/2/89 for HOL88
;;; Modified printing of let-terms
;;; Modified by RJB 16.11.92
(defun print-ol-let (tm typedvars)
   (let ((bnd (cadr tm))
         (body (caddr tm))
         (letvars nil))
      (pbegin 0)
      (ptoken |let |)
      (let ((result (print-ol-bnd (car bnd) typedvars)))
         (setq letvars (append (car result) letvars))
         (setq typedvars (cdr result)))
      (mapc
         #'(lambda (y) (pbreak 1 0 ) (ptoken |and |)
              (let ((result (print-ol-bnd y typedvars)))
                 (setq letvars (append (car result) letvars))
                 (setq typedvars (cdr result))))
         (cdr bnd))
      (pbreak 1 0)
      (ptoken |in|)
      (pbreak 1 1)
      (let ((bodyvars (append letvars typedvars)))
         (setq typedvars
            (append
               (ldiff (print-tm body 'let-body bodyvars) bodyvars)
               typedvars)))
      (pend)
      typedvars))

;;; MJCG 2/2/89 for HOL88
;;; code for printing "\(v1,v2,...,vn).t"

;;; MJCG 2/2/89 for HOL88
;;; function for making pairs: ("t1" "t2") --> "(t1,t2)"

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


;;; dest-uncurry is defined by the rules:
;;;
;;;    ------------------------------------
;;;    "UNCURRY(\x.\y. t)" --> ("x,y" . t)
;;;
;;;          "(UNCURRY t)" --> ("p" . t1)
;;;    -----------------------------------------
;;;    "UNCURRY(\x. UNCURRY t)" --> ("x,p" . t1)
;;;
;;;       "(UNCURRY t)" --> ("p" . "\x.t1")
;;;    -------------------------------------
;;;    "UNCURRY(UNCURRY t)" --> ("p,x" . t1)
;;;
;;;       "(UNCURRY t)" --> ("p" . "\q.t1")
;;;    -------------------------------------  ("q" a tuple)
;;;    "UNCURRY(UNCURRY t)" --> ("p,q" . t1)
;;;
;;; If none of these apply, then nil is returned
;;; The Lisp code below shows why Prolog is such a nice language!

;;; Bugfix for Common Lisp: added test that argument is a combination (is-comb)
;;; MJCG 3 March 1991

(defun dest-uncurry (tm)
  (and
   (is-comb tm)
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
                                 (cdr q)))))))))))))



;;; (prep-ol-uncurry "\(v1,v2,...,vn).t") --> (quant \\ "v1,...,vn" t)

(defun prep-ol-uncurry (tm)
   (and (is-special-comb tm '(UNCURRY))
      (let ((p (dest-uncurry tm)))
         (and p (list 'quant ol-lam-sym (prep-tm(car p)) (prep-tm(cdr p)))))))

;;; code for printing "[t1; ... ;tn]"

;;; is-ol-list tests whether tm is of the form:
;;;       CONS t1 (CONS t2 ... (CONS tn nil) ... )

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

;;; pre-prep-ol-list gets a list of the elements of an OL value representing
;;; a list - e.g CONS 1(CONS 2(CONS 3 NIL)) -> (1 2 3)

(defun pre-prep-ol-list (tm)
   (cond ((null-ol-list tm) nil)
      (t (cons (prep-tm (hd-ol-list tm))
            (pre-prep-ol-list (tl-ol-list tm))))))

(defun prep-ol-list (tm)
   (if (is-ol-list tm)
      (make-prep-term 'ol-list
         (pre-prep-ol-list tm)
         (get-ol-list-type tm))))

;;; Modified by RJB 16.11.92

(defun print-ol-list (tm typedvars)
   (let ((termlist (get-term-list tm)))
      (pibegin 1)
      (ptoken |[|)
      (cond (termlist
            (setq typedvars (print-tm (car termlist) t typedvars))
            (mapc
               #'(lambda (y) (ptoken |;|) (pbreak 0 0)
                    (setq typedvars (print-tm y t typedvars)))
               (cdr termlist))))
      (ptoken |]|)
      (pend)
      typedvars))

;;; code for printing "{t1, ... ,tn}"
;;; Duplicates code for lists -- would be more space-efficientr to fold set
;;; and list printing code into one set of routines.
;;; The current empty set and finite set constructor are held in the globals
;;; %empty-set, %finite-set-constructor.
;;; The current set abstraction constructor is held in the global
;;; %set-abstraction-constructor

;;; is-ol-finite-set tests whether tm is of the form:
;;;       INSERT t1 (INSERT t2 ... (INSERT tn EMPTY) ... )

(defun is-ol-set-cons (tm)
   (and (is-comb tm)
      (let ((rator (get-rator tm)))
         (and (is-comb rator)
            (is-const (get-rator rator))
            (eq (get-const-name(get-rator rator)) %finite-set-constructor)))))

(defun is-ol-finite-set (tm)
   (or (null-ol-set tm)
      (and (is-ol-set-cons tm)
         (is-ol-finite-set(tl-ol-set tm)))))

;;; pre-prep-ol-finite-set gets a list of the elements of an OL value
;;; representing a finite set
;;; - e.g INSERT 1(INSERT 2(INSERT 3 EMPTY)) -> (1 2 3)

(defun pre-prep-ol-finite-set (tm)
   (cond ((null-ol-set tm) nil)
      (t (cons (prep-tm (hd-ol-set tm))
            (pre-prep-ol-finite-set (tl-ol-set tm))))))

(defun prep-ol-finite-set (tm)
   (if (is-ol-finite-set tm)
      (make-prep-term 'ol-finite-set
         (pre-prep-ol-finite-set tm)
         (get-ol-set-type tm))))

;;; Modified by RJB 16.11.92

(defun print-ol-finite-set (tm typedvars)
   (let ((termlist (get-term-list tm)))
      (pibegin 1)
      (ptoken |{|)
      (cond (termlist
             (setq typedvars (print-tm (car termlist) 'fin-set typedvars))
             (mapc
               #'(lambda (y) (ptoken |,|)
                             (pbreak 0 0)
                             (setq typedvars (print-tm y 'fin-set typedvars)))
               (cdr termlist))))
      (ptoken |}|)
      (pend)
      typedvars))

;;; Prepare set abstractions for printing
;;; MJCG 12/11/90: Modified not to print set abstractions if no variables bound

(defun prep-ol-set-abstraction (rator rand ty)
 (and (is-const rator)
      (eq (get-const-name rator) %set-abstraction-constructor)
      (or (is-abs rand) (dest-uncurry rand))
      (let ((vp (if (is-abs rand)
                    (cons (get-abs-var rand) (get-abs-body rand))
                    (dest-uncurry rand))))
        (if (is-pair (cdr vp))
            (let ((p1 (get-fst (cdr vp)))  ;;; p1   in GSPEC(\vars.(p1,p2))
                  (p2 (get-snd (cdr vp)))  ;;; p2   in GSPEC(\vars.(p1,p2))
                  (vs (freevars(car vp)))) ;;; vars in GSPEC(\vars.(p1,p2))
              (and (equal vs (intersect (freevars p1) (freevars p2)))
                   (make-prep-term
                    'ol-set-abstraction
                    (list (prep-tm p1) (prep-tm p2))
                    ty)))))))

;;; Modified by RJB 16.11.92

(defun print-ol-set-abstraction (tml typedvars)
   (ptoken |{|)
   (setq typedvars (print-tm (first tml) 'set-abs1 typedvars))
   (ptoken | \| |)
   (pbreak 0 1)
   (setq typedvars (print-tm (second tml) 'set-abs2 typedvars))
   (ptoken |}|)
   typedvars)

;;; prepare conditional for printing
;;; put the combination (((COND P) X) Y)  into a special format

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

;;; print conditionals
;;; Modified by RJB 16.11.92

(defun print-cond (tml typedvars)
   (ptoken |(|)
   (setq typedvars (print-tm (first tml) 'then typedvars))
   (ptoken | => |)
   (pbreak 0 1)
   (setq typedvars (print-tm (second tml) 'else typedvars))
   (ptoken " | ")             ; vertical bar
   (pbreak 0 1)
   (setq typedvars (print-tm (third tml) 'else typedvars))
   (ptoken |)|)
   typedvars)


;;; print a long combination (f x1 ... xn)
;;; Copied from f-writol.l and modified by RJB 16.11.92
(defun print-listcomb (tml typedvars)
   (let ((y (pop tml)) (prev nil))
      (setq typedvars (print-tm y 'ratorofcomb typedvars))
      (while tml
         (setq prev y) (setq y (pop tml))
         (if (and(memq (term-class prev) '(var const))
               (memq (term-class y)    '(var const)))
            (ptoken | |))  ; space between two identifiers
         (pbreak 0 0)
         (setq typedvars (print-tm y 'listcomb typedvars)))
      typedvars))


;;; (is-special-comb tm '(tok1 tok2 ...)) checks that tm has the form "F t"
;;; where "F" is a constant.

(defun is-special-comb (tm tokl)
   (and (is-comb tm)
      (let ((rator (get-rator tm)))
         (and (is-const rator)
            (memq (get-const-name rator) tokl)))))


;;; MJCG 27/10/88 for HOL88
;;; replace a name by its interface-print property (if it exists)
(defmacro get-print-name (name)
   `(or (get ,name 'interface-print) ,name))

;;; MJCG 27/10/88 for HOL88
;;; (prep-ol-quant "Q" "\x.t" ty) --> (quant 'Q "x" "t")
;;; Modified to use get-print-name
;;; MJCG 3/2/88 for HOL88
;;; Modified to handle uncurried functions

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

;;; MJCG 24/1/91
;;; (prep-ol-restrict "Q P" "\x.t" ty) --> (restrict 'Q "P" "x" "t")

(defun prep-ol-restrict (t1 t2 ty)
   (and (is-comb t1)
        (is-const (get-rator t1))
        (get (get-print-name(get-const-name(get-rator t1))) 'unrestrict)
        (or (and (is-abs t2)
                 (list
                  'restrict
                  (get (get-const-name (get-rator t1)) 'unrestrict)
                  (prep-tm (get-rand t1))
                  (prep-tm(get-abs-var t2))
                  (prep-tm(get-abs-body t2))))
            (and (is-special-comb t2 '(UNCURRY))
                 (let ((p (dest-uncurry t2)))
                   (and p
                       (list
                        'restrict
                        (get (get-const-name(get-rator t1)) 'unrestrict)
                        (prep-tm (get-rand t1))
                        (prep-tm (car p))
                        (prep-tm (cdr p)))))))))


(setq hol-unops  '(|~|))
(setq hol-binops '(/\\ \\/ |==>| |=| |,|))
(setq binders    '(\\ |!| |?| |@|))

;;; (prep-ol-unop "F" "t" ty) --> (F t)
;;; where F is an atom and t is a term

(defun prep-ol-unop (t1 t2 ty)
   (if (and (is-const t1) (memq (get-const-name t1) hol-unops))
      (list (get-const-name t1)
         (prep-tm t2))))

;;; (prep-ol-binop "F t1" "t2" ty) --> (F t1 t2)
;;; where F is an atom and t1,t2 are terms

(defun prep-ol-binop (t1 t2 ty)
   (if (is-special-comb t1 hol-binops)
      (list (get-const-name(get-rator t1))
         (prep-tm(get-rand t1))
         (prep-tm t2))))

;;; print a formula built from a unary operator
;;; Modified by RJB 16.11.92

(defun print-ol-unop (fm typedvars)
   (case (first fm)
      (|~| (print-neg fm typedvars))))

;;; print a formula built from a binary operator
;;; suppress parentheses using right-associativity (except for =)
;;; print tuples as an inconsistent block

;;; first an ad-hoc function for printing equations
;;; MJCG 20/10/88 for HOL88
;;; modified to use pistring

;;; Modified by RJB 16.11.92

(defun print-eq (fm typedvars)
   (setq typedvars (print-tm (second fm) '|=| typedvars))
   ;;;  (ptoken | =|)              ; old code
   (ptoken | |)(pistring '|=|)
   (pbreak 1 0)
   (print-tm (third fm) '|=| typedvars))

;;; MJCG 19/10/88 for HOL88
;;; print a user-defined infix operator
;;; modified to invert interface-map
;;; Modified by RJB 16.11.92
;;; MJCG added comment on 31/01/94 for HOL88.2.02
(defun print-infixcomb (tml typedvars)
   (setq typedvars (print-tm (second tml) 'infixcomb typedvars))
   (ptoken | |)
   (pistring (get-const-name (first tml))) ;;; N.B. OK for infixed variables as
   (pbreak 1 0)                            ;;;      get-const-name = get-var-name (ugh!)
   (print-tm (third tml) 'infixcomb typedvars))  ; print-infixcomb

;;; MJCG 19/10/88 for HOL88
;;; print a binary operator
;;; modified to invert interface-map
;;; Modified by RJB 16.11.92

(defun print-ol-binop (fm typedvars)
   (let ((op (first fm)))
      (case op
         (|=| (print-eq fm typedvars))
         (t (case op
               (|,| (pibegin 0))
               (t   (pbegin 0)))
            (while (eq op (first fm))
               (setq typedvars (print-tm (second fm) op typedvars))
               (case (first fm)
                  ;;;           (|,|   (ptoken |,|)    (pbreak 0 0))
                  ;;;           (|=|   (ptoken | =|)   (pbreak 1 0))
                  ;;;           (/\\  (ptoken \ /\\)  (pbreak 1 0))
                  ;;;           (\\/  (ptoken \  \\/   (pbreak 1 0))
                  ;;;           (|==>| (ptoken | ==>|) (pbreak 1 0)))
                  (|,| (cond
                        ((and |%interface_print-flag|
                              (get '|,| 'interface-print))
                           (ptoken | |)(pistring '|,|) (pbreak 1 0))
                        (t (ptoken |,|) (pbreak 0 0))))
                  (/\\   (ptoken | |)(pistring '/\\)   (pbreak 1 0))
                  (\\/   (ptoken | |)(pistring '\\/)   (pbreak 1 0))
                  (|==>| (ptoken | |)(pistring '|==>|) (pbreak 1 0)))
               (setq fm (third fm)))
            (setq typedvars (print-tm fm op typedvars))
            (pend)
            typedvars))))

;;; MJCG 20/10/88 for HOL88
;;; modified to use pistring
;;; print a negation
;;; Modified by RJB 16.11.92

(defun print-neg (fm typedvars)
   (pistring '|~|) (print-tm (second fm) (first fm) typedvars))

;;; print Qx y z.w  instead of Qx. Qy. Qz. (where Q is a binder)
;;; this makes a big difference if the formula is broken over several lines
;;; "\" is treated as a quantifier for printing purposes

(eval-when (load)
   (putprop lam-sym t 'binder))


;;; MJCG 19/10/88 for HOL88
;;; print a quantifier
;;; modified to invert interface-map

(setq |%print_uncurry-flag| t)

;;; Modified by RJB 16.11.92

(defun print-ol-quant (fm typedvars)
   (let ((quant (second fm))
         (vars (third fm))
         (body (fourth fm)))
      (pbegin 1)
      (pistring quant)
      (if (not(memq quant binders)) (ptoken | |))
      (pibegin 0)
      (let ((boundvars (print-tm vars 'quant nil)))
         (while (and (eq (first body) 'quant) (eq (second body) quant))
            (pbreak 1 0)
            (setq boundvars
               (append (print-tm (third body) 'quant nil) boundvars))
            (setq body (fourth body)))
         (pend)
         (ptoken |.|)
         (pend)
         (pbreak 1 1)
         (let ((bodyvars (append boundvars typedvars)))
            (append (ldiff (print-tm body 'quant bodyvars) bodyvars)
               typedvars)))))

;;; MJCG 24.1.91
;;; Modified by RJB 16.11.92
(defun print-ol-restrict (fm typedvars)
   (let ((quant (second fm))
         (restrict (third fm))
         (vars (fourth fm))
         (body (fifth fm)))
      (pbegin 1)
      (pistring quant)
      (if (not(memq quant binders)) (ptoken | |))
      (pibegin 0)
      (let ((boundvars (print-tm vars 'restrict nil)))
         (while (and (eq (first body) 'restrict)
                     (eq (second body) quant)
                     (equal (third body) restrict))
            (pbreak 1 0)
            (setq boundvars
               (append (print-tm (fourth body) 'restrict nil) boundvars))
            (setq body (fifth body)))
         (pend)
         (ptoken | ::|)
         (pbreak 1 1)
         (setq typedvars (print-tm restrict 'restrict typedvars))
         (ptoken |.|)
         (pend)
         (pbreak 1 1)
         (let ((bodyvars (append boundvars typedvars)))
            (append
               (ldiff (print-tm body 'restrict bodyvars) bodyvars)
               typedvars)))))

;;; Change printing of predicate formulae to suppress HOL_ASSERT
;;; Modified by RJB 16.11.92

(defun print-pred-form (fm)
   (cond ((not (eq (get-pred-sym fm) 'HOL_ASSERT))
         (pstring (get-pred-sym fm))
         (pbreak 1 0)))
   (print-tm (get-pred-arg fm) t nil))

;;; MJCG 10.12.90 for Centaur:
;;; Flag to determine whether to pretty-print lisp
(setq |%pp_sexpr-flag| t)

;;; MJCG 10.12.90 for Centaur:
;;; Flag to determine whether to print in S-expression form
(setq |%print_sexpr-flag| nil)

;;; MJCG 10.12.90 for Centaur:
;;; Add these flags to the list of known flags
;;; MJCG 7.4.91: %pp_sexpr-flag and %print_sexpr-flag
;;; declared in f-iox-stand.l

;;; MJCG 10.12.90 for Centaur:
;;; Print function: |%pp_sexpr-flag| true causes pretty-printing, otherwise not
(defun sexpr-print (x) (if |%pp_sexpr-flag| #+franz (pp-form x)
                                          #-franz (pprint x) (princ x)))

;;; MJCG 10.12.90 for Centaur: redefined to switch on |%print_sexpr-flag|
;;; Overwrites definition in f-writol.l
;;; Modified by RJB 16.11.92
(defun ml-print_term (tm)
 (cond (|%print_sexpr-flag| (sexpr-print(reshape-tm tm)))
       (t (ptoken |"|)
          (print-tm (prep-tm tm) t nil)
          (ptoken |"|))))  ;ml-print_term

;;; RJB 1.7.92
;;; Function to print a term without quotes
(dml |print_unquoted_term| 1 ml-print_unquoted_term (|term| -> |void|))

;;; Modified by RJB 16.11.92
(defun ml-print_unquoted_term (tm)
 (cond (|%print_sexpr-flag| (sexpr-print(reshape-tm tm)))
       (t (print-tm (prep-tm tm) t nil))))

;;; MJCG 10.12.90 for Centaur:
;;; Function to convert a term value into an S-expression form that can
;;; be read by a dumb Lisp parser (essentially just add extra brackets)
(defun reshape-tm (tm)
 (cond ((is-var tm)
        `(var ,(get-var-name tm) ,(get-type tm)))
       ((is-const tm)
        `(const ,(get-const-name tm) ,(get-type tm)))
       ((is-comb tm)
        `(comb
          ,(reshape-tm(get-rator tm))
          ,(reshape-tm(get-rand tm))
          ,(get-type tm)))
       ((is-abs tm)
        `(abs
          ,(reshape-tm(get-abs-var tm))
          ,(reshape-tm(get-abs-body tm))
          ,(get-type tm)))))

;;; MJCG 10.12.90 for Centaur:
;;; Function to reshape a hypothesis or conclusion of a theorem
;;; (hypotheses and conclusions are wrapped with a HOL_ASSERT for
;;; historical LCF reasons)
(defun reshape-thm (x) (reshape-tm(cddr x)))

;;; Changes top-level printing of theorems to suppress quotes
;;; MJCG 10.12.90 for Centaur: modified to switch on |%print_sexpr-flag|
;;; TFM 92.07.08 : [DES] 8Jul92 line below installed.
;;; TFM 92.07.09 : previous change uninstalled, pending better solution.
;;; JRH 92.07.20 : better solution (from DES) put in; old code commented out

;;; (defun ml-print_thm (th)
;;;  (cond (|%print_sexpr-flag|
;;;         (sexpr-print
;;;           (list 'thm
;;;                 (mapcar (function reshape-thm) (car th))
;;;                 (reshape-thm (cdr th)))))
;;;        (t
;;;          (cond ((not(null(car th)))
;;;                 (mapc #'(lambda (x) (ptoken |.|)) (car th))
;;;             (ptoken | |)))  ;;; line below replaces this one.
;;; ;;;         (pbreak 1 2)))  ;;; allow a break if many hyps [DES] 8jul92
;;;          (pstring %turnstile)
;;;          (print-fm (prep-fm(cdr th)) t))))

(defun ml-print_thm (th)
 (cond (|%print_sexpr-flag|
        (sexpr-print
          (list 'thm
                (mapcar (function reshape-thm) (car th))
                (reshape-thm (cdr th)))))
       (t
         (cond ((not(null(car th)))
                (pibegin 0)
                (mapc #'(lambda (x) (progn (ptoken |.|) (pbreak 0 0))) (car th))
                (pend)
                (cond ((> (length(car th)) (/ %margin 5)) (pbreak 1 2))
                      (t (ptoken | |)))))
         (pstring %turnstile)
         (print-fm (prep-fm(cdr th)) t))))

;;; Printing a theorem and all its assumptions

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

(dml |print_all_thm| 1 ml-print_all_thm (|thm| -> |void|))


;;; MJCG 10.12.90 for Centaur:
;;; Flag to switch on parsing of ML parse trees
(setq |%print_parse_trees-flag| nil)

;;; MJCG 10.12.90 for Centaur:
;;; Add |%print_parse_trees-flag| to the list of known flags
;;; MJCG 7.4.91: declaration of %print_parse_trees-flag|
;;; moved to f-iox-stand.l

;;; MJCG 10.12.90 for Centaur:
;;; Holds the true parse tree (the one in %pt is sometimes wrong)
(setq %pt1 '(mk-empty))

;;; Print value, type of top-level expression
;;; HOL: modified not to print ": thm" after theorems
;;; MJCG 31/1/89 for HOL88
;;; Added test for |%print_top_types-flag|
;;; MJCG 7/2/89 for HOL88
;;; Added test for |%print_top_val-flag|
;;; MJCG 10.12.90 for Centaur: ML or S-expression form used
;;; depending on |%print_sexpr-flag|
;;; Printing of types suppressed if |%print_sexpr-flag| is nil
;;; (S-expression printing of values is handled by print functions
;;; invoked by prinml)
;;; If |%print_sexpr-flag| then
;;; sexpr-print is defined in f-writol.l
(setq |%print_top_types-flag| t)
(setq |%print_top_val-flag| t)
(defun prvalty (x ty)
   (cond
      (|%print_top_val-flag|
         (prinml x ty nil)
         (cond ((not(eq (car ty) 'mk-thmtyp))
                (pbreak 1 0)
                (cond ((and (not |%print_sexpr-flag|) |%print_top_types-flag|)
                       (ptoken |: |)
                       (printmty ty)))))
         (pnewline)
         (cond (|%print_parse_trees-flag|
                (terpri)
                (sexpr-print %pt1)
                (terpri))))))

;;; MJCG 27/10/88 for HOL88
;;; detect infixes and long combinations
;;; modified to invert interface-map
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


;;; MJCG 27/10/88 for HOL88
;;; detect infixes and long combinations
;;; see if ((tm1 tm2 ...) y) is the curried infix "tm2 <tm1> y"
;;; otherwise return (tm1 tm2 ... y)
;;; modified to invert interface-map
;;; MJCG 31/01/94 for HOL88.2.02
;;; Modified to support infixed variables
(defun prep-curr (tml y ty)
   (let ((tm1 (car tml)) (tm2 (cadr tml)) (tmtail (cddr tml)))
      (if (or (and (null tmtail) (is-const tm1) |%print_infix-flag|
                   (eq (get (get-print-name(get-const-name tm1)) 'olinfix) 'curried))
              (and (null tmtail) (is-var tm1) |%print_infix-flag|
                   (memq (get-var-name tm1) hol-var-binops)))
         (make-prep-term 'infixcomb (list tm1 tm2 y) ty)
         (make-prep-term 'listcomb (append tml (list y)) ty)
         )))                                 ;prep-curr


;;; MJCG 7/2/89 for HOL88
;;; MJCG 30/92/89 for HOL88, Ton Kalker: save |%print_lettypes-flag|
;;; Function to print currently defined types
(defun prdeftypes ()
 (prog (saved-flag)
   (setq saved-flag |%print_lettypes-flag|)
   (setq |%print_lettypes-flag| nil)
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
   (pnewline)
   (setq |%print_lettypes-flag| saved-flag)))

(dml |print_defined_types| 0 prdeftypes (|void| -> |void|))


