;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        print_hacks.l - from hol-writ.l                 ;;;
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
;;;      Gratuitously copied and modified by Donald Syme, ANU, 1992, a la Mike Gordon & proglogic88   ;;;
;;;      Changes to cope with pretty printing of finite partial functions noted  ;;;
;;;      Adds two new flags - "print_fpf"                                   ;;;
;;;                                                                         ;;;
;;;   REVISION HISTORY: (none)                                              ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "f-franz")
   (include "f-constants")
   (include "f-macro")
   (include "f-ol-rec")
   (include "genmacs")
   (special ol-lam-sym hol-unops hol-binops binders |%show_types-flag|
      |%interface_print-flag| %turnstile |%print_top_types-flag|
      |%print_list-flag| |%print_cond-flag| 
      |%print_quant-flag| |%print_restrict-flag|
      |%print_let-flag| |%print_uncurry-flag| |%print_infix-flag|
      |%print_lettypes-flag| |%print_top_val-flag|  |%print_set-flag|
      |%empty-set| |%finite-set-constructor| |%set-abstraction-constructor|
; =============== Added to support finite partial functions ===============
            |%print_fpf-flag| rator %flags
; =====================================================================
      |%pp_sexpr-flag| |%print_sexpr-flag| %pt1 |%print_parse_trees-flag|))




; =============== Added to support finite partial functions ===============
(eval-when (load)
   (setq %flags (cons '|%print_fpf-flag| %flags))
   (setq |%print_fpf-flag| t))


(defmacro null-ol-fpf (tm)
   `(and (is-const ,tm) (eq (get-const-name ,tm) '|ZIP|)))
 
(defmacro dom-hd-ol-fpf (tm)
   `(get-rand (get-rator (get-rand (get-rator ,tm)))))
 
(defmacro ran-hd-ol-fpf (tm)
   `(get-rand (get-rand (get-rator ,tm))))

(defmacro tl-ol-fpf (tm)
   `(get-rand ,tm))
 
(defmacro get-ol-fpf-type (tm)
   `(first (get-type-args (get-type ,tm))))


; =====================================================================


#+franz
(declare
   (localf prep-ol-let
      print-ol-let
      pre-prep-ol-list
      prep-ol-list
      print-ol-list
      pre-prep-ol-finite-set
      prep-ol-finite-set
      print-ol-finite-set
; =============== Added to support finite partial functions ===============
      pre-prep-ol-finite-fpf
      prep-ol-finite-fpf
      print-ol-finite-fpf
; =====================================================================
      prep-ol-set-abstraction
      print-ol-set-abstraction
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

;;; If T1 is a 'closes property of T2 then brackets will be put around
;;; T1 when it is printed in the context of T2

(eval-when (load)
   (mapc
      #'(lambda (x) (putprop (car x) (cdr x) 'closes))
      '((|~| . (quant restrict /\\ \\/ |==>| |<=>| |,| |=|))
         (/\\ . (quant restrict /\\ \\/ |==>| |<=>| |,| |=|))
         (\\/ . (quant restrict \\/ |==>| |<=>| |,| |=|))
         (|==>| . (quant restrict |==>| |<=>| |,| |=|))
         (|<=>| . (quant restrict |<=>| |,| |=|))
         (|,| . (quant restrict |,| /\\ \\/ |==>| |<=>| ol-let |=|))
         (|=| . (quant restrict ol-let |=|))
         (then . (quant restrict then |=| /\\ \\/ |~| |==>| |<=>|))
         (else . (quant restrict then |,| |=| /\\ \\/ |==>| |<=>|))
         (listcomb . (quant restrict listcomb infixcomb then 
                      |,| typed ol-let |=| /\\ \\/ ==> <=>))
         (infixcomb . (quant restrict listcomb infixcomb then 
                       |,| typed ol-let |=| /\\ \\/ ==> <=>))
         (varstruct . (|,|))
         (let-rhs . (|=|))
         (let-body . (quant restrict  |=| /\\ \\/ |~| |==>| |<=>|))
         (typed . (infixcomb))
         (fun . (fun))
         (sum . (sum fun))
         (prod . (prod sum fun))
         (quant . (|,| typed))
         (restrict . (|,| typed))
         (fin-set . (|,|))
         (set-abs1 . (|,|))
         (eqn-rhs . (quant restrict listcomb infixcomb then |,| typed))
)))


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
; =============== Added to support finite partial functions ===============
                   ((and |%print_fpf-flag| (eq (get-const-name tm) '|ZIP|))
                    `(ol-finite-fpf . (nil . ,(get-ol-fpf-type tm))))
; =====================================================================
                   ((and |%print_list-flag| (eq (get-const-name tm) 'NIL))
                    `(ol-list . (nil . ,(get-ol-list-type tm))))
                   (t tm)))
      (abs (list 'quant ol-lam-sym (get-abs-var tm) (prep-tm (get-abs-body tm))))
      (comb (let ((rator (get-rator tm))
               (rand (get-rand tm))
               (ty (get-type tm)))
            (or (and |%print_set-flag|     (prep-ol-finite-set tm))
                (and |%print_fpf-flag|     (prep-ol-finite-fpf tm))
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
                  (cond (print-cond tml needty))
                  (listcomb (print-listcomb tml pcrator))
                  (infixcomb (print-infixcomb tml pcrator))
                  (restrict (print-ol-restrict tm))
                  (quant (print-ol-quant tm))
                  (|~| (print-ol-unop tm))
                  ((|=| /\\ \\/ |==>| |<=>| |,|) (print-ol-binop tm))
                  (ol-let (print-ol-let tm))
                  (ol-list (print-ol-list tm))
                  (ol-finite-set (print-ol-finite-set tm))
; =============== Added to support finite partial functions ===============
                  (ol-finite-fpf (print-ol-finite-fpf tm))
; =====================================================================
                  (ol-set-abstraction (print-ol-set-abstraction tml))
                  (t (lcferror "print-tm")))
               (cond (tyflag            ; print type
                     (if cl2 (ptoken |)|)
                        (ifn (memq op2 '(var const)) (ptoken | |)))
                     (pbreak 0 0)
                     (ptoken |:|) (print-ty ty t)))
               (if cl1 (ptoken |)|))
               (pend)))))) 

;;; MJCG 20/10/88 for HOL88
;;; string printing function that inverts interface
(defun pistring (str)
   (pstring (or (and |%interface_print-flag| (get str 'interface-print))
         str)))

;;; MJCG 19/10/88 for HOL88
;;; print a constant (may be a prefix, infix or binder standing alone)
;;; modified to invert interface-map
; =============== Modified to support programming language ===============
(defun print-const (name op1)
 (cond ((or (get name 'olinfix)
            (get name 'prefix)
            (get name 'binder))
        (ptoken |$|)))
    (pistring name)
 )
)
; =====================================================================

;;; MJCG 3/2/89 for HOL88
;;; Function for stripping of the varstructs of a function
;;; "\v1 v2 ... vn. t"  --> ((v1 v2 ... vn) . t)
;;; "t"                 --> (nil . t)  -- t not a function
;;; (vi either a variable or a varstruct)

(defun strip-abs (tm)
   (or (and (is-abs tm)
         (let ((p (strip-abs(get-abs-body tm))))
            (cons (cons (get-abs-var tm) (car p)) (cdr p))))
      (and (is-special-comb tm '(UNCURRY))
         (let* ((p (dest-uncurry tm))
               (q (strip-abs (cdr p))))
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

(defun prep-ol-let (tm)
   (and (is-comb tm)
      (is-special-comb (get-rator tm) `(LET))
      (let* ((tms    (strip-let tm))
            (args   (cdr tms))                 ; (u1 ... un) 
            (p      (strip-abs(car tms)))
            (params (car p))                   ; (x1 ... xn)
            (body   (cdr p)))                  ; tm
         (and (= (length params) (length args))
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

;;; MJCG 3/2/89 for HOL88
;;; Printing of let bindings
;;;    ((x) . u) --> x = u
;;; 
;;;    ((f v1 ... vn) . u) --> f v1 ... vn = u

(defun print-ol-bnd (b)
   (pibegin 0)
   (print-tm (caar b) 'varstruct nil)
   (pbreak 0 0)
   (mapc 
      (function
         (lambda (y) (ptoken | |) (pbreak 0 1) (print-tm y 'varstruct nil)))
      (cdar b))
   (ptoken | = |)
   (pbreak 0 2)
   (print-tm (cdr b) 'let-rhs nil)
   (pend))

;;; MJCG 3/2/89 for HOL88
;;; Modified printing of let-terms
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
      (print-tm body 'let-body nil)
      (pend)))

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

(defun print-ol-finite-set (tm)
   (let ((termlist (get-term-list tm)))
      (pibegin 1)
      (ptoken |{|)
      (cond (termlist
             (print-tm (car termlist) 'fin-set nil)
             (mapc 
               #'(lambda (y) (ptoken |,|) 
                             (pbreak 0 0)
                             (print-tm y 'fin-set nil))
               (cdr termlist))))
      (ptoken |}|)
      (pend)))


; =============== Added to support finite partial functions ===============




;;; code for printing "{d |-> r, ... ,d |-> r}"
;;; Duplicates code for lists -- would be more space-efficientr to fold fpf, list and set
;;; printing code into one set of routines.

(defun is-ol-fpf-cons (tm)
   (and (is-comb tm)
      (let ((rator (get-rator tm)))
         (and (is-comb rator)
            (is-const (get-rator rator))
            (eq (get-const-name(get-rator rator)) '|EXT|)))))

(defun is-ol-finite-fpf (tm)
   (or (null-ol-fpf tm)
      (and (is-ol-fpf-cons tm)
         (is-ol-finite-fpf(tl-ol-fpf tm)))))

;;; pre-prep-ol-finite-fpf gets a list of the elements of an OL value 
;;; representing a finite fpf
;;; - e.g EXT (a,b) (EXT (c,d) ZIP) -> ((a,b) (c,d))

(defun pre-prep-ol-finite-fpf (tm)
   (cond ((null-ol-fpf tm) nil)
      (t (cons (cons (prep-tm (dom-hd-ol-fpf tm)) (prep-tm (ran-hd-ol-fpf tm)) )
               (pre-prep-ol-finite-fpf (tl-ol-fpf tm))))))

(defun prep-ol-finite-fpf (tm)
   (if (is-ol-finite-fpf tm) 
      (make-prep-term 'ol-finite-fpf 
         (pre-prep-ol-finite-fpf tm)
         (get-ol-fpf-type tm))))

(defun print-ol-finite-fpf (tm)
   (let ((termlist (get-term-list tm)))
      (pibegin 1)
      (ptoken |{|)
      (cond (termlist
             (print-tm (car (car termlist)) 'fin-fpf nil)
             (ptoken " |-> ")
             (print-tm (cdr (car termlist)) 'fin-fpf nil)
             (mapc 
               #'(lambda (y) (ptoken |, |) 
                             (pbreak 0 0)
                             (print-tm (car y) 'fin-fpf nil)
                             (ptoken " |-> ")
                             (print-tm (cdr y) 'fin-fpf nil))
               (cdr termlist))))
      (ptoken |}|)
      (pend)))





; =====================================================================


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

(defun print-ol-set-abstraction (tml)
   (ptoken |{|)
   (print-tm (first tml) 'set-abs1 nil)
   (ptoken | \| |)
   (pbreak 0 1)
   (print-tm (second tml) 'set-abs2 nil)
   (ptoken |}|))

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

(defun print-cond (tml needty)
   (ptoken |(|)
   (print-tm (first tml) 'then nil)
   (ptoken | => |)
   (pbreak 0 1)
   (print-tm (second tml) 'else nil)
   (ptoken " | ")             ; vertical bar
   (pbreak 0 1)
   (print-tm (third tml) 'else needty)
   (ptoken |)|))
   
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
(setq hol-binops '(/\\ \\/ |==>| |=| |<=>| |,|))
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

(defun print-ol-unop (fm)
   (case (first fm)
      (|~| (print-neg fm))))

;;; print a formula built from a binary operator
;;; suppress parentheses using right-associativity (except for =)
;;; print tuples as an inconsistent block

;;; first an ad-hoc function for printing equations
;;; MJCG 20/10/88 for HOL88
;;; modified to use pistring

(defun print-eq (fm)
   (print-tm (second fm) '|=| nil)
   ;;;  (ptoken | =|)              ; old code
   (ptoken | |)(pistring '|=|)
   (pbreak 1 0)
   (print-tm (third fm) '|=| nil))

;;; MJCG 19/10/88 for HOL88
;;; print a user-defined infix operator
;;; modified to invert interface-map
(defun print-infixcomb (tml pcrator)
   (print-tm (second tml) 'infixcomb pcrator)
   (ptoken | |)
   (pistring (get-const-name (first tml)))
   (pbreak 1 0)
   (print-tm (third tml) 'infixcomb pcrator))  ; print-infixcomb

;;; MJCG 19/10/88 for HOL88
;;; print a binary operator
;;; modified to invert interface-map

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
                  ;;;           (|,|   (ptoken |,|)    (pbreak 0 0))
                  ;;;           (|=|   (ptoken | =|)   (pbreak 1 0))
                  ;;;           (/\\  (ptoken \ /\\)  (pbreak 1 0))
                  ;;;           (\\/  (ptoken \  \\/   (pbreak 1 0))
                  ;;;           (|==>| (ptoken | ==>|) (pbreak 1 0))
                  ;;;           (|<=>| (ptoken | <=>|) (pbreak 1 0)))
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
   
;;; MJCG 20/10/88 for HOL88
;;; modified to use pistring
;;; print a negation

(defun print-neg (fm) (pistring '|~|) (print-tm (second fm) (first fm) t))

;;; print Qx y z.w  instead of Qx. Qy. Qz. (where Q is a binder)
;;; this makes a big difference if the formula is broken over several lines
;;; "\" is treated as a quantifier for printing purposes

(eval-when (load)
   (putprop lam-sym t 'binder))


;;; MJCG 19/10/88 for HOL88
;;; print a quantifier
;;; modified to invert interface-map

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

;;; MJCG 24.1.91
(defun print-ol-restrict (fm)
   (let ((quant (second fm))
         (restrict (third fm))
         (vars (fourth fm))
         (body (fifth fm)))
      (pbegin 1)
      (pistring quant)
      (if (not(memq quant binders)) (ptoken | |))
      (pibegin 0)
      (print-tm vars 'restrict t)
      (while (and (eq (first body) 'restrict) 
                  (eq (second body) quant)
                  (equal (third body) restrict))
         (pbreak 1 0)
         (print-tm (fourth body) 'restrict t)
         (setq body (fifth body)))
      (pend)
      (ptoken | ::|)
      (pbreak 1 1)
      (print-tm restrict 'restrict t)
      (ptoken |.|)
      (pend)
      (pbreak 1 1)
      (print-tm body 'restrict t)))

;;; Change printing of predicate formulae to suppress HOL_ASSERT

(defun print-pred-form (fm)
   (cond ((not (eq (get-pred-sym fm) 'HOL_ASSERT))
         (pstring (get-pred-sym fm))
         (pbreak 1 0)))
   (print-tm (get-pred-arg fm) t t))

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
;;; Overwrties definition in f-writol.l
(defun ml-print_term (tm)
 (cond (|%print_sexpr-flag| (sexpr-print(reshape-tm tm)))
       (t (ptoken |"|)
          (print-tm (prep-tm tm) t t)
          (ptoken |"|))))  ;ml-print_term

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
(defun ml-print_thm (th)
 (cond (|%print_sexpr-flag|
        (sexpr-print 
          (list 'thm 
                (mapcar (function reshape-thm) (car th))
                (reshape-thm (cdr th)))))
       (t
         (cond ((not(null(car th)))
                (mapc #'(lambda (x) (ptoken |.|)) (car th))
                (ptoken | |)))
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
(defun prep-curr (tml y ty)
   (let ((tm1 (car tml)) (tm2 (cadr tml)) (tmtail (cddr tml)))
      (if (and (null tmtail) (is-const tm1) |%print_infix-flag|
            (eq (get (get-print-name(get-const-name tm1)) 'olinfix) 'curried))
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



