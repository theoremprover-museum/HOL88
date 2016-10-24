;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-tran.l                                            ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Translate ML to lisp                                ;;;
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
;;;   REVISION HISTORY: Original code: tran  (lisp 1.6) part of Edinburgh   ;;;
;;;                     LCF by M. Gordon, R. Milner and C. Wadsworth (1978) ;;;
;;;                     Transported by G. Huet in Maclisp on Multics, Fall  ;;;
;;;                     1981                                                ;;;
;;;                                                                         ;;;
;;;                     V2.2 :throw instead of err                          ;;;
;;;                                                                         ;;;
;;;                     V3.1 Unix -- Made MK-ABSTR generate defun's instead ;;;
;;;                         of embedded lambdas                             ;;;
;;;                                                                         ;;;
;;;                     V4-4 Optimization of code transferred from F-tml.   ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Specials for compiling tran:  %p, %loop, %test
;;; Specials for compiling tran-output:  %e

;;; Sets manifests:  isomclosure, isom, dummy, empty, tzero

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (*lexpr concat))

#+franz
(declare
   (localf translation-failed
      nfirst
      access_code
      access_path
      upd_ap
      rap
      access
      stor
      copyst
      copys
      storst
      bvpat
      varpat
      trex
      trin
      tr-match
      combinetree
      lispfunpat
      chkvarstr
      chkvarstrx
      inserttransfun
      mkclosure
      lispfunclosure
      lispargs
      fastap
      genloop
      isloop
      trarms
      trtrap
      qreturn
      trlast
      testeval
      trb
      trabstyb
      isompat
      make-cond-case
      gencheck
      gencheckl
      checkst
      checks
      checks2
      checksl
      trdecl
      optimize-code
      optimize-ap
      trans-sexpr
      build-lb))


;;; translation tables for OL parse trees

;;; phyla for which all subtrees must be translated (via trq)

(eval-when (compile load eval)
   (defconstant %q-trans-args
      '(                                   ; term constructors
         (MK=TYPED . q-mk_typed)   
         (MK=ABS . q-mk_abs)
         (MK=COMB . q-mk_comb)
         (MK=PAIR . q-mk_pair)
         (MK=COND . q-mk_cond)
         ; formula constructors
         (MK=EQUIV . q-mk_equiv)
         (MK=INEQUIV . q-mk_inequiv)
         (MK=NEG . q-mk_neg)
         (MK=CONJ . q-mk_conj)
         (MK=DISJ . q-mk_disj)
         (MK=IMP . q-mk_imp)
;;;      (MK=IFF . q-mk_iff)           DELETED [TFM 90.01.20]
         (MK=FORALL . q-mk_forall)
         (MK=EXISTS . q-mk_exists))))

;;; phyla for which the one subtree must be quoted

(eval-when (compile load eval)
   (defconstant %q-quote-arg
      '((MK=VAR . q-mk_var)
         (MK=CONST . q-mk_const)
         (MK=VARTYPE . q-mk_vartype))))

(eval-when (compile load eval)
   (defconstant isomclosure (cons 'car 'isomclosure))      ;new 
   (defconstant isom '%isom)
   (defconstant rec '%rec)
   (defconstant ord '%ord)
   (defconstant dummy '%dummy))


;;; Franz compiler cannot compile the catch-throw and throw-from macros
;;; properly when making lisp object code from ML since it does not
;;; know about them. So macroexpand into *catch and *throw for it.

(defun make-catch-form (x)
   #+franz `(*catch 'evaluation ,x)
   #-franz `(catch 'evaluation ,x))

(defun make-throw-form (x)
   #+franz `(*throw 'evaluation ,x)
   #-franz `(throw 'evaluation ,x))


(defun make-lambda-binding (var val &rest forms)
   #+franz `((lambda (,var) ,@forms) ,val)
   #-franz `(let ((,var ,val)) ,@forms))


(defun remember-tran-function (name arglist body-forms)
   (push
      `(defun ,name ,arglist
          #-franz (declare (optimize (speed 2) (safety 0)))
          ,@body-forms)
      %compfns))


;;; For translation error messages
(defun translation-failed (msg)
   (llprinc msg)
   (llterpri)
   (throw-from translation nil))  ;translation-failed 


;;; Get the global Lisp binding of the ml identifier i
;;; returns nil if undeclared
(defun get-lisp-binding (i)
   (or (assq1 i rec%env) (assq1 i global%env)))

(defun nfirst (l n)
   (if (zerop n) nil
      (cons (car l) (nfirst (cdr l) (- n 1)))))

(defun access_code (l)
   (if (null l) '%e
      (if (< (length l) 5)
         `(,(concatl `(c ,@l r)) %e)
         `(,(concatl `(c ,@(nfirst l 4) r)) ,(access_code (cddddr l))))))

(defun access_path (i rho)
   (let ((tac nil))
      (ifn (null rho)
         (cond
            ((atom (car rho))
               (cond
                  ((equal (car rho) i) (cons ord '(a)))
                  ((equal (car rho) isom) (if (memq i (cdr rho))
                        (list isom)))
                  ((equal (car rho) rec) (if (setq tac (rap i (cdr rho)))
                        `(,rec . ,tac)))
                  ((atom (cdr rho)) (if (equal (cdr rho) i)
                        (cons ord '(d))))
                  ((setq tac (access_path i (cdr rho))) (upd_ap tac 'd))))
            ((setq tac (access_path i (car rho))) 
               (upd_ap tac 'a))
            ((atom (cdr rho)) (if (equal (cdr rho) i)
                  (cons ord '(d))))
            ((setq tac (access_path i (cdr rho)))
               (upd_ap tac 'd))))))             ;access_path

(defun upd_ap (path move)
   (cond
      ((eq (car path) isom) path)
      ((eq (car path) rec) (rplacd (cdr path) (cons move (cddr path))) path)
      ((eq (car path) ord) (rplacd path (cons move (cdr path))))))

(defun rap (i rho)
   (let ((tac nil))
      (cond
         ((atom (car rho)) (if (equal (car rho) i) (cons (cdr rho) nil)))
         ((atom (caar rho)) 
            (cond
               ((equal (caar rho) i)
                  (cons (cdar rho) '(a)))
               ((atom (cadr rho) )
                  (if (equal (cadr rho) i) (cons (cddr rho) '(d))))
               ((setq tac (rap i (cdr rho))) 
                  (rplacd tac (cons 'd (cdr tac))))))
         ((setq tac (rap i (car rho))) 
            (rplacd tac (cons 'ad (cdr tac))))
         ((atom (cadr rho))
            (if (equal (cadr rho) i) (cons (cddr rho) '(d))))
         ((setq tac (rap i (cdr rho))) 
            (rplacd tac (cons 'd (cdr tac)))))))        ;rap

(defun access (i)
   (let ((path (access_path i %p)))
      (ifn (null path)
         (cond
            ((eq (car path) isom) path)
            ((eq (car path) ord)
               (cons (car path) 
                  (access_code (reverse (cdr path)))))
            ((eq (car path) rec)
               (cons (car path)
                  (cons (cadr path)
                     (access_code (reverse (cddr path)))))))))) ;access

(defun stor (i rhs)
   (let ((path (access_path i %p)))
      (ifn (null path)
         (let ((ipath (reverse (cdr path))))
            `(,(concatl `(r p l a c ,(car ipath)))
               ,(access_code (cdr ipath))
               ,rhs)))))                        ;stor

(defun copyst (s e)
   (cond ((atom s) e)
      ((and (not (atom e))
            (not (atom (cdr e)))
            (memq (car e) '(cons list)))
         (list 'cons (copyst (car s) (cadr e))
            (copyst (cdr s) (cond
                  ((eq (car e) 'cons) (caddr e))
                  (t (cons 'list (cddr e)))))))
      (t (make-lambda-binding 'a e (copys s 'a))))) ;copyst

(defun copys (s ans)
   (cond ((atom s) ans)
      (t (list 'cons (copys (car s) (list 'car ans))
            (copys (cdr s) (list 'cdr ans))))))

;;; Splits up pattern of letref and assigns to its parts
;;; Top-level letrefs are assigned using "setq", others via code from "stor"
(defun storst (s arg)
   (cond
      ((or (eq s empty) (eq s nill)) nil)
      ((atom s) (cond ((stor s arg))
            ((let 
                ((lb (get-lisp-binding s)))
                (if lb 
                   #+franz `(setq ,lb ,arg)
                   #-franz `(setf (symbol-value ',lb) ,arg)
                   nil)))
            (t (lcferror '|no variable in translation of := |))))
      (t (if (eq (car s) '%con) (storst (cdr s) `(cdr ,arg))
            (list 'prog2
               (storst (car s) (list 'car arg))
               (storst (cdr s) (list 'cdr arg)))))))    ;storst

(defun bvpat (d)
   (varpat (cadr (if (memq (car d) '(mk-abstype mk-absrectype))
            (caddr d)
            d))))                       ;bvpat

;;; Experimental bugfix for top-level wildcards
;;; MJCG 21/10/90 for HOL88.1.12
;;; MJCG 25/10/90 for HOL88.1.12

(defun varpat (s)
   (case (car s)                                
;;;   (mk-empty empty)
      ((mk-empty mk-wildcard) empty)
      (mk-var (cadr s))
      (mk-straint (varpat (cadr s)))
;;;   (mk-wildcard '(%wild))
      (mk-con0 '(%con))
      (mk-appn (cons '%con (varpat (caddr s))))
      ((mk-intconst mk-boolconst mk-tokconst) '%const)
      (mk-dupl (cons (varpat (cadr s)) (varpat (caddr s))))
      (mk-binop (cons (varpat (caddr s)) (varpat (cadddr s))))
      (mk-list (nconc (mapcar (function varpat) (cdr s)) nill))
      (t 
         (translation-failed "bad variable structure"))))       ;varpat

;;; call tre, pushing new layer of environment
(defun trex (new%p e)
   (let ((%p (cons new%p %p)))  (tre e)))       ;trex

;;; Translate expression
;;; Bugfix: ap changed to %ap
;;; MJCG 10 Nov 1990 for HOL88.1.12
(defun tre (e)
   (case (car e)
      ((mk-boolconst mk-intconst) (cadr e))
      (mk-tokconst (qeval (cadr e)))
      (mk-quot
         (list 'qtrap
            (make-catch-form
               (make-lambda-binding '%vtyl nil
                  `(quotation ,(trq (cadr e)))))))
      (mk-tyquot
         (list 'qtrap
            (make-catch-form `(list ,(trq (cadr e))))))
      (mk-var (let ((acfn (access (cadr e))))
            (cond  ((eq (car acfn) isom) 'isomclosure)
               ((eq (car acfn) ord) (cdr acfn))
               ((eq (car acfn) rec) (cddr acfn))
               ((get-lisp-binding (cadr e))    ; global variable
                  (let ((var (get-lisp-binding (cadr e))))
                     #+franz var
                     #-franz `(symbol-value ',var)
                     ))
               ((primval (cadr e)))     ; predefined constant dml/dmlc
               )))
      (mk-con (tre `(mk-abstr (mk-var x) (mk-appn ,e (mk-var x)))))
      (mk-con0 `(quote ,(cadr e)))
      (mk-fail
         (make-throw-form (list 'quote '|fail|)))  ;new look
      (mk-failwith
         (make-throw-form (tre (cadr e))))        ;new look
      (mk-empty nil)
      (mk-dupl (testeval `(cons ,(tre (cadr e)) ,(tre (caddr e)))))
      (mk-list (testeval (cons 'list (mapcar (function tre) (cdr e)))))
      (mk-straint (tre (cadr e)))
      (mk-appn (cond
            ((eq (caadr e) 'mk-con)
               ;; application of constructor is special case
               `(cons (quote ,(cadadr e)) ,(tre (caddr e))))
            ((eq (caadr e) 'mk-var)
               ;; application of variable is special case
               (let ((acfn (access (cadadr e))) (arg (tre (caddr e))))
                  (cond ((eq (car acfn) isom) arg)
                     ((eq (car acfn) ord)  `(%ap ,(cdr acfn) ,arg))
                     ((eq (car acfn) rec)  `(,(cadr acfn) 
                           (cons ,arg (cdr ,(cddr acfn)))))
                     ((let
                         ((lb (get-lisp-binding (cadadr e))))
                         (if lb
                            #+franz `(%ap ,lb ,arg)
                            #-franz `(%ap (symbol-value ',lb) ,arg)
                            nil)))
                     ((fastap (cadadr e) arg))
                     (`(%ap ,(primval(cadadr e)) ,arg)))))
            (`(%ap ,(tre (cadr e)) ,(tre (caddr e))))))
      (mk-binop (tre `(mk-appn (mk-var ,(cadr e))
               (mk-dupl . ,(cddr e)))))
      (mk-unop (tre `(mk-appn . ((mk-var ,(cadr e)). ,(cddr e)))))
      (mk-seq
         `(cond (t .
               ,(nconc (mapcar (function tre) (cadr e))
                  (list (tre (caddr e)))))))
      (mk-assign
         (chkvarstr (cadr e)
            '|multiple occurrence of a variable in left-hand side of assignment|
            '|application of a non-constructor in left-hand side of assignment|)
         (make-lambda-binding 'a (checkst (cadr e) (tre (caddr e)))
            (storst (varpat (cadr e)) 'a)
            'a))
      (mk-while
         `(prog () $etiq$
            (cond
               (,(tre (cadr e)) ,(tre (caddr e)) (go $etiq$))
               (t (return nil)))))
      (mk-test
         (let ((%loop (genloop (cdr e))))
            (let ((a (trarms t (cdr e))))
               (cond (%loop (list 'prog nil (cadr %loop) a)) (t a)))))
      (mk-case
         (make-lambda-binding '%e `(cons ,(tre (cadr e)) %e)
            (tr-match (caddr e))))
      (mk-trap
         (let ((%loop (genloop (cddr e))))
            (let
               ((e0
                   (make-catch-form `(list ,(tre (cadr e)))))
                (a (trarms nil (cddr e))))
               (if %loop
                  (list 'prog '(b) (cadr %loop) (list 'setq 'b e0) a)
                  (make-lambda-binding 'b e0 a)))))
      (mk-fun
         (let ((checkbody (tr-match (cadr e)))
               (newfun
                  (if (null (cddr e))
                     (uniquesym 'FUN %timestamp)
                     (caddr e))))
            ;; store away as function to evaluate later
            (remember-tran-function newfun '(%e) (list checkbody))
            ;; store curry binding, if any, for optimization
            (eval-remember
               `(putprop (quote ,newfun)
                   (quote ,(currybind checkbody))
                   'currybind))
            ;; must use "quote" instead of "function"
            ;; to avoid binary bindings or expansion of function bodies
            ;; in compiled code, especially to allow optimization of function
            ;; calls
            `(cons (quote ,newfun) %e)))
      (mk-abstr
         (chkvarstr (cadr e)
            '|multiple occurrence of a variable in an abstraction|
            '|misplaced constructor in abstraction|)
         (let ((cl (checks (cadr e) '(car %e)))
               (body (trex (varpat (cadr e)) (caddr e))))
            (let ((checkbody (gencheck cl body))
                  (newfun
                     (if (null (cdddr e))
                        (uniquesym 'FUN %timestamp)
                        (cadddr e))))
               ;; store away as function to evaluate later
               (remember-tran-function newfun '(%e) (list checkbody))
               ;; store curry binding, if any, for optimization
               (eval-remember
                  `(putprop ',newfun
                      ',(currybind checkbody)
                      'currybind))
               ;; must use "quote" instead of "function"
               ;; to avoid binary bindings or expansion of function bodies
               ;; in compiled code, especially to allow optimization of function
               ;; calls
               `(cons (quote ,newfun) %e))))
      ((mk-in mk-ina) (trin (cadr e) (caddr e)))
      (mk-ind (tre (caddr e)))
      (t (lcferror (cons e '(bad arg tre))))))  ;tre


(defun trin (decl exp)
   (if (eq (car decl) 'mk-letrec)
      (let ((bvs (bvpat decl)))
         (let ((lispfuns (lispfunpat bvs)))
            `(let
                ((%e
                   ,(let
                       ((body
                          (trex (cons rec (combinetree bvs lispfuns))
                             (inserttransfun (caddr decl) lispfuns))))
                       `(let ((%e (cons nil %e)))
                           (rplaca %e ,body)))))
                ,(trex (cons rec (combinetree bvs lispfuns)) exp))))
      `(let ((%e ,(trdecl decl)))
          ,(trex (bvpat decl) exp)))
   );trin

(defun tr-match (funcase-list)
   (gencheckl
      (mapcar
         #'(lambda (funcase)
            (chkvarstr (car funcase)
               '|multiple occurrence of a variable in a pattern|
               '|misplaced constructor in pattern|)
            (cons (checks (car funcase) '(car %e))
               (trex (varpat (car funcase)) (cdr funcase))))
         funcase-list)))

(defun combinetree (t1 t2)
   (ifn (null t1)
      (if (atom t1) (cons t1 t2)
         (cons (combinetree (car t1) (car t2))
            (combinetree (cdr t1) (cdr t2)))))) 

(defun lispfunpat (pat)
   (ifn (null pat)
      (if (atom pat) (uniquesym 'FUN %timestamp)
         (cons (lispfunpat (car pat)) (lispfunpat (cdr pat))))))

(defun chkvarstr (x msg1 msg2)
   (chkvarstrx x nil msg1 msg2) x)              ;chkvarstr

;;; accumulate checks in the idlst
(defun chkvarstrx (x idlst msg1 msg2)
   (case (car x)
      (mk-straint (chkvarstrx (cadr x) idlst msg1 msg2))
      (mk-var
         (ifn (memq (cadr x) idlst)
            (cons (cadr x) idlst)
            (translation-failed msg1)))
      (mk-appn
         (if (eq (caadr x) 'mk-con)
            (chkvarstrx (caddr x) idlst msg1 msg2)
            (translation-failed msg2)))
      (mk-dupl
         (chkvarstrx (caddr x) (chkvarstrx (cadr x) idlst msg1 msg2) msg1 msg2))
      ((mk-wildcard mk-empty mk-con0 mk-intconst mk-boolconst mk-tokconst) idlst)
      (mk-con (translation-failed msg2))
      (mk-list
         (itlist (function (lambda (x idlst) (chkvarstrx x idlst msg1 msg2)))
            (cdr x) idlst))
      (t (if (and (eq (car x) 'mk-binop) (eq (cadr x) '|.|))
            (chkvarstrx (cadddr x)
               (chkvarstrx (caddr x) idlst msg1 msg2) msg1 msg2)
            (translation-failed msg2)))))               ;chkvarstrx

(defun inserttransfun (e funpat)
   (case (car e)
      ((mk-abstr mk-fun)  `(,@e ,funpat))
      (mk-dupl
         `(mk-dupl
            ,(inserttransfun (cadr e) (car funpat))
            ,(inserttransfun (caddr e) (cdr funpat))))
      (mk-straint (inserttransfun (cadr e) funpat))
      (t (translation-failed "bad use of letrec"))))    ; inserttransfun

;;; primitive value from dml, dmlc, or "it"
(defun primval (i)
   (cond
      ((null i) nil)                 ;new code for nil
      ((get i 'numargs) (qeval (mkclosure i)))
      ((get i 'mltype) `(get ',i 'mlval))       ;NEW -- "it" is now restricted
      (t (lcferror 'primval))))           ;primval

(defun mkclosure (i)
   (cond
      ((get i 'closure))
      (t (putprop i (lispfunclosure i) 'closure))))       ;mkclosure

(defun lispfunclosure (i)
   (let ((in (get i 'numargs)))
      (cons
         `(lambda (%e) ,(cons (car in) (lispargs (cdr in) '(car %e))))
         i)
      ))					;lispfunclosure

(defun lispargs (n a)
   (cond ((zerop n) nil)
      ((= n 1) (list a))
      (t (cons (list 'car a) (lispargs (sub1 n) (list 'cdr a))))))      ;lispargs

;;; apply an ML function to its arguments
;;; called in generated code    
;;; Bugfix: ap changed to %ap
;;; MJCG 10 Nov 1990 for HOL88.1.12
(defun %ap (fn arg)
   (funcall (car fn) (cons arg (cdr fn))))      ;%ap

;;; Generate code to call a dml'd function directly, if it is called
;;; with the correct number of arguments
(defun fastap (i arg)
   (let ((in (get i 'numargs)))
      (and in (fap (cdr in) arg (list (car in))))))     ;fastap

(defun fap (n a r)
   (cond
      ((zerop n) r)
      ((= n 1) (nconc r (list a)))
      ((not (atom a))
         (case (car a)
            (cons (fap (sub1 n) (caddr a) (nconc r (list (cadr a)))))
            (quote (cond
                  ((atom (cdr a)) (lcferror 'fap))
                  ((fap (sub1 n) (qeval (cdadr a)) (nconc r (list (qeval (caadr a))))))))
            (t nil)))))                         ;fap

;;; If function body has the form `(cons ,fun %e)  then return "fun"
;;; Such bodies occur in code generated for curried ML functions
(defun currybind (body)
   (ifn (atom body)                     ;to avoid destructuring a number
      (let ((x-cons (car body))
            (x-quofun (cadr body))
            (x-e (caddr body)))
         (if (and (eq x-cons 'cons)
               (consp x-quofun)
               (eq (car x-quofun) 'quote)
               (eq x-e '%e))
            (cadr x-quofun)))))         ;currybind

(defun genloop (arms) 
    (let ((looper #-franz (concat "" (symbol-name (gensym)))
                  #+franz (concat "" (get_pname (gensym)))))
          (cond ((isloop arms) (list 'go looper)))))       ;genloop

(defun isloop (arms)
   (exists
      #'(lambda (a) (eq (car a) 'iter))
      (nconc (cond ((cdr arms)
               (list (if (atom (caadr arms)) (cadr arms) (caadr arms)))))
         (car arms))))          ;isloop

(defun trarms (%test arms)
   (nconc
      (cond
         (%test (list 'cond))
         (t (list 'cond (list '(not (atom b)) (qreturn '(car b))))))
      (mapcar (function (lambda (a)
               (cons (if %test (tre (cadr a)) (trtrap (cadr a)))
                  (testtrap (car a) (tre (cddr a))))))
         (car arms))
      (cond
         ((cdr arms) (list (trlast (cadr arms))))
         ((not %test)
            (list
               (list 't
                  (make-throw-form 'b)))))))        ;trarms

(defun trtrap (e)
   (cond
      ((and (eq (car e) 'mk-list) (= (length (cdr e)) 1))
         (list #+franz 'eq #-franz 'eql 'b (tre (cadr e))))
      (t (list 'memq 'b (tre e)))))             ;trtrap

(defun testtrap (sort ans)
   (case sort
      (once (list (qreturn ans)))
      (iter (list ans %loop))
      (t (lcferror (cons sort '(bad sort in testtrap))))))      ;testrap

(defun qreturn (ans) (if %loop (list 'return ans) ans)) ;qreturn

(defun trlast (a)
   (let ((z
            (cond 
               ((atom (car a))
                  (testtrap (car a) (tre (cdr a))))
               (t
                  (testtrap (caar a)
                     `(let ((%e (cons b %e)))
                         ,(trex (cdar a) (cdr a))))))))
      (cons 't z)))    ;trlast

(defun testeval (e) (if (is_constant e) (qeval (eval e)) e))    ;testeval

(defun is_constant (e)
   (if (atom e) (or (numberp e) (memq e '(t nil)))
      (case (car e)
         (quote t)
         ((cons list) (forall 'is_constant (cdr e)))
         (t nil))))                             ;is_constant

(defun trb (b)
   (case (car b)
      ((mk-abstype mk-absrectype) (trabstyb (cadr b) (caddr b)))
      (t 
         (chkvarstr
            (cadr b)
            "multiple occurrence of a variable in left hand side of a definition"
            "bad variable structure")
         (let ((rhs (checkst (cadr b) (tre (caddr b)))))
            (case (car b)
               (mk-letref (copyst (bvpat b) rhs))
               (t rhs))))))                     ;trb

(defun trabstyb (eqnl d)
   (checkst (cadr d)
      `(let ((%e (cons dummy %e)))
          ,(trex (isompat eqnl) (caddr d))))) ;trabstyb

;;; lcp - absty, repty are now abs_ty, rep_ty
;;; must be consistent with code in F-typeml
(defun isompat (eqnl)
   (cons isom
      (nconc (mapcar #'(lambda (eqn) (concat '|abs_| (car eqn))) eqnl)
         (mapcar #'(lambda (eqn) (concat '|rep_| (car eqn))) eqnl)
         )))                            ;isompat

(defun make-cond-case (cl ans)
   `(,(ifn cl t (ifn (cdr cl) (car cl) (cons 'and cl))) ,ans))  ;make-cond-case

(defun gencheck (cl ans)
   (ifn cl ans
      `(cond
          ,(make-cond-case cl ans)
          (t ,(make-throw-form (list 'quote '|pattern|))))))     ;gencheck

(defun gencheckl (cl-ans-list)
   `(cond
       ,@(mapcar #'(lambda (p) (make-cond-case (car p) (cdr p))) cl-ans-list)
       (t
          ,(make-throw-form (list 'quote '|pattern|))))) ;gencheckl

(defun checkst (s ans)
   (let ((cl (checks s 'a)))
      (if (null cl) ans
         `(let ((a ,ans)) ,(gencheck cl 'a)))))
;checkst

(defun checks (s arg)
   (case (car s)
      ((mk-empty mk-var mk-wildcard) nil)
      (mk-straint (checks (cadr s) arg))
      (mk-con0
         `((and (atom ,arg)
             (#+franz eq #-franz eql (quote ,(cadr s)) ,arg) )))
      (mk-appn
         (ifn (eq (caadr s) 'mk-con)
            (translation-failed "bad variable structure (error 1)")
            (cons
               `(and (consp ,arg)
                   (#+franz eq #-franz eql (car ,arg) ',(cadadr s)))
               (checks (caddr s) `(cdr ,arg)))))
      ((mk-intconst mk-boolconst)
         `((#+franz eq #-franz eql ,(cadr s) ,arg)))
      (mk-tokconst
         `((#+franz eq #-franz eql ',(cadr s) ,arg)))
      (mk-dupl (checks2 (cdr s) arg))
      (mk-binop (cons arg (checks2 (cddr s) arg)))
      (mk-list (cons
            (list '= (list 'length arg) (length (cdr s)))
            (checksl (cdr s) arg)))
      (t (translation-failed  "bad variable structure (error 2)"))));checks

(defun checks2 (s2 arg)
   (nconc
      (checks (car s2) (list 'car arg))
      (checks (cadr s2) (list 'cdr arg))))      ;checks2

(defun checksl (sl arg)
   (if (null sl) nil (nconc
         (checks (car sl) (list 'car arg))
         (checksl (cdr sl) (list 'cdr arg)))))  ;checksl

;;; Translate declaration
(defun trdecl (d)
   (case (car d)
      ((mk-let mk-letref mk-abstype mk-absrectype) `(cons ,(trb d) %e))
      (mk-letrec
         (let ((body (trex (varpat (cadr d)) (caddr d))))
            `(let ((%e (cons nil %e))) (rplaca %e ,body))))
      (t (lcferror (cons d '(bad decl))))))     ;trdecl

;;; Translate ML to Lisp.
;;; Set new%%lb to pattern of atoms for making Lisp bindings
;;;    These atoms will allow reliable reference to ML variables.
;;;    When compiled code is loaded, these same Lisp atoms will be set.
;;; Set %compfns to the defun's that must be eval'ed before evaluation of code
;;; Each function in %compfns is defined before its first use.  Otherwise
;;; compilation can fail.
(defun tran (pt)
   (setq %compfns nil)
   (setq new%%lb nil)
   (setq rec%env nil)
   (let
      ((pr
         (optimize-code
            (case (car pt)
               ((mk-deftype mk-type mk-rectype) nil)
               ((mk-let mk-letref mk-letrec mk-abstype mk-absrectype)
                  (let ((bvs (bvpat pt)))
                     (setq new%%lb (build-lb (car pt) bvs))
                     (if (eq (car pt) 'mk-letrec)
                        `(cons (quote ,bvs)
                           ,(trb `(mk-let ,(cadr pt) (mk-in ,pt ,(cadr pt)))))
                        `(cons (quote ,bvs)
                           ,(trb pt)))))
               (t (tre pt)))
            nil)))
      (do
         ((compfns %compfns (cdr compfns)))
         ((null compfns)
            (setq %compfns (nreverse %compfns)))
         (rplaca compfns (optimize-code (car compfns) nil)))
      ;; Retain compatibility with old franz versions. Do proper thing for CL
      #+franz pr
      #-franz
      `(lambda (%e)
          (declare (optimize (speed 2) (safety 0)))
          ,pr)))   ;tran


;;; Optimize Lisp code. Lambda expressions inside quoted data may profitably
;;; be yanked out into separate functions which may then be compiled.
;;; Bugfix: ap changed to %ap
;;; MJCG 10 Nov 1990 for HOL88.1.12
(defun optimize-code (code inside-quote)
   (cond
      ((atom code) code)
      ((and (eq (car code) 'lambda) inside-quote)
         (let
            ((name (uniquesym 'FUN %timestamp))
             (forms (optimize-code (cddr code) nil)))
            (remember-tran-function name (cadr code) forms)
            name))
      ((eq (car code) 'quote)
         `(quote ,(optimize-code (cadr code) t)))
      ((eq (car code) '%ap)
         (optimize-ap code))
      (t
         (trans-sexpr code inside-quote))))          ; optimize-code

;;; Unwind calls (f x y) where f is a curried function "\a. \b. body"
;;; call innermost function directly
;;; This optimization requires that closure functions be quoted with "quote"
;;; instead of "function" -- it needs the function name and not just its
;;; binding. Using "quote" probably slows execution in some cases, but most
;;; of them should be removed by this optimization.
;;; Bugfix: ap changed to %ap
;;; MJCG 10 Nov 1990 for HOL88.1.12

(defun optimize-ap (comb)
   (let ((code comb)(randstack nil)(lispfun nil)(env nil)(envcode nil))
      ;;; strip off and stack operands, find inner function
      (while (and (consp code) (eq (car code) '%ap))
         (push (optimize-code (caddr code) nil) randstack)  ; save rand
         (setq code (optimize-code (cadr code) nil)))       ; look at rator
      (cond
         (#+franz
          (and (atom code)
             (memq (car (explode-word code)) 
                '(mk-let mk-letrec mk-abstype mk-absrectype)))
          #-franz
          (and (consp code) (eq (car code) 'symbol-value)
             (memq (car (explode-word (cadadr code)))
                '(mk-let mk-letrec mk-abstype mk-absrectype)))
            ;; this is call to top-level ML function (not letref)
            ;; macro-expand what "ap" would execute (now %ap, MJCG 10 Nov 1990)
            (setq env (eval code))
            (setq lispfun (car env)) (setq env (cdr env))
            ;; keep environment if there is one - could be `(quote ,env)
            ;; here except that could be circular (so unable to dump to
            ;; file when compiling)
            (setq envcode
               `(cons ,(pop randstack) ,(if env `(cdr ,code) nil)))
            (while (and randstack (get lispfun 'currybind))
               (setq lispfun (get lispfun 'currybind))
               (setq envcode
                  `(cons ,(pop randstack) ,envcode)))
            (setq code `(,lispfun ,envcode)))
         ((and (consp code) (eq (car (explode-word (car code))) 'FUN))
            (setq lispfun (car code)) (setq envcode (cadr code))
            (while (and randstack (get lispfun 'currybind))
               (setq lispfun (get lispfun 'currybind))
               (setq envcode
                  `(cons ,(pop randstack) ,envcode)))
            (setq code `(,lispfun ,envcode))))
      ;;; build up ordinary calls for remaining rands
      (while randstack
         (setq code `(%ap ,code ,(pop randstack))))
      code))

;;; Map optimize-code over an S-expression, preserving its structure
;;; cannot use mapcar since not all S-expressions are lists
(defun trans-sexpr (code inside-quote)
   (if (atom code) code
      (cons (optimize-code (car code) inside-quote)
         (trans-sexpr (cdr code) inside-quote))))   ;trans-sexpr

;;; Build Lisp Binding for declaration "dc" and bound vars "bvs"
;;; a pattern of new atoms corresponding to new ML names being declared
;;; the atoms contain the declaration class in order to distinguish
;;; the "letrefs" -- for correct optimization
(defun build-lb (dc bvs)
   (if (atom bvs) (if (eq bvs '%con) '%con (uniquesym dc bvs))
      (cons (build-lb dc (car bvs)) (build-lb dc (cdr bvs)))))  ;build-lb

;;; Translate quotation.
(defun trq (e)
   (let ((qfun (assq1 (car e) %q-trans-args)))
      (if qfun (cons qfun (mapcar (function trq) (cdr e)))
         (let ((qfun (assq1 (car e) %q-quote-arg)))
            (if qfun `(,qfun (quote ,(cadr e)))
               (case (car e)
                  (MK=ANTIQUOT `(q-mk_antiquot ,(tre (cadr e))))
                  (MK=TYPE=ANTIQUOT (tre (cadr e)))
                  (MK=PREDICATE
                     `(q-mk_pred (quote ,(cadr e)) ,(trq (caddr e))))
                  (MK=TYPE
                     `(q-mk_type (quote ,(cadr e))
                        (list . ,(mapcar (function trq) (cddr e)))))
                  (t (lcferror (cons e '(bad arg trq))))))))))  ; trq

