;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-typeml.l                                          ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Functions for typechecking ML                       ;;;
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
;;;   REVISION HISTORY: Original code: typeml (lisp 1.6) part of Edinburgh  ;;;
;;;                     LCF by M. Gordon, R. Milner and C. Wadsworth (1978) ;;;
;;;                     Transported by G. Huet in Maclisp on Multics, Fall  ;;;
;;;                     1981                                                ;;;
;;;                                                                         ;;;
;;;                     V2.2 :new-exit instead of err                       ;;;
;;;                                                                         ;;;
;;;                     V4.3 : (\x.e)e' typechecks like let x=e' in e    GH ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (special |%print_lettypes-flag|))

#+franz
(declare
   (localf structon
      structoff
      genmlink
      listtyping
      typing
      adjust-fundef
      adjust-abstraction
      is-constructor
      is-local-constructor
      record-abstype
      record-conctype
      abstract-typing
      concrete-typing
      test-trap-typing
      parserr
      tidycdrs
      varbindings
      layer
      layerl
      gettype
      get-builtin
      gettypeid
      mutant
      mutant1
      immut
      isdeftype
      getdeftype
      rectyping
      newdeftype
      gettypet
      tyscoperr
      checkabst
      gettypetid
      typebindings
      popenv
      poptenv
      tidy
      tidyup
      condpstring
      printabstype
      printtytail
      make-atom-ty
      mlink
      instof
      prune
      occursbt
      polyb
      unifyt
      unifybt
      unifytl))

;;; make a circular list (x x x x ...)
(defun twistlist (x)
   (let ((lx (list x))) (rplacd lx lx)))       ;twistlist

(defun structon (x) (setq structcheck t) x)     ;structon

(defun structoff (x) (setq structcheck nil) x)  ;structoff

;;; Generate a type variable
(defun genmlink () (list '%MLINK))              ;genmlink


;;; Check the types of several objects, recording all type errors
;;; (listtyping (ob1 ... obn) (ty1 .. tyn) ty)
;;;     unifies the type of each obi with type tyi, finally returns ty
;;; if type errors occur, return a new type variable to prevent error cascade

(defun listtyping (obl tyl ty)
   (let ((OK t))
      (while obl
         (let ((ty$ (typing (car obl))))
            (when (and (car tyl) (not (unifyt ty$ (car tyl))))
               (incf type%errors)
               (setq OK nil)
               (llterpri)
               (llprinc '|ill-typed phrase: |)
               (print-ml-text (car obl) %mlprindepth)
               (llterpri)
               (let ((%temt tenv))
                  (ptoken |has an instance of type|)
                  (pbreak 2 4)
                  (printmty (tidy ty$))
                  (pnewline)
                  (ptoken |which should match type|)
                  (pbreak 2 4)
                  (printmty (tidy (car tyl)))
                  (pnewline))))
         (setq obl (cdr obl)) (setq tyl (cdr tyl)))
      (if OK ty (genmlink))))   ; listtyping


;;; Deduce types of ML syntax tree
;;; also deduces ML types inside quotations, for typing of antiquotations

(defun typing (ob)      
   (let ((c (car ob)) (l (cdr ob)) (ty (genmlink)) (ty$ (genmlink)))
      (case c
         (mk-empty (if structcheck ty nullty))
         (mk-boolconst boolty)
         (mk-intconst  intty)
         (mk-tokconst  tokty)
         (MK=VARTYPE   typety)
         ((MK=VAR MK=CONST)   termty)
         (mk-fail ty)
         (mk-failwith (listtyping l (list tokty) ty))
         ((mk-con mk-con0) (gettype (car l)))
         (mk-wildcard
            (if structcheck (genmlink) 
               (progn
                  (llprinc '|wildcard allowed only in patterns|)
                  (llterpri)
                  (throw-from typecheck nil))))
         (mk-var
            (let ((c-arity (is-constructor (car l))))
               (when c-arity
                  (rplaca ob (if (zerop c-arity) 'mk-con0 'mk-con)))
               (gettype (car l))))
         (mk-consttyp
            (if (checkabst l)
               (cons (gettypet (car l)) (mapcar #'typing (cdr l)))
               (gettypet (car l))))
         (mk-vartyp
            (cond
               ((assoc1 (car l) %vartypes))
               ((push (cons (car l) ty) %vartypes) ty)))

;;; mk-objtyp deleted from the following list  [TFM 90.09.09]

;;; MJCG 11 May 1992. 
;;; Test for badly formed list types (e.g. (bool,bool)list) added.
         (mk-listyp
            (cond ((cdr l)
                   (llprinc '|too many args to list |)
                   (llterpri)
                   (throw-from typecheck nil))
                  (t (cons c (list(typing(car l)))))))

         ((mk-inttyp mk-booltyp mk-termtyp mk-formtyp mk-typetyp mk-thmtyp
               mk-toktyp mk-nulltyp 
;;;            mk-listyp    ;;; Commented out by MJCG 11 May 1992
               mk-prodtyp mk-funtyp mk-sumtyp)
            (cons c (mapcar #'typing l)))
         (mk-straint
            (let ((ty (typing (cadr l))))
               (listtyping (list (car l)) (list ty) ty)))
         (mk-dupl 
            `(mk-prodtyp ,(typing (car l)) ,(typing (cadr l))))
         (mk-seq (listtyping (car l) (twistlist nil) (typing (cadr l))))
         (mk-list (listtyping l (twistlist ty) (list 'mk-listyp ty)))
         (mk-appn
            (ifn (eq (caar l) 'mk-abstr)
               (listtyping l (list (list 'mk-funtyp ty ty$) ty) ty$)
               (dis-place 
                (cadr ob)
                (adjust-abstraction (cadadr ob) (caddadr ob)))
               (typing `(mk-let (,(cadar l) . ,(cadr l))))
               (popenv (typing (caddar l)))))
         ;;; types (\x.e1)e2 like let x=e2 in e1  [GH]
         ;;; maybe %pt should be changed accordingly, so that the translator may
         ;;; take advantage of the transformation too.
         (mk-binop
            (ifn structcheck
               (typing `(mk-appn (mk-var ,(car l)) (mk-dupl ,@(cdr l))))
               (setq ty$ `(mk-listyp ,ty))
               (listtyping (cdr l) (list ty ty$) ty$)))
         (mk-unop (typing `(mk-appn (mk-var ,(car l)) ,(cadr l))))
         (mk-assign (let ((ty nil))
               (structon (setq asscheck t))
               (setq ty (typing (car l)))
               (structoff (setq asscheck nil))
               (listtyping (cdr l) (list ty) ty)))
         ((mk-test mk-trap) (test-trap-typing c l ty ty$))
         (mk-while (listtyping (list (car l)) (twistlist boolty) nil)
            (typing (cadr l)) nullty)
         (mk-case (typing `(mk-appn (mk-fun ,(cadr l)) ,(car l)))) 
         (mk-abstr
            (dis-place ob (adjust-abstraction (car l) (cadr l)))
            (setq l (cdr ob))
            (varbindings (car l) c)
            (popenv (list 'mk-funtyp
                  (structoff (typing (structon (car l)))) (typing (cadr l)))))
         (mk-fun       
            (listtyping
               (mapcar #'(lambda (funcase) 
                     `(mk-abstr ,(car funcase) ,(cdr funcase)))
                  (car l))
               (twistlist ty)    
               ty))
         (mk-in  (typing (car l))  (popenv (typing (cadr l))))
         (mk-ind (typing (car l)) (poptenv (typing (cadr l))))
         ((mk-ina mk-inc) (typing (car l))
            (typescopechk (popenv (poptenv (typing (cadr l))))))
         ((mk-let mk-letref)
            (let* ((consl1l2 (split (mapcar #'adjust-fundef l)))
                  (l1 (car consl1l2))
                  (l2 (cdr consl1l2)))
               (rplacd ob (list (binarize l1 'mk-dupl) (binarize l2 'mk-dupl))))
            (setq l (cdr ob))
            (let ((ty (typing (cadr l))))
               (prog2
                  (varbindings (car l) c)
                  (structoff (listtyping (structon (list (car l))) (list ty) ty))
                  (if (eq c 'mk-let) (rplaca (car env) 'let)))))
         (mk-letrec
            (let* ((consl1l2 (split (mapcar #'adjust-fundef l)))
                  (l1 (car consl1l2))
                  (l2 (cdr consl1l2)))
               (rplacd ob (list (binarize l1 'mk-dupl) (binarize l2 'mk-dupl)))
               (setq l (cdr ob))
               (varbindings (car l) c)
               (rectyping l)))
         ((mk-abstype mk-absrectype) (abstract-typing c l))
         ((mk-type mk-rectype) (concrete-typing c l))
         (mk-deftype
            (typebindings (mapcar #'newdeftype (car l)))
            nullty)
         ((mk-tyquot mk-quot MK=ANTIQUOT MK=TYPE=ANTIQUOT)
            (typing (car l)))
         (MK=TYPE  (listtyping (cdr l) (twistlist typety) typety))
         (MK=TYPED (listtyping l (list termty typety) termty))
         ((MK=COMB MK=PAIR MK=ABS MK=COND)
            (listtyping l (list termty termty termty ) termty))
         (MK=NEG (listtyping l (list formty) formty))

;;; MK=IFF deleted in the following list

         ((MK=CONJ MK=DISJ MK=IMP)
            (listtyping l (list formty formty) formty))
         ((MK=FORALL MK=EXISTS) (listtyping l (list termty formty) formty))
         (MK=PREDICATE (listtyping (cdr l) (list termty) formty))
         ((MK=EQUIV MK=INEQUIV) (listtyping l (list termty termty) formty))
         (t (parserr c))
         )))                                    ;typing


;;; parse-failed removed by MJCG to avoid crashing into lisp

(defun adjust-fundef (paire)
   (let ((x (car paire)) (y (cdr paire)))
      (case (car x)
         (mk-straint (adjust-fundef (cons (cadr x) `(mk-straint ,y ,(caddr x)))))
         (mk-appn (if (and (eq (caadr x) 'mk-var) (is-constructor (cadadr x)))
               (cons x y) 
               (adjust-fundef (cons (cadr x) `(mk-abstr ,(caddr x) ,y)))))
         ((mk-var mk-binop mk-dupl mk-list mk-empty) (cons x y))
         (t (princ 
               '|Syntax error detected by typechecker.|)
            (terpri)
            (princ '|Bad left hand side of definition: |)
            (print-ml-text x %mlprindepth)
            (llterpri)(throw-from typecheck nil)))))  ; adjust-fundef

(defun adjust-abstraction (a b)
   (if (or (not (eq (car a) 'mk-appn))
         (and (eq (caadr a) 'mk-var) (is-constructor (cadadr a))))
      `(mk-abstr ,a ,b)
      (adjust-abstraction (cadr a) `(mk-abstr ,(caddr a) ,b))))  ; adjust-abstraction

(defun is-constructor (f)
   (or (get f 'constructor) (is-local-constructor f env))) ; is-constructor

(defun is-local-constructor (f e)
   (when e (if (and (eq (caar e) 'CONC) (assoc-equal f (car e)))
         (if (eq (car (assoc-equal f (car e))) 'mk-funtyp) 1 0)
         (is-local-constructor f (cdr e))))) ; is-local-constructor

;;; generate an atom and store abstype info on its property list
(defun record-abstype (eqn)
   (let ((tysym (uniquesym "ABS" (car eqn))))
      (eval-remember
         `(progn
            (putprop (quote ,tysym) (quote ,(length (cadr eqn))) 'arity)
            (putprop (quote ,tysym) (quote ,(car eqn)) 'abstyname)))
      (cons (car eqn) tysym)))                  ; record-abstype

;;; similar for concrete types 
(defun record-conctype (eqn)
   (let ((tysym (uniquesym "CONC" (car eqn))))
      (eval-remember
         `(progn
            (putprop (quote ,tysym) (quote ,(length (cadr eqn))) 'arity)
            (putprop (quote ,tysym) (quote ,(car eqn)) 'tyname)))
      (cons (car eqn) tysym)))                  ; record-conctype

;;; processing of abstract types
(defun abstract-typing (c l)
   (let ((eqnl (car l)))
      (let ((tyops (mapcar #'record-abstype eqnl))
            (isoms nil))
         (if (eq c 'mk-absrectype) (typebindings tyops))
         (mapc
            #'(lambda (eqn)
               (let ((%vartypes
                        (mapcar #'(lambda (v) (cons v (genmlink))) (cadr eqn)))
                     (ty2 (typing (cddr eqn)))
                     (ty1 (cons (assoc1 (car eqn) tyops) (mapcar #'cdr %vartypes))))
                  (unless (= (length (cadr eqn)) (length %vartypes))
                     (llprinc '|free vartype in abstype equation|)
                     (llterpri)
                     (throw-from typecheck nil))
                  (push
                     (list (concat '|rep_| (car eqn))
                        'mk-funtyp ty1 ty2) isoms)
                  (push
                     (list (concat '|abs_| (car eqn))
                        'mk-funtyp ty2 ty1) isoms)))
            eqnl)
         (if (eq c 'mk-abstype) (typebindings tyops))
         (push (cons 'abs isoms) env)
         (prog1 (typing (cadr l)) (popenv (rplacd (cadr env) (cdar env))))))
   )                                            ; abstract-typing

;;; processing of concrete types
(defun concrete-typing (c eqnl)
   (let ((tyops (mapcar #'record-conctype eqnl))
         (constrs nil))
      (if (eq c 'mk-rectype) (typebindings tyops))
      (mapc
         #'(lambda (eqn)
            (let ((%vartypes (mapcar #'(lambda (v) (cons v (genmlink))) (cadr eqn))))
               (let ((ty1 (cons (assoc1 (car eqn) tyops) (mapcar #'cdr %vartypes))))
                  (mapc 
                     #'(lambda (constr-def)
                        (let ((ty (ifn (cdr constr-def)
                                    ty1
                                    (list 'mk-funtyp (typing (cdr constr-def)) ty1))))
                           (push (cons (car constr-def) ty) constrs)))
                     (reverse (cdddr eqn))))))
         eqnl)
      (if (eq c 'mk-type) (typebindings tyops))
      (push (cons 'constructors constrs) env)
      (binarize (mapcar #'cdr (cdar env)) 'mk-prodtyp)))        ; concrete-typing

(defun test-trap-typing (c l ty ty$)
   (cond ((eq c 'mk-trap)
         (setq l
            (cons (cons (triple 'once '(mk-list) (car l)) (cadr l)) (cddr l)))))
   (listtyping
      (mapcar #'cadr (car l))
      (twistlist (if (eq c 'mk-test) boolty (list 'mk-listyp tokty)))
      nil)
   (let ((b nil) (e nil))
      (cond ((cdr l)
            (setq e (cdadr l)) (setq b (caadr l))
            (unless (atom b)
               (setq e `(mk-in (mk-let ((mk-var ,(cdr b)) . (mk-tokconst))) ,e))
               (setq b (car b)))
            (setq ty$ (typing e))
            (if (eq b 'once) (setq ty ty$)))
         (t (if (eq c 'mk-test) (setq ty nullty)))))
   (listtyping
      (mapcar #'cddr (car l))
      (mapcar #'(lambda (x) (if (eq (car x) 'once) ty)) (car l))
      ty))                                      ; test-trap-typing

(defun parserr (c) (lcferror (catenate '|bad parser constructor | c))) ;parserr

(defun initmltypenv ()
   (setq nullty '(mk-nulltyp))
   (setq boolty '(mk-booltyp))
   (setq intty '(mk-inttyp))
   (setq tokty '(mk-toktyp))
;;;(setq objty '(mk-objtyp))     deleted: [TFM 90.09.09]
   (setq typety '(mk-typetyp))
   (setq termty '(mk-termtyp))
   (setq formty '(mk-formtyp))
   (setq thmty '(mk-thmtyp))
   (setq %emt nil)
   (setq %temt  nil)
   (setq %deftypes nil))                       ;inittmltypenv

(eval-when (load)
   (cond (initial%load (initmltypenv))))


;;; Top-level type checker
(defun typecheck (ob)
   (let ((ph (car ob)) (env %emt) (tenv %temt) (type%errors 0)
         (asscheck nil) (structcheck nil) (glassl nil) (%vartypes nil))
      (let ((ty (tidy (typing ob))))
         (unless (zerop type%errors)
            (llprinc type%errors)
            (llprinc '| error|)
            (if (> type%errors 1) (llprinc '|s|))
            (llprinc '| in typing|)
            (llterpri)
            (throw-from typecheck nil))
         (typescopechk ty)
         (when (and (eq ph 'mk-letref) (poly ty))
            (llprinc '|top-level letref has polytype |)
            (printmty ty)
            (pnewline)
            (throw-from typecheck nil))
         (mapc #'(lambda (x)
               (cond ((poly (cdr x))
                     (llprinc '|non-local assignment to polytyped variable |)
                     (llprinc (car x))
                     (llterpri)
                     (throw-from typecheck nil))))
            glassl)
         (unless (eq tenv %temt)
            (setq %thistydec (car tenv)))
         (unless (eq env %emt)
            (tidycdrs (cdr (setq %thisdec (car env)))))
         ty)))                                  ; typecheck

(defun tidycdrs (l)
   (mapc #'(lambda(x) (rplacd x (tidy (cdr x)))) l))   ;tidycdrs

(defun updatetypes ()
   (cond
      (%sections
         (if %thisdec (push %thisdec %emt))
         (if %thistydec (push %thistydec %temt)))
      (t 
         (setq %deftypes (append %thistydec %deftypes))
         (when %thisdec
            (putpropl (cdr %thisdec) 'mltype)
            (mapc #'(lambda (x)
                  (if (eq 'mk-letref (car %thisdec)) (putprop (car x) t 'refvar)
                     (remprop (car x) 'refvar)))
               (cdr %thisdec))
            (mapc #'(lambda (x)
                  (if (eq 'constructors (car %thisdec))
                     (putprop (car x) 
                        (if (eq (cadr x) 'mk-funtyp) 1 0)
                        'constructor)))
               (cdr %thisdec))))))              ;updatetypes

;;; Push a new layer of bindings onto the environment
;;; "binder" tells how binders were created;   mk-let, mk-letrec, etc.
(defun varbindings (st binder)
   (push (cons binder (layer st)) env))        ;varbindings

(defun layer (st)
   (case (car st)
      (mk-var (ifn (is-constructor (cadr st)) 
            (list (cons (cadr st) (genmlink)))))
      (mk-appn (layerl (cdr st)))
      (mk-straint (layer (cadr st)))
      ((mk-dupl mk-list) (layerl (cdr st)))
      (mk-binop (layerl (cddr st)))
      (t nil)))                                 ;layer

(defun layerl (stl)
   (cond (stl (append (layer (car stl)) (layerl (cdr stl)))))) ;layerl

;;; get the type of the identifier
;;; if unbound, print message and assume identifier is bound by "letref"
(defun gettype (%id)
   (cond  ((let ((nonloc nil)) (gettypeid env)))
      (t (incf type%errors)
         (llterpri)
         (llprinc '|unbound or non-assignable variable |)
         (llprinc %id)
         (llterpri)
         (varbindings (list 'mk-var %id) 'mk-letref)
         (genmlink))))                     ; gettype

;;; Look up "it", or a dmlc'd constant
(defun get-builtin ()
   (when (and (eq %id lastvalname) (assq 'mk-abstr env))
      (llprinc '|May not use '|)
      (llprinc lastvalname)
      (llprinc '|' in a function body|)
      (llterpri)
      (throw-from typecheck nil))
   (get %id 'mltype))                          ; get-builtin

;;; Get type type of %id in environment e
;;;   asscheck is true if this is the left-hand of an assignment
;;;   nonloc is true if e was found underneath a mk-abstr binding
(defun gettypeid(e)
   (ifn e
      (let ((ty (get-builtin)))      
         (cond
            ((get %id 'refvar)ty)
            (asscheck (if (is-constructor %id) ty))
            (ty (mutant ty nil))))
      (let ((ty (assoc1 %id (cdar e))))
         (cond ((null ty)
               (cond ((eq (caar e) 'mk-abstr) (setq nonloc t)))
               (gettypeid (cdr e)))
            ((eq (caar e) 'mk-letref)
               (cond ((and asscheck nonloc) (push (cons %id ty) glassl)))
               ty)
            (asscheck nil)                 ; assignable variable needed?
            ((memq (caar e) '(let abs)) (mutant ty (cdr e)))
            (t ty)
            ))))                           ; gettypeid

;;; Rename type variables for different uses of a let-bound identifier
;;;    (also abstract type isomorphisms)
(defun mutant (ty %env) 
   (if (poly ty) (let ((%l nil)) (mutant1 ty)) ty))    ;mutant

(defun mutant1 (ty)
   (cond
      ((instof ty) (mutant1 (instof ty)) )
      ((or (atom ty) (mlink ty))
         (cond ((assq1 ty %l))
            ((immut ty %env) ty)
            ((cdar (push (cons ty (genmlink)) %l)))))
      ((cons (car ty) (mapcar #'mutant1 (cdr ty))))))   ;mutant1


;;; A type variable is immutable only if all its uses are in let-bound
;;;    identifiers (or abstract type isomorphisms)
(defun immut (tyv e)
   (and e
      (or (and (not (memq (caar e) '(let abs)))
            (exists #'(lambda (x) (occurst tyv (cdr x))) (cdar e)))
         (immut tyv (cdr e)))))            ;immut

;;; See if a synonym exists for a given type, returns (tok . ty) or nil
;;; This test is used to see if the type is monomorphic.  The token returned
;;; may actually be out of scope.
(defun isdeftype (ty te)
   (cond ((null te) (revassoc ty %deftypes))
      ((revassoc ty (car te)))
      ((isdeftype ty (cdr te)))))           ; isdeftype

;;; Get the current synonym for type ty in environment te
;;; Returns nil if none, else (tok . ty)
;;; "nil" is a legal type name
(defun getdeftype (ty te)
   (let ((typair (isdeftype ty te)))
      (if (and typair (equal ty (gettypetid (car typair) te)))
         typair)))                             ; getdeftype

(defun rectyping (l)
   (let ((ty (structoff (typing (structon (car l))))))
      (listtyping (cdr l) (list ty) ty)
      (rplaca (car env) 'let)
      ty))                                      ;retyping

(defun newdeftype (ob)
   (let ((id (car ob)) (ty (typing (cdr ob))))
      (cond ((poly ty)
            (llprinc '|type variable in DEFTYPE|)
            (llterpri)
            (throw-from typecheck nil))
         ((cons id (tidy ty))))))            ; newdeftype

;;; See if the abstract or concrete types in ty are still accessible
(defun typescopechk (ty) (prog (%l) (atch ty) (return ty)))     ;typescopechk

(defun atch (ty)
   (cond
      ((assq ty %l) nil)
      ((instof ty) (atch (instof ty)))
      ((mlink ty) nil)
      ((atom ty) nil)
      (t (push ty %l)
         ;;;;; built-in type operator or user-defined abstract type
         (let ((arity (get (car ty) 'arity)) 
               (name (or (get (car ty) 'abstyname) (get (car ty) 'tyname))))
            (if (and arity (not (eq (gettypet name) (car ty))))
               (tyscoperr name)))
         (exists 'atch (cdr ty)))))             ; atch

(defun gettypet (tyid)
   (cond ((gettypetid tyid tenv)) ((tyscoperr tyid)))) ;gettypet

(defun tyscoperr (x)
   (llprinc '| type |)
   (llprinc x)
   (llprinc '| out of scope |)
   (llterpri)
   (throw-from typecheck nil))                 ;tyscoperr


;;; MJCG: Reorganization and bugfix 4 May 1992 
;;; Old code:
;;; (defun checkabst (idargs)
;;;   (let ((ty (gettypet (car idargs))))
;;;      (cond
;;;         ((atom ty)
;;;            (cond
;;;               ((or (= (get ty 'arity) (length (cdr idargs)))
;;;                     (llprinc '|bad args for abstype |) (llprinc (car idargs)) (llterpri)
;;;                     (throw-from typecheck nil))
;;;                  t))))))
(defun checkabst (idargs)
   (let ((ty (gettypet (car idargs))))
      (cond ((atom ty)
             (cond ((= (get ty 'arity) (length (cdr idargs))) t)
                   (t (llprinc '|bad args for abstype |)
                      (llprinc (car idargs))
                      (llterpri)
                      (throw-from typecheck nil))))))) ;checkabst

;;; Look up the type tyid in environment te or %deftypes
(defun gettypetid (tyid te)
   (cond
      ((null te) (assq1 tyid %deftypes))
      ((assq1 tyid (car te)))
      ((gettypetid tyid (cdr te)))))            ;gettypetid

(defun typebindings (l) (push l tenv))          ;typebindings

(defun popenv (x) (pop env) x)                  ;popenv

(defun poptenv (x) (pop tenv) x)                        ;poptenv

;;; Strip out links, replace type variables with stars
(defun tidy (ty) (let ((%l nil) (%star '||)) (tidyup ty)))      ;tidy

(defun tidy1 (ty) (let ((tenv %temt)) (tidy ty)))       ;tidy1  

(defun tidyup (ty)
   (cond
      ((instof ty) (tidyup (instof ty)))
      ((assq1 ty %l))
      ((or (atom ty) (mlink ty))
         (setq %star (concat '|*| %star))
         (push (cons ty %star) %l)
         %star)
      ((cons (car ty) (mapcar #'tidyup (cdr ty))))))    ;tidyup

;;; Print (car string) if non-nil, return value of string
(defun condpstring (str)
   (if str (pstring (car str))) str)           ;condpstring

;;; MJCG 7/2/89 for HOL88
;;; Function to filter the output of getdeftype if
;;; |%print_lettypes-flag| is nil
;;; This only filters the top level of defined types.
;;; To filter all levels the recursive calls of
;;; getdeftype must also be filtered (i.e. the definition
;;; of getdeftype must be changed instead of just wrapping
;;; a filter around its call in printmty).

(setq |%print_lettypes-flag| t)

(defun lettype-filter (x)
   (cond (|%print_lettypes-flag| x)
      (t (if (atom(cdr x)) x))))

;;; MJCG 7/2/89 for HOL88
;;; lettype-filter wrapped around getdeftype
(defun printmty (tidyty)
   (cond
      ((condpstring (lettype-filter(getdeftype tidyty %temt))))
      ((atom tidyty) (pstring tidyty))
      ((case (car tidyty)
            (mk-nulltyp (ptoken |void|))
            (mk-inttyp (ptoken |int|))
            (mk-booltyp (ptoken |bool|))
            (mk-toktyp (ptoken |string|))     ; used to be tok     GH 7/28/83
;;;         (mk-objtyp (ptoken |obj|))        ; obj deleted [TFM 90.09.09]
            (mk-typetyp (ptoken |type|))
            (mk-termtyp (ptoken |term|))
            (mk-formtyp (ptoken |form|))
            (mk-thmtyp (ptoken |thm|))
            (t (let ((abs (getdeftype (car tidyty) %temt)))
                  (cond
                     (abs (printabstype (cdr tidyty) (car abs)))
                     ((eq (car tidyty) 'mk-listyp)
                        (printabstype (cdr tidyty) '|list|))
                     (t (pbegin 1)
                        (ptoken |(|)
                        (printmty (cadr tidyty))
                        (printtytail (car tidyty) (caddr tidyty))
                        (ptoken |)|)
                        (pend)))))))))               ; printmty

(defun printabstype (args name)
   (pbegin 0)
   (cond 
      ((cdr args)                               ; more than one arg, so print brackets
         (pbegin 1) (ptoken |(|)
         (printmty (car args))
         (mapc #'(lambda (arg) (ptoken |,|) (printmty arg)) (cdr args))
         (ptoken |)|) (pend)
         (pbreak 1 0))
      (args (printmty (car args))  (pbreak 1 0)))
   (pstring name)
   (pend))                                     ; printabstype

;;; supress parentheses in t1 op t2 op t3 op t4, for any one op
(defun printtytail (op ty)
   (case op
      (mk-prodtyp (ptoken | #|))
      (mk-sumtyp  (ptoken | +|))
      (mk-funtyp  (ptoken | ->|))
      (t (lcferror '|bad type to print|)))
   (pbreak 1 0)
   (cond ((condpstring (getdeftype ty %temt)))
      ((and (consp ty) (eq op (car ty)))
         (printmty (cadr ty))
         (printtytail op (caddr ty)))
      (t (printmty ty))))                   ; printtytail

;;; convert a human-readable Lisp form into an ML type
(defun makety (e)
   (cond
      ((null e) nullty)
      ((atom e) (make-atom-ty e))
      ((eq (cadr e) '|list|)                    ; bars added JAC 7/89
         (list 'mk-listyp (makety (car e))))
      ((eq (cadr e) arrow-sym)
         (list 'mk-funtyp (makety (car e)) (makety (caddr e))))
      ((eq (cadr e) sum-sym)
         (list 'mk-sumtyp (makety (car e)) (makety (caddr e))))
      ((eq (cadr e) prod-sym)
         (list 'mk-prodtyp (makety (car e)) (makety (caddr e))))
      (t (lcferror 'makety))))                  ;makety

;;; look up a type name
(defun make-atom-ty (e)
   (case e
      ((|void| |.|) nullty)
      (|int|   intty)
      (|bool|  boolty)
      ((|string| |tok| |token|)  tokty)
;;;   (|obj|   objty)   deleted : [TFM 90.09.09]
      (|type|  typety)
      (|term|  termty)
      (|form|  formty)
      (|thm|   thmty)
      (t e)))                                   ; make-atom-ty

;;; check for a type variable
(defun mlink (ty) (ifn (atom ty) (eq (car ty) '%MLINK)))        ;mlink

;;; See if type variable has been unified with some type
(defun instof (ty) (if (mlink ty) (cdr ty)))    ;instof

(defun prune (ty) (if (instof ty) (prune (instof ty)) ty))      ;prune

(defun occurst (v ty) (occursbt v (prune ty)))  ;occurst

(defun occursbt (tyv bty)
   (if (mlink bty)
      (eq tyv bty)
      (exists #'(lambda (ty) (occurst tyv ty))  (cdr bty))))   ;occurstb

;;; See if the type is polymorphic
(defun poly (ty) (polyb (prune ty)))            ;poly

(defun polyb (bty)
   (or (atom bty) (mlink bty) (exists 'poly (cdr bty))))       ;polyb


;;; Return t if types can be unified.
;;;    side-effect --  link certain type variables to types
(defun unifyt (ty1 ty2) (unifybt (prune ty1) (prune ty2)))      ;unifyt

(defun unifybt (bty1 bty2)
   (cond
      ((eq bty1 bty2))
      ((mlink bty1) (cond ((occursbt bty1 bty2) nil)
            (t (rplacd bty1 bty2))))
      ((mlink bty2) (cond ((occursbt bty2 bty1) nil)
            (t (rplacd bty2 bty1))))
      ((eq (car bty1) (car bty2))
         (unifytl (cdr bty1) (cdr bty2)))))       ;unifybt

;;; unify corresponding types in each list
;;; returns t if each pair can be unified
(defun unifytl (tyl1 tyl2)
   (cond
      ((null tyl1))
      ((unifyt (car tyl1) (car tyl2)) (unifytl (cdr tyl1) (cdr tyl2)))
      ))  ;unifytl


