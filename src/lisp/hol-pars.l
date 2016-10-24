;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        hol-pars.l                                          ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Modified version of f-parsol.l to parse HOL         ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-franz.l (or f-cl.l), f-constants.l, f-macro.l.,   ;;;
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
;;;   REVISION HISTORY: Bugfix by MJCG on 08.02.94                          ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; hol-pars.l
;;; Modified version of F-parsol.l to parse HOL.
;;; See mk_HOL.ml for more details.

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (include "lisp/f-ol-rec")
   (include "lisp/genmacs")
   (special ol-lam-sym select-tok pair-tok toklbearer
      constrs zeros-count %interface-map |%interface_print-flag|
      %interface-props %hidden-consts %name |%read_sexpr-flag|
      %sexpression %syntax-block-enabled))

#+franz
(declare
   (localf build-lam-vstruc quant-wrap checkbit mk-zeros-list))


(setq spec-toks  '(\\  \|  |:|  |(|  |)|  |^|  |=>| |.| |"|))


;;; parse an OL quotation (for ML)

;;;  HOL: test for "dangling predicate symbols" modified to use constrs
;;;       instead of term-constrs and form-constrs

(defun parse-ol ()
   (let ((lang1 'ol1)(lang2 'ol2)(langlp 'ollp)(atom-rtn '(ol-atomr))
         (juxtlevel 120)        ; precedence of application
         (%mk=antiquot 'MK=ANTIQUOT)
         (juxt-rtn '(oljuxt arg1))(ibase 10)(parsedepth 0))
      (parse-level 0)
      ; this check catches dangling predicate symbols
      (if (memq (car arg1) constrs)
         arg1
         (parse-failed "syntax error in quotation"))
      ))  ;parse-ol

;;; declare a user-defined OL infix
;;; called from theory package
;;; HOL: not changed
(defun olinfix (x typ)
   (let ((lang1 'ol1)(lang2 'ol2)(langlp 'ollp))
      (putprop x typ 'olinfix)
      (binop x (+ olinprec 5)     ; right-associative
         (list (if (eq typ 'paired) 'olinf-rtn 'olcinf-rtn)(list 'quote x)))
      ))  ;olinfix

;;; parse paired OL infix
;;; HOL: term-check removed
(defun olinf-rtn (x)
   (list 'MK=COMB
      (mk-ol-atom x)
      (list 'MK=PAIR arg1 (parse-level olinprec))))

;;; parse curried OL infix
;;; HOL: term-check removed
(defun olcinf-rtn (x)
   (list 'MK=COMB
      (list 'MK=COMB (mk-ol-atom x) arg1)
      (parse-level olinprec)))

;;; handle parentheses, also special token ()
;;; HOL: not changed
(defun lpar-rtn ()
   (cond ((eq token rparen-sym) (gnt) '(MK=CONST |()|))
      (t (check rparen-sym (parse-level 0) "bad paren balance")))
   )  ;lpar-rtn

;;; MJCG 20/10/88 for HOL88
;;; term-rtn changed 
;;; logical connectives
;;; HOL: (term-rtn const a b) --> `(MK=COMB (MK=COMB ,const ,a) ,b)
(defun term-rtn (const a b)
   `(list 'MK=COMB (list 'MK=COMB (mk-ol-atom (quote ,const)) ,a) ,b))


;;; routine for OL atoms, linked to atom-rtn
;;; HOL: not changed yet 
;;;      (modification for numbers and bitstrings in other files)
(defun ol-atomr () (mk-ol-atom ptoken))  ;ol-atomr



;;; determine the use of an OL atom : constant or variable
;;; for OL, numbers are scanned as symbols
;;; HOL: clause for predicates deleted
;;; MJCG 19/10/88 for HOL88
;;; Added applying interface map (including code for syn-const)
;;; It applies an interface map to variables and constants on-the-fly as
;;; they are parsed. I am not convinced it is fully correct!
;;; MJCG 8/11/88 for HOL88
;;; changed from using constp to has-const to handle hidden constants.

(eval-when (compile)
   (defmacro has-const (tok) `(get ,tok (quote const))))

;;; MJCG for HOL88.1.02 on 28/3/1989
;;; Check for parsing hol strings before type ":string" defined added
;;; MJCG for HOL88.1.12 on 24/7/1990. Bugfix to allow nil to be mapped.

(defun mk-ol-atom (x)
   (cond
      ((memq x spec-toks) (parse-failed (concat x '| cannot be a term|)))
      ((numberp x) (list 'MK=CONST (atomify x)))
      ((or (has-const x) (tokconstp x) (numconstp x) (wordconstp x))
         (let ((p (get x 'interface-parse)))
            (if p (list 'MK=CONST (car p))
               (list 'MK=CONST x))))
      ((eq x tokflag)
         (if (equal (get '|string| 'canon) '(|string|))
            (list 
               'MK=CONST
               (let ((tok (car toklist)))
                  (setq toklist (cdr toklist))
                  (imploden
                     (append '(96) (append (exploden tok) '(96))))))
            (parse-failed 
               '|type ":string" not defined -- load library string?|)))
      (t (let ((p (get x 'interface-parse)))
            (cond (p (list 'MK=CONST (car p)))
               ((get x 'syn-const) (list 'MK=CONST x))
               (t (list 'MK=VAR x)))))))

;;; routine for juxtaposed OL objects, linked to juxt-rtn
;;; handles predicates and combinations
;;; HOL: code for predicates removed and term-check removed
(defun oljuxt (x) (list 'MK=COMB x (parse-level juxtlevel)))

;;; Parse lambda or quantifier
;;; HOL: rewritten to allow "\(x:num) (y:bool,z) ..." etc
;;; extra argument (const-name) for better error messages
;;; MJCG for HOL88 10/2/89
;;; Bugfix: to prevent Alex Bronstein's bug
;;; (i.e. "!x.\y.t" parsing as "!x y.t")
;;; build-lam-struc takes const-name instead of const
;;; Modified by MJCG 24.1.91 for restrictions
;;; Period precedence is stacked to cope with "!x y::(\z. Q z). x<y"
;;; MJCG 17/11/93
;;; Bugfix: move hol-restrictsetup out of conditional
(defun lamq-rtn (const-name constr n)
   (prog (vars pred period-prec)
      (setq period-prec (get period-sym 'ollp))
      (putprop period-sym 0 'ollp)
      (putprop restrict-tok 0 'ollp)
      (setq vars (parse-level 0))
      (cond ((eq token restrict-tok)
             (gnt)
             (setq pred (parse-level 0))))
      (hol-restrictsetup)
      (putprop period-sym period-prec 'ollp)
      (check period-sym nil (concat "missing period after " const-name))
      (return (build-lam-struc const-name pred vars (parse-level n)))))

(defun get-restrict-name (binder-name)
  (or (get binder-name 'restrict) 
      (parse-failed
       (concat "no restriction constant associated with " binder-name))))

;;; in "\v1,v2.t" the varstructs "v1" and "v2" must satisfy the grammar
;;; 
;;;    v ::= x | x:ty | ^t:ty | ^t | (v1,v2) | (v1,v2):ty1#ty2

;;; build-lam-struc and build-lam-vstruc apply the transformations T and TV
;;; specified below:
;;; 
;;; T[\x.t]                =  \x.t
;;; T[\x:ty.t]             =  \x:ty.t
;;; T[\^x:ty.t]            =  \^x:ty.t
;;; T[\^x.t]               =  \^x.t
;;; T[\t1 t2.t]            =  T[\t1.T[\t2.t]]
;;; T[\(t1,t2).t]          =  UNCURRY(TV[\t1.TV[\t2.t]])
;;; T[\(t1,t2):ty1#ty2.t]  =  UNCURRY(TV[\t1:ty1.TV[\t2:ty2.t]])
;;; T[\t1 t2:ty.t]         =  T[\(t1:ty) (t2:ty).t]
;;; 
;;; TV[\x.t]                =  \x.t
;;; TV[\x:ty.t]             =  \x:ty.t
;;; TV[\^x:ty.t]            =  \^x:ty.t
;;; TV[\^x.t]               =  \^x.t
;;; TV[\(t1,t2).t]          =  UNCURRY(TV[\t1.TV[\t2.t]])
;;; TV[\(t1,t2):ty1#ty2.t]  =  UNCURRY(TV[\t1:ty1.TV[\t2:ty2.t]])

;;; MJCG 10/2/88 for HOL88
;;; Bugfix: to prevent Alex Bronstein's bug
;;; (i.e. "!x.\y.t" parsing as "!x y.t")
;;; quant-wrap inserted into build-lam-struc
;;; instead of second pass using (now deleted) mk-quant-pt
;;; Modified 24.1.91 by MJCG for restrictions

(defun quant-wrap (const-name pred fun)
   (if (null pred)
       (if (eq const-name lam-sym)
           fun
           `(MK=COMB ,(mk-ol-atom const-name) ,fun))
        `(MK=COMB 
          (MK=COMB ,(mk-ol-atom (get-restrict-name const-name)) ,pred) 
          ,fun)))

;;; Modified 24.1.91 by MJCG for restrictions

(defun build-lam-struc (const-name pred vars body)
   (cond ((or (eq (car vars) 'MK=VAR)
            (and (eq (car vars) 'MK=TYPED)
               (memq (caadr vars) '(MK=VAR MK=ANTIQUOT)))
            (eq (car vars) 'MK=ANTIQUOT))
         (quant-wrap const-name pred `(MK=ABS ,vars ,body)))
      ((eq (car vars) 'MK=COMB)
         (cond ((and (eq (caadr vars) 'MK=COMB)
                  (equal (cadadr vars) '(MK=CONST |,|)))
               (quant-wrap 
                  const-name 
                  pred
                  `(MK=COMB
                     (MK=CONST |UNCURRY|)
                     ,(build-lam-vstruc
                        (caddadr vars)
                        (build-lam-vstruc (caddr vars) body)))))
            (t (build-lam-struc
                  const-name
                  pred
                  (cadr vars)
                  (build-lam-struc const-name pred (caddr vars) body)))))
      ((and (eq (car vars) 'MK=TYPED)
            (eq (caadr vars) 'MK=COMB))
         (cond ((and (eq (caadadr vars) 'MK=COMB)
                  (equal (cadadadr vars) '(MK=CONST |,|))
                  (eq (cadaddr vars) 'prod))
               `(MK=COMB
                  (MK=CONST |UNCURRY|)
                  ,(build-lam-vstruc
                     (list 'MK=TYPED (caddadadr vars) (caddaddr vars))
                     (build-lam-vstruc
                        (list 'MK=TYPED (caddadr vars) (cadddaddr vars))
                        body))))
            (t (build-lam-struc
                  const-name
                  pred
                  `(MK=COMB
                     (MK=TYPED ,(cadadr vars)  ,(caddr vars))
                     (MK=TYPED ,(caddadr vars) ,(caddr vars)))
                  body))))
      (t (parse-failed "bad variable structure in quotation"))))

;;; MJCG for 10/2/89 for HOL88
;;; first argument (constr) eliminated
(defun build-lam-vstruc (vars body)
   (cond ((or (eq (car vars) 'MK=VAR)
            (and (eq (car vars) 'MK=TYPED)
               (memq (caadr vars) '(MK=VAR MK=ANTIQUOT)))
            (eq (car vars) 'MK=ANTIQUOT))
         `(MK=ABS ,vars ,body))
      ((and (eq (car vars) 'MK=COMB)
            (eq (caadr vars) 'MK=COMB)
            (equal (cadadr vars) '(MK=CONST |,|)))
         `(MK=COMB
            (MK=CONST |UNCURRY|)
            ,(build-lam-vstruc
               (caddadr vars)
               (build-lam-vstruc (caddr vars) body))))
      ((and (eq (car vars) 'MK=TYPED)
            (eq (caadr vars) 'MK=COMB)
            (eq (caadadr vars) 'MK=COMB)
            (equal (cadadadr vars) '(MK=CONST |,|))
            (eq (cadaddr vars) 'prod))
         `(MK=COMB
            (MK=CONST |UNCURRY|)
            ,(build-lam-vstruc
               (list 'MK=TYPED (caddadadr vars) (caddaddr vars))
               (build-lam-vstruc
                  (list 'MK=TYPED (caddadr vars) (cadddaddr vars))
                  body))))
      (t (parse-failed "bad paired variable structure in quotation"))))

;;; HOL: call to lamq-rtn modified and precedence weakened
(defun lam-rtn () (lamq-rtn lam-sym 'MK=ABS 10))

;;; MJCG 17/1/89 for HOL88
;;; Code from Davis Shepherd for changing lambda symbol
;;; "\" is not disabled
(setq ol-lam-sym '\\)
   
(defun ml-set_lambda (tok)
   (prog1 ol-lam-sym 
      (setq ol-lam-sym tok)
      (let ((lang1 'ol1) (lang2 'ol2) (langlp 'ollp))
         (unop tok '(lam-rtn)))))

(dml |set_lambda| 1 ml-set_lambda (|string| -> |string|))

;;; MJCG 10/2/88 for HOL88
;;; Bugfix: to prevent Alex Bronstein's bug
;;; (i.e. "!x.\y.t" parsing as "!x y.t")
;;; quant-wrap inserted into build-lam-struc
;;; instead of second pass using (now deleted) mk-quant-pt

(defun quant-rtn (const-name)
   (lamq-rtn const-name 'MK=ABS 5))

;;; makes a token a binder - declared as ML function: parse_as_binder
(defun binder-rtn (tok)
   (let ((lang1 'ol1) (lang2 'ol2) (langlp 'ollp))
      (putprop tok t 'binder)
      (unop tok `(quant-rtn (quote ,tok)))
      tok))

;;; Moved here from parse_as_binder.l [TFM 92.10.01 for HOL88 2.01]
;;; |tok| changed to |string|
(dml |parse_as_binder| 1 binder-rtn (|string| -> |string|))

;;; negation -- extends over predicates only
;;; HOL: "~t" --> "NOT t"
(defun neg-rtn () `(MK=COMB (MK=CONST ,neg-tok) ,(parse-level 59)))

;;; HOL: Convert "(t => e1 | e2)" to "COND t e1 e2"
(defun hol-cond-rtn (p)
   `(MK=COMB
      (MK=COMB 
         (MK=COMB (MK=CONST COND) ,p)
         ,(check else-tok (parse-level 80) "need 2 nd branch to conditional"))
      ,(parse-level 80)))

;;; antiquotation of terms/forms (MK=ANTIQUOT) or types (MK=TYPE=ANTIQUOT)
;;; HOL: not changed
(defun metacall ()
   (list %mk=antiquot
      (progn (gnt)
         (cond ((eq ptoken lparen-sym)
               (check rparen-sym (parseml metaprec) "bad antiquotation"))
            ((= ptoktyp 1) (mlatomr))
            ((parse-failed "junk in antiquotation"))))))  ;metacall

;;; type constraint on term
;;; HOL: term-check removed
(defun oltyp-rtn ()
   (list 'MK=TYPED arg1 (olt)))  ;oltyp-rtn


;;; free-standing type quotation
;;; this is presumably a separate recursive descent parser
(defun olt ()
   (let ((%mk=antiquot 'MK=TYPE=ANTIQUOT))
      (olt1 (olt2 (olt3 (olt4))))))  ;olt

(defun olt1 (x)
   (cond ((eq token arrow-tok) (gnt) (list 'MK=TYPE '|fun| x (olt)))
      (t x)))  ;olt1

;;; PPLAMBDA does not have any built-in "sum" type, but user may define it
(defun olt2 (x)
   (cond ((eq token sum-tok) (gnt)
         (list 'MK=TYPE '|sum| x (olt2 (olt3 (olt4)))))
      (t x)))  ;olt2

(defun olt3 (x)
   (cond ((eq token prod-tok) (gnt) (list 'MK=TYPE '|prod| x (olt3 (olt4))))
      (t x)))  ;olt3

;;; vartype-rtn (from ~lcp/lcf/franz/f-parser.l) needs to be modified
;;; to cope with gnt returning ** etc. as a single token
(defun vartype-rtn ()
   (prog (n)
      ;;;     (if cflag (return mul-sym))  replaced by line below (ISD/TFM bug)
      (if cflag (return ptoken))
      (setq n (length(exploden ptoken)))
      loop (ifn (or
            (numberp token)
            (= toktyp 1)
            (test-list-els (exploden token) '(42)))
         (return (imploden (itrate multiply n))))
      (gnt)
      (when (and (test-list-els (exploden ptoken) '(42)) (not cflag))
         (setq n (+ n (length(exploden ptoken))))
         (go loop))
      (return (imploden (nconc (itrate multiply n) (exploden ptoken)))))
   )  ;vartype-rtn

(defun olt4 ()
   (prog (x)
      (gnt)
      (when (eq ptoken lparen-sym)
         (setq x (cond ((eq token rparen-sym) (gnt) nil) (t (olt5))))
         (go l))
      (setq x (list
            (cond ((eq ptoken anticnr-tok) (metacall))
               ((test-list-els (exploden ptoken) '(42))
                  (list 'MK=VARTYPE (vartype-rtn)))
               ((not (= ptoktyp 1))
                  (parse-failed
                     (catenate ptoken " is not allowed in a type")))
               (t (list 'MK=TYPE ptoken)))))
      l  (cond ((= toktyp 1) (gnt))
         ((and x (null (cdr x))) (return (car x)))
         (t (parse-failed "missing type constructor")))
      (setq x (list (cons 'MK=TYPE (cons ptoken x))))
      (go l)))  ;olt4

(defun olt5 ()
   (prog (x)
      (setq x (list (olt)))
      loop (cond ((eq token rparen-sym) (gnt) (return x))
         ((eq token comma-sym) (gnt) (setq x (append x (list (olt))))
            (go loop))
         (t (parse-failed "missing separator or terminator in type")))
      ))  ;olt5


;;; set up OL symbols and precedences

(setq select-tok '|@|)

(setq eq-tok '|=|)
(setq pair-tok comma-sym)

;;; MJCG for HOL88 2/11/1988
;;; mark certain symbols to always parse as a constant

(eval-when (load)
   (putprop conj-tok   t 'syn-const)
   (putprop disj-tok   t 'syn-const)
;;;(putprop iff-tok    t 'syn-const)   DELETED [TFM 90.01.20]
   (putprop imp-tok    t 'syn-const)
   (putprop eq-tok     t 'syn-const)
   (putprop neg-tok    t 'syn-const)
   (putprop pair-tok   t 'syn-const)
   
(putprop forall-tok t 'syn-const)
(putprop exists-tok t 'syn-const)
(putprop select-tok t 'syn-const)
(putprop '|?!|      t 'syn-const)

(let ((lang1 'ol1) (lang2 'ol2) (langlp 'ollp))
   
(putprop endcnrtok 0 'ollp)
(putprop rparen-sym 0 'ollp)
(unop lparen-sym '(lpar-rtn))
(unop neg-tok '(neg-rtn))
(binder-rtn forall-tok)
(binder-rtn exists-tok)
(binder-rtn select-tok)
(binder-rtn 'OUTER_FREE_VARIABLE)


; in OL, all infixes associate to RIGHT
; iff-tok deleted [TFM 90.01.20]

(binop eq-sym    15 (term-rtn eq-tok   'arg1 '(parse-level 10)))
;;;(binop iff-tok   25 (term-rtn iff-tok  'arg1 '(parse-level 20)))
(binop imp-tok   35 (term-rtn imp-tok  'arg1 '(parse-level 30)))
(binop disj-tok  45 (term-rtn disj-tok 'arg1 '(parse-level 40)))
(binop conj-tok  55 (term-rtn conj-tok 'arg1 '(parse-level 50)))

(binop comma-sym 95 (term-rtn pair-tok 'arg1 '(parse-level 90)))

;;; Old definitions (for debugging)
;;;  (setq PAIR-pt   `(MK=CONST ,pair-tok))
;;;  (defun old-term-rtn (const a b) `(MK=COMB (MK=COMB ,const ,a) ,b))
;;;  (binop comma-sym 95 '(old-term-rtn PAIR-pt arg1 (parse-level 90)))


(binop condl-tok 85 '(hol-cond-rtn arg1))

(unop lambda-tok '(lam-rtn))

(putprop else-tok 10 'ollp)   ; the value of the number seems irrelevant

(binop colon-sym 105 '(oltyp-rtn))
(unop anticnr-tok '(metacall))
(unop exfix-sym '(progn (gnt) (mk-ol-atom ptoken)))

)

(putprop neg-tok t 'prefix)

(setq olinprec 100)

;;; HOL: term-constrs and form-constrs are merged to constrs (and many removed)
(setq constrs '(MK=ANTIQUOT MK=CONST MK=VAR MK=COMB
      MK=ABS MK=TYPED MK=ANTIQUOT))
)


;;; The code that follows is for parsing numbers and bitstrings

(defun checkbit (x)
   (cond ((or (= x #/1) (= x #/0)) x)
      (t (parse-failed '|non-bit in word|))))

(defun mk-zeros-list (n)
   (cond ((zerop n) nil) (t (cons #/0 (mk-zeros-list (sub1 n))))))

;;; Bugfix by MJCG 08.02.94
;;; Maybe support for "#..." notation for ":word<n>" types can be deleted.
(setq zeros-count 0)

(defun word-rtn (x)
   (if (eq (car x) 'MK=CONST)
      (list 'MK=CONST 
         (imploden 
            (cons #/# (append
                  (mk-zeros-list zeros-count)
                  (cond
                     ((eq (cadr x) '|0|) nil)
                     (t (mapcar #'checkbit (exploden (cadr x)))))))))
      (parse-failed '|non-word after #|)))

(defun hol-persetup () (putprop period-sym 650 'ollp))

;;; Added 23.1.91 by MJCG to support variable restrictions
;;; Used in f-parser.l
(defun hol-restrictsetup () (putprop restrict-tok 105 'ollp))

(eval-when (load)
   (let ((lang1 'ol1)(lang2 'ol2)(langlp 'ollp))
      (unop prod-tok '(word-rtn (parse-level 1000)))))

(eval-when (load)
   (put-double '|=| '(#/> #/=))
   (put-double '|-| '(#/>))
   (put-double '|:| '(#/=))
   (put-double '|;| '(#/;))
   (put-double '|/| '(#/\))
   (put-double '\\  '(#//))
   (put-double '|>| '(#/< #/> #/=))
   (put-double '|<| '(#/< #/> #/- #/=))
   (put-double '|-| '(#/- #/>))
   (put-double '|--| '(#/> #/-))
   (put-double '|==| '(#/= #/>))
   (put-double '|<-| '(#/- #/>))
   (put-double '|<=| '(#/= #/>))
   (put-double '|?| '(#/! #/? #/\))
   (put-double '|!| '(#/! #/? #/\))
   (put-double '|+| '(#/+))
   (put-double '|*| '(#/*))
   (put-double '|/| '(#// #/\)))
         
(setq infixables
   '(|/| |#| |*| |+| |-| |<| |=| |>| /\\ \\/ |==>| |<=>| |,| |^|
      |++| |**| |--| |//| |<-| |<--| |<=| |<==| |<<| |>>| |<>| |><|))

;;; := added TFM 88.03.31
(setq 
   legalconsts
   '(|/| |#| |*| |+| |-| |<| |=| |>| |;| |&| |==>| |<=>| |~| 
      /\\ \\/
      |,| |!| |?| |@| |??| |!!| |?!| |!?| 
      |==| |<<| |>>| |<=| |>=| |<>| |><| |-->| |++| |**| |--| |//|
      |<-| |<--| |<=| |<==| |<<| |>>| |:=|))



;;; MJCG 21/10/88 for HOL88
;;; Code to support interface maps


;;; %interface-map is a list ((a1.v1) ... (an.vn)) where each ai is 
;;; translated to vi by the parser, and vi to ai by the pretty printer.
;;; Each vi must be a HOL constant.
;;; Each ai can be either a variable or constant.
;;; When an interface map is activated eah vi is made an interface-parse
;;; property of ai, and each ai is made an interface-print property of vi.

(setq %interface-map nil)

;;; |%interface_print-flag| determines whether the inverse interface map
;;; is applied when printing
(setq |%interface_print-flag| t)

;;; MJCG 19/10/88 for HOL88
;;; dml-ed function for setting interface printing status from ML
;;; old value returned
;;;(defun ml-interface_printing (x) 
;;; (prog1 |%interface_print-flag| (setq |%interface_print-flag| x)))
;;;(dml |interface_printing| 
;;;     1 
;;;     ml-interface_printing
;;;     (|bool| -> |bool|))

;;; MJCG 17/10/88 for HOL88
;;; dml-ed function for getting interface map from ML
(defun ml-interface_map () %interface-map)
(dml |interface_map| 
   0
   ml-interface_map 
   (|void| -> ((|string| |#| |string|) |list|)))


;;; MJCG 21/10/88 for HOL88
;;; Properties moved from a constant to its new name
;;; paired with property old values are saved under.
;;; MJCG 24/1/91 -- restrict and unrestrict saved
(setq 
   %interface-props 
   '((ollp . ollp-save) 
      (ol1 . ol1-save)
      (ol2 . ol2-save)
      (olinfix . olinfix-save)
      (binder . binder-save)
      (restrict . restrict-save)
      (unrestrict . unrestrict-save)))

;;; MJCG 21/10/88 for HOL88
;;; Function for moving properties, saving old values is necessary.
;;; The property saved indicates that the properties have been saved
;;; MJCG for HOL88.1.12 on 24/7/1990. Bugfix to allow nil to be mapped.
;;;  -- (list val) instead of val.

(defun put-save (name val)
   (if (has-const name) (putprop name t 'saved))
   (mapc
      (function
         (lambda (pp)
            (let ((prop     (car pp))
                  (saveprop (cdr pp)))
               (if (has-const name)
                   (putprop name (get name prop) saveprop))
               (putprop 
                  name 
                  (subst-equal `(quote ,name) `(quote ,val) (get val prop))
                  prop))))
      ;;;      subst above an awful hack -- sorry!
      %interface-props)
   (putprop name (list val) 'interface-parse)
   (putprop val name 'interface-print))

;;; MJCG 21/10/88 for HOL88
;;; Function for restoring old values.
;;; MJCG 9/1/89 for HOL88
;;; Bugfix (bug report from David Shepherd)
;;; new-name and old-name added as parameters.
;;; interface-print property removed from old-name

(defun restore-prop (new-name old-name)
   (mapc
      (function
         (lambda (pp)
            (let ((prop     (car pp))
                  (saveprop (cdr pp)))
               (cond ((get new-name 'saved)
                     (putprop new-name (get new-name saveprop) prop)
                     (remprop new-name saveprop))
                  ((not (has-const new-name))
                     (remprop new-name prop)
                     (remprop new-name saveprop))))))
      %interface-props)
   (remprop new-name 'interface-parse)
   (remprop old-name 'interface-print)
   (remprop new-name 'saved))

;;; MJCG 4/1/89 for HOL88 (bugfix from David Shepherd of Inmos)
;;; distinctp defined here as it is a local function of genfns.l
;;;(distinctp (x1 ... xn)) is t if x1, ... ,xn are distinct and nil otherwise.

(defun distinctp (x)
   (cond ((null x) t)
      (t (and (not(memq (car x) (cdr x))) (distinctp (cdr x))))))


;;; MJCG 17/10/88 for HOL88
;;; dml-ed function for setting an interface map from ML
;;; The old interface map is undone and returned.
;;; The code for propagating properties from a constant to its new
;;; name is pretty awful .. but it seems to work.
;;; MJCG 9/1/89 for HOL88
;;; Bugfix (bug report from David Shepherd)
;;; new and old name passed to restore-prop
;;; (previously just the new name was passed)
(defun ml-set_interface_map (new-map)
   (prog (pair map old-map source range)
      (if (null new-map) (go undo))
      (setq map (reverse new-map))
      (setq source nil)
      (setq range nil)
      loop (if (null map) (go test)) ;  unzip new-map into source and range
      (setq pair (car map))
      (setq source (cons (car pair) source))
      (setq range  (cons (cdr pair) range))
      (setq map (cdr map))
      (go loop)
      test (if (not (distinctp source)); test map single valued
         (failwith "interface map not single valued"))
      (if (not (distinctp range)); test map 1-1
         (failwith "interface map not 1-1"))
      (mapc                    ; prevent existing constants becoming hidden
         (function
            (lambda (a)
               (if (and (has-const a)
                     (not(memq a range)))
                  (failwith (concat a " would become hidden")))))
         source)
      (mapc                    ; check range consists of constants
         (function
            (lambda (v)
               (if (not(has-const v))
                  (failwith (concat v " not a constant")))))
         range)
      undo (mapc                    ; undo old interface
         (function(lambda (p) (restore-prop (car p) (cdr p))))
         %interface-map)
      (mapc                    ; set up infix and binder status
         (function(lambda (p) (put-save (car p) (cdr p))))
         new-map)
      (setq old-map %interface-map)
      (setq %interface-map new-map)
      (return old-map)))

(dml |set_interface_map| 
   1 
   ml-set_interface_map
   (((|string| |#| |string|) |list|) -> ((|string| |#| |string|) |list|)))


;;; MJCG 17/10/88 for HOL88
;;; dml-ed function for testing whether a string is a constant
(defun ml-is_constant (str) (not (null (constp str))))
(dml |is_constant| 1 ml-is_constant (|string| -> |bool|))

;;; MJCG 17/10/88 for HOL88
;;; dml-ed function for testing whether a string is an infix
(defun ml-is_infix (str) (not (null (get str `ol2))))
(dml |is_infix| 1 ml-is_infix (|string| -> |bool|))

;;; MJCG 17/10/88 for HOL88
;;; dml-ed function for testing whether a string is a binder
(defun ml-is_binder (str) (get str `binder))
(dml |is_binder| 1 ml-is_binder (|string| -> |bool|))


;;; MJCG 22/01/90 for HOL88
;;; dml-ed function for testing whether a string is a type
(defun ml-is_type (str) (get str `olarity))

(dml |is_type| 1 ml-is_type (|string| -> |bool|))

;;; MJCG 22/01/90 for HOL88
;;; dml-ed function for getting the arity of a type operator
;;; from its name

(defun ml-arity (str) 
 (let ((n (get str `olarity)))
   (if (null n) (failwith '|arity|) n)))

(dml |arity| 1 ml-arity (|string| -> |int|))

;;; MJCG 22/01/90 for HOL88
;;; dml-ed function for getting the HOL type of a constant from
;;; its name (failure if not a constant)
(defun ml-get_const_type (str) 
 (let ((val (get str `const)))
   (if (null val) 
       (failwith '|get_const_type|)
       val)))

(dml |get_const_type| 1 ml-get_const_type (|string| -> |type|))


;;; MJCG 27/10/88 for HOL88
(defun ml-is_letter (x) 
   (let ((l (exploden x)))
      (if (lessp 1 (length l))
          (failwith '|is_letter|)
          (letterp (car l)))))

(dml |is_letter| 1 ml-is_letter (|string| -> |bool|))

(defun ml-new_letter (x)
   (let ((l (exploden x)))
      (if (lessp 1 (length l))
          (failwith '|new_letter|)
          (setq %special-letters (cons (car l) %special-letters)))))

(dml |new_letter| 1 ml-new_letter (|string| -> |void|))

;;; MJCG 27/10/88 for HOL88
(defun ml-is_alphanum (x) 
   (let ((l (exploden x)))
      (if (lessp 1 (length l))
          (failwith '|is_alphanum|)
          (alphanump (car l)))))

(dml |is_alphanum| 1 ml-is_alphanum (|string| -> |bool|))

(defun ml-new_alphanum (x)
   (let ((l (exploden x)))
      (if (lessp 1 (length l))
          (failwith '|new_alphanum|)
          (setq %special-alphanums (cons (car l) %special-alphanums)))))

(dml |new_alphanum| 1 ml-new_alphanum (|string| -> |void|))


;;; MJCG 27/10/88 for HOL88
;;; Function for converting %special-table to formal for ML

;;; First a function for converting a pair (c . (m1 ... mn))
;;; to (cm1' ... cmn') where cmi' is c concatenated onto
;;; the character represented by mi.
(defun make-special-list (c l)
   (prog (l1 r)
      (setq l1 l)
      (setq r nil)
      loop (if (null l1) (return (reverse r)))
      (setq r (cons (concat c (ascii (car l1))) r))
      (setq l1 (cdr l1))
      (go loop)))

(defun ml-special_symbols ()
   (prog (lisp-table ml-table)
      (setq lisp-table #+franz (cdr %special-table) #-franz %special-table)
      (setq ml-table nil)
      loop (if (null lisp-table) (return ml-table))
      (setq
         ml-table 
         (append ml-table
            (make-special-list (car lisp-table) (cadr lisp-table))))
      (setq lisp-table (cddr lisp-table))
      (go loop)))

(dml |special_symbols| 0 ml-special_symbols (|void| -> (|string| |list|)))


;;; MJCG 27/10/88 for HOL88
;;; Add a new special symbol
;;; MJCG 29/3/89 for HOL88.1.02
;;; new special symbols added to legalconsts

(defun ml-new_special_symbol (string)
   (let ((l (exploden string)))
      (if (lessp (length l) 2)
         (failwith "new special symbol must have more than one character"))
      (if (letterp (car l))
         (failwith "special symbol can't start with a letter"))
      (if (alphanump (car l))
         (failwith "special symbol can't start with an alphanumeric"))
      (if (not (memq string legalconsts))
         (setq legalconsts (cons string legalconsts)))
      (mapl
         (function
            (lambda (x) 
               (if (cdr x)
                  (let ((str (imploden (reverse (cdr x)))))
                     (if (not (memq str legalconsts))
                        (setq legalconsts (cons str legalconsts)))
                     (put-double str (list (car x)))))))
         (reverse l)))
   nil)

(dml |new_special_symbol| 1 ml-new_special_symbol (|string| -> |void|))

;;; MJCG 7/11/88 for HOL88
;;; Commands for removing constants

(setq %hidden-consts '(const ollp ol1 ol2 olinfix binder))
;;; Test data: (mapc #'(lambda(x) (putprop 'foo t x)) %hidden-consts)
;;; MJCG 1/2/89 for HOL88.1.01
;;; Bugfix: saving of empty properties suppressed
(defun ml-hide_constant (%name)
   (if (has-const %name) 
      (prog (saved-props)
         (mapcar
            (function
               (lambda (prop) 
                  (let ((val (get %name prop)))
                     (cond 
                        (val (setq saved-props (cons (cons prop val) saved-props))
                           (remprop %name prop))))))
            %hidden-consts)
         (putprop %name saved-props 'hidden-const))
      (failwith (concat %name " not a constant that can be hidden"))))

;;; MJCG 1/2/89 for HOL88.1.01
;;; Bugfix: hidden-const property not removed in HOL88.1.00
(defun ml-unhide_constant (%name)
   (let ((props (get %name 'hidden-const)))
      (cond
         (props
            (mapc
               (function
                  (lambda (p) (if (cdr p) (putprop %name (cdr p) (car p)))))
               props)
            (remprop %name 'hidden-const)
            nil)
         (t (failwith (concat %name " is not a hidden constant"))))))

(dml |hide_constant| 1 ml-hide_constant (|string| -> |void|))
(dml |unhide_constant| 1 ml-unhide_constant (|string| -> |void|))


;;; MJCG 1/2/89 for HOL88.1.01
;;; ML function for telling whether a constant is hidden

(defun ml-is_hidden (tok) (not(null(get tok 'hidden-const))))
(dml |is_hidden| 1 ml-is_hidden (|string| -> |bool|))

;;; MJCG 1/2/90 for HOL88.1.12
;;; Function to change the escape character in strings 
;;; (default `\`, i.e. ascii 92)

(defun ml-set_string_escape (n) (prog1 escape (setq escape n)))
(dml |set_string_escape| 1 ml-set_string_escape (|int| -> |int|))


;;; Added 2.2.90 by MJCG
;;; Defines new syntax blocks 

(defun ml-new_syntax_block (beg end mlfun)
 (setq %syntax-block-enabled t)
 (putprop beg (cons mlfun end) 'syntax-block))

(dml |new_syntax_block| 
     3 
     ml-new_syntax_block 
     ((|string| |#| (|string| |#| |string|)) |->| |void|))

;;; MJCG 24.1.91
(defun ml-associate_restriction (x y)
 (putprop x y 'restrict)
 (putprop y x 'unrestrict))

(dml |associate_restriction| 
     2 
     ml-associate_restriction
     ((|string| |#| |string|) |->| |void|))
(putprop forall-tok 'RES_FORALL   'restrict)
(putprop exists-tok 'RES_EXISTS   'restrict)
(putprop select-tok 'RES_SELECT   'restrict)
(putprop lambda-tok 'RES_ABSTRACT 'restrict)

(putprop 'RES_FORALL forall-tok   'unrestrict)
(putprop 'RES_EXISTS exists-tok   'unrestrict)
(putprop 'RES_SELECT select-tok   'unrestrict)
(putprop 'RES_ABSTRACT lambda-tok 'unrestrict)


;;; MJCG 10.12.90 for Centaur: 
;;; Defines new S-expression blocks 

(defun new-sexpression-block (beg end lispfun)
 (putprop beg (cons lispfun end) 'sexpression-block))

;;; MJCG 10.12.90 for Centaur: identity function
(defun Id (x) x)

;;; MJCG 10.12.90 for Centaur: set up parse tree input
(new-sexpression-block 
 '|begin_parse_tree| 
 '|end_parse_tree| 
 '|Id|)

;;; MJCG 10.12.90 for Centaur: 
;;; Function to convert a type value to a parse tree 
;;; that will evaluate to the type
(defun ty-to-pt (ty)
 (cond ((is-vartype ty) 
        `(MK=VARTYPE ,(get-vartype-op ty)))
       (t `(MK=TYPE 
            ,(get-type-op ty) 
            ,@(mapcar (function ty-to-pt) (get-type-args ty))))))

;;; MJCG 10.12.90 for Centaur: 
;;; Function to convert a reshaped term value into the parse tree
;;; of an expression that evaluates to the value
(defun rtm-to-pt (rtm) 
 (case (car rtm)
       (var
        `(MK=TYPED (MK=VAR ,(cadr rtm)) ,(ty-to-pt(caddr rtm))))
       (const
        `(MK=TYPED (MK=CONST ,(cadr rtm)) ,(ty-to-pt(caddr rtm))))
       (comb
        `(MK=TYPED
           (MK=COMB ,(rtm-to-pt(cadr rtm)) ,(rtm-to-pt(caddr rtm)))
           ,(ty-to-pt(cadddr rtm))))
       (abs
        `(MK=TYPED
           (MK=ABS (MK=VAR ,(cadr(cadr rtm))) ,(rtm-to-pt(caddr rtm)))
           ,(ty-to-pt(cadddr rtm))))))

;;; MJCG 10.12.90 for Centaur: 
;;; Convert a reshaped term value to a quotation parse tree
(defun rtm-to-qt (rtm) `(mk-quot ,(rtm-to-pt rtm)))

;;; MJCG 10.12.90 for Centaur: set up reshaped term input
(new-sexpression-block 
 '|begin_term| 
 '|end_term| 
 '|rtm-to-qt|)
