;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-parsml.l                                          ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Functions for parsing ML                            ;;;
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
;;;   REVISION HISTORY: Original code: parsml (lisp 1.6) part of Edinburgh  ;;;
;;;                     LCF by M. Gordon, R. Milner and C. Wadsworth (1978) ;;;
;;;                     Transported by G. Huet in Maclisp on Multics, Fall  ;;;
;;;                     1981                                                ;;;
;;;                                                                         ;;;
;;; V4-1 Added primitive type obj  GH                                       ;;;
;;;      Corrected bug sec-rtn                                              ;;;
;;;                                                                         ;;;
;;; Hol version 1.12: deleted obj type : [TFM 90.09.09]                     ;;;
;;; Hol version 2.02: made preterm_handler work in CL : [MJCG 04.12.92]     ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (special %parse-tree-buffer |%preterm-flag| %nil)
   (*lexpr concat))

;;; To make sure that the preterm flag is off [TFM 91.01.28]
(eval-when (load eval)
   (setq |%preterm-flag| nil))


#+franz
(declare 
   (localf istypedec isabstypedec isconctypedec istypeabbrevdec declnchk 
      ultabstr idchk funcase-rtn bind-rtn bind-rtn1 typeabbrev-rtn next-equals 
      abstypbind-rtn conctypbind-rtn constrs-rtn constr-rtn mlt mlt1 mlt2 mlt3 
      mlt4 curr-ml-type mlt5))


(defun parseml (pl)
   (let ((lang1 'ml1)
         (lang2 'ml2)
         (langlp 'mllp)
         (atom-rtn '(mlatomr))
         (juxtlevel 1010)
         (juxt-rtn '(mljuxt arg1))
         (ibase 10)
         (parsedepth 0))
      (parse-level pl)))                        ;parseml

(defun istypedec (class)
   (memq class '(mk-deftype mk-defrectype mk-abstype mk-absrectype)))  ;istypedec

(defun isabstypedec (class)
   (memq class '(mk-abstype mk-absrectype)))   ;isabstypedec

(defun isconctypedec (class)
   (memq class '(mk-type mk-rectype)))         ;isconctypedec

(defun istypeabbrevdec (class)
   (memq class '(mk-deftype)))                 ;istypeabbrevdec

(defun declnchk (x msg)
   (if (memq (car x) declnconstrs) x (parse-failed msg)))      ;delnchk

(defun ultabstr (e)
   (or (eq (car e) 'mk-abstr)
      (and (eq (car e) 'mk-straint) (ultabstr (cadr e)))))    ;ultabstr

(defun idchk (id msg)
   (if (or (numberp id) (memq id spec-syms) (memq id rsvdwds)) 
      (parse-failed msg)
      id))                                    ;idchk

(defun eqsetup ()
   (putprop eq-sym '(appl-rtn 550 '=) 'ml2)
   (putprop eq-sym 540 'mllp))                 ;eqsetup

(defun persetup () (binop period-sym 650 '(appl-rtn 640 '|.|)))  ;persetup

(defun scolonsetup () (putprop scolon-sym 150 'mllp))  ;scolonsetup

;;; MJCG 28/10/88 for HOL88
;;; Sections commented out for HOL88
;;; MJCG 1/2/90
;;; Sections reinstated 
;;; (but intended for system use only)

(defun sec-rtn (x)
    (let ((l '||))
      (ifn (= parsedepth 1)
        (parse-failed '|sections can only be opened or closed at top level|))
      (while (not (eq token tml-sym))
          (ifn (or (eq token period-sym) (= toktyp 1))
               (parse-failed '|bad section name|))
          (setq l (concat l token))
          (gnt))
      (cons x (when l (list l)))))           ;sec-rtn

(defun mlinfix2 (x typ)
   (putprop x typ 'mlinfix)                    ;yes ??
   (binop x 450 (list (if (eq typ 'paired) 'mlinf-rtn 'mlcinf-rtn)
         (qeval x))))     ;mlinfix2

;;; MJCG 5/2/89 for HOL88
;;; Function to make the parse tree of an ML variable and, as a side effect,
;;; to take autoload action. 
;;; See lisp/f-tml.l for details of %parse-tree-buffer and
;;; computation of the autoload action.

(setq %parse-tree-buffer nil)

;;; Bugfix by MJCG for HOL88.1.02 on 22/3/89
;;; Deletion of hol-autoload property also done by code put
;;; in parse tree buffer by axiom_msg_lfn, definition_msg_lfn
;;; and theorem_msg_lfn.
;;; Bugfix by MJCG for HOL88.1.12 on 25/10/90
;;; Variable nil parsed to value of %nil to avoid obscure bugs (e.g. \().nil)
;;; Value of %nil is a non-null non-interned atom with printname `nil'
#+franz (setq %nil (maknam '(n i l)))
#-franz (setq %nil (make-symbol "nil"))
(defun mk-var-fun (x)
   (and (get x 'hol-autoload)
      (let ((v (get x 'hol-autoload)))
         (setq
            %parse-tree-buffer
            (cons (autoload v) %parse-tree-buffer))
         (ifn (eq (car v) 'eval) (remprop x 'hol-autoload))))
;;;(list 'mk-var x)) ; Old code
   (list 'mk-var (if x x %nil))) 

(defun mlinf-rtn (x)
   (list 'mk-appn (mk-var-fun x) (list 'mk-dupl arg1 (parse-level 460))))      ;mlinf-rtn

(defun mlcinf-rtn (x)
   (list 'mk-appn (list 'mk-appn (mk-var-fun x) arg1) (parse-level 460)))      ;mlcinf-rtn

(defun exfix-rtn ()
   (gnt)
   (mk-var-fun (if (eq ptoken tokflag) toklist ptoken)))       ;exfix-rtn

(defun mlatomr ()
   (cond ((memq ptoken spec-syms) 
         (parse-failed (concat ptoken '| cannot be a var|)))
      ((numberp ptoken) (list 'mk-intconst ptoken))
      ((eq ptoken tokflag) (list 'mk-tokconst (pop toklist)))
      ((eq ptoken wildcard-sym) '(mk-wildcard))
      (t (mk-var-fun ptoken))))             ;mlatomr

(defun appl-rtn (pl rn)
   (let ((x arg1)) (parse-level pl) (list 'mk-binop rn x arg1)))       ;appl-rtn

(defun lparen-rtn () 
   (cond ((eq token rparen-sym) (gnt) '(mk-empty))     ; cond needed here
      (t (check rparen-sym (parse-level 15) '|bad paren balance|))))        ;lparen-rtn

(defun while-rtn ()
   (let ((x (parse-level 30)))
      (if (eq token '|do|) (gnt) (parse-failed '|missing do after while|))
      `(mk-while ,x ,(parse-level 160)))
   );  while-rtn


(defun case-rtn ()
   (let (x)
      (setq x (parse-level 30))
      (if (eq token '|of|) (gnt)
         (parse-failed '|missing of after case|))
      (let ((c (fun-rtn)))
         `(mk-case ,x ,(if (eq (car c) 'mk-fun)
               (cadr c)              ; le case a plusieurs alternants et
               ; fun-rtn renvoie 
               ; (mk-fun (vs1.e1)..(vsn.en))
               (list (cons (cadr c) (caddr c)))))))) ;case-rtn

(defun test-rtn ()
   (prog (x1 x2 xl xt)
      loop  (setq x1 (parse-level 30))
      (setq xt token)
      (if (memq xt '(|then| |loop|)) (gnt)
         (parse-failed '|missing then or loop after if|))
      (setq x2 (parse-level 320))
      (setq xl (cons (cons (if (eq xt '|then|) 'once 'iter) (cons x1 x2)) xl))
      (when (eq token '|if|) (gnt) (go loop))
      (setq xt token)
      (cond ((memq xt '(|else| |loop|)) (gnt)
            (return (list 'mk-test
                  (reverse xl)
                  (cons (if (eq xt '|else|) 'once 'iter) (parse-level 320)))))
         (t (return (list 'mk-test (reverse xl)))))))    ;test-rtn

(defun trap-rtn (trap)
   (prog (x x1 x2 xl)
      (setq x arg1)
      loop  (setq x1 (parse-level 1020))
      (if (memq token trap-syms) (parse-failed '|missing trap body|))
      (setq x2 (parse-level 270))
      (setq xl (cons (cons trap (cons x1 x2)) xl))
      (when (memq token trap-syms)
         (setq trap
            (if (memq token (list trap-then-sym trapif-then-sym trapbind-then-sym)) 
               'once  'iter)))
      (when (memq token (list trapif-then-sym trapif-loop-sym)) 
         (gnt)
         (go loop))
      (when (memq token (list trap-then-sym trap-loop-sym))
         (gnt)
         (return (list 'mk-trap x (reverse xl) 
               (cons trap (parse-level 240)))))
      (when (memq token (list trapbind-then-sym trapbind-loop-sym))
         (gnt)
         (return (list 'mk-trap
               x
               (reverse xl)
               (cons (cons trap token) (progn (gnt) (parse-level 270))))))
      (return (list 'mk-trap x (reverse xl)))))     ;trap-rtn

(defun trapbind-rtn (trap)
   (list 'mk-trap arg1 nil
      (cons (cons trap (idchk token (concat token '| cannot be bound|)))
         (progn (gnt) (parse-level 270)))))      ;trapbind-rtn

(defun list-rtn ()
   (prog (l scolonlp)
      (setq scolonlp (get scolon-sym 'mllp))
      loop (when (eq token rbrkt-sym) 
         (gnt)
         (return (cons 'mk-list (reverse l))))
      (putprop scolon-sym 20 'mllp)
      (setq l (cons (parse-level 30) l))
      (putprop scolon-sym scolonlp 'mllp)
      (cond
         ((eq token rbrkt-sym)
            (go loop))
         (t
            (check scolon-sym arg1 '|funny list separator|)
            (go loop)))))                   ;list-rtn

(defun fun-rtn ()
   (prog (x)
      loop (setq x (cons (funcase-rtn) x))
      (when (eq token case-sym) (gnt) (go loop))
      (return (ifn (cdr x)
            `(mk-abstr ,(caar x) ,(cdar x))
            `(mk-fun ,(reverse x))))))       ;  fun-rtn

(defun funcase-rtn ()
   (let (x)
      (binop period-sym 220 '(appl-rtn 210 '|.|))    
      (setq x (parse-level 230))
      (persetup)
      (check period-sym x '|lost period in fun-case|)
      (cons x (parse-level 130))))     

(defun seq-rtn ()
   (prog (xl)
      (setq xl (list arg1))
      loop (setq xl (cons (parse-level 160) xl))
      (when (eq token scolon-sym) (gnt) (go loop))
      (return (list 'mk-seq (reverse (cdr xl)) (car xl)))))  ;seq-rtn

(defun let-rtn (class)
   (setq arg1 (bind-rtn class))
   (cond ((eq token '|in|) (gnt) (in-rtn))
      ((lessp 1 parsedepth)
         (parse-failed '|non top level decln must have in clause|))
      (t arg1)))                            ;let-rtn

(defun bind-rtn (class)
   (cond ((isabstypedec class) (abstypbind-rtn class))
      ((isconctypedec class) (conctypbind-rtn class))
      ((istypeabbrevdec class) (typeabbrev-rtn class))
      (t (cons class (bind-rtn1)))))        ; bind-rtn

(defun bind-rtn1 ()
   (let ((x nil) (y nil))
      (binop eq-sym 30 '(parse-failed '|= inside definiend|))
      (setq x (check eq-sym (parse-level 50) '|lost = in decln|))
      (eqsetup)
      (setq y (parse-level 120))
      (ifn (eq token '|and|) (list (cons x y))
         (gnt) (cons (cons x y) (bind-rtn1)))))       ;  bind-rtn1

(defun typeabbrev-rtn (class)
   (let ((dl nil))
      (block andloop
         (while t
            (let ((tyname token))
               (cond ((not (= toktyp 1))
                     (parse-failed (concat token '| not allowed as a type|)))
                  ((memq token bastypes)
                     (parse-failed (concat token '| musn't be redefined|)))
                  ((assoc-equal token dl)
                     (parse-failed (concat token '| defined more than once|))))
               (gnt)
               (next-equals)
               (push (cons tyname (mlt)) dl)
               (unless (eq token '|and|) (return-from andloop nil))
               (gnt))))
      (list class dl)))                         ;typeabbrev-rtn

(defun next-equals ()
   (unless (eq token eq-sym)
      (parse-failed '|missing = in declaration|))
   (gnt))                                      ; next-equals

;;; modified for HOL to handle ** being a token etc.
(defun abstypbind-rtn (class)
   (prog (tyargs dl)
      loop (setq tyargs nil)
      (cond ((test-list-els (exploden token) '(42))
            (gnt)
            (setq tyargs (list (vartype-rtn))))
         ((eq token lparen-sym)
            (if (eq (gnt) rparen-sym)
               (gnt)
               (go l2))))
      l1  (unless (= toktyp 1) (parse-failed '|bad type constructor|))
      (let ((tyname token))
         (gnt)
         (next-equals)
         (push (cons tyname (cons tyargs (mlt))) dl))
      (cond ((eq token '|and|) (gnt) (go loop))
         ((eq token '|with|) (gnt))
         (t (parse-failed '|missing with|)))
      (return (list class dl (bind-rtn 'mk-let)))
      l2  (ifn (test-list-els (exploden token) '(42))
         (parse-failed '|type constructor's args not variables|))
      (gnt)
      (setq tyargs (append tyargs (list (vartype-rtn))))
      (cond ((eq token comma-sym) (gnt) (go l2))
         ((eq token rparen-sym) (gnt) (go l1))
         (t (parse-failed '|bad args to type constructor|)))))   ;abstyp-rtn

;;; modified for HOL to cope with ** being a token etc.
(defun conctypbind-rtn (class)
   (prog (tyargs dl)
      loop (setq tyargs nil)
      (cond ((test-list-els (exploden token) '(42))
            (gnt) (setq tyargs (list (vartype-rtn))))
         ((eq token lparen-sym)
            (if (eq (gnt) rparen-sym) (gnt) (go l2))))
      l1   (unless (= toktyp 1) (parse-failed '|bad type constructor|))
      (let ((tyname token))
         (gnt) (next-equals)
         (push (cons tyname (cons tyargs (constrs-rtn))) dl))
      (ifn (eq token '|and|)
         (return (cons class dl))
         (gnt) (go loop))
      l2   (ifn (test-list-els (exploden token) '(42))
         (parse-failed '|type constructor's args not variables|))
      (gnt)
      (setq tyargs (append tyargs (list (vartype-rtn))))
      (cond ((eq token comma-sym) (gnt) (go l2))
         ((eq token rparen-sym) (gnt) (go l1))
         (t (parse-failed '|bad args to type constructor'|)))))  ;conctyp-rtn

(defun constrs-rtn ()
   (prog (x)
      loop (setq x (cons (constr-rtn) x))
      (when (eq token case-sym) (gnt) (go loop))
      (return (cons 'mk-construct (reverse x)))))   ; constrs-rtn

(defun constr-rtn ()
   (let ((x token))
      (cond
         ((not (eq (gnt) '|of|))
            (list x))
         (t
            (gnt)
            (cons x (mlt))))))  ;  constr-rtn

;;; MJCG 9 Nov 1992. Check for local datatypes added and previous buggy code commented out.
(defun in-rtn ()
   (list (cond ((isabstypedec (car arg1)) 'mk-ina)
;        ((isconctypedec (car arg1)) 'mk-inc)  
         ((isconctypedec (car arg1)) (parse-failed "Local concrete types not supported"))  
         ((istypeabbrevdec (car arg1)) 'mk-ind)
         (t 'mk-in))
      (declnchk arg1 '|in must follow decln|)
      (parse-level 100)))                   ;in-rtn

(defun where-rtn (class)
   (let ((e arg1))
      (list (cond ((isabstypedec class) 'mk-ina)
            ((istypedec class) 'mk-ind)
            (t 'mk-in))
         (declnchk (bind-rtn class) '|bad decln in where|)
         e)))                                ;where-rtn

(defun lamb-rtn ()
   (let (x)
      (binop period-sym 220 '(appl-rtn 210 '|.|))
      (setq x (parse-level 230))
      (persetup)
      (check period-sym x '|lost period in abstrn|)
      `(mk-abstr ,x ,(parse-level 130))))       ;lamb-rtn

;;; (defun iter-rtn (a b)
;;;     (cond ((eq (car a) 'mk-appn) (iter-rtn (cadr a)
;;;             (list 'mk-abstr
;;;                   (chkvarstr (caddr a)
;;;                            '|multiple lambda binding for var|
;;;                            '|bad var structure in iterated abstrn|)
;;;                   b)))
;;;     (t (list 'mk-abstr
;;;              (chkvarstr a
;;;                     '|multiple lambda binding for var|
;;;                     '|bad var structure in abstrn|)
;;;              b))))  ;iter-rtn

(defun assign-rtn ()
   (list 'mk-assign arg1 (parse-level 350)))   ;assign-rtn

(defun dupl-rtn ()
   (list 'mk-dupl arg1 (parse-level 370)))  ;dupl-rtn

(defun cond-rtn ()
   (prog (x1 x2 xl)
      loop (setq x1 arg1)
      (setq x2 (parse-level 30))
      (setq xl (cons (cons 'once (cons x1 x2)) xl))
      (if (eq token else-sym) (gnt) 
         (parse-failed (list 'missing else-sym))) 
      (parse-level 430)
      (cond ((eq token condl-sym) (gnt) (go loop)))
      (return (list 'mk-test (reverse xl) (cons 'once arg1)))))     ;cond-rtn

(defun failwith-rtn ()
   (list 'mk-failwith (parse-level 340)))      ;failwith-rtn

(defun mltyp-rtn ()
   (list 'mk-straint arg1 (mlt)))              ;mltyp-rtn

(defun mlt ()
   (mlt1 (mlt2 (mlt3 (mlt4)))))  ;mlt

(defun mlt1 (x)
   (cond ((eq token arrow-sym)
         (gnt) (list 'mk-funtyp x (mlt)))
      (t x)))                               ;mlt1

(defun mlt2 (x)
   (cond ((eq token sum-sym)
         (gnt) (list 'mk-sumtyp x (mlt2 (mlt3 (mlt4)))))
      (t x)))                               ;mlt2

(defun mlt3 (x)
   (cond ((eq token prod-sym)
         (gnt) (list 'mk-prodtyp x (mlt3 (mlt4))))
      (t x)))                               ;mlt3

(defun mlt4 ()
   (prog (x)
      (gnt)
      (when (eq ptoken lparen-sym)
         (setq x (cond ((eq token rparen-sym) (gnt) nil) (t (mlt5))))
         (go l))
      (setq x (list (curr-ml-type)))
      l    (cond ((or (not (= toktyp 1)) (memq token rsvdwds))
            (cond ((and x (null (cdr x))) (return (car x)))
               (t (parse-failed '|missing type constructor|))))
         (t (gnt)))
      (setq x (cond ((eq ptoken '|list|) (list (cons 'mk-listyp x)))
            (t (list (cons 'mk-consttyp (cons ptoken x))))))
      (go l)))                      ;mlt4

;;; modified for HOL to deal with ** being a token etc

(defun curr-ml-type ()
   (case ptoken
      (|int| '(mk-inttyp))
;;;   (|obj| '(mk-objtyp))		[TFM 90.09.09]
      (|thm| '(mk-thmtyp))
      (|void| '(mk-nulltyp))
      (|bool| '(mk-booltyp))
      (|type| '(mk-typetyp))
      (|term| '(mk-termtyp))
      (|form| '(mk-formtyp))
      ((|string| |token| |tok|) '(mk-toktyp))
      (|*| (list 'mk-vartyp (vartype-rtn)))
      (t (cond ((test-list-els (exploden ptoken) '(42))
               (list 'mk-vartyp (vartype-rtn)))
            ((= ptoktyp 1) (list 'mk-consttyp ptoken))
            (t (parse-failed 
                  (concat ptoken '| is not allowed in a type|)))))))

(defun mlt5 ()
   (prog (x)
      (setq x (list (mlt)))
      loop (cond ((eq token rparen-sym) (gnt) (return x))
         ((eq token comma-sym) (gnt) (setq x (append x (list (mlt)))) (go loop))
         (t (parse-failed '|missing separator or terminator in type|))))
   )                                           ;mlt5

(defun mljuxt (x)
   (list 'mk-appn x (parse-level 1020)))       ;mljuxt

;;; quotations
;;; in OL digits are considered letters, there should be no numbers
;;; parse-ol sets a flag which the lexer consults when it sees a digit
;;; however stupid parsing algorithm looks too far ahead, so the first
;;; variable in a quotation may be read as a number
;;; the first line fixes this.   It handles "1==2" but not "1a==2"
;;; (defun cnr-rtn ()
;;;    (when (numberp token) (setq token (imploden (exploden token))))
;;;    (check endcnr-sym
;;;       (case token
;;;          (|:| (gnt) (list 'mk-tyquot (olt)))
;;;          (t (list 'mk-quot (parse-ol))))
;;;       '|cannot find end of quotation|))    ;cnr-rtn

(defun cnr-rtn ()
   (when (numberp token) (setq token (imploden (exploden token))))
   (check endcnr-sym
      (case token
         (|:| (gnt) (list 'mk-tyquot (olt)))
         (t (if |%preterm-flag|
                `(mk-appn 
                  (mk-var |preterm_handler|)
                  ,(term-to-preterm (parse-ol)))
                (list 'mk-quot (parse-ol)))))
      '|cannot find end of quotation|))

;;; Convert a parse tree of a term to a parse tree for a pre-term
;;; const, var, etc renamed to preterm_const, preterm_var, etc
;;; [TFM 90.11.19] 

(defun term-to-preterm (pt)
  (case (car pt)
   (MK=CONST    `(mk-appn (mk-con |preterm_const|) (mk-tokconst ,(cadr pt))))
   (MK=VAR      `(mk-appn (mk-con |preterm_var|) (mk-tokconst ,(cadr pt))))
   (MK=COMB     `(mk-appn 
                  (mk-con |preterm_comb|)
                  (mk-dupl 
                    ,(term-to-preterm (cadr pt))
                    ,(term-to-preterm (caddr pt)))))
   (MK=ABS      `(mk-appn 
                  (mk-con |preterm_abs|)
                  (mk-dupl 
                    ,(term-to-preterm (cadr pt))
                    ,(term-to-preterm (caddr pt)))))
   (MK=TYPED    `(mk-appn 
                  (mk-con |preterm_typed|)
                  (mk-dupl 
                    ,(term-to-preterm (cadr pt))
                    (mk-tyquot ,(caddr pt)))))
   (MK=ANTIQUOT `(mk-appn (mk-con |preterm_antiquot|) ,(cadr pt)))))




(eval-when (load)
   (setq lang1 'ml1)
   (setq lang2 'ml2)
   (setq langlp 'mllp)
   (setq metaprec 20))

;;; MJCG 19/10/88 for HOL88
;;; Sections commented out from HOL88
;;; MJCG 1/2/90
;;; Sections reinstated 
;;; (but intended for system use only)
(eval-when (load)
   (unop '|begin_section| '(sec-rtn 'mk-begin))
   (unop '|end_section| '(sec-rtn 'mk-end)))

;;; MJCG for HOL88 30/1/89
;;; Parser hack to ensure top_print is only applied at top level
;;; (see lisp/f-writml.l)

;;; MJCG 17/5/92 bugfix: eta-convert argument to top_print 
;;; (avoids obscure bug discovered by TFM).
;;; Bound variable of dummy eta-conversion is %top_print-dummy.
(eval-when (load)
   (unop
      '|top_print|
      '(cond ((greaterp parsedepth 1)
            (parse-failed
               "top_print can only be applied at the top level of ML"))
         ((eq token '|;;|)
            (parse-failed "missing argument to top_print"))
         (t `(mk-appn 
              (mk-var |top_print|) 
              (mk-abstr
               (mk-var %top_print-dummy)
               (mk-appn ,(parse-level 0) (mk-var %top_print-dummy))))))))

(eval-when (load)
   (unop tml-sym '(parse-failed '(stuff missing)))
   (unop '|true| ''(mk-boolconst t))
   (unop '|false| ''(mk-boolconst nil))
   (unop '|fail| ''(mk-fail))
   (unop exfix-sym '(exfix-rtn))
   (unop lparen-sym '(lparen-rtn))
   (unop '|do| '(list 'mk-unop '|do| (parse-level 410)))
   (unop '|if| '(test-rtn))
   (unop '|while| '(while-rtn))
   (unop '|loop| '(list 'mk-test nil (cons 'iter (parse-level 320))))
   (unop '|else| '(list 'mk-test nil (cons 'once (parse-level 320))))
   (bnop trap-then-sym
      '(list 'mk-trap arg1 nil (cons 'once (parse-level 240))))
   (bnop trap-loop-sym
      '(list 'mk-trap arg1 nil (cons 'iter (parse-level 240))))
   (bnop trapif-then-sym '(trap-rtn 'once))
   (bnop trapif-loop-sym '(trap-rtn 'iter))
   (bnop trapbind-then-sym '(trapbind-rtn 'once))
   (bnop trapbind-loop-sym '(trapbind-rtn 'iter))
   (unop lbrkt-sym '(list-rtn))
   (bnop scolon-sym '(seq-rtn))
   (unop '|let| '(let-rtn 'mk-let))
   (unop '|letrec| '(let-rtn 'mk-letrec))
   (unop '|letref| '(let-rtn 'mk-letref))
   (unop '|deftype| '(let-rtn 'mk-deftype))
   (unop '|lettype| '(let-rtn 'mk-deftype))
   (unop '|typeabbrev| '(let-rtn 'mk-deftype))
   (unop '|abstype| '(let-rtn 'mk-abstype))
   (unop '|absrectype| '(let-rtn 'mk-absrectype))
   (unop '|type| '(let-rtn 'mk-type))
   (unop '|rectype| '(let-rtn 'mk-rectype))
   (bnop '|in| '(in-rtn))
   (bnop '|where| '(where-rtn 'mk-let))
   (bnop '|whererec| '(where-rtn 'mk-letrec))
   (bnop '|whereref| '(where-rtn 'mk-letref))
   (bnop '|wheretype| '(where-rtn 'mk-deftype))
   (bnop '|whereabstype| '(where-rtn 'mk-abstype))
   (bnop '|whereabsrectype| '(where-rtn 'mk-absrectype))
   (unop lam-sym  '(lamb-rtn))
   (unop '|fun| '(fun-rtn))
   (unop '\| '(fun-rtn))
   (unop '|case| '(case-rtn))
   (bnop assign-sym '(assign-rtn))
   (bnop comma-sym '(dupl-rtn))
   (bnop condl-sym '(cond-rtn))
   (bnop disj-sym '(appl-rtn 470 '|%or|))
   (bnop conj-sym '(appl-rtn 510 '|%&|))
   (unop '|failwith| '(failwith-rtn))
   (unop '|not| '(list 'mk-unop '|not| (parse-level 530)))
   (bnop eq-sym '(appl-rtn 550 eq-sym))
   (bnop lt-sym '(appl-rtn 610 lt-sym))
   (bnop gt-sym '(appl-rtn 570 gt-sym))
   (bnop conc-sym '(appl-rtn 620 conc-sym))
   (bnop period-sym '(appl-rtn 640 period-sym))
   (bnop plus-sym '(appl-rtn 710 plus-sym))
   (bnop mns-sym '(appl-rtn 670 mns-sym))
   (unop mns-sym '(list 'mk-unop '%- (parse-level 760)))
   (bnop mul-sym '(appl-rtn 750 mul-sym))
   (bnop div-sym '(appl-rtn 730 div-sym))
   (bnop colon-sym '(mltyp-rtn))
   (unop cnr-sym '(cnr-rtn)))

(eval-when (load)
   (putprop tml-sym 0 langlp)
   (putprop '|of| 20 langlp)
   (putprop rparen-sym 10 langlp)
   (putprop '|eqindec| 30 langlp)
   (putprop '|in| 60 langlp)
   (putprop '|and| 70 langlp)
   (putprop '|perinlam| 140 langlp)
   (putprop scolon-sym 150 langlp)
   (putprop rbrkt-sym 20 langlp)
   (putprop '|where| 150 langlp)
   (putprop '|whereref| 150 langlp)
   (putprop '|whererec| 150 langlp)
   (putprop '|wheretype| 150 langlp)
   (putprop '|whereabstype| 150 langlp)
   (putprop '|whereabsrectype| 150 langlp)
   (putprop '|perinvs| 220 langlp)
   (putprop trap-then-sym 250 langlp)
   (putprop trap-loop-sym 250 langlp)
   (putprop trapif-then-sym 260 langlp)
   (putprop trapif-loop-sym 260 langlp)
   (putprop trapbind-then-sym 260 langlp)
   (putprop trapbind-loop-sym 260 langlp)
   (putprop '|loop| 20 langlp)
   (putprop '|else| 20 langlp)
   (putprop '|then| 20 langlp)
   (putprop '|if| 310 langlp)
   (putprop '|while| 310 langlp)
   (putprop '|do| 20 langlp)
   (putprop '|case| 310 langlp)
   (putprop assign-sym 360 langlp)
   (putprop comma-sym 400 langlp)
   (putprop case-sym 20 langlp)
   (putprop else-sym 20 langlp)
   (putprop condl-sym 440 langlp)
   (putprop '|mlinfix| 450 langlp)
   (putprop '|or| 500 langlp)
   (putprop conj-sym 520 langlp)
   (putprop gt-sym 560 langlp)
   (putprop lt-sym 600 langlp)
   (putprop eq-sym 540 langlp)
   (putprop conc-sym 630 langlp)
   (putprop period-sym 650 langlp)
   (putprop mns-sym 660 langlp)
   (putprop plus-sym 700 langlp)
   (putprop div-sym 720 langlp)
   (putprop mul-sym 740 langlp)
   (putprop colon-sym 770 langlp)
   (putprop '|primary| 1010 langlp))
