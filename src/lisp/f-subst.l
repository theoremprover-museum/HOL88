;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-subst.l                                           ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Substitution functions                              ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-franz.l (or f-cl.l), f-constants.l, f-macro.l,    ;;;
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
;;;   REVISION HISTORY: Original code: ol2 (lisp 1.6) part of Edinburgh LCF ;;;
;;;                     by M. Gordon, R. Milner and C. Wadsworth   (1978)   ;;;
;;;                     Transported by G. Huet in Maclisp on Multics, Fall  ;;;
;;;                     1981                                                ;;;
;;;                                                                         ;;;
;;; V2.2 : new-exit instead of err                                          ;;;
;;;                                                                         ;;;
;;; V4 : rewrote substitution, re-arranged arguments of substoccs           ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (include "lisp/f-ol-rec"))


#+franz
(declare
   (localf alpha-fm vars-fm addvar occrec subst-fm find-sub quant-sub
      abs-sub varfilter choose-var all-frees2 prime unprime))


;;; *********************************************

;;; No formulas in HOL: paired_aconv_form deleted	[TFM 90.04.19]
;;; (dml |paired_aconv_form| 2 alphaconv ((|form| |#| |form|) -> |bool|))


;;; ---------------------------------------------------------------
;;; This paired function later gets REDEFINED to be a curried 
;;; function (in ml/ml-hol-syn.ml)
;;; Used to be called "paired_aconv_term".
;;;  --------------------------------------------------------------

(dml |aconv| 2 alphaconv ((|term| |#| |term|) -> |bool|))


(defun alphaconv (ob1 ob2)
   (or (#+franz eq #-franz eql ob1 ob2)
      (let ((%varpairs nil))
         (alpha-fm ob1 ob2))))  ;alphaconv


;;; alpha-convertability of formulas (also passes on terms)
(defun alpha-fm (fm1 fm2)
   (and (eq (form-class fm1)(form-class fm2))
      (case (form-class fm1)
         ((forall exists)
            (let ((%varpairs (cons (cons(get-quant-var fm1)(get-quant-var fm2))
                        %varpairs)))
               (alpha-fm (get-quant-body fm1)(get-quant-body fm2))))
         ((conj disj imp) ; iff deleted [TFM 90.01.20]
            (and (alpha-fm (get-left-form fm1)(get-left-form fm2))
               (alpha-fm (get-right-form fm1)(get-right-form fm2))))
         (pred (and (eq (get-pred-sym fm1) (get-pred-sym fm2))
               (alpha-tm (get-pred-arg fm1)(get-pred-arg fm2))))
         (t (alpha-tm fm1 fm2))
         )))  ;alpha-fm


;;; alpha-convertability of terms
(defun alpha-tm (tm1 tm2)
   (and (eq (term-class tm1) (term-class tm2))
      (case (term-class tm1)
         (const (eq tm1 tm2))   ; assumes sharing of constants
         (var    ; if either bound then bindings must match
            ; free case assumes variables are shared
            (let ((p1 (assoc-equal tm1 %varpairs))
                  (p2 (revassq tm2 %varpairs)))
               (if (or p1 p2)
                  (#+franz eq #-franz eql p1 p2) (eq tm1 tm2))))
         (abs
            (let ((%varpairs (cons (cons(get-abs-var tm1)(get-abs-var tm2))
                        %varpairs)))
               (alpha-tm (get-abs-body tm1)(get-abs-body tm2))))
         (comb (and (alpha-tm (get-rator tm1)(get-rator tm2))
               (alpha-tm (get-rand tm1)(get-rand tm2))))
         (t (lcferror 'alpha-tm))
         )))  ;alpha-tm



;;; *********************************************

;;; term_frees renamed to be frees [TFM 90.06.04]
;;; (dml |term_frees| 1 freevars (|term| -> (|term| |list|)))

(dml |frees| 1 freevars (|term| -> (|term| |list|)))

;;; Deleted: formulas not used in HOL  [TFM 90.05.27]
;;; (dml |form_frees| 1 freevars (|form| -> (|term| |list|)))

(defun freevars (ob)
   (let ((%all nil)(%vars nil))
      (vars-fm ob nil)
      (nreverse %vars)))  ;freevars


;;; term_vars renamed to be vars [TFM 90.06.04]
;;; (dml |term_vars| 1 allvars (|term| -> (|term| |list|)))

(dml |vars| 1 allvars (|term| -> (|term| |list|)))

;;; Deleted: formulas not used in HOL  [TFM 90.06.27]
;;; (dml |form_vars| 1 allvars (|form| -> (|term| |list|)))



(defun allvars (ob)
   (let ((%all t)(%vars nil))
      (vars-fm ob nil)
      (nreverse %vars)))  ;allvars


;;; record the variables in a formula (or term)
;;; if %all then record all variables, even those bound but never used
;;; else record only free variables
(defun vars-fm (fm bvars)
   (case (form-class fm)
      ((forall exists)
         (if %all (addvar (get-quant-var fm)))
         (vars-fm (get-quant-body fm) (cons (get-quant-var fm) bvars)))
      ((conj disj imp) ; iff deleted [TFM 90.01.20]
         (vars-fm (get-left-form fm) bvars) (vars-fm (get-right-form fm) bvars))
      (pred (vars-tm (get-pred-arg fm) bvars))
      (t (vars-tm fm bvars))))  ;vars-fm


;;; record all (free) variables in a term
(defun vars-tm (tm bvars)
   (case (term-class tm)
      (const)
      (var (ifn (memq tm bvars) (addvar tm)))
      (abs (if %all (addvar (get-abs-var tm)))
         (vars-tm (get-abs-body tm) (cons (get-abs-var tm) bvars)))
      (comb (vars-tm (get-rator tm) bvars) (vars-tm (get-rand tm) bvars))
      (t (lcferror 'vars-tm))))  ;vars


;;; record a variable if not seen already
;;; relies on sharing of variables
(defun addvar (v)
   (ifn (memq v %vars) (push v %vars)))  ;addvar



;;; *********************************************

;;; ---------------------------------------------------------------
;;; This paired function later gets REDEFINED to be a curried 
;;; function (in ml/ml-hol-syn.ml). Used to be called "paired_subst_term".
;;;  --------------------------------------------------------------

(dml |subst| 2 hol-substitute
   ((((|term| |#| |term|) |list|) |#| |term|) -> |term|))

;;; No formulas in HOL: paired_subst_form deleted	[TFM 90.04.19]
;;; (dml |paired_subst_form| 2 hol-substitute
;;;   ((((|term| |#| |term|) |list|) |#| |form|) -> |form|))

;;; ---------------------------------------------------------------
;;; This paired function later gets REDEFINED to be a curried function 
;;; (in ml/ml-hol-syn.ml). Used to be called "paired_subst_occs_term".
;;;  --------------------------------------------------------------

(dml |subst_occs| 3 substitute-occs
   ((((|int| |list|) |list|) |#| (((|term| |#| |term|) |list|) |#| |term|))
      -> |term|))

;;; No formulas in HOL: paired_subst_occs_form deleted	[TFM 90.04.19]
;;;(dml |paired_subst_occs_form| 3 substitute-occs
;;;   ((((|int| |list|) |list|) |#| (((|term| |#| |term|) |list|) |#| |form|))
;;;      -> |form|))


(defun hol-substitute (jobl ob)
   (let ((%newvars nil))
      (subst-fm (mapcan #'(lambda (job) (substrec t job)) jobl) ob))
   )   ; hol-substitute


(defun substitute-occs(occsl jobl ob)
   (let ((%newvars nil))
      (ifn (= (length occsl) (length jobl))
         (throw-from evaluation 'subst))
      (subst-fm(mapcan 'substrec occsl jobl) ob))
   )   ; substitute-occs


(eval-when (compile)
   (defmacro get-term1 (sr) `(car ,sr))
   (defmacro get-term2 (sr) `(cadr ,sr))
   (defmacro get-occs (sr) `(caddr ,sr))
   (defmacro get-frees1 (sr) `(cadddr ,sr))
   (defmacro get-frees2 (sr) `(car (cddddr ,sr))) ;gh
   (defmacro put-occs (sr val) `(rplaca (cddr ,sr) ,val)))


;;; preprocess a substitution
;;; check types, compute free variables, set up occurrence lists
;;; return a record holding this info
;;; return nil if substitution is null
;;; for use with mapcan (NOT mapcar!)
(defun substrec(occs job)
   (let ((tm2 (car job)) (tm1 (cdr job)))
      (ifn (equal (get-type tm1) (get-type tm2))
         (throw-from evaluation 'subst))
      (ifn (eq tm2 tm1)
         (list (list tm1 tm2 (occrec 1 occs) (freevars tm1) (freevars tm2)))))
   )   ; substrec


;;; convert an ascending list of positive integers
;;; into a list of nil's, with t's interspersed where the integers indicate
(defun occrec(n l)
   (cond
      ((atom l) (twistlist l))      ; extend out to infinity
      ((greaterp n (car l)) (throw-from evaluation 'subst))  ; not ascending
      ((= n (car l)) (cons t (occrec (add1 n)(cdr l))))
      ((cons nil (occrec (add1 n) l)))
      ))


;;; substitute in a formula (or term)
(defun subst-fm (srl fm)
   (cond ((and (null srl) (null %newvars)) fm)
      ((case (form-class fm)
            ((forall exists) (quant-sub srl fm))
            ((conj disj imp) ; iff deleted [TFM 90.01.21]
               (make-conn-form (get-conn fm)
                  (subst-fm srl (get-left-form fm))
                  (subst-fm srl (get-right-form fm))))
            (pred (make-pred-form (get-pred-sym fm)
                  (subst-tm srl (get-pred-arg fm))))
            (t (subst-tm srl fm))))))  ;subst-fm


;;; substitute in a term
(defun subst-tm (srl u)
   (cond ((and (null srl) (null %newvars)) u)
      ((find-sub srl u))
      ((case (term-class u)
            (const u)
            (var (or (assq1 u %newvars) u))     ; rename bound variable
            (abs (abs-sub srl u))
            (comb (make-comb (subst-tm srl (get-rator u))
                  (subst-tm srl (get-rand u)) (get-type u)))
            (t (lcferror 'subst-tm))))))  ;subst-tm


;;; base case of substitution
;;; if match found, step down its occurrence list
;;;   and return non-nil even if this occurrence is not included
;;; return nil if no match
(defun find-sub(srl u)
   (block found
      (mapc #'(lambda (sr)
            (let ((tm1 (get-term1 sr)) (tm2 (get-term2 sr)))
               (if (alphaconv u tm1)       ; match found
                  (let ((occs (get-occs sr)))
                     (put-occs sr (cdr occs))
                     (return-from found (if (car occs) tm2 u))))))
         srl)
      nil         ; indicate not found
      ))    ; find-sub



;;; substitution through a bound variable
;;;   if var could be introduced, then rename it

;;; Old version with bug discovered by TFM
;;;(defun quant-sub (srl fm)
;;; (let ((var (get-quant-var fm)) (body (get-quant-body fm)))
;;;  (let ((new-srl (varfilter var srl)))
;;;    (let ((new-var (choose-var new-srl var body)))
;;;        (let ((%newvars (if (eq new-var var) %newvars
;;;                          (cons (cons var new-var) %newvars))))
;;;        (make-quant-form (get-quant fm)
;;;            new-var (subst-fm new-srl body))))))
;;; )    ; quant-sub

;;; New version with bugfix by LCP (18 June 87)

(defun quant-sub (srl fm)
   (let ((var (get-quant-var fm)) (body (get-quant-body fm)))
      (let ((new-srl (varfilter var srl)))
         (let ((new-var (choose-var new-srl var body)))
            (let ((%newvars (cons (cons var new-var) %newvars)))
               (make-quant-form (get-quant fm)
                  new-var (subst-fm new-srl body))))))
   )    ; quant-sub


;;; substitute through a lambda-abstraction

;;; Old version with bug discovered by TFM
;;;(defun abs-sub (srl tm)
;;; (let ((var (get-abs-var tm)) (body (get-abs-body tm)))
;;;  (let ((new-srl (varfilter var srl)))
;;;    (let ((new-var (choose-var new-srl var body)))
;;;        (let ((%newvars (if (eq new-var var) %newvars
;;;                          (cons (cons var new-var) %newvars))))
;;;        (make-abs new-var (subst-tm new-srl body) (get-type tm))))))
;;; )    ; abs-sub

;;; New version with bugfix by LCP (18 June 87)

(defun abs-sub (srl tm)
   (let ((var (get-abs-var tm)) (body (get-abs-body tm)))
      (let ((new-srl (varfilter var srl)))
         (let ((new-var (choose-var new-srl var body)))
            (let ((%newvars (cons (cons var new-var) %newvars)))
               (make-abs new-var (subst-tm new-srl body) (get-type tm))))))
   )    ; abs-sub


;;; filter (from the srl) all rewrites where the var is free
;;; since substitution replaces only free terms
(defun varfilter (var srl)
   (if srl
      (if (memq var (get-frees1 (car srl)))
         (varfilter var (cdr srl))
         (cons (car srl) (varfilter var (cdr srl))))
      ))   ; varfilter


;;; choose a new bound variable if old one is mentioned in rewrites
;;; RECENT BUG FIX -- now considers any new variables being introduced
;;; as a result of outer name clashes
;;; #let tm = "\x':*.f (y:*,z:*) (\x:*.(g (x',x,y,z) : tr) ):tr";;
;;; #let tm1 = subst_term ["x'","z"; "x","y"] tm;;
;;; SHOULD GIVE  tm1 = "\x''.f(x,x')(\x'''.g(x'',x''',x,x'))" : term
(defun choose-var (srl var body)
   (let ((frees2 (append (mapcar #'cdr %newvars) (all-frees2 srl))))
      (if (memq var frees2)
         (ml-variant (nconc (allvars body) frees2) var)
         var)))


;;; union of all frees2 fields of srl
(defun all-frees2 (srl)
   (if srl (append (get-frees2 (car srl)) (all-frees2 (cdr srl))))
   )    ; all-frees2



;;; *********************************************


;;; ---------------------------------------------------------------
;;; This paired function later gets REDEFINED to be a curried 
;;; function (in ml/ml-hol-syn.ml). Used to be called 
;;; "paired_term_freein_term".
;;;  --------------------------------------------------------------

(dml |free_in| 2  freein-tm ((|term| |#| |term|) -> |bool|))

;;; No formulas in HOL: paired_term_freein_form deleted	[TFM 90.04.19]
;;; (dml |paired_term_freein_form| 2  freein-fm ((|term| |#| |form|) -> |bool|))
;;; No formulas in HOL: paired_term_freein_form deleted	[TFM 90.04.19]
;;; (dml |paired_form_freein_form| 2  freein-fm ((|form| |#| |form|) -> |bool|))

;;; in the current logic, formulas cannot occur in terms
;;; but in general, all four cases are reasonable,
;;; and it is convenient to define freein in terms of "objects",
;;; where objects are either terms or formulas.




;;; see if the ob is free in a formula (or term)
(defun freein-fm (ob fm)
   (or (alphaconv ob fm)
      (case (form-class fm)
         ((forall exists)
            (and (not (freein-fm (get-quant-var fm) ob))
               (freein-fm ob (get-quant-body fm))))
         ((conj disj imp) ; iff deleted [TFM 90.01.20]
            (or (freein-fm ob (get-left-form fm))
               (freein-fm ob (get-right-form fm))))
         (pred (freein-tm ob (get-pred-arg fm)))
         (t (freein-tm ob fm))
         )))  ;freein-fm



;;; see if the ob is free in a term
(defun freein-tm (ob tm)
   (or (alphaconv ob tm)
      (case (term-class tm)
         ((var const) nil)
         (abs (and (not (freein-tm (get-abs-var tm) ob))
               (freein-tm ob (get-abs-body tm))))
         (comb (or (freein-tm ob (get-rator tm)) (freein-tm ob (get-rand tm))))
         (t (lcferror 'freein-tm))
         )))  ;freein-tm




;;; *********************************************


;;; ---------------------------------------------------------------
;;; PAIRED variant function later gets REDEFINED to be curried 
;;; in hol-syn.ml
;;;  --------------------------------------------------------------

(dml |variant| 2 ml-variant (((|term| |list|) |#| |term|) -> |term|))


;;; prime v until its name is neither a constant's nor one of the vl
(defun ml-variant (vl v)
   (ifn (memq (term-class v) '(var const)) (throw-from evaluation 'variant) )
   (let ((tokl  (var-name-list vl 'variant)))
      (mk_realvar (variant-name tokl (get-var-name v)) (get-type v)))
   )  ;ml-variant


;;; get the names of the list of variables
(defun var-name-list (vl failtok)
   (mapcar #'(lambda (tm) (if (is-var tm) (get-var-name tm)
            (throw-from evaluation failtok)))
      vl))                   ; var-name-list


;;; prime tok until it is neither a constant's name nor one of the tokl
;;; no longer strips primes first, that caused problems in ML programs
;;; MJCG 1/2/89 for HOL88.1.01
;;; Hidden constants no longer primed
(defun variant-name (tokl tok)
   (while (or (memq tok tokl)
         (and (constp tok) (not (get tok 'hidden-const))))
      (setq tok (prime tok)))
   tok)  ; variant-name


(defun prime (tok) (concat tok '|'|))  ;prime


;;; strip all primes from tok (including those inside)
(defun unprime (tok) (imploden (delq #/' (exploden tok))))  ;unprime


