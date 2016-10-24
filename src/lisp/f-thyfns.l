;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-thyfns.l                                          ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Functions relating to theories                      ;;;
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
;;;   REVISION HISTORY: Original code: thyfns (lisp 1.6) part of Edinburgh  ;;;
;;;                     LCF by M. Gordon, R. Milner and C. Wadsworth (1978) ;;;
;;;                     Transported by G. Huet in Maclisp on Multics, Fall  ;;;
;;;                     1981                                                ;;;
;;;                                                                         ;;;
;;; V1.4 : Arbitrary non-empty tokens allowed as names of axioms & theorems ;;;
;;;        Theories represented by a lisp structure %theorydata rather than ;;;
;;;        by a text file. Structure of drafts and theories changed.        ;;;
;;;        Functions axioms types operators infixes parents added.          ;;;
;;;                                                                         ;;;
;;; V1.3 : newinfix replaces newolinfix and newolcinfix. The authorized     ;;;
;;;        constants/infixes symbols declared in legalconsts. Feb 82, GH    ;;;
;;;                                                                         ;;;
;;; V1.2 : Files names and headers changed, Dec. 1981, G.Huet               ;;;
;;;                                                                         ;;;
;;; V2.2 : exit instead of err                                              ;;;
;;;        exit if error while loading                                      ;;;
;;;                                                                         ;;;
;;; V4:    deleted closeup and dischall, which are better implemented in ML ;;;
;;;                                                                         ;;;
;;; V4.1 : timestamps  GH                                                   ;;;
;;;                                                                         ;;;
;;; V4.2 : removed obsolete special declarations.                           ;;;
;;;        removed message functions;  failure tokens include messages.     ;;;
;;;        reduced use of %theorydata and %theorems.                        ;;;
;;;        theory cache,                                                    ;;;
;;;        extend_theory, new_theory, close_theory replace make_theory      ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;  Sets Manifests:  dash olreserved legalconsts


;;;  Sets Globals:  %current, %kind, %ancestry
;;;                 %theorydata, %theorems

;;;  Specials:  %e, %newtypes, %newconsts

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (include "lisp/f-ol-rec"))


#+franz
(declare 
   (localf defaultp currentp ancestorp add-ancestor not-theory not-draft 
      not-init neg-arity polym not-ancestor clash bad-or-clash add-to-chapter 
      replace-chapter get-chapter update-thm load-theory-parent 
      basic-update-cache update-cache open-thy-file thy-read load-theorydata 
      load-theorems load-thy-threms get-thy-tree get-parent remty remcon 
      add-const-pred save-axiom-thm get-axiom-thm abs-thm extract-axioms-thms 
      flush-draft write-thy-file abs-form abs-term cond-abs-type abs-type 
      encode-thm encode-form encode-term encomb new-sharetype encode-type))


;;; initialise manifests outside of initial%load

(setq dash '|-|)
(setq olreserved nil)   ;NEW used to contain ^
(setq legalconsts '(|/| |#| |*| |+| |-| |<| |=| |>| |?| |@|))
;NEW used to be same as
;infixables in LCF    now ^ forbidden ~ { } % allowed
(setq %loading-thy nil)


(eval-when (load)
   (when initial%load                              ;  Globals
      (setq %current '-)                            ;  Settings to enable
      (setq %kind 'init)                            ;  pplamb in system load
      (setq %newconsts nil)
      (setq %newtypes nil)  
      (setq %ancestry nil)
      (setq %thy-cache nil)))

(defun defaultp (tok) (eq tok dash))

(defun currentp (tok) (eq tok %current))  ;currentp

(defun ancestorp (tok) (member-equal tok %ancestry))  ;ancestorp

(defun add-ancestor (tok)
   (ifn (ancestorp tok) (push tok %ancestry)))  ;add-ancestor

;;; Functions that produce error messages
;;; if no error, they return nil

;;; most are called by the theory extension functions (new_constant, ...)
;;; which create new theories (where %loading-thy is nil)
;;; and load existing ones (where %loading-thy is t)

(defun not-theory ()
   (ifn (eq %kind 'theory) "only allowed in a theory"))  ;not-theory

;;; MJCG 22/11/88 for HOL88
;;; ML function to tell if one is in draft mode
(defun ml-draft_mode () (eq %kind 'draft))
(dml |draft_mode| 0 ml-draft_mode (|void| |->| |bool|))

(defun not-draft ()
   (ifn (or %loading-thy (eq %kind 'draft))
      "Legal only in drafts")
   )  ;not-draft

(defun not-init ()
   (ifn (eq %kind 'init) "only allowed in new session"))  ;not-init

(defun neg-arity (n tok)
   (if (lessp n 0) (catenate tok " has negative arity")))  ;neg-arity

(defun polym (tok ty)
   (if (opoly ty) (catenate tok " would be polymorphic")))  ;polym

(defun not-ancestor (tok)
   (ifn (ancestorp tok) (catenate tok " is not an ancestor")))  ;not-ancestor


;;; check if the token is acceptable for the given sort
(defun bad (sort tok)
   (ifn %loading-thy
      (if (case sort
            (theory (not (filetokp sort tok)))
            (type  (or (member-equal tok olreserved) (not (idenp tok))))
            ((constant infix) 
               (or (member-equal tok olreserved)
                  (not (or (eq tok '|()|) (idenp tok) (nump tok)
                        (member-equal tok legalconsts)))))
            (t nil))
         (catenate tok " cannot be " sort " token")))
   )  ;bad

;;; MJCG 22/11/88 for HOL88
;;; ML function to test whether a string could be (or is) a constant
;;; Bugfix 3/12/90 by MJCG for HOL88.1.12. TFM period bug fixed.
(defun ml-allowed_constant (str)
   (not (or (eq str period-sym) (bad 'constant str))))

(dml |allowed_constant| 1 ml-allowed_constant (|string| -> |bool|))

;;; check that the given token has not already been used for the sort
;;; must be performed when either loading or creating a theory
(defun clash (sort tok)
   (cond
      ((case sort
            (theory (fileexists 'theorydata tok))
            (type (get tok 'olarity))
            ((constant infix)
               (setq sort
                  (cond ((get tok 'olinfix) 'infix)
                     ((get tok 'const) 'constant)))))
         (catenate tok " clashes with existing " sort)))
   )  ;clash


(defun bad-or-clash (sort tok)
   (or (bad sort tok) (clash sort tok)))  ;bad-or-clash


(dml |new_theory| 1 ml-new_theory (|string| -> |void|))

;;; Set up lists to hold data for a draft
;;;   Since structures are modified destructively, "copy" is called
(defun ml-new_theory (thy)
   (cond-failwith "new_theory" (bad-or-clash 'theory thy))
   (flush-draft)
   (setq %newconsts nil)
   (setq %newtypes nil)  
   (setq %date (clock))
   (setq %theorydata
      (copy-tree `((parents . ,(ifn (eq %kind 'init) (list %current)))
            (types) (nametypes) (operators)
            (paired-infixes) (curried-infixes) (predicates)
            (version . ,%version)
            (stamp . ,%date))))  ;stamp with draft-setting time
   (setq %theorems (copy-tree '((sharetypes 0) (axiom) (fact))))
   (setq %kind 'draft)
   (add-ancestor thy)
   (setq %current thy)
   )  ;ml-new_theory


(dml |close_theory| 0 ml-close_theory (|void| -> |void|))

;;; terminate draft mode and write theory file
(defun ml-close_theory ()
   (cond-failwith "close_theory" (not-draft))
   (flush-draft)
   (setq %kind 'theory)
   )                              ; ml-close_theory


;;; Add an element to a chapter of the current draft in %theorydata
;;; do nothing if called during loading of an existing theory
(defun add-to-chapter (sort value)
   (cond ((not %loading-thy)
         (let ((chapter (assq sort %theorydata)))
            (rplacd chapter (cons value (cdr chapter))))))
   )  ;add-to-chapter

;;; Replace an existing chapter of the draft in %theorydata
(defun replace-chapter (sort value)
   (let ((chapter (assq sort %theorydata)))
      (rplacd chapter value)))  ;replace-chapter


;;; get a chapter of a draft or theory 
(defun get-chapter (thydata sort)
   (cdr (assq sort thydata))) ; get-chapter


;;; Update a field of threms
(defun update-thm (threms sort factname thm)
   (let ((thl (assq sort threms)))
      (if (assoc-equal factname (cdr thl))
         (msg-failwith %failtok factname " clashes with existing " sort)
         (rplacd thl (cons (cons factname (encode-thm threms thm)) (cdr thl))))
      ))     ; update-thm


(dml |load_theory| 1 ml-load_theory (|string| -> |void|))

;;; Load an existing theory -- must be descendant of current theory
;;; Must already be in some theory (possibly PPLAMBDA), not in a draft
;;; Allowed in init mode (the empty theory)   NEW
(defun ml-load_theory (thy)
   (let ((%failtok "load_theory")) (load-theory-parent thy))
   (setq %kind 'theory)
   )  ;ml-load_theory


(dml |extend_theory| 1 ml-extend_theory (|string| -> |void|))

;;; allow the user to extend an existing theory
(defun ml-extend_theory (thy)
   (let ((%failtok "extend_theory")) (load-theory-parent thy))
   (setq %kind 'draft)
   )  ;ml-extend_theory


(dml |new_parent| 1 ml-new_parent (|string| -> |void|))

;;; add a new parent to the current draft
(defun ml-new_parent (thy)
   (cond-failwith "new_parent" (not-draft))
   (let ((%failtok "new_parent")) (load-theory-parent thy))
   (add-to-chapter 'parents thy))  ;ml-new_parent

;;; return the ancestors of the current theory in ML

(defun ml-ancestry () %ancestry)
(dml |ancestry| 0 ml-ancestry (|void| -> (|string| |list|)))

;;; Load a theory at top-level for load_theory, extend_theory, or new_parent
(defun load-theory-parent (thy)
   (let ((prev-ancestry %ancestry)
         (%newtypes nil)
         (%newconsts nil)
         (%new-ancestors nil)
         (%loading-thy t))
      (failtrap   ; if any failure then unload the new theory
         #'(lambda (errtok) (unload-theory thy prev-ancestry) (failwith errtok))
         (let ((thydata (get-thy-tree thy)))
            (cond ((member-equal %failtok '("load_theory" "extend_theory"))
                  (cond ((or ; check ancestry (time-stamp check suppressed)
                           (eq %kind 'init)
                           (member-equal %current %new-ancestors))
                        (flush-draft)
                        (setq %date (get-chapter thydata 'stamp))
                        (setq %theorydata thydata)
                        (setq %theorems (load-theorems thy))
                        (setq %current thy))
                     (t (msg-failwith %failtok "not a descendant of " %current)))))
            (llprinc "Theory ")(llprinc thy)(llprinc " loaded")(llterpri))))
   )  ;load-theory-parent


;;; The theory cache is not just for speed.
;;; It also avoids the need to find theory files on remote directories
;;; particularly PPLAMB, which is on the system builder's directory,
;;; and which is an ancestor of every theory.
;;; Eventually we will need a better treatment of remote theories

;;; an alternative is to provide a cache for time-stamps only, since we
;;; must always check the time-stamp of a parent, even if it is loaded already
;;; the parent PPLAMB is never checked anyway, since it is re-built often.



;;; update theory cache
(defun basic-update-cache (thy data)
   (if (defaultp thy) (setq thy %current))
   (let ((entry (assoc-equal thy %thy-cache)))
      (if entry (rplacd entry data)
         (push (cons thy data) %thy-cache)))
   )                              ; basic-update-cache


(defun update-cache (thy thydata threms)
   (basic-update-cache thy (cons thydata threms))
   )                              ; update-cache


;;; needed after proving a theorem in a session concurrent with this one
(dml |delete_cache| 1 ml-delete_cache (|string| -> |void|))

(defun ml-delete_cache (thy)
   (basic-update-cache thy nil)
   )                              ; delete-cache

;;; MJCG 7/2/89 for HOL88
;;; Function to return the lists of cached theories and uncached theories
(defun ml-cached_theories ()
   (mapcar 
      (function(lambda (x) (cons (car x) (null(cdr x)))))
      %thy-cache))
(dml 
   |cached_theories| 
   0 ml-cached_theories 
   (|void| -> ((|string| |#| |bool|) |list|)))

;;; the globals %theorydata and %theorems hold the %current theory

;;; MJCG 13/10/88 for HOL88
;;; find-file wrapped around fileof
;;; open and return a channel to the theory file
;;; if the thy is already loaded, return (thydata . threms)
;;; N.B. The error trapping stops working if one ^Ds into Lisp
;;; and then tmls back into ML (MJCG 21/3/89).
(defun open-thy-file (thy)
   (if (defaultp thy) (setq thy %current))
   (cond 
      ((currentp thy) (cons %theorydata %theorems))
      ((assoc1 thy %thy-cache))
      (t (cond-failwith %failtok (not-ancestor thy))
         (errortrap #'(lambda (ertok)  
               (msg-failwith %failtok thy " theory missing"))
            (infile 
               (find-file (fileof 'theorydata thy)))))))



;;; read, reporting any errors
(defun thy-read (thy #+franz piport #-franz *standard-input*)
   (second        ; to ignore the (quote ...) -- temporary??
      (third        ; to ignore the (setq %theorydata...)
         (errortrap #'(lambda (ertok) (msg-failwith %failtok thy " theory damaged"))
            (llread)))))    ; thy-read


;;; load the given theory and return the value of its theorydata field
;;; does not enter into cache, since theorydata is only needed
;;; when first loading theory hierarchy
(defun load-theorydata (thy) 
   (let ((channel (open-thy-file thy)))
      (if (consp channel) (car channel)
         (prog1 (thy-read thy channel) (close channel))
         )))            ; load-theorydata


;;; load the given theory and return its theorems field, update cache
(defun load-theorems (thy) 
   (cdr (load-thy-threms thy))
   )              ; load-theorems


;;; load a theory and return its theorydata and theorems fields
;;; also save them in the cache
(defun load-thy-threms (thy)
   (let ((channel (open-thy-file thy)))
      (cond ((consp channel) channel)
         (t (let ((thydata (thy-read thy channel)))
               (let ((threms (thy-read thy channel)))
                  (close channel) 
                  (update-cache thy thydata threms)
                  (cons thydata threms))))))
   )                              ; load-thy-threms



;;; load a theory hierarchy, return theorydata of root
;;; must return theorydata even if theory is already loaded,
;;; in order to check the time-stamp.
;;; side-effect -- store the types, constants, etc. of the hierarchy
(defun get-thy-tree (thy)
   (push thy %new-ancestors)
   (cond ((ancestorp thy) (load-theorydata thy))
      (t 
         (add-ancestor thy)
         (let ((thydata (load-theorydata thy)))
            ;parents
            (let ((%date (get-chapter thydata 'stamp)))
               (mapc #'get-parent (get-chapter thydata 'parents)))
            ;types
            (mapc #'(lambda (type) (ml-new_type (car type)(cdr type)))
               (get-chapter thydata 'types))
            ;nametypes
            (mapc #'(lambda (type) (ml-new_type_abbrev (car type)(cdr type)))
               (get-chapter thydata 'nametypes))
            ;constants
            (mapc #'(lambda (con) (ml-new_constant (car con)(cdr con)))
               (get-chapter thydata 'operators))
            ;paired infixes
            (mapc #'(lambda (infix) (ml-new_paired_infix (car infix)(cdr infix)))
               (get-chapter thydata 'paired-infixes))
            ;curried infixes
            (mapc #'(lambda (infix) (ml-new_curried_infix (car infix)(cdr infix)))
               (get-chapter thydata 'curried-infixes))
            ;predics
            (mapc #'(lambda (pred) (ml-new_predicate (car pred)(cdr pred)))
               (get-chapter thydata 'predicates))
            thydata))))  ;get-thy-tree


;;; get a parent for get-thy-tree, and check its stamp
(defun get-parent (par)
   (failtrap #'(lambda (errtok) ; put suffix onto any failure
         (msg-failwith errtok " ancestor " par))
      (let ((pardata (get-thy-tree par)))))
   )                            ; get-parent

;;; LP -- deleted this time-stamp check from inside the "let"
;;; it doesn't work with extend_theory
;;; instead of checking the order of time stamps, it should check for an
;;; exact match (associate a time-stamp with each parent)
;;;       (ifn (lessp (get-chapter pardata 'stamp) %date)
;;;          (msg-failwith %failtok "time stamps out of sequence"))))


;;; An error occurred while loading theories, so undo new definitions
;;; It may seem cleaner to not store the constants and types until we know
;;;     that the load was successful, but this is impossible since loading
;;;     a theory requires the environment of its parents to be set up.
(defun unload-theory (tok prev-ancestry)
   (mapc #'remcon %newconsts)     ;restore constants
   (mapc #'remty %newtypes)       ;and types
   (setq %ancestry prev-ancestry)   ;and ancestors
   )  ;unload-theory

;;; Remove a type
(defun remty (tok)
   (remprop tok 'canon)
   (remprop tok 'olarity))  ;remty

;;; Remove a constant or predicate
(defun remcon (tok)
   (remprop tok 'const)
   (remprop tok 'predicate)
   (remprop tok 'olinfix)
   (remprop tok 'ol2)            ; used in OL parser 
   (remprop tok 'ollp))  ;remcon


;;; functions for building drafts
;;; called by get-thy-tree to load an existing theory 
;;; or from ML to construct new draft 

(dml |paired_new_type| 2 ml-new_type ((|int| |#| |string|) -> |void|))

(defun ml-new_type (n tok)
   (cond-failwith "new_type" 
      (not-draft) (bad-or-clash 'type tok) (neg-arity n tok))
   (push tok %newtypes)
   (add-to-chapter 'types (cons n tok))
   (putprop tok n 'olarity)
   (if (= n 0) (putprop tok (cons tok nil) 'canon)))
;ml-new_type

;;; Modification J.Joyce Apr 87 - vertical bars |new_type_abbrev|
;;; doesn't work for now, the nametypes are not expanded properly
;;; if this is re-introduced, nametypes should be expanded at parse time
(dml |new_type_abbrev| 2 ml-new_type_abbrev ((|string| |#| |type|) -> |void|))

(defun ml-new_type_abbrev  (tok ty)
   (cond-failwith "new_type_abbrev"
      (not-draft) (bad-or-clash 'nametype tok) (polym tok ty))
   (push tok %newtypes)
   (add-to-chapter 'nametypes (cons tok ty))
   (putprop tok 0 'olarity)
   (putprop tok ty 'canon)
   )
;;; Stuff below deleted for HOL (MJCG can't understand it!)
;;;  (cond ((cdr ty)(putprop tok (cons (car ty) (cdr ty)) 'eqtype)
;;;            (rplaca (rplacd ty nil) tok))))  ;ml-new_type_abbrev

;;;  add a new constant or predicate to the current theory
(defun add-const-pred (chap prop tok ty)
   (let ((aty (abs-type ty)))
      (push tok %newconsts)
      (add-to-chapter chap (cons tok aty))
      (putprop tok aty prop)))   ; add-const-pred


;;; LP - I really don't like new_operator... how is TT an operator?
;;;(dml |new_operator| 2 ml-new_constant ((|string| |#| |type|) -> |void|))
(dml |new_constant| 2 ml-new_constant ((|string| |#| |type|) -> |void|)) 

(defun ml-new_constant  (tok ty)
   (cond-failwith "new_constant" (not-draft) (bad-or-clash 'constant tok))
   (add-const-pred 'operators 'const tok ty)
   )  ;ml-new_constant


;;;(dml |new_paired_infix| 2 ml-new_paired_infix ((|string| |#| |type|) -> |void|))

;;; Now called new_infix   [TFM 91.03.17]
(dml |new_infix| 2 ml-new_curried_infix ((|string| |#| |type|) -> |void|))

;;; Declare paired infix operator
(defun ml-new_paired_infix (tok ty)
   (cond-failwith '|new_paired_infix| (not-draft) (bad-or-clash 'infix tok))
   (ifn (and (eq (get-type-op ty) '|fun|) 
         (eq (get-type-op (first (get-type-args ty))) '|prod|))
      (msg-failwith '|new_paired_infix| tok " is not a function on pairs"))
   (add-const-pred 'paired-infixes 'const tok ty)
   (olinfix tok 'paired)
   ) ;ml-new_paired_infix

;;; Declare curried infix operator
(defun ml-new_curried_infix (tok ty)
   (cond-failwith "new_curried_infix" (not-draft) (bad-or-clash 'infix tok))
   (ifn (and (eq (get-type-op ty) '|fun|) 
         (eq (get-type-op (second (get-type-args ty))) '|fun|))
      (msg-failwith "new_curried_infix" tok " is not a curried function"))
   (add-const-pred 'curried-infixes 'const tok ty)
   (olinfix tok 'curried)
   ) ;ml-new_curried_infix


(dml |new_predicate| 2 ml-new_predicate ((|string| |#| |type|) -> |void|))

(defun ml-new_predicate  (tok ty)
   (cond-failwith "new_predicate" (not-draft) (bad-or-clash 'constant tok))
   (add-const-pred 'predicates 'predicate tok ty)
   )  ;ml-new_predicate



(dml |new_open_axiom| 2 ml-new_open_axiom ((|string| |#| |form|) -> |thm|))

(defun ml-new_open_axiom  (factname fm)
   (cond-failwith "new_axiom" (not-draft))
   (let ((%failtok "new_axiom")) (save-axiom-thm 'axiom factname fm))
   )  ;ml-new_open_axiom


;;; cannot save theorems with assumptions, as it would be difficult
;;; to re-load them using the quotation mechanism
;;; renamed to "save_thm" [TFM 90.12.01]
(dml |save_thm| 2 ml-save_thm ((|string| |#| |thm|) -> |thm|))

(defun ml-save_thm  (factname thm)
   (if (get-hyp thm) 
      (msg-failwith "save_thm" "cannot save theorems with hypotheses"))
   (let ((%failtok "save_thm"))
      (save-axiom-thm 'fact factname (get-concl thm)))
   )  ;ml-save_thm


;;; save an axiom or theorem on the current theory-draft
(defun save-axiom-thm (sort factname fm)
   (let* ((consthydatathrems (load-thy-threms %current))
         (thydata (car consthydatathrems))
         (threms (cdr consthydatathrems))
         (thm (make-thm nil (ml-rename_form fm))))
      (update-thm threms sort factname thm)
      (write-thy-file %current thydata threms)
      thm))                                     ; save-axiom-thm

(dml |paired_delete_thm| 2 ml-delete_thm ((|string| |#| |string|) -> |thm|))

;;; returns the theorem, in case you delete the wrong one by mistake
(defun ml-delete_thm (thy factname)
   (if (defaultp thy) (setq thy %current))
   (let ((%failtok "delete_thm"))
      (let* ((consthydatathrems (load-thy-threms thy))
            (thydata (car consthydatathrems))
            (threms (cdr consthydatathrems)))
         (let ((thl (assq 'fact threms)))
            (let ((thpair (assoc-equal factname (cdr thl))))
               (cond
                  (thpair
                     (delq thpair thl)
                     (write-thy-file thy thydata threms)
                     (abs-thm threms (cdr thpair)))
                  (t (msg-failwith "delete_thm" 
                        factname " not found on theory " thy)))))))
   )      ; ml-delete_thm

(dml |axiom| 2 ml-axiom ((|string| |#| |string|) -> |thm|))

(defun ml-axiom  (thy factname)
   (let ((%failtok "axiom"))  (get-axiom-thm 'axiom thy factname))
   )  ;ml-axiom   


(dml |paired_theorem| 2 ml-theorem ((|string| |#| |string|) -> |thm|))

(defun ml-theorem  (thy factname)
   (let ((%failtok "theorem")) (get-axiom-thm 'fact thy factname))
   )  ;ml-theorem


;;; Get the axiom or theorem (sort) named factname from the theory thy
(defun get-axiom-thm (sort thy factname)
   (if (defaultp thy) (setq thy %current))
   (let ((threms (load-theorems thy)))
      (let ((result (assoc-equal factname (cdr (assq sort threms)))))
         (if result (abs-thm threms (cdr result))
            (msg-failwith %failtok factname " not found on theory " thy))))
   )      ; get-axiom-thm


;;; Re-build a theorem from its abstract form retrieved form the file
;;; Sets up proper internal format of variables and types
;;; Also links up the "sharetypes" used to save space on files
;;; invokes quotation system (F-typeol, F-ol-syntax)
(defun abs-thm (threms thm)
   (let ((%sharetypes (cddr (assq 'sharetypes threms))))
      (make-thm nil 
         (failtrap 
            #'(lambda (ftok) 
               (lcferror (catenate ftok " -- while reading theory file")))
            (car (let ((%vtyl nil)) (quotation (abs-form thm)))))))
   )  ;abs-thm


(dml |axioms| 1 ml-axioms (|string| -> ((|string| |#| |thm|) |list|)))

(defun ml-axioms (thy) 
   (let ((%failtok "axioms"))  (extract-axioms-thms 'axiom thy))
   )  ;ml-axioms


(dml |theorems| 1 ml-theorems (|string| -> ((|string| |#| |thm|) |list|)))

(defun ml-theorems (thy) 
   (let ((%failtok "theorems")) (extract-axioms-thms 'fact thy))
   )  ;ml-theorems

;;; =====================================================================
;;; TFM 07.04.90 for HOL88.1.12
;;; ML function to test whether an axiom (or definition) is stored under 
;;; a given name in a given theory.

(defun ml-is_axiom (thy name)
   (if (defaultp thy) (setq thy %current))
   (let ((%failtok "is_axiom"))
   (let* ((threms (cdr (load-theorems thy)))
	  (thl (assq 'axiom threms)))
     (if (assoc name (cdr thl)) t nil))))

(dml |is_axiom| 2 ml-is_axiom ((|string| |#| |string|) -> |bool|))

;;; =====================================================================

(defun extract-axioms-thms (sort thy)
   (if (defaultp thy) (setq thy %current))
   (let ((threms (load-theorems thy)))
      (mapcar #'(lambda (name-thm)
            (cons (car name-thm) (abs-thm threms (cdr name-thm))))
         (cdr (assq sort threms))))
   )      ; extract-axioms-thms

;;; MJCG 31/1/89 for HOL88
(defun ml-current_theory () %current)
(dml |current_theory| 0 ml-current_theory (|void| -> |string|))


(dml |constants| 1 ml-constants (|string| -> (|term| |list|)))

(defun ml-constants (thy)  
   (let ((%failtok "constants")) (extract-chapter thy 'operators)))


;;; no paired infixes in HOL.         [TFM 91.03.17]
;;;(dml |paired_infixes| 1 ml-paired_infixes (|string| -> (|term| |list|)))

;;;(defun ml-paired_infixes (thy) 
;;;   (let ((%failtok "paired_infixes"))
;;;   (extract-chapter thy 'paired-infixes)))  ;ml-infixes

;;; Now called infixes   [TFM 91.03.17]
(dml |infixes| 1 ml-curried_infixes (|string| -> (|term| |list|)))

(defun ml-curried_infixes (thy)
   (let ((%failtok "curried_infixes"))
      (extract-chapter thy 'curried-infixes)))  ;ml-curried_infixes


;;;(dml |predicates| 1 ml-predicates (|string| -> ((|string| |#| |type|) |list|)))

;;;(defun ml-predicates (thy)
;;;   (let ((%failtok "predicates"))
;;;      (extract-chapter thy 'predicates)))  ;ml-predicates


(dml |parents| 1 ml-parents (|string| -> (|string| |list|)))

(defun ml-parents (thy)
   (let ((%failtok "parents"))
      (extract-chapter thy 'parents)))  ;ml-parents


(dml |types| 1 ml-types (|string| -> ((|int| |#| |string|) |list|)))

(defun ml-types (thy)
   (let ((%failtok "types"))
      (extract-chapter thy 'types)))  ;ml-types

(dml |type_abbrevs| 1 ml-nametypes (|string| -> ((|string| |#| |type|) |list|)))

(defun ml-nametypes (thy)
   (let ((%failtok "nametypes"))
      (extract-chapter thy 'nametypes)))  ;ml-nametypes

(defun extract-chapter (thy kind)
   (if (defaultp thy) (setq thy %current))
   (let ((thydata (load-theorydata thy)))        ; 'extract-chapter
      (let ((chapter (get-chapter thydata kind)))
         (case kind
            ((parents types nametypes predicates) chapter)
            ((operators paired-infixes curried-infixes)
               (mapcar #'(lambda (con) 
                     (ml-mk_const (car con) (abs-type (cdr con))))
                  chapter))
            (t (lcferror '(bad kind in extract-chapter)))))
      ))  ;extract-chapter


(defun flush-draft ()
   (if (eq %kind 'draft) (write-thy-file %current %theorydata %theorems))
   )                              ; flush-draft


;;; MJCG 13/10/88 for HOL88
;;; find-file wrapped around fileof
;;; Write out theory `thy`
;;; First line is thydata : types, constants, infixes
;;; Second line is threms : axioms, facts, and sharetypes for them
(defun write-thy-file (thy thydata threms)
   (let ((%outport (outfile (find-file (fileof 'theorydata thy))))
         ($gcprint nil))
      (hol-print-file `(setq %theorydata (quote ,thydata)))
      (hol-print-file `(setq %theorems (quote ,threms)))
      (close %outport))
   (update-cache thy thydata threms)
   )  ;write-thy-file


;;;Build the abstract syntax of fm s.t. fm=quotch[abs-form[fm]]
(defun abs-form (fm)
   (case (form-class fm)
      (conj (q-mk_conj (abs-form (get-left-form fm))
            (abs-form (get-right-form fm))))
      (disj (q-mk_disj (abs-form (get-left-form fm))
            (abs-form (get-right-form fm))))
      (imp (q-mk_imp (abs-form (get-left-form fm))
            (abs-form (get-right-form fm))))
;;;   (iff (q-mk_iff (abs-form (get-left-form fm))  DELETED [TFM 90.01.20]
;;;         (abs-form (get-right-form fm))))
      (forall (q-mk_forall (abs-term (get-quant-var fm))
            (abs-form (get-quant-body fm))))
      (exists (q-mk_exists (abs-term (get-quant-var fm))
            (abs-form (get-quant-body fm))))
      (pred (q-mk_pred (get-pred-sym fm) (abs-term (get-pred-arg fm))))
      (t (lcferror '(bad axiom or theorem)))))  ;abs-form
;;; note that in general [abs-form [quotch abs]] # abs. for instance,
;;; (q-mk_pair x y) becomes (q-mk_comb (q-mk_comb (q-mk_tok pair) x) y).


(defun abs-term (tm) ;builds the abstract syntax of tm
   (case (term-class tm)
      (var (cond-abs-type (q-mk_var (get-var-name tm)) (get-type tm)))
      (const (cond-abs-type (q-mk_const (get-const-name tm)) (get-type tm)))
      (comb (cond-abs-type
            (q-mk_comb (abs-term (get-rator tm))(abs-term (get-rand tm)))
            (get-type tm)))
      (abs (q-mk_abs (abs-term (get-abs-var tm))(abs-term (get-abs-body tm))))
      (t (lcferror '(bad axiom or theorem)))))  ;abs-term


;;; Include type if present
;;;   to save space, redundant types are not stored on theory files
(defun cond-abs-type (tm ty)
   (if ty (q-mk_typed tm (abs-type ty)) tm))


;;; build up a pplambda type, linking in %sharetypes
(defun abs-type (ty)
   (case (type-class ty)
      (%t (abs-type (cdr (assq (cdr ty) %sharetypes))))
      (%VARTYPE (q-mk_vartype (get-vartype-name ty)))
      (t (q-mk_type (get-type-op ty)
            (mapcar #'abs-type (get-type-args ty))))
      ))  ;abs-type


;;; Encode a theorem for storage on a theory file
;;; throw away redundant information to save space
;;;   types stored in `comb` and `abs` nodes are ignored anyway
;;; Side-effect -- record new shared types
(defun encode-thm (threms thm)
   (let ((share (assq 'sharetypes threms)))
      (let ((%sharecount (cadr share)) (%sharetypes (cddr share)))
         (let ((ethm (encode-form (cdr thm))))
            (rplacd share (cons %sharecount %sharetypes))
            ethm))))   ; encode-thm


(defun encode-form (fm)
   (case (car fm)
      ((conj disj imp) ; iff deleted [TFM 90.01.20]
         (make-conn-form (get-conn fm)
            (encode-form (get-left-form fm))
            (encode-form (get-right-form fm))))
      ((forall exists)
         (make-quant-form (get-quant fm)
            (encode-term (get-quant-var fm) t)
            (encode-form (get-quant-body fm))))
      (pred (make-pred-form (get-pred-sym fm)
            (encode-term (get-pred-arg fm) t)))
      (t (lcferror '(bad axiom or theorem)))))  ;encode-form


;;; Space reduction for terms:
;;;    don't write the types of "abs" and "comb" nodes
;;;    don't write the type of a monomorphic constant
;;;    share types of constants and variables
;;; Write type only if "needty" is true -- otherwise type is redundant
(defun encode-term (tm needty)
   (case (term-class tm)
      (var (let ((tok (get-var-name tm))
               (ty (get-type tm)))
            (make-var tok (if needty (new-sharetype tok ty)))))
      (const (let ((tok (get-const-name tm))
               (ty (get-type tm)))
            (make-const tok
               (if (and needty (opoly (constp tok)))
                  (new-sharetype tok ty)))))
      (comb (encomb tm needty))
      (abs (make-abs (encode-term (get-abs-var tm) needty)
            (encode-term (get-abs-body tm) needty)
            nil))
      (t (lcferror '(bad axiom or theorem)))))  ;encode-term


;;; LP - can this be coded recursively?
;;; Encode a combination
;;; Type suppression taken from "F-writol/print-tm"
;;;   If the innermost rator is a polymorphic constant, don't output its type
;;;      instead output types of all rands and of the result type
;;; The type of the rator determines all the other types
(defun encomb (tm needty)
   (let ((rator tm) (rands nil) (ans nil))
      (while (eq 'comb (term-class rator))
         (push (get-rand rator) rands)
         (setq rator (get-rator rator)))
      (let ((pcrator (and (eq 'const (term-class rator))
                  (opoly (constp (get-const-name rator))))))
         (setq ans (encode-term rator (not pcrator)))
         (while rands
            (setq ans (make-comb ans (encode-term (pop rands) pcrator)
                  nil)))
         (if (and needty pcrator)
            (put-type ans         ; can we use q-mk_typed instead of update?
               (new-sharetype (get-const-name rator)
                  (get-type tm)))))
      ans))       ; encomb


;;; LP --  this logic should be improved or deleted!
;;; Put the type `ty` on the sharetypes list if:
;;;      the type is "big" and not shared already
;;; Give it a name `tok`%nnn  where `tok` is the name of the variable or const
(defun new-sharetype (tok ty)
   (if (and (bigger ty 9) (not (revassoc ty %sharetypes)))
      (progn (let ((sharename (concat tok '% %sharecount)))
            (incf %sharecount)
            (push (cons sharename ty) %sharetypes))))
   (encode-type ty))           ; sharetype


;;; Encode a type -- copy it, using sharetypes whenever possible
(defun encode-type (ty)
   (let ((sharename (car (revassoc ty %sharetypes))))
      (if sharename (cons '%t sharename)
         (if (is-vartype ty) (q-mk_vartype (get-vartype-name ty))
            (make-type (get-type-op ty)
               (mapcar #'encode-type (get-type-args ty)))
            ))))  ;encode-type

