;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-parser.l                                          ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      System parser                                       ;;;
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
;;;   REVISION HISTORY: Original code: parser (lisp 1.6) part of Edinburgh  ;;;
;;;                     LCF by M. Gordon, R. Milner and C. Wadsworth (1978) ;;;
;;;                     Transported by G. Huet in Maclisp on Multics, Fall  ;;;
;;;                     1981                                                ;;;
;;;                                                                         ;;;
;;; V1.4 :idents may not start with ', but may include.                     ;;;
;;;       strings may include%                                              ;;;
;;;                                                                         ;;;
;;; V2.2 :new-exit instead of err in function parse-failed                  ;;;
;;;                                                                         ;;;
;;; V3.1 : |...| notation for literal atoms                                 ;;;
;;;                                                                         ;;;
;;; to do:                                                                  ;;;
;;;    replace parser completely                                            ;;;
;;;    speed it up                                                          ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (special %skiplimit %char-buffer %special-letters %special-alphanums 
            %special-table %ch |%read_sexpr-flag| %syntax-block-enabled))


(eval-when (compile)
   (defmacro bounded (lower a upper) 
      `(and (<= ,lower ,a) (<= ,a ,upper))))    ; bounded

(setq %skiplimit 30)          ; number of strings to print when skipping

;;; Object language strings

(setq eq-tok '|==|)


;;; iff-tok removed [TFM 91.01.20]
(setq spec-toks
   (list lambda-tok else-tok '|:| '|(| '|)| anticnr-tok condl-tok
      '|,| '|.| eq-tok '|<<| '|~| conj-tok disj-tok imp-tok 
      exists-tok forall-tok endcnrtok))


;;; Meta language symbols

(setq %char-buffer nil)

(defun next-char ()
   ;; pop %char-buffer if it is non-empty, otherwise read a character.
   (cond
      (%char-buffer 
         (prog1
            (car %char-buffer)
            (setq %char-buffer (cdr %char-buffer))))
      (t (nextcn))))


;;; Added by MJCG on 3/3/89 for HOL88.1.01
;;; Function to skip regular comments % ... % and supercomments %< ... >%
;;; Entered after %< read.

(defun skip-comments ()
   (prog (ch)
      (setq ch (next-char))
      (setq %ch  (next-char))
      loop (cond ((and (= ch cmntchr) (= %ch cmnt-start))
            (skip-comments)
            (setq %ch (next-char)))
         ((and (= ch cmnt-end) (= %ch cmntchr))
            (return)))
      (setq ch %ch)
      (setq %ch (next-char))
      (go loop)))

;;; get next char
;;; (not possible to skip blanks because of vartypes)
;;; Changed by MJCG on 3/3/89 for HOL88.1.01 to call skip-comments
;;; and use global %ch

(defun gnc ()
   (setq %ch (next-char))
   (cond ((= %ch cmntchr)
         (setq %ch (next-char))
         (cond ((= %ch cmntchr))
            ((= %ch cmnt-start) (skip-comments))
            (t (while (not (= (next-char) cmntchr)))))
         (gnc))
      (t %ch)))


;;; Old code (pre HOL88.1.01)
;;;(defun gnc ()
;;;    (let ((ch (next-char)))
;;;      (cond ((= ch cmntchr)
;;;          (while (not (= (next-char) cmntchr)))     ;skip comments
;;;          (gnc))
;;;         (t ch))))                           ;gnc

;;; initialize lexical analyzer

(defun initlean ()
   (setq token nil)
   (setq tokchs nil)
   (setq toktyp nil)
   (setq hol-char hol-space)
   (setq toklist nil))                         ;initlean


;;; get next string
;;; BUG: scans the first number in a quotation as a number instead of an
;;;      identifier (see gnt.l).

(defun gnt ()
   (setq cflag (spacep hol-char))                      ;for vartypes (berk)
   (setq ptoken token)
   (setq ptokchs tokchs)
   (setq ptoktyp toktyp)
   (setq pchar hol-char)
   (while (spacep hol-char)(setq pchar (setq hol-char (gnc))));remove spacing
   (setq toktyp 1)
   (cond ((letterp hol-char) (setq tokchs (list  hol-char))   ;ident
         (ident))
      ((digitp hol-char) (setq tokchs (list hol-char))   ;number (ML only)
         (if (eq lang1 'ml1) (numb) (ident)))
      ((= hol-char tokqt) (setq tokchs nil)        ;string
         (tcn))
      (t (setq toktyp 2)
         (setq hol-char (gnc)) 
         (setq token (ascii pchar))
         (if (and(eq token scolon-sym)(= hol-char lf)) ;multics: lines end
            (setq hol-char (gnc))) ; with lf was (prog2 (gnc)(gnc))
         (while (memq hol-char (get token 'double))
            (setq token (concat token (ascii hol-char)))
            (setq hol-char (gnc)))))
   token)                                      ;gnt

(defun numb ()
   ;;scan a number and return its numeric value
   (let ((accu (- hol-char #/0)))
      (while (digitp (setq hol-char (next-char)))
         (setq accu (+ (* accu 10) (- hol-char #/0))))
      (setq token accu)))             ; numb

(defun ident ()
   ;; scan an identifier as a symbol (used also for numbers in OL)
   (while (alphanump (setq hol-char (gnc)))
      (push hol-char tokchs))
   (setq token (imploden (reverse tokchs))))     ;ident

;;;  Changed nconc to append to fix RJB bug (MJCG 12/11/89)

(defun tcn ()
   (while (not (= (setq hol-char (next-char)) tokqt))
      (if (= hol-char escape)
         (setq tokchs (append (escape-rtn (next-char)) tokchs))
         (push hol-char tokchs)))
   (newr toklist (imploden (reverse tokchs)))
   (setq hol-char (gnc))
   (setq token tokflag))                         ; tcn

(defun escape-rtn (char)
   (cond ((= char #/0) (itrate hol-space 10))
      ((digitp char) (itrate hol-space (- char #/0))) 
      ((get (ascii char) 'stringmacro))             
      (t (list char))))                       ;escape-rtn

(defun vartype-rtn ()
   (prog (n)
      (if cflag (return mul-sym))
      (setq n 1)
      loop  (ifn (or (numberp token) (= toktyp 1) (eq token mul-sym))
         (return (imploden (itrate multiply n))))
      (gnt)
      (when (and (eq ptoken mul-sym) (not cflag))
         (setq n (add1 n))
         (go loop))
      (return (imploden (nconc (itrate multiply n) (exploden ptoken))))
      ))                                    ;vartype-rtn

(setq token nil)
(setq ptoken nil)
(setq tokchs nil)
(setq ptokchs nil)
(setq toktyp nil)
(setq ptoktyp nil)
(setq hol-char hol-space)


;;; MJCG 27/10/88 for HOL88

(setq %special-letters nil)
(setq %special-alphanums nil)

(defun charp (ch)
   (bounded #/! ch #/~))                       ; charp
(defun upperp (ch)
   (bounded #/A ch #/Z))                       ; upperp
(defun lowerp (ch)
   (bounded #/a ch #/z))                       ; lowerp


;;; MJCG 27/10/88 for HOL88
;;; Added %special-letters

(defun letterp (ch)
   (or (upperp ch) (lowerp ch) (memq ch %special-letters)))    ; letterp

(defun digitp (ch)
   (bounded #/0 ch #/9))                       ; digitp


;;; MJCG 27/10/88 for HOL88
;;; Added %special-alphanums

(defun alphanump (ch)
   (or (upperp ch)
      (lowerp ch)
      (digitp ch)
      (= ch #/')
      (= ch #/_)
      (memq ch %special-letters)
      (memq ch %special-alphanums)))                            ; alphanump


(defun spacep (ch)
   (memq ch (list hol-space cr lf tab ff)))            ; spacep


;;; set up token escape codes

(putprop '|L| (list lf) 'stringmacro)
(putprop '|F| (list ff) 'stringmacro)
(putprop '|R| (list cr) 'stringmacro)
(putprop '|S| (list hol-space) 'stringmacro)
(putprop '|T| (list tab) 'stringmacro)


;;; set up lexical analysis of multi-character special symbols
;;; ideally should be divided ML from OL


;;; MJCG 27/10/88 for HOL88
;;; Function for setting up double property and recording the
;;; result in %special-table (a disembodied property list)

(setq %special-table #+franz (list 'special-table) #-franz nil)

(defun put-double (x l)
   (prog2
      #+franz
      (putprop %special-table (union l (get %special-table x)) x)
      #-franz
      (setf (getf %special-table x) (union l (getf %special-table x)))
      (putprop x (union l (get x 'double)) 'double)))

(eval-when (load)
   (put-double '|=| '(#/> #/=))
   (put-double '|-| '(#/>))
   (put-double '|<| '(#/< #/=))
   (put-double '|:| '(#/=))
   (put-double '|?| '(#/? #/\))
   (put-double '|;| '(#/;))
   (put-double '|:| '(#/:))
   (put-double '|!| '(#/! #/\))
   (put-double '|/| '(#/\))
   (put-double '\\ '(#//))
   (put-double '|==| '(#/>))
   (put-double '|<=| '(#/>)))
            

(defun unop (op code)
   (putprop op code lang1))                    ;unop

(defun bnop (op code)
   (putprop op code lang2))                    ;bnop

(defun binop (op lp code)
   (putprop op code lang2) (putprop op lp langlp))       ;binop


;;; check for expected token, return rslt if OK
;;; the token is expected AFTER the parsing of rslt

(defun check (tok rslt msg)
   (cond ((eq tok token) (gnt) rslt) (t (parse-failed msg))))    ;check

(defun parse-failed (msg)
   (llprinc msg)
   (llterpri)
   (llprinc '|skipping: |)
   (llprinc ptoken)
   (llprinc space-sym)
   (llprinc token)
   (llprinc space-sym)
   (do ((i %skiplimit (1- i)))
      ((eq token tml-sym) (if (<= i 0) (llprinc '|. . .|)))
      (gnt)
      (when (> i 0) (llprinc token) (llprinc space-sym)))
   (initlean)
   (eqsetup)
   (persetup)
   (scolonsetup)
   (hol-persetup)        ; defined in: hol-pars.l
   (hol-restrictsetup)   ; defined in: hol-pars.l
   (hol-insetup)         ; defined in: parslet.l
   (hol-andsetup)        ; defined in: parslet.l
   (hol-eqsetup)         ; defined in: parslet.l
   (hol-commasetup)      ; defined in: parslist.l
   (hol-scolonsetup)     ; defined in: parslist.l
   (throw-from parse nil))  ;parse-failed 

(setq arg1 nil)

;;; Lisp flag that says at least one syntax block is in operation
;;; Set to t by ml-new_syntax_block in hol-pars.l
(setq %syntax-block-enabled nil)

;;; Added 2.2.90 by MJCG for syntax blocks
;;; Grabs raw characters up to (but not including) the terminator
;;; and returns the result imploded into a string

(defun syntax-block-rtn (terminator)
 (prog (chars terminator-chars remaining)
       (setq chars nil)
       (setq terminator-chars (exploden terminator))
  loop (setq remaining (cdr terminator-chars))
       (while 
        (not (= (setq hol-char (next-char)) (car terminator-chars)))
         (if (= hol-char escape)
             (setq chars (append (escape-rtn (next-char)) chars))
             (push hol-char chars)))
       (ifn remaining (go exit))
       (push hol-char chars)
       (while
        (and remaining (= (setq hol-char (next-char)) (car remaining)))
        (setq remaining (cdr remaining))
        (push hol-char chars))
       (ifn remaining (go exit))
       (push hol-char chars)
       (go loop)
  exit (setq remaining terminator-chars)
       (while remaining 
         (setq remaining (cdr remaining))
         (setq chars (cdr chars)))
       (setq ptoken terminator)
       (setq hol-char (gnc))
       (setq token (gnt))
       (return (imploden(nreverse chars)))))


;;; Added 2.2.90 by MJCG
;;; Constructs the parse tree of the translation of a syntax block
(defun mk-syntax-block (tok)
 `(mk-appn
    (mk-var ,(car(get tok 'syntax-block)))
    (mk-tokconst ,(syntax-block-rtn (cdr(get tok 'syntax-block))))))

;;; MJCG 10.12.90 for Centaur: 
;;; Constructs the parse tree of the translation of an S-expression block

(defun mk-sexpression-block (tok)
 (prog (%sexpression terminator)
       (setq %sexpression (read))
       (setq terminator (cdr(get tok 'sexpression-block)))
       (if (eq %sexpression terminator)
           (parse-failed "Missing S-expression"))
       (gnt)
       (cond ((eq token terminator)
              (gnt)
              (return 
               (apply (car(get tok 'sexpression-block)) (list %sexpression)))))
       (parse-failed (concat "Missing terminator: " terminator))))

;;; MJCG 10.12.90 for Centaur: 
;;; Flag to enable input in S-expression form
;;; Modified 13.12.90 by JVT.  Moved the addition of |%read_sexpr-flag| to
;;; the %flags list to the file lisp/f-iox-stand.l.  The reason being that
;;; %flags is an unknown variable at this stage.

(setq |%read_sexpr-flag| nil)

;;; main parse routine
;;; parses text until reaching level cpl
;;; saves its result in the *special arg1
;;; Modified 2.2.90 by MJCG to handle syntax blocks
;;; Modified 10.2.90 by JVT to fix the syntax blocks for Common Lisp.
;;;   -- Involves the adding of a check on numbers because CL doesn't
;;;      like one doing a "get" on them (e.g. (get '0 'syntax-block))
;;; MJCG 10.12.90 for Centaur: added support for S-expression input 

(defun parse-level (cpl)
 (prog (x)
       (incf parsedepth)
       (cond ((and %syntax-block-enabled
                   (not (numberp token)) 
                   (get token 'syntax-block)) 
              (decf parsedepth)
              (return (setq arg1 (mk-syntax-block token))))
             ((and |%read_sexpr-flag|
                   (not (numberp token)) 
                   (get token 'sexpression-block)) 
              (decf parsedepth) 
              (return (setq arg1 (mk-sexpression-block token))))
             (t
              (gnt)))
       (setq arg1
             (ifn (or (numberp ptoken) (null (setq x (get ptoken lang1))))
                  (eval x)
                  (eval atom-rtn)))
  loop (setq x (ifn (numberp token) (get token langlp)))
       (unless x
         (when (lessp cpl juxtlevel) (setq arg1 (eval juxt-rtn)) (go loop))
         (decf parsedepth)
         (return arg1))
       (unless (lessp cpl x) (decf parsedepth) (return arg1))
       (if (memq (car arg1) declnconstrs)
           (parse-failed '|non top level decln must have IN clause|))
       (setq x (get token lang2))
       (if (null x)
           (parse-failed (catenate '|`| token '|` in the wrong place|)))
       (gnt)
       (setq arg1 (eval x))
       (go loop)))                           ;parse-level

