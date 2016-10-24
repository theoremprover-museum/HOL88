;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-franz.l                                           ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Compatibility file for Franz Lisp                   ;;;
;;;                                                                         ;;;
;;;   USES FILES:       (none)                                              ;;;
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

(eval-when (compile) 
   (macros t)   
   (*lexpr concat uconcat catenate)
   (special user-top-level ER%all $gcprint prinlength prinlevel
      %std-input fin-ligne %debug |%theory_pp-flag| %liszt
      poport piport inputstack outfiles %outport %directory))


(sstatus translink on)
(sstatus ignoreeof t)


;;; Exit from lisp. (quit) is a normal exit. Calling (quit 1) should set
;;; an error return code so that an enclosing OS make will also terminate.

(defun quit (&rest args)
   (apply #'exit args))


;;; Saving a core image

(defun ml-save (tok)
   (setq tok
      (cond
         ((and (boundp '%directory) (symbol-value '%directory))
            (catenate (symbol-value '%directory) tok))
         (t tok)))
   ;; set top level loop to be (tml)
   (gc)
   (let ((user-top-level 'drain-tml))
      (apply 'dumplisp (list tok))))


;;; LCF must die upon receiving the hangup signal (HUP)
;;; otherwise LCF jobs started under Emacs will remain around causing havoc

(defun exit-fun (x) (exit 0))
(signal 1 'exit-fun)


;;; Declarations

(defmacro defconstant (x y)
   `(progn 'compile
       (eval-when (compile load) (special ,x))
       (eval-when (compile load eval) (setq ,x ,y))))


(defmacro synonymq (sym1 sym2)
   `(putd ',sym1 (getd ',sym2)))


;;; Control constructs

(defmacro block (name . body)
   `(*catch ',name (progn ,@body)))

(defmacro return-from (name . body)
   `(*throw ',name
      ,(if (cdr body) `(progn ,@body) (car body))))


(defmacro catch-throw (name . body)
   `(*catch ',name (progn ,@body)))

(defmacro throw-from (name . body)
   `(*throw ',name
      ,(if (cdr body) `(progn ,@body) (car body))))


(defmacro if (test then . else)
   `(cond (,test ,then) (t nil ,@else)))

(defmacro unless (test . body)
   `(cond (,test nil) (t ,@body)))

(defmacro when (test . body)
   `(cond (,test ,@body)))


(defmacro mapl (fn &rest lsts)
   `(map ,fn ,@lsts))

;;; Old version (commented out on 28 Sept 1989 by MJCG)
;;;(defun case-aux (clause var)
;;;   (cond
;;;      ((memq (car clause) '(t otherwise))
;;;         (cons 't (cdr clause)))
;;;      ((atom (car clause))
;;;         (cons (list 'eq var (list 'quote (car clause)))
;;;            (cdr clause)))
;;;      (t
;;;         (cons (list 'memq var (list 'quote (car clause)))
;;;            (cdr clause)))))
;;; 
;;;(defmacro case (sel . lclauses)
;;;   (let ((var (gensym)))
;;;      `(let ((,var ,sel))
;;;         (cond
;;;            ,@(mapcar
;;;               #'(lambda (clause) (case-aux clause var))
;;;               lclauses)))))

;;; New version (prompted by DES bug) MJCG 28 Sept 1989
(defmacro case (sel . lclauses)
 `(selectq ,sel ,@lclauses))


(defmacro ifn (test then . else)
   `(cond ((not ,test) ,then) (t nil ,@else)))


(defmacro newr (var val)
   `(setq ,var
      (cond
         (,var (nconc ,var (list ,val)))
         (t (list ,val)))))


(defmacro until (test . body)
   ;; The let avoids double evaluation of test on exit.
   ;; This will give compiler warnings in Franz compiler, since
   ;; the go and the return are non-local.
   (let ((lable (gensym)) (valvar (gensym)))
      `(prog ()
         ,lable
         (let ((,valvar ,test))
            (cond
               (,valvar (return ,valvar))
               (t ,@body
                  (go ,lable)))))))


(defmacro while (test . body)
   (let ((lable (gensym)))
      `(prog ()
         ,lable
         (cond
            (,test ,@body (go ,lable))
            (t (return nil))))))


;;; Arithmetic
;;;
;;; IMPORTANT!
;;; In franz changed decf, incf, and when to use cond instead of if
;;; decr did not work because "if" was undefined for it
;;; the manifestation of this bug was most obscure.

(defmacro decf (var val)
   `(setq ,var
      ,(cond ((null val) `(1- ,var)) (t `(- ,var ,val)))))

(defmacro incf (var val)
   `(setq ,var
      ,(cond ((null val) `(1+ ,var)) (t `(+ ,var ,val)))))


(defmacro <= (x y)
   `(not (greaterp ,x ,y)))

(defmacro >= (x y)
   `(not (lessp ,x ,y)))


(defmacro integerp (x) `(fixp ,x))

(defmacro truncate (x y) `(*quo ,x ,y))


;;; List manipulation

(defmacro first (x) `(car ,x))
(defmacro second (x) `(cadr ,x))
(defmacro third (x) `(caddr ,x))
(defmacro fourth (x) `(cadddr ,x))
(defmacro fifth (x) `(car (cddddr ,x)))

(synonymq assoc-equal assoc)
(synonymq member-equal member)
(synonymq subst-equal subst)

(defmacro copy-tree (x)
   `(copy ,x))


(defmacro list* l
   `(cons ,(car l)
      ,(cond
         ((null (cddr l)) (cadr l))
         (t `(list* ,@(cdr l))))))


(defmacro pop (var)
   `(prog1 (car ,var) (setq ,var (cdr ,var))))

(defmacro push (val var)
   `(setq ,var (cons ,val ,var)))


(defun union (x y)
   ;; union of two lists, without repetitions using eq test
   (cond
      ((null x) y)
      ((memq (car x) y) (union (cdr x) y))
      (t (cons (car x) (union (cdr x) y)))))


;;; Misc

(defun canonise-case-symbol (x) x)


(synonymq probe-file probef)


(defmacro gensym-interned nil
   '(intern (gensym)))

(defmacro atomify (x) `(implode (explodec ,x)))


;;; The scanner functions

(synonymq imploden implode)
(synonymq printint exploden)

(synonymq consp dtpr)


(defun catenate (&rest l)
   ;; catenate a list of things into a STRING
   (get_pname (apply 'uconcat l)))


(defun cascii (a)
   ;; the ascii code of symbol a
   (getcharn a 1))


;;; IO functions

(defun llterpri () (terpri poport))

(defun llprinc (expr) (princ expr poport))


(defun llprint (expr) 
   ;; changed by MJCG for HOL so that if |%theory_pp-flag| is t
   ;; then theories are pretty-printed.
   (if |%theory_pp-flag|
      (pp-form expr poport) (print expr poport)))


(defun llreadcn ()
   (let ((char (readc piport)))
      (if char (cascii char))))

(defun llread () (read piport))


;;; Re-direct input from terminal to given file
;;; inputstack holds all previous values of piport

(defun infilepush (filespec)
   (push piport inputstack)
   (setq piport (infile filespec)))            ; infilepush


(defun infilepop ()
   ;; Restore previous input file after closing current one
   (close piport)
   (setq piport (pop inputstack)))


(defun clock ()
   ;; Get absolute time - just for time-stamps
   (sys:time))


;;; stupid Franz does not have a symbol bound to standard input

(setq %std-input piport)        ; for flushing tty


;;; Turn debugging on/off
;;; sets Lisp debugging switches, interrupt handler, and top-level

(defun setdebug (flag)
   (cond
      (flag
         (debugging t)
         (setq $gcprint t)             ; monitor garbage collections
         (setq prinlength 6)           ; control printing of circular lists
         (setq prinlevel 4)
         (sstatus translink nil)
         (signal 2 '|sys:int-serv|)    ; restore Franz interrupt handler
         ; was INT in Cambridge version
         (setq user-top-level nil))
      (t (sstatus translink on)
         (setq $gcprint nil)
         (setq prinlength nil)
         (setq prinlevel nil)
         (setq ER%all nil)              ; remove error handler
         (*rset nil)
         (signal 2 'handle-interrupt)
         (setq user-top-level 'tml))))


;;; make an interrupt cause a break
;;; called when user hits interrupt key

(defun handle-interrupt (signal-number)
   (terpri)
   (princ "HOL interrupted")
   (break))


;;; Function called on returning from tml command loop
;;; Clears user-top-level to prevent automatic re-entry to ML

(defun finalize-tml ()
   (setdebug t)
   (reset))


;;; Turn off debugging switches and set top level to (tml)
;;; initialize $ldprint, which is the internal value of |%print_fasl-flag|

(defun setup nil
   (setdebug nil)
   (setq $ldprint nil)     ; to turn off ugly fasl messages [TFM 91.01.20]
   ;; (allocate 'list 500) ; to help gc problems - only for LCF
   (reset))

;;; set the internal |%print_fasl-flag| value
(defun set-fasl-flag (val) (setq $ldprint val) (setq |%print_fasl-flag| val))

(defun setup-ml nil
   (setdebug nil)
   (reset))


;;; initialize system in experimental mode - turn debug options on

(defun experimental-init ()
   (princ "Experimental version!") (terpri)
   (load "f-franz")
   (load "f-macro")
   (load "f-ol-rec")
   (setdebug t))


;;; set up batch loading of system via Makefile

(defun set-make () (setq ER%all 'make-err-handler))


;;; report error to log file and abort job

(defun make-err-handler (msg)
   (princ '|error during loading of system:|)(terpri)
   (let (((type id cont string . data) msg))
      (princ string)
      (mapc #'(lambda (x) (princ '| |) (print x)) data)
      (terpri)
      (baktrace)
      (quit 1)))


;;; get the date as a string
;;; date changed to include year (TFM 88.08.02)

(defun date nil  
   (concat (substring (status ctime) 5 6)
      (substring (status ctime) 20 5)))


(defun flatsize2 (str)
   ;; standard flatc does not work on bignums
   (if (bigp str) (length (explodec str)) (flatc str)))


;;; Return (jobtime . gctime) where jobtime does not include gctime
;;; in 10ths of seconds (rounded)

(defun runtime10th ()
   (let (((proc gc) (ptime)))
      (cons (quotient (- proc gc) 6) (quotient gc 6))))


(defun bigger (obj size)  (> (flatc obj size) size))


(defun drain-tml ()
   ;; throws away junk left in Make commands (stupid Franzlisp!)
   (drain %std-input) (setq fin-ligne t)
   (tml))


(defun init-io ()
   (setq piport nil)
   (setq poport nil)
   (setq outfiles nil)
   (setq inputstack nil)
   (setq %outport nil))


;;; Call a lisp listener

(defun ml-break nil
   (break))
