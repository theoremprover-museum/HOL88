;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-cl.l                                              ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Compatibility file for Common Lisp                  ;;;
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

(eval-when (compile load eval) (in-package 'user))

;;; IBCL uses the same settings as KCL, so add kcl to feature list
;;; (PJW 09.01.90)
#+ibcl (setq *features* (push :kcl *features*))

#-lucid
(proclaim
   '(optimize (speed 2) (safety 0) (space 0) (compilation-speed 0)))

#+allegro
(proclaim
   '(optimize (speed 3) (safety 0) (space 0) (debug 0)))

#+lucid
(proclaim
   '(optimize (speed 3) (safety 0) (space 0) (compilation-speed 0)))


(proclaim
   '(special |%theory_pp-flag| inputstack %debug outfiles %outport
       %directory))


(defvar *debugging* nil)

;;; KCL by default drops one into the break-level debugger when a
;;; lisp error occurs.  This is particularly nasty when running HOL, 
;;; as the user is dropped into the lisp system, with no clue about
;;; what to do.  The problem was first noticed by Phil Windley, and 
;;; is fixed with the following setq (JVT 27.12.89)

#+kcl (setq *break-enable* nil)

#+allegro (setq *global-gc-behavior* :auto)
;;; The franz feature is used for distinguishing between CL and
;;; Franz lisp. Remove it from features if it appears in a common
;;; lisp implementation.

(eval-when (compile load eval)
   (setq *features* (remove :franz *features*)))


;;; Errset. Return a list of the evaluation result if no error, else
;;; an atom. Only errors should be trapped - throws must pass
;;; through untrapped.
;;;
;;; Some tests:
;;;
;;;   (let ((xx 1)) (errset (cons xx 2))) -> ((1 . 2))
;;;
;;;   (cons (errset (error "lisp error")) 1) ->
;;;      <"lisp error" reported as an error>
;;;      (<an atom> . 1)
;;;
;;;   (catch 'tag (cons (errset (throw 'tag 1)) 2)) -> 1 or NIL,
;;;      but not (<something> . 2)

(defmacro errset (x)
   #+procyon
   `(multiple-value-bind (.res. .type. .tag.)
       (trap-exits ,x)
       (cond
          ((eq .type. 'throw)
             (throw .tag. (car .res.)))
          ((eq .type. 'error)
             (fresh-line *terminal-io*) nil)
          (t .res.)))
   #+lucid
   `(multiple-value-bind (.res. .error-p.)
       (lucid:with-error-trapping ,x)
       (if .error-p.
          (progn
             (format t "~&error -- ~?~%" (third .res.) (fourth .res.))
             "error")
          .res.))
   #+kcl
   `(let ((.fn. (function (lambda nil ,x))))
       ;; Have to capture lexical environment first since evaluation
       ;; takes place in the null environment
       (multiple-value-bind (.error-p. .res.)
          (si:error-set (list 'funcall (list 'quote .fn.)))
          (cond
             ((not .error-p.) (list .res.))
             ((atom .error-p.)
                (throw .error-p. nil))
             (t '|error|))))
   #+allegro
   `(multiple-value-bind (.no-error-p. .res.)
       (excl:errorset ,x t)
       (when .no-error-p. (list .res.)))
   #+:coral
   `(ccl:catch-error
       (ccl:catch-abort (ccl:catch-cancel (list ,x))))
   #-(or procyon lucid kcl allegro :coral)
   (error
"errset macro (in lisp/f-cl.l) has not been defined for this lisp"))


;;; Exit from lisp. (quit) is a normal exit. Calling (quit 1) should set
;;; an error return code so that an enclosing OS make will also terminate.

;;; Lucid CL 3.0 defined quit directly with the proper form (returns exit
;;; optional exit status).  PJW -- 04OCT90

#-lcl3.0
(eval-when (compile load eval) (shadow '(quit)))

#-lcl3.0
(eval-when (compile load eval)
   (defun quit (&rest args)
      (let ((code (cond (args (car args)) (t 0))))
         #+procyon (procyon:quit :quit code)
         #+lucid (system:quit code)
         #+kcl (bye code)
         #+allegro (exit code :quiet t)
         #+:coral (quit)
         )))


;;; Saving a core image. Set top level loop to be tml on restart.

(defun ml-save (tok)
   (setq tok (string tok))
   (let
      ((file
          (if (and (boundp '%directory) (symbol-value '%directory))
             (concatenate 'string (symbol-value '%directory) tok)
             tok)))
      #+procyon
      (save-image :image-file file
         :start-up-function
         (compile nil
            `(lambda nil
                (setf (procyon:stream-title *terminal-io*) %system-name)
                (tml))))
      #+lucid
      (disksave file :restart-function
         (compile nil '(lambda nil (tml) (quit)))
         :gc t)
      #+kcl
      (progn
         (setf (symbol-function 'si:top-level)
            `(lambda nil (tml)))
         (gbc t)
         (save file))
      #+allegro
      (progn
         (setf (symbol-function 'excl::copyright-banner)
            (compile nil '(lambda nil nil)))
         (gc t)
         (excl:dumplisp :name file :restart-function 'tml
            :read-init-file nil))
      #+:coral
      (dumplisp (pathname file) :toplevel-function
         (symbol-function 'tml))
      ))


;;; Control of input. Ignore EOF on standard-input stream

#+kcl (eval-when (load) (setf si:*ignore-eof-on-terminal-io* t))

#+allegro (eval-when (load) (setf top-level:*exit-on-eof* nil))

#+(and procyon pc)
(defmethod cg:location-fasl-file-p ((stream pc::dos-location))
   ;; patch so that '.o' is recognised as a possible extension for binary
   ;; files as well as the standard '.fsl'
   (member (pathname-type (pro:stream-location stream))
      '("fsl" "o") :test #'equalp))

#+(and procyon pc)
(defun pc:check-for-length-and-wildcard (string length error-insert-string)
   ;; patch so that long file and directory names are allowed, but are
   ;; silently truncated to the OS limit (8 characters in DOS)
   (when (i> (length (the string string)) length) 
      (setq string (subseq string 0 length)))
   (if (whole-string= string "*") :wild string))

;;; Text editor environment customisation for Procyon lisp. Make sure
;;; the HOL pretty-print margin follows the width of the interaction
;;; window, that newline and enter send last line to reader, and that
;;; hitting enter when cursor is just before an ML expression in a window
;;; causes expression to be evaluated as ML.

#+procyon
(eval-when (load)

(comtab:set-event-function toploop::*toploop-comtab* null-event 
   ;; Make sure %margin always holds the interaction window width
   #'(lambda (x)
        (declare (special %margin %prettyon))
        (when
           (and (boundp '%margin)
              (not (eql %margin (line-length *terminal-io*))))
           (setq %margin (line-length *terminal-io*))
           (setpretty %prettyon))
        (funcall
           '#.(comtab:event-function toploop::*toploop-comtab* null-event)
           x)))
  

(defvar *enter-event-fn*
   (comtab:event-function toploop::*toploop-comtab*
      #+macintosh enter #+pc pc:vk-enter))

(comtab:set-event-function toploop::*toploop-comtab*
   #+macintosh enter #+pc pc:vk-enter
   ;; Configure the toploop so that enter sends the last line
   ;; to the reader
   #'(lambda (window)
        (file-position *terminal-io* :end)
        #+pc (write-char #\linefeed *terminal-io*)
        #+macintosh (terpri *terminal-io*)
        (funcall *enter-event-fn* window)))

(comtab:set-event-function toploop::*toploop-comtab* #\Newline 
   (comtab:event-function toploop::*toploop-comtab*
    #+macintosh enter #+pc pc:vk-enter))


(comtab:set-event-function te:*text-edit-comtab*
   #+macintosh enter #+pc pc:vk-enter
   #'(lambda (window)
       (when (peek-char t window nil nil)
          (setq *standard-input* window)
          (te:return-to-reader window))))
)


;;; More environment customisation for Procyon lisp on Mac. Selecting a region
;;; and going 'evaluate selection' from the menu evaluates as ML, and quit menu
;;; item asks for confimation.

#+(and procyon macintosh)
(eval-when (load)
 
(comtab:defcom ml-eval-region te:*text-edit-comtab* (window)
   (multiple-value-bind (start end)
      (te:get-region window)
      (while
         (and (peek-char t window nil nil)
            (> end (file-position window)))
         (let ((*standard-input* window))
            (ml-read-eval-print)))
      ;; restore selection
      (te:set-region window start end)
      ;; set prompt position for toploop window
      (toploop::fix-prompt-position *terminal-io*)))
            
(comtab:set-menu-command te:*text-edit-comtab* :eval 'ml-eval-region)


(comtab:defcom tml-quit te:*text-edit-comtab* (window)
   (when (y-or-n-p "Do you really want to quit?")
      (quit)))
            
(comtab:set-menu-command te:*text-edit-comtab* :quit 'tml-quit)
)

;;; Make sure that the system knows that '.o' (compiled ML) files
;;; are binary files containing compiled lisp code.


#+allegro
(eval-when (load eval)
   (setq excl::*load-foreign-types* nil))


;;; Do CL equivalents for franz declarations at top of files. If
;;; %directory is bound, then prepend it to filename. If PC then make
;;; directory separator \ rather than /, otherwise make it :

(eval-when (compile load eval) (shadow '(include)))

(defmacro include (x)
   `(flet
       ((file-abs-path (name)
           (concatenate 'string
              (or (and (boundp '%directory) (symbol-value '%directory))
                 "")
               #+unix name
               ;; JAC 19.06.92
               #+pc (substitute #\\ #\/ name)
               #-(or unix pc) (substitute #\: #\/ name))))
       (let
          ((file (file-abs-path ,x)))
          (when *load-verbose*
             (format t "~&;;; Including ~A" (namestring file)))
          (load file :verbose nil :print nil))))


(defmacro special (&rest vars)
   `(proclaim '(special ,@vars)))


(progn
   (defmacro macros (&rest x) (declare (ignore x))
      nil)
   (defmacro *lexpr (&rest x) (declare (ignore x))
      nil))


;;; New #-macro sub-character '/' - like '\' but returns the 
;;; character code, rather than the character.

(eval-when (compile load eval)
   (set-dispatch-macro-character #\# #\/
      #'(lambda (stream subchar arg)
           (declare (ignore subchar arg))
           (char-int (read-char stream t nil t)))))
  

;;; Control constructs

(defmacro catch-throw (name &rest body)
   `(catch ',name ,@body))

(defmacro throw-from (name &rest body)
   `(throw ',name
       ,(if (cdr body) `(progn ,@body) (car body))))


(defmacro ifn (test then . else)
   `(cond ((not ,test) ,then) (t nil ,@else)))


(defmacro newr (var val)
  `(setq ,var
      (cond
         (,var (nconc ,var (list ,val)))
         (t (list ,val)))))


(eval-when (compile load eval)
   (shadow '(until while)))

(defmacro until (test . body)
   ;; The let avoids double evaluation of test on exit.
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


(defmacro cadaddr (x) `(car (cdaddr ,x)))
(defmacro cadddaddr (x) `(caddr (cdaddr ,x)))
(defmacro caddaddr (x) `(cadr (cdaddr ,x)))
(defmacro caddadadr (x) `(caddr (cadadr ,x)))
(defmacro cadadadr (x) `(cadr (cadadr ,x)))
(defmacro caadadr (x) `(car (cadadr ,x)))
(defmacro caddadr (x) `(car (cddadr ,x)))

(defmacro add (x y) `(+ ,x ,y))
(defmacro times (x y) `(* ,x ,y))
(defmacro plus (x y) `(+ ,x ,y))
(defmacro sub1 (x) `(1- ,x))
(defmacro add1 (x) `(1+ ,x))
(defmacro difference (x y) `(- ,x ,y))
(defmacro fix (x) `(truncate ,x))

(defmacro greaterp (x y) `(> ,x ,y))
(defmacro lessp (x y) `(< ,x ,y))


;;;

(eval-when (compile load eval)
   ;; Some CL implementations try to be 'helpful' in defining these as
   ;; functions. They are macros here.
   (shadow '(memq assq delq putprop)))

(defmacro memq (x lst)
   `(member ,x ,lst))

(defmacro assq (x lst)
   `(assoc ,x ,lst))

(defmacro delq (x lst)
   `(delete ,x ,lst))

(defmacro assoc-equal (x lst)
   `(assoc ,x ,lst :test #'equal))

(defmacro member-equal (x lst)
   `(member ,x ,lst :test #'equal))

(defmacro subst-equal (x y lst)
   `(subst ,x ,y ,lst :test #'equal))


(defmacro putprop (sym val prop)
   `(setf (get ,sym ,prop) ,val))


;;;

(defmacro alphalessp (x y)
   `(and (string< (string ,x) (string ,y)) t))

(defmacro atomify (x) `(intern (princ-to-string ,x)))

(defmacro ascii (x)
   `(intern (string (int-char ,x))))

(defun exploden (x)
   (declare (optimize (speed 3) (safety 0) (space 0)))
   (do*
      ((string
            (typecase x
               (symbol (symbol-name x))
               (string x) 
               (t (princ-to-string x))))
       (len (length string))
       (res nil)
       (ind 0 (1+ ind)))
      ((eql ind len) (nreverse res))
      (push (char-int (char string ind)) res)))


(defun imploden (lst)
   (intern (coerce (mapcar #'int-char lst) 'string)))

(defun flatc (x)
   (length (princ-to-string x)))

(defmacro gensym-interned nil
   '(gentemp))
   
;;;(defun maknum (x)
;;;   (warn "ML function address called - returning zero")
;;;   0)


(defun infile (filename)
   (open (string filename) :direction :input))

(defun outfile (filename)
   (open (string filename) :direction :output :if-exists :supersede
      :if-does-not-exist :create))

(defun readc (&optional (stream *standard-input*))
   (intern (string (read-char stream nil '|nil|))))


;;; This is close to the franz concat - princ-to-string takes care of the
;;; number case.  The difference between uconcat and concat is that the symbol
;;; is interned only in the case of concat.

;;;(defun uconcat (&rest l)
;;;   (make-symbol
;;;      (apply #'concatenate 'string (mapcar #'princ-to-string l))))

;;;(defun concat (&rest l)
;;;   (intern
;;;      (apply #'concatenate 'string (mapcar #'princ-to-string l))))

;;;(defun concatl (l) (apply #'concat l))


(defun concat-aux (l)
  (do ((chars (reverse l) (cdr chars))
      (res '"" (concatenate 'string (princ-to-string (car chars)) res)))
      ((null chars) res)))

(defun uconcat (&rest l)
   (make-symbol (concat-aux l)))

(defun concat (&rest l)
   (intern (concat-aux l)))

(defun concatl (l) (intern (concat-aux l)))


(defun canonise-case-symbol (x)
   ;; From a symbol, return the one that would have been returned by
   ;; reading it - i.e. one with an uppercase print name.
   ;; Changed to only return the string, rather than make it all
   ;; all upcase [JVT 03.04.91].
   (intern (string x)))


;;;(defun catenate (&rest l)
;;;   (apply #'concatenate 'string
;;;      (mapcar #'princ-to-string l)))

(defun catenate (&rest l)
    (concat-aux l))

(defun cascii (a)
   ;; ascii code of first character of a symbol
   (char-int (char (symbol-name a) 0)))


;;; IO functions

(defun llterpri () (terpri *standard-output*))

(defun llprinc (expr)
   (princ expr *standard-output*)
   (finish-output *standard-output*))


(defun llprint (expr)
   ;; changed by MJCG for HOL so that if |%theory_pp-flag| is t
   ;; then theories are pretty-printed.
   (if |%theory_pp-flag|
      (pprint expr *standard-output*)
      (print expr *standard-output*)))


(defun llreadcn () 
   (let ((char (read-char *standard-input* nil nil)))
      (when char (char-int char))))

(defun llread () (read *standard-input*))


;;; Re-direct input to be taken from the given file
;;; inputstack holds all previous values of input stream

(defun infilepush (filespec)
    (push *standard-input* inputstack)
    (setq *standard-input* (infile filespec)))            ; infilepush


(defun infilepop ()
   ;; Restore previous input stream, closing current one
   (let
      ((current-input *standard-input*))
      (setq *standard-input* (pop inputstack))
      (close current-input)))


(defun clock ()
   ;; Get absolute time - just for time-stamps
   (get-universal-time))


;;; Add extension .o to a file name for output name in process of
;;; compiling an ML file.

#-lucid
(defun make-object-filename (x)
   (let
      ((len (length x)))
      (concatenate 'string
         ;; remove existing .l extension, if any
         (if (and (> len 2) (eql (schar x (1- len)) #\l)
               (eql (schar x (- len 2)) #\.))
            (subseq x 0 (- len 2)) x)
         ".o")))


;; Functions slash-pos & slash-pos1, used to alleviate problem with
;; LUCID Common Lisp inserting extra directory names into filename before
;; compilation.  (SMB - 24/5/90)

;;; Note to JVT: SMB is Steve Bancroft who assisted me with HOL at Davis.

#+lucid
(defun slash-pos (filename)
  (slash-pos1 filename 0))

#+lucid
(defun slash-pos1 (filename position)
  (let ((len (length filename)))
    (cond ((= 0 len) 0)
          ((eq #\/ (schar filename 0)) (1+ position))
          (t (slash-pos1 (subseq filename 1 len) (1+ position))))))

;; Modified make-object-filename for lucid to use slash-pos
;; (SMB - 24/5/90)

#+lucid
(defun make-object-filename (x)
   (let
      ((len (length x)))
       (setq temp (concatenate 'string
         ;; remove existing .l extension, if any
         (if (and (> len 2) (eql (schar x (1- len)) #\l)
               (eql (schar x (- len 2)) #\.))
            (subseq x 0 (- len 2)) x)
         ".o"))
     (subseq temp (slash-pos temp) (length temp))))

;;; Function called on returning from tml command loop

(defun finalize-tml () nil)


;;; Turn off debugging switches and set top level to (tml)

(defun setup nil
   (setq *load-verbose* nil)
   #+allegro-v4.0 (setq *compile-verbose* nil)
   #+allegro-v4.1 (setq *compile-verbose* nil)
   #+allegro-v4.1 (setq *compile-print* nil)
   #+allegro (gc t)
   #+kcl (gbc 3)
   (setdebug nil))

;;; set the internal |%print_fasl-flag| value
(defun set-fasl-flag (val) 
   (setq *load-verbose* val) 
   (setq |%print_fasl-flag| val))

(defun setup-ml nil
   (setdebug nil))


(defun setdebug (flag)
   (setq *debugging* flag))


;;; Initialize system in experimental mode - turn debug options on

(defun experimental-init ()
   (princ "Experimental version!") (terpri)
   (setdebug t))


;;; Set up for loading of system

(defun set-make ()
   ;; Called after all lisp code for HOL has been loaded, just before
   ;; ML top loop is entered.
   ;; Franz version sets up the error handler to print the error
   ;; message and quit - not in general possible in CL
   #+allegro-v4.0
   (progn 
       (setq *redefinition-warnings* nil)
       (setq *record-source-files* nil)
       (setq *load-verbose* nil)
       (setq *compile-verbose* nil))
   #+allegro-v4.1
   (progn 
       (setq *redefinition-warnings* nil)
       (setq *record-source-files* nil)
       (setq *load-verbose* nil)
       (setq *compile-print* nil)
       (setq *compile-verbose* nil))
   #+lucid
   (progn
      (setup-gc-time-monitoring)
      (setq *redefinition-action* nil)
      (compiler-options :messages nil :warnings nil))
   #+kcl
   (progn
      ;; Turn off compiler messages
      (system:gbc-time 0)
      (setq compiler:*compile-verbose* nil)
      (setq compiler::*suppress-compiler-notes* t)
      (setq compiler::*suppress-compiler-warnings* t)
      )
   nil)


;;; Get the current date as a string: dd/mm/yy

(defun date nil
   (multiple-value-bind (sec min hour day mon year)
      (get-decoded-time)
      (declare (ignore sec min hour))
      (format nil "~D/~D/~D" day mon (rem year 100))))


(defun flatsize2 (str)
   (length (princ-to-string str)))


;;; Record time spent in GC

#+kcl
(progn () (system:gbc-time 0))

#+lucid
(progn
   (defvar *internal-gc-time* 0)
   (defvar *last-gc-start-time* 0))


#+lucid
(defun setup-gc-time-monitoring nil
   (setq *gc-silence*
      (compile nil
         '(lambda (when)
             (case when
                (:before
                   (fresh-line *terminal-io*)
                   (princ ";;; GC")
                   (finish-output *terminal-io*)
                   (setq *last-gc-start-time* (get-internal-run-time)))
                (:after
                   (terpri)
                   (incf *internal-gc-time*
                      (- (get-internal-run-time) *last-gc-start-time*)))
                (t))))))


;;; Return (jobtime . gctime) where jobtime does not include gctime
;;; in 10ths of seconds (rounded)

(defun runtime10th ()
   (flet
      ((sec-10ths (x)
         (cons
            (truncate (* (car x) 10) internal-time-units-per-second)
            (truncate (* (cdr x) 10) internal-time-units-per-second))))
      (sec-10ths
         #+lucid
         (cons (- (get-internal-run-time) *internal-gc-time*)
            *internal-gc-time*)
         #+procyon
         (let ((gc (system:%gctime t)))
            (cons (- (get-internal-run-time) gc) gc))
         #+allegro
         (multiple-value-bind (user system gc-user gc-system)
            (excl::get-internal-run-times)
            (declare (ignore system gc-system))
            ;; exclude system overheads for this process
            ;; - otherwise (cons (+ user system) (+ gc-user gc-system))
            (cons user gc-user))
         #+kcl
         (let ((gc (system:gbc-time)))
            (cons (- (get-internal-run-time) gc) gc))
         #-(or lucid procyon allegro kcl)
         (cons (get-internal-run-time) 0))))


(defun bigger (obj size)  (> (flatsize2 obj) size))  ;bigger


(defun init-io ()
   (setq outfiles nil)
   (setq inputstack nil))
 

;;; Call a lisp listener. Break is a grubby but implementation-
;;; independent way to get into a lisp debugger loop.

(defun ml-break nil
   #+(or procyon allegro)
   (break "Enter lisp debugger top level loop")
   #+lucid
   (progn
      (format t
         "~%Entering lisp top level loop - type (q) to exit~%~%")
      (lucid::enter-top-level t))
   #+kcl
   (let ((si::*quit-tag* (cons nil nil)))
      (catch si::*quit-tag*
         (break "Entering lisp debugger - type :q to exit")))
   )


#+lucid (defun q nil (throw 'tmllooptag nil))


;;; Compile a list of function definitions - but the kcl compiler is
;;; _really_ slow for individual functions.

(defun compile-functions-if-needed (forms)
   (mapc
      #'(lambda (form)
           (unless (compiled-function-p (symbol-function (cadr form)))
              (compile (cadr form))))
      forms))


;;; End of file
