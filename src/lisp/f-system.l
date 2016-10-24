;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-system.l                                          ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      All operating system dependent functions in here    ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-franz.l (or f-cl.l), f-macro.l                    ;;;
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
   #+franz (include "lisp/f-franz")
   (include "lisp/f-macro")
   (special %liszt %debug %hol-dir %display-function))


;;; Check validity of file token
;;; must limit the file part (excluding directories) to 11 chars
;;; to allow for Unix's 14 char limit, and a suffix .xx
;;; (Unless this Unix has long filenames). Assume by default it has.

(eval-when (compile load eval)
   #+franz (sstatus feature long-filenames)
   #-franz (pushnew :long-filenames *features*))


#+(and unix (not long-filenames))
(defun filetokp (kind tok)
   (let ((chars (nreverse (exploden tok)))
         (count 0))
      (while (and chars (not (= (pop chars) #//)))
         (incf count))
      (<= count 11)))

#+(or (not unix) long-filenames)
(defun filetokp (kind tok) t)


;;; MJCG 8/11/88 for HOL88
;;; Changed help and kwic cases - looking for help files goes through
;;; variable %search-path
;;; extensions should not exceed 2 characters
;;; Clauses for jac and doc added by MJCG 7 Dec 1989.

(defun fileof (kind name) 
   (case kind
      (theory (catenate name ".th"))
      (theorydata (catenate name ".th"))
      (theoremdata (catenate name ".th"))
      (help (catenate name ".hlp"))
      (doc  (catenate name ".doc"))
      (jac  (catenate name ".jac"))
      (kwic (catenate name ".kwic"))
      (ml (catenate name ".ml"))
      (lisp (catenate name "_ml.l"))
      (code (catenate name "_ml.o"))
      (|m*| (catenate name ".m*"))
      (t
         (lcferror (cons kind '(bad arg fileof))))))


;;; Exec-system-command. Return an integer representing success status.

(defun exec-system-command (cmd)
   #+franz
   (apply '*process (list cmd))
   #+lucid
   (shell (string cmd))
   #+kcl
   (system (string cmd))
   #+allegro
   (shell (string cmd))
   #-(or franz lucid kcl allegro)
   (failwith "system: no system commands implemented"))

;;; Call help/Reference/doc-to-help.sed on .doc help file
;;; Call help/Reference/jac-to-help.sed on .jac help file
;;; Replaces: (exec-system-command (uconcat "more " fname))
;;; MJCG 7 Dec 1989
;;; MJCG 12/11/90: Replaced "more" by %display-function
;;; TFM 90.12.01: help/Reference/ changed to help/bin/
(setq %display-function "cat")

(defun display-file (fname kind)
   #+unix
   (exec-system-command 
    (uconcat "sed -f "
             %hol-dir
             "/help/bin/"
             (if (eq kind '|jac|) "jac-to-help.sed " "doc-to-help.sed ") 
             "'" fname "'"
             " | " 
             %display-function))
   #-unix
   (with-open-file (stream fname :direction :input)
      (let (line)
         (loop
            (multiple-value-bind (line eof-p)
               (read-line stream nil t nil)
               (when (or eof-p (not (stringp line)))
                  (return nil))
               (princ line) (terpri)))
         (terpri))))


;;; Keyword facility deleted                    [TFM 90.09.08]
;;; (defun keyword-search (key fname)
;;;    #+unix
;;;    (exec-system-command (uconcat "fgrep '" key "' " fname " | more"))
;;;    #-unix
;;;    (with-open-file (stream fname :direction :input)
;;;       (let (line (key-string (string key)))
;;;          (loop
;;;             (multiple-value-bind (line eof-p)
;;;                (read-line stream nil t nil)
;;;                (when (search key-string line)
;;;                   (princ line) (terpri))
;;;                (when (or eof-p (not (stringp line)))
;;;                   (return nil))))
;;;          (terpri))))


;;; MJCG 3/11/88 for HOL88
;;; Some System-dependent commands in ML
;;; dml-ed versions in F-dml.l

(defun ml-getenv (thing)
   #+unix (let ((varble #+franz (getenv thing)
                        #+kcl   (system:getenv (string thing))
                        #+lucid (environment-variable (string thing))
                        #+allegro (system:getenv thing)))
               (cond ((or (eq varble '||) (null varble))
                     (msg-failwith "getenv" "No value for " thing))
                     (t #+franz varble
                        #-franz (intern varble))))
   #-unix (msg-failwith "getenv" "Unix-dependant function")
)

(defun ml-host_name ()
   #+franz (sys:gethostname)
   #-franz (machine-version))


(defun ml-link (old new) 
   #-franz
   (progn
      (setq old (string old)) (setq new (string new)))
   (if (equal old new)
      (failwith "link: source and destination equal")
      (if (probe-file old) 
         (prog2
            #+franz
            (sys:link old new)
            #+(and unix (not franz))
            (exec-system-command
               (concatenate 'string "ln " old " "  new))
            #-unix
            (failwith "link: cannot link files")
            nil)
         (failwith (concat "link: " old " doesn't exist")))))


(defun ml-unlink (file) 
   (if (probe-file #+franz file #-franz (string file)) 
      #+franz (sys:unlink file)
      #-franz (delete-file (string file))
      (failwith (concat "unlink: " file " doesn't exist"))))


;;; MJCG 3/11/88 for HOL88
;;; Definitions of ML functions for character IO from ML 

(defun ml-openi (file)
   (if (probe-file #+franz file #-franz (string file))
      #+franz (infile file)
      #-franz (open (string file) :direction :input)
      (failwith (concat "openi: " file " doesn't exist"))))

#+franz
(defun write-and-drain (port exp) 
   (patom exp port) (drain port) nil)

#-franz
(defun write-and-drain (port exp) 
   (princ exp port) (finish-output port) nil)


#+franz
(defun tty-write-and-drain (exp) 
   (patom exp) (drain) nil)

#-franz
(defun tty-write-and-drain (exp) 
   (princ exp) (finish-output) nil) 


(defun ml-append_openw (file)
   #+franz (outfile file 'a)
   #-franz
   (open (string file) :direction :output :if-exists :append
      :if-does-not-exist :create))


;;; call Lisp compiler from Lisp (for compiling ML)
;;; %liszt for franz lisp set by makefile

(defun compile-lisp (filename)
   (princ "Calling Lisp compiler") (terpri)
   #+franz
   (cond
      ((not
            (zerop
               (exec-system-command (concat %liszt " -w -q " filename))))
         (msg-failwith '|compile| "error during Lisp compilation")))
   #-franz
   (errortrap
      #'(lambda (x) (msg-failwith '|compile| "Lisp compilation failed"))
      ;; added binding of ANSI variable *compile-verbose* - JAC 19.06.92
      (let ((*load-verbose* nil) (*compile-verbose* nil))
         (compile-file filename
            :output-file (make-object-filename (string filename)))))
   (cond
      ((not %debug)
         (errortrap
            #'(lambda (x)
               (msg-failwith '|compile| "couldn't delete " filename))
            (#+franz sys:unlink #-franz delete-file filename)))))


;;; End of file
