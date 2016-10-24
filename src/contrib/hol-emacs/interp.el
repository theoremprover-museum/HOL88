
;; interpreter -- Run an interpreter as a subprocess of emacs
;; Principle author: Phillip J. Windley, University of California, Davis
;; November 26, 1988

;; This file must be run in conjunction with another file which specifies
;; what interpreter to run, etc.  See xuscheme.el for an example.

;; Friday August 18, 1989 - PJW
;;
;; Added history variable and the ability to output the text being
;; sent to the interpreter in the interaction buffer if the
;; variable *interpreter-history* is true.

;; Wednesday September 20, 1989 - PJW
;;
;; Added interpreter-recenter-output-buffer command for recentering the
;; interaction buffer when it gets out of sync.

;; Monday January 22, 1990 - SMB
;;
;; Added variable *interpreter-max-string-length* to alleviate the stopping
;; problem that emacs has with sending large ranges of text to a process.
;; Emacs will send *interpreter-max-string-length* bytes of text at a time
;; until the range of text to be sent is exhausted.

(provide 'interp)

;;; Mode stuff goes here

(defun interpreter-evaluation-commands (keymap)
  "Add evaluation key bindings to a keymap.  This may be used
on more than one keymap.  They are defined in interpreter
interaction mode and can be added to any other mode map
that is appropriate.  

For example, if you have a mode specifically for you interpreter, 
these can be added in the interpreter specific code to provide
this mode's functionality in other buffers as well."
  (define-key keymap "\C-x\C-e" 'interpreter-send-previous-expression)
  (define-key keymap "\eo" 'interpreter-send-buffer)
  (define-key keymap "\e\C-m" 'interpreter-send-previous-expression)
  (define-key keymap "\e\C-z" 'interpreter-send-region)
  (define-key keymap "\C-cn" 'interpreter-send-next-expression)
  (define-key keymap "\C-cp" 'interpreter-send-previous-expression)
  (define-key keymap "\C-c\C-l" 'interpreter-recenter-output-buffer)
  (define-key keymap "\C-c\C-t" 'interpreter-toggle-history)
  (define-key keymap "\C-c\C-s" 'interpreter-select-process-buffer))

(defun interpreter-interaction-mode ()
  "Major mode for interacting with the inferior interpreter process.

All output from the interpreter process is written in the interpreter
process buffer, which is by the variable \"*interpreter-buffer-name*\".
The result of evaluating a interpreter expression is also printed in the
process buffer, in a comment with the string given in
\"*interpreter-result-highlight-string*\" to highlight it.  If the process
buffer is not visible at that time, the value will also be displayed in the
minibuffer.  If an error occurs, the process buffer will automatically pop
up to show you the error message.

While the interpreter process is running, the modelines of all buffers in
interpreter-mode are modified to show the state of the process.  The
possible states and their meanings are:

input		waiting for input
run		evaluating

The process buffer's modeline contains additional information where
the buffer's name is normally displayed; the information depends on the
interpreter being run.

Some possible command interpreter types and their meanings are:

[Evaluator]	read-eval-print loop for evaluating expressions

Commands:
Delete converts tabs to spaces as it moves back.
Blank lines separate paragraphs.  Semicolons start comments.
\\{*interpreter-interaction-mode-map*}

Entry to this mode calls the value of interpreter-interaction-mode-hook
with no args, if that value is non-nil."
  (interactive)
  (kill-all-local-variables)
  (interpreter-interaction-mode-initialize)
;  (interpreter-mode-variables)
  (make-local-variable '*interpreter-previous-send*)
  (run-hooks 'interpreter-interaction-mode-hook))

(defun interpreter-interaction-mode-initialize ()
  (use-local-map *interpreter-interaction-mode-map*)
  (setq major-mode 'interpreter-interaction-mode)
  (setq mode-name (concat *interpreter-mode-line-name* "Interaction")))

(defun interpreter-interaction-mode-commands (keymap)
  (define-key keymap "\C-c\C-m" 'interpreter-send-current-line)
  (define-key keymap "\C-c\C-p" 'interpreter-send-proceed)
  (define-key keymap "\C-c\C-y" 'interpreter-yank-previous-send))

(defvar *interpreter-interaction-mode-map* nil)

(if (not *interpreter-interaction-mode-map*)
    (progn
      (setq *interpreter-interaction-mode-map* (make-keymap))
      (interpreter-evaluation-commands *interpreter-interaction-mode-map*)
      (interpreter-interaction-mode-commands 
                                        *interpreter-interaction-mode-map*)))

(defun interpreter-enter-interaction-mode ()
  (save-excursion
    (set-buffer (interpreter-process-buffer))
    (if (not (eq major-mode 'interpreter-interaction-mode))
	    (interpreter-interaction-mode-initialize)
	    (interpreter-interaction-mode))))


;;; Internal Variables

(defvar *interpreter-process-command-line* nil
  "Command used to start the most recent interpreter process.")

(defvar *interpreter-previous-send* ""
  "Most recent expression transmitted to the interpreter process.")

(defvar *interpreter-previous-result* ""
  "Most recent expression received from the interpreter process.")

(defvar *interpreter-allow-output-p* t
  "Allow output to the buffer.")

(defvar *interpreter-runlight-string* ""
  "String to display status of interpreter.")

(defvar *interpreter-mode-string* ""
  "String for interpreter mode.")

(defvar *interp-temp-name* nil
  "Temporary name to write buffer to for loading into interpreter.")

(defvar *interpreter-max-string-length* 1500
  "Maximum number of chars to send at a time to a process.")


;;; Functions for staring the thing up

(defun run-interpreter (command-line)
   "Run an interpreter in an inferior process."
   (run-hooks 'interpreter-var-hook)
   (interactive
      (list (let ((default 
                    (or *interpreter-process-command-line*
		       (interpreter-default-command-line))))
	   (if current-prefix-arg
	       (read-string "Run interpreter: " default)
	       default))))
   (setq *interpreter-process-command-line* command-line)
   (switch-to-buffer-other-window (interpreter-start-process command-line)))

(defun interpreter-default-command-line ()
  (concat *interpreter-program-name* *interpreter-under-emacs-switch*
	  (if *interpreter-program-arguments*
	      (concat " " *interpreter-program-arguments*)
	      "")))

(defun reset-interpreter ()
  "Reset the interpreter process."
  (interactive)
  (let ((process (get-process *interpreter-process-name*)))
    (cond ((or (not process)
	       (not (eq (process-status process) 'run))
	       (yes-or-no-p
"The interpreter process is running, are you SURE you want to reset it? "))
	   (message "Resetting interpreter process...")
	   (if process (kill-process process t))
	   (interpreter-start-process *interpreter-process-command-line*)
	   (message "Resetting interpreter process...done")))))


;;;; Basic Process Control

(defun interpreter-start-process (command-line)
  (let ((buffer (get-buffer-create *interpreter-buffer-name*)))
    (let ((process (get-buffer-process buffer)))
      (save-excursion
	(set-buffer buffer)
	(if (and process (memq (process-status process) '(run stop)))
	    (set-marker (process-mark process) (point-max))
	    (progn (if process (delete-process process))
                   (if *interpreter-default-directory* 
                       (cd  *interpreter-default-directory*))
		   (goto-char (point-max))
		   (interpreter-interaction-mode)
		   (setq process
			 (let ((process-connection-type 
                                    *interpreter-connection-type*)) 
			   (apply 'start-process
				  (cons *interpreter-process-name*
					(cons buffer
					      (interpreter-parse-command-line
					       command-line))))))
		   (set-marker (process-mark process) (point-max))
		   (interpreter-process-filter-initialize t)
		   (interpreter-modeline-initialize)
		   (set-process-sentinel process 'interpreter-process-sentinel)
		   (set-process-filter process 'interpreter-process-filter)
		   (run-hooks 'interpreter-start-hook)))))
    buffer))

(defun interpreter-parse-command-line (string)
  (setq string (substitute-in-file-name string))
  (let ((start 0)
	(result '()))
    (while start
      (let ((index (string-match "[ \t]" string start)))
	(setq start
	      (cond ((not index)
		     (setq result
			   (cons (substring string start)
				 result))
		     nil)
		    ((= index start)
		     (string-match "[^ \t]" string start))
		    (t
		     (setq result
			   (cons (substring string start index)
				 result))
		     (1+ index))))))
    (nreverse result)))

(defun interpreter-wait-for-process ()
  (sleep-for 2)
  (while interpreter-running-p
    (sleep-for 1)))


;;; Initialization routines

(defun interpreter-modeline-initialize ()
  (setq *interpreter-runlight-string* "")
  (setq *interpreter-mode-string* "")
  (setq mode-line-buffer-identification 
        (list *interpreter-mode-line-name* *interpreter-mode-string*)))

(defun interpreter-process-filter-initialize (running-p)
  (setq interpreter-running-p running-p)
  (setq *interpreter-allow-output-p* t)
  (setq interpreter-mode-line-process '(": " *interpreter-runlight-string*))
  (setq *interpreter-previous-result* nil)
  )


;;; Filter routines

(defun interpreter-process-sentinel (proc reason)
  (let ((inhibit-quit t))
    (interpreter-process-filter-initialize (eq reason 'run))
    (if (eq reason 'run)
	(interpreter-modeline-initialize)
	(progn
	 (setq interpreter-mode-line-process "")
	 (setq *interpreter-mode-string* "no process"))))
  (if (not (memq reason '(run stop)))
      (progn (beep)
	     (message
"The interpreter process has died!  Do M-x reset-interpreter to restart it"))))

(fset 'interpreter-default-output 'interpreter-write-value)

(setq interpreter-output-process 'interpreter-write-value)

(defun interpreter-process-filter (process string)
  (progn
     (interpreter-enter-input-wait)
     (let* ((start (string-match "\e" string))
	    (next-num (if start (+ start 1) 0))
	    (next (string-match "\e" string next-num)))
       (let ((before 
                (substring string 0 (if (not start) 0 start)))
             (after 
                (substring string (if (not start) 0 (+ start 2))
                                  (if (not next) (length string) next)))
             (command
                (if (not start) nil (aref string (+ start 1)))))
        (progn
          (if (> (length before) 0)
                 (progn (setq *interpreter-previous-result* before)
                        (funcall interpreter-output-process before)))
          (if *interpreter-process-filter-alist*
                   (interpreter-process-filter-dispatch command))
          (if (> (length after) 0) 
                 (progn (setq *interpreter-previous-result* after)
                        (funcall interpreter-output-process after)))
          (if next 
                 (interpreter-process-filter process 
	 		       (substring string next))))))))

(defun interpreter-process-filter-dispatch (char)
  (let ((entry (assoc char *interpreter-process-filter-alist*)))
    (if entry
	(setq interpreter-output-process (nth 1 entry))
	(setq interpreter-output-process 'interpreter-default-output))))



;;; output routines
(defun interpreter-message (string)
  (if (not (zerop (length string)))
      (interpreter-write-message-1 string (format 
           (concat *interpreter-begin-comment*
                   " %s "
                   *interpreter-end-comment*) string))))

(defun interpreter-write-value (string)
   (interpreter-write-with-message
           *interpreter-result-highlight-string* string))

(defun interpreter-write-with-message (msg string)
   "Write a message to the interpreter buffer with a message."
   (interpreter-write-message-1 string (format 
           (concat *interpreter-begin-comment*
                   msg "%s" 
                   *interpreter-end-comment*) string)))

(defun interpreter-write-message-1 (message-string output-string)
  (let* ((process (get-process *interpreter-process-name*))
	 (window (get-buffer-window (process-buffer process))))
    (if (or (not window)
	    (not (pos-visible-in-window-p (process-mark process)
					  window)))
	(message "%s" message-string)))
  (interpreter-guarantee-newlines 0)
  (interpreter-process-filter-output output-string))
   
;;;; Process Filter Output


(defun interpreter-process-filter-output (&rest args)
  (if *interpreter-allow-output-p*
      (save-excursion
	(interpreter-goto-output-point)
	(apply 'insert-before-markers args))))

(defun interpreter-guarantee-newlines (n)
  (if *interpreter-allow-output-p*
      (save-excursion
	(interpreter-goto-output-point)
	(let ((stop nil))
	  (while (and (not stop)
		      (bolp))
	    (setq n (1- n))
	    (if (bobp)
		(setq stop t)
		(backward-char))))
	(interpreter-goto-output-point)
	(while (> n 0)
	  (insert-before-markers ?\n)
	  (setq n (1- n))))))

(defun interpreter-goto-output-point ()
  (let ((process (get-process *interpreter-process-name*)))
    (set-buffer (process-buffer process))
    (goto-char (process-mark process))))


;;; Functions for sending strings to the process

(defun interpreter-send-string (&rest strings)
  "Send the string arguments to the interpreter process.
The strings are concatenated and terminated by a newline."
  (cond ((not (interpreter-process-running-p))
	 (if (yes-or-no-p "The interpreter process has died.  Reset it? ")
	     (progn
	       (reset-interpreter)
	       (interpreter-wait-for-process)
	       (goto-char (point-max))
	       (apply 'insert-before-markers strings)
	       (interpreter-send-string-1 strings))))
	(t (interpreter-send-string-1 strings))))

(defun interpreter-send-string-1 (strings)
  (let ((string (apply 'concat strings)))
    (interpreter-send-string-2 string)
    (if *interpreter-history* 
        (interpreter-write-with-message "" (concat string "\n")))
    (setq *interpreter-previous-send* string)))

(defun interpreter-send-string-2 (string)
  (progn 
     (interpreter-exit-input-wait)
     (let ((process (get-process *interpreter-process-name*))
	   (start 0)
	   (end (length string))
	   current)
       (cond ((not (equal "\n" (substring string (- end 1) end)))
	      (setq string (concat string "\n"))
	      (setq end (length string))))
       (while (< start end)
	 (setq current (min end (+ start *interpreter-max-string-length*)))
	 (send-string process (substring string start current))
	 (setq start current))
     (if (interpreter-process-buffer-current-p)
	 (set-marker (process-mark process) (point))))))

(defun interpreter-yank-previous-send ()
  "Insert the most recent expression at point."
  (interactive)
  (push-mark)
  (insert *interpreter-previous-send*))

(defun interpreter-select-process-buffer ()
  "Select the interpreter process buffer and move to its output point."
  (interactive)
  (let ((process (or (get-process *interpreter-process-name*) 
                     (error "No interpreter process"))))
    (let ((buffer (or (process-buffer process) (error "No process buffer"))))
      (let ((window (get-buffer-window buffer)))
	(if window
	    (select-window window)
	    (switch-to-buffer buffer))
	(goto-char (process-mark process))))))

(defun interpreter-toggle-history ()
   "Toggle the history function."
   (interactive)
   (if *interpreter-history* (progn (setq *interpreter-history* nil)
                                  (message "History function is off"))
                           (progn (setq *interpreter-history* t)
                                  (message "History function is on"))))

;;; freely borrowed from tex-mode.el
(defun interpreter-recenter-output-buffer (linenum)
  "Redisplay the interaction buffer so that most recent output can be seen.
The last line of the buffer is displayed on
line linenum of the window, or centered if linenum is nil."
  (interactive "P")
  (let ((inter-buf (get-buffer *interpreter-buffer-name*))
        (old-buffer (current-buffer)))
    (if (null inter-buf)
        (message "No interaction buffer")
      (pop-to-buffer inter-buf)
      (bury-buffer inter-buf)
      (goto-char (point-max))
      (recenter (if linenum
                    (prefix-numeric-value linenum)
                  (/ (window-height) 2)))
      (pop-to-buffer old-buffer)
      )))

(defun interpreter-send-region (start end)
  "Send the current region to the interpreter.
The region is sent terminated by a newline."
  (interactive "r")
  (if (interpreter-process-buffer-current-p)
      (progn (goto-char end)
	     (set-marker 
               (process-mark (get-process *interpreter-process-name*)) end)))
  (interpreter-send-string (buffer-substring start end)))

(defun interpreter-send-next-expression ()
  "Send the expression to the right of `point' to the interpreter process."
  (interactive)
  (let ((start (point)))
    (interpreter-send-region start 
              (save-excursion (interpreter-forward-expr) (point)))))

(defun interpreter-send-previous-expression ()
  "Send the expression to the left of `point' to the interpreter process."
  (interactive)
  (let ((end (point)))
    (interpreter-send-region 
         (save-excursion (interpreter-backward-expr) (point)) end)))

;
; This is hol specific and shouldn't be in here, but I'm not sure
; what to do with it.  For right now, it stays.
;
(defun interpreter-send-buffer ()
  "Send the current buffer to the interpreter process."
  (interactive)
  (if (not *interp-temp-name*)
     (setq *interp-temp-name* 
             (concat *interpreter-default-directory* "/"
                     (make-temp-name "hol") ".ml")))
  (if (interpreter-process-buffer-current-p)
      (error "Not allowed to send this buffer's contents to the interpreter"))
  (write-region (point-min) (point-max) *interp-temp-name*)
  (interpreter-send-string 
       (concat "loadt `" *interp-temp-name* "`;;\n"
               "system `/bin/rm " *interp-temp-name* "`;;\n")))

(defun interpreter-send-char (char)
  "Prompt for a character and send it to the interpreter process."
  (interactive "cCharacter to send: ")
  (send-string *interpreter-process-name* (char-to-string char)))


;;; Buffer functions

(defun interpreter-process-running-p ()
  "True iff there is a interpreter process whose status is `run'."
  (let ((process (get-process *interpreter-process-name*)))
    (and process
	 (eq (process-status process) 'run))))

(defun interpreter-process-buffer ()
  (let ((process (get-process *interpreter-process-name*)))
    (and process (process-buffer process))))

(defun interpreter-process-buffer-window ()
  (let ((buffer (interpreter-process-buffer)))
    (and buffer (get-buffer-window buffer))))

(defun interpreter-process-buffer-current-p ()
  "True iff the current buffer is the interpreter process buffer."
  (eq (interpreter-process-buffer) (current-buffer)))


;;; Running light variables and routines

(defun interpreter-set-runlight (runlight)
  (setq *interpreter-runlight-string* runlight)
  (interpreter-modeline-redisplay))

(defun interpreter-modeline-redisplay ()
  (save-excursion (set-buffer (other-buffer)))
  (set-buffer-modified-p (buffer-modified-p))
  (sit-for 0)
  (setq mode-line-buffer-identification 
        (list *interpreter-mode-line-name* *interpreter-runlight-string*)))

(defconst interpreter-runlight:running "run"
  "The character displayed when the interpreter process is running.")

(defconst interpreter-runlight:input "input"
  "The character displayed when the interpreter process is waiting for input.")

(defun interpreter-enter-input-wait ()
  (interpreter-set-runlight interpreter-runlight:input)
  (setq interpreter-running-p nil))

(defun interpreter-exit-input-wait ()
  (interpreter-set-runlight interpreter-runlight:running)
  (setq interpreter-running-p t))

