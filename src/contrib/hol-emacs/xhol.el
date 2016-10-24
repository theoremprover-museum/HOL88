
;; xhol -- Run HOL from within emacs
;; Principle author: Phillip J. Windley, University of California, Davis
;; November 26, 1988

;; This file must be run in conjunction with interpreter.el

(require 'hol) 
(require 'interp)

;;; Functions and variables for specifying the interpreter to use

;;; add interpreter key bindings to mode map
(interpreter-evaluation-commands *hol-mode-map*)

;;; add xhol specific key bindings to mode map
(defun xhol-commands (keymap)
  "Add specialized xhol command key bindings to a keymap.  
This may be used on more than one keymap.  They are defined in 
interpreter interaction mode and can be added to any other mode map
that is appropriate."

  (define-key keymap "\C-c\C-b" 'xhol-backup)
  (define-key keymap "\C-c\C-r" 'xhol-rotate-goal-stack)
  (define-key keymap "\C-c\C-p" 'xhol-print-top-goal)
  (define-key keymap "\C-ch" 'xhol-help))

(xhol-commands *hol-mode-map*) 
(xhol-commands *interpreter-interaction-mode-map*) 

(fset 'run-hol 'run-interpreter)

(defvar *interpreter-program-name* "hol"
   "*Program invoked by the `run-interpreter' command.")

(defvar *interpreter-under-emacs-switch* " "
   "*Switch to pass to interpreter to tell it that its 
running under emacs.")
(defvar *interpreter-program-arguments* nil
   "*Arguments passed to the interpreter by the `run-interpreter' command.")

(defvar *interpreter-buffer-name* "*hol*"
   "*Name of buffer to start interpreter in.")

(defvar *interpreter-process-name* "hol"
   "*Name to use for process identification.")

(defvar *interpreter-mode-line-name* "HOL: "
   "*String to print on modeline before process status.")

(defvar *interpreter-connection-type* t
   "*Set to t to use pty's, nil to use pipes.")

(defvar *interpreter-default-directory* nil
   "*Default directory to start intepreter in, nil for don't care.")

(defvar *interpreter-history* nil
   "*Should commands sent to interpreter be display in interaction buffer?
Nil for no.")

;;; For HOL, % is comment string, but it also has special meaning
;;; to format in emacs, so we double it.

;;; leave these empty for now.  
(defvar *interpreter-begin-comment* ""
   "*String that begins comments in the interpreter.")

(defvar *interpreter-end-comment* ""
   "*String that ends comments in the interpreter.")

(defvar *interpreter-result-highlight-string* ""
   "*Default string to highlight results from the interpreter
in the Interaction buffer.")

;;; var hooks are run before starting the process to change the default
;;; values of variables in the xhol file.
(setq interpreter-var-hook hol-var-hook)

;;; start hooks are run after the process has been started, they can be
;;; used to send messages to the interpreter.
(setq interpreter-start-hook hol-start-hook)


(fset 'interpreter-forward-expr 'hol-forward-expr)
(fset 'interpreter-backward-expr 'hol-backward-expr)

;;; output routines and process filter association list

;;; HOL doesn't supply command characters for emacs, so this isn't used.
(defvar *interpreter-process-filter-alist* nil
  "Table used to decide how to handle process filter commands.
Value is a list of entries, each entry is a list of two items.

The first item is the character that the process filter dispatches on.
The second item is the action to be taken, a function.

When the process filter sees a command whose character matches a
particular entry, it calls the handler with two arguments: the action
and the string containing the rest of the process filter's input
stream.  It is the responsibility of the handler to invoke the action
with the appropriate arguments, and to reenter the process filter with
the remaining input.")


(defun interpreter-default-output (string)
   (if (and (not (string-equal string "\n"))
            (not (string-equal "\n " string )))
      (interpreter-write-with-message "" string)))


;;; functions for finding beginning and end of expression.

;;; search for a double ;; and then the preceeding blanks line.
(defun hol-backward-expr ()
   "Searches for the blank line before the last two semi-colons."
   (progn
      (re-search-backward ";;" nil t)
      (re-search-backward "^[ ]*$" nil t)))

;;; search for a double ;; and then the following blanks line.
(defun hol-forward-expr ()
   "Searches for the blank line following next two semi-colons."
   (progn
      (re-search-forward ";;" nil t)
      (re-search-forward "^[ ]*$" nil t)))


;;; new key bindings for functions defined here

(defun xhol-backup ()
   (interactive)
   (interpreter-send-string "backup();;\n"))

(defun xhol-print-top-goal ()
   (interactive)
   (interpreter-send-string "top_goal();;\n"))

(defun xhol-rotate-goal-stack (number)
   (interactive "P")
   (if number (interpreter-send-string (concat "rotate("
                                               (int-to-string number)
                                               ");;\n"))
              (interpreter-send-string "rotate(1);;\n")))
              

(defun xhol-help ()
   (interactive)
   (interpreter-send-string (concat "help `" 
                                    (read-string "Topic: ")
                                    "`;;\n")))



