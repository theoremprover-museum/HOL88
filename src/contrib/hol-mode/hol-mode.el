;;; File: hol-mode.el
;;;
;;; HOL (Higher Order Logic) Mode 
;;;
;;; (C) Copyright 1989 Kim Dam Petersen.
;;;

;;; Description
;;;
;;; Mode for interactive editing and execution of HOL proof scripts
;;;
;;; The editing mode defines the syntax of HOL words, comments,
;;; strings and terms.
;;; The execution mode defines an interface from the editing mode to a
;;; HOL process running under emacs control.  This interface consists
;;; of a predefined collection of operations for transmitting selected
;;; ML code (e.g. goals, tactics) to the HOL process.

;;; Customization
;;;
;;; Two hooks exists for customization:  `hol-mode-hook`  for editor
;;; buffers and `hol-shell-hook'  for hol process.
;;;
;;; The name of the HOL program is in variable `hol-prog-name', and the
;;; emacs name of the HOL process is found in variable `hol-process-name'.
;;; These should be changed prior to starting the HOL process; e.g. by
;;; being set in the `local variables' part of the HOL proof file.

;;; Low level HOL process interface
;;;
;;; The emacs-lisp function `hol-send-string' is the basic function
;;; for sending input to the HOL process.  Voluminous input is stored
;;; in a temporary which is loaded using ``loadt'', hence input should
;;; make up complete ML expression(s).


;;;
;;; HOL mode constants, variables and functions.
;;;

(defconst hol-mode-version-string
  "HOL mode Version 2.01. Sep 15 1992, (C) Copyright 1989,1991,1992 Kim Dam Petersen."
  "The HOL Version")

(defvar hol-mode-syntax-table nil
  "The syntax table used in HOL mode")

(defvar hol-mode-map nil
  "The mode map used in HOL mode")

;;; Making a syntax table for HOL mode
(setq hol-mode-syntax-table (make-syntax-table))
(modify-syntax-entry ?\( "()1"  hol-mode-syntax-table)
(modify-syntax-entry ?\) ")(4"  hol-mode-syntax-table)
(modify-syntax-entry ?\\ "\\"   hol-mode-syntax-table)
(modify-syntax-entry ?\* ". 23" hol-mode-syntax-table)
(modify-syntax-entry ?_  "w"    hol-mode-syntax-table)
(modify-syntax-entry ?\' "w"    hol-mode-syntax-table)
(modify-syntax-entry ?%  "< 1"    hol-mode-syntax-table)
(modify-syntax-entry ?<  "< 2"    hol-mode-syntax-table)
(modify-syntax-entry ?>  "> 3"    hol-mode-syntax-table)
(modify-syntax-entry ?%  "> 4"    hol-mode-syntax-table)

;;; Defining a local keymap for HOL mode
(setq hol-mode-map (make-sparse-keymap))
(define-key hol-mode-map "\C-c\C-v" 'hol-mode-version)
(define-key hol-mode-map "\C-c\x"   'hol-select-shell)
;; HOL ML interaction
(define-key hol-mode-map "\C-c\C-b" 'hol-send-buffer)
(define-key hol-mode-map "\C-c\C-f" 'hol-send-file)
(define-key hol-mode-map "\C-c\C-c" 'hol-send-expression)
(define-key hol-mode-map "\C-c\C-r" 'hol-send-region)
(define-key hol-mode-map "\C-c\C-l" 'hol-send-let)
;; HOL prove interaction
(define-key hol-mode-map "\^Cs"     'hol-send-setgoal)
(define-key hol-mode-map "\^Ce"     'hol-send-expand-THEN)
(define-key hol-mode-map "\^Cr"     'hol-send-expand-region)
(define-key hol-mode-map "\^Cb"     'hol-send-backup)

;;; Defining HOL-mode
(defun hol-mode ()
  "Major mode for developing HOL proofs.
   
Allows interaction with an inferior HOL process.

Default keys:

  C-c x    Start HOL process and switch to the HOL process buffer
  C-c C-v  HOL mode version

  C-c C-b  Send buffer to the HOL process
  C-c C-f  Send a file to the HOL process
  C-c C-c  Send an ML expression (terminated by `;;') to the HOL process
  C-c C-r  Send current region as an ML expression to the HOL process

  C-c s    Send next HOL term as setgoal to HOL process
  C-c e    Send a tactic (terminated by `THEN'/`THENL') to the HOL process
  C-c r    Send current region as a tactic to the HOL process
  C-c b    Send a backup to the HOL process

The HOL program and process names may be set using the local variables:
  hol-program-name : name of the HOL program (Unix) [default: \"hol\"]
  hol-process-name : name of the HOL process (Emacs) [default: \"HOL\"]

The hol-mode and the hol-shell may be customized by use of the hooks:
  hol-mode-hook  : applied in every hol-mode buffer
  hol-shell-hook : applied in hol-shell buffer"

  (interactive)

  (setq major-mode 'hol-mode)
  (setq mode-name  "HOL")

  (set-syntax-table hol-mode-syntax-table)
  (use-local-map hol-mode-map)

  (make-local-variable 'comment-start)
  (setq comment-start "%<")
  (make-local-variable 'comment-end)
  (setq comment-end ">%")

  (make-local-variable 'paragraph-start)
  (setq paragraph-start (concat "^[\t ]*$\\|" page-delimiter))

  (make-local-variable 'paragraph-separate)
  (setq paragraph-separate paragraph-start)

  (run-hooks 'hol-mode-hook))

(defun hol-mode-version ()
  "Print the version of HOL mode"
  (interactive)
  (message hol-mode-version-string))

(defun hol-indent-line ()
  "Indent current line of HOL proof."
  (interactive)
  (message "hol-indent-line not Implemented yet."))

;;;
;;; HOL Shell constants, variables and functions.
;;;

(defvar hol-program-name "hol" "*The name of the HOL program")
(defvar hol-process-name "HOL" "*The Emacs name of the hol-process")

(defconst hol-tmp-file   "/tmp/hol-tmp.ml")

(defconst hol-shell-prompt-pattern "^# *"
  "*The prompt pattern for the inferior shell running HOL.")

(defvar hol-shell-map nil "The mode map for HOL shell.")

(defun get-hol-process ()
  "Returns the hol-process.  Start it if necessary."
  (hol-shell)
  (get-process hol-process-name))

(defun hol-shell ()
  "Inferior shell, that invokes HOL.
Only one such shell may be active at a time."
  (interactive)
  (if (not (and (get-process hol-process-name)
		(process-status (get-process hol-process-name))))
      (save-excursion
	(let
	    ((prog-nam hol-program-name)
	     (proc-nam hol-process-name))
	(require 'shell)

	(message (concat "Starting " proc-nam "..."))
	;; Start the shell
	(set-buffer (make-shell proc-nam prog-nam))
	(erase-buffer)

	;; Make hol-pro{gram,cess}-name local variables
	(make-local-variable 'hol-program-name)
	(setq hol-program-name prog-nam)
	(make-local-variable 'hol-process-name)
	(setq hol-process-name proc-nam)
	(setq hol-tmp-file
	      (concat "/tmp/hol-" (process-id(get-hol-process)) "-tmp.ml"))
	(if hol-shell-map
	    ()
	  (setq hol-shell-map (copy-sequence shell-mode-map))
	  (define-key hol-shell-map "\C-c\C-f" 'hol-send-file))
	(use-local-map hol-shell-map)

	(make-local-variable 'shell-prompt-pattern)
	(setq shell-prompt-pattern hol-shell-prompt-pattern)

	(setq major-mode 'hol-shell)
	(setq mode-name  (concat proc-nam " shell"))
	(setq mode-line-format
	      "-----Emacs: %17b   %M   %[(%m: %s)%]----%3p--%-")
	(let
	    ((procs (process-list)))
	  (while (and (consp procs)
		      (not (string-equal (process-name (car procs))
				    proc-nam)))
	    (setq procs (cdr procs)))
	  (set-process-filter (car procs) 'hol-process-filter))
	(message (concat "Starting " proc-nam "...done"))
	(run-hooks 'hol-shell-hook)))))

;;; Process output from HOL process
(defun hol-process-filter (proc str)
  "Filter to handle output from the inferior HOL shell."
  (let ((cur (current-buffer))
	(pop-up-windows t))
    (if (eq cur (process-buffer proc))
	()
      (pop-to-buffer (concat "*" (process-name proc) "*")))
    (goto-char (point-max))
    (insert str)
    (set-marker (process-mark proc) (point-max))
    (if (eq cur (process-buffer proc))
	()
      (switch-to-buffer-other-window cur))))

(defun hol-select-shell ()
  "Switch to the HOL shell window."
  (interactive)
  (hol-shell)
  (let
      ((pop-up-windows t))
    (pop-to-buffer (process-buffer (get-process hol-process-name)))))

;;; Write a string to a file
(defun write-string (string file &optional append visit)
  "Write string into specified file.
When called from a program, takes two arguments:
STRING and FILE.
Optional third argument APPEND if non-nil means
  append to file.
Optional fourth argument VISIT if t means
  set last-save-file-modtime of buffer to this file's modtime
  and mark buffer not modified."
  (interactive "sString to write: \nFFile to write: ")
  (save-excursion
    (switch-to-buffer "*write string*")
    (erase-buffer)
    (insert-string string)
    (write-region (point-min) (point-max) file append visit)
    (kill-buffer "*write string*")))

;;; Send a string to the HOL process
(defun hol-send-string (str)
  "Send a string to the HOL shell process.
A RET is appended to the string if not already there.
A ``loadt '' command is used if string is long."
  (interactive "sSend string: ")
  (let
      ((proc-buf (process-buffer (get-process hol-process-name))))
    (save-some-buffers)
    ;; Test if string is too long
    (if (< 250 (length str))
	(progn
	  ;; Use a temporary file
	  (write-string str hol-tmp-file nil 1)
	  (if (equal (substring str -1) "\n")
	      ()
	    (write-string "\n" hol-tmp-file t 1))
	  (hol-send-string (concat "loadt`" hol-tmp-file "`;;")))
      ;; Short string send it directly to the HOL process
      (send-string hol-process-name str)
      (message "HOL input: %s" str)
      (if (equal (substring str -1) "\n")
	  ()
	(send-string hol-process-name "\n")))))

;;; Send a file to be executed by HOL
(defun hol-send-file (file)
  "Send a \"loadt file\" command to the HOL shell process."
  (interactive "FSend HOL file: ")
  (save-some-buffers)
  (hol-shell)
  (hol-send-string (concat "loadt `" (expand-file-name file) "`;;")))

;;; Send a region to the HOL process
(defun hol-send-region (beg end)
  "Send the region to the HOL shell process, terminated by a newline."
  (interactive "r")
  ;; Write the region to a temporary file
  (hol-send-string (buffer-substring beg end)))

;;; Send the (nested) let expression to the HOL shell
(defun hol-send-let ()
  "Send the nested let expression to the HOL shell process."
  (interactive)
  (save-excursion
    (let (e b)
      (end-of-line)
      (setq e (point))
      (beginning-of-line)
      (search-forward "let" e)
      (setq b (- (point) 3))
      (search-forward " in\n")
      (setq e (- (point) 3))
      (hol-send-string (concat (buffer-substring b e) ";;")))))

;;; Send the contents of the buffer to the HOL shell
(defun hol-send-buffer ()
  "Send the whole buffer to the HOL shell process."
  (interactive)
  (let
      ((nam (buffer-file-name (current-buffer))))
    (if (stringp nam)
	(hol-send-file nam)
      (hol-send-string (buffer-string)))))

;;; HOL send expression
(defun hol-send-expression ()
  "Send an expression from the current point to `;;' to the HOL process"
  (interactive)
  (let
      ((beg (point))
       (end 0))
    (save-excursion
      (search-forward ";;")
      (setq end (point))
      (hol-send-string (buffer-substring beg end)))
    (goto-char (+ end 1))))

;;; HOL send setgoal
(defun hol-send-setgoal ()
  "Send the goal following the cursor to the HOL process,
encapsulated by ``set_goal([], ... );;''"
  (interactive)
  (save-excursion
    (if (eq (char-after (point)) ?\")
	()
      (search-forward "\"")
      (backward-char 1))
    (let
	((beg (point)))
      (forward-sexp 1)
      (hol-send-string
       (concat "set_goal([]," (buffer-substring beg (point)) ");;")))))

;;; HOL send expand
;(defun hol-send-expand-THEN ()
;  "Send tactic from cursor to nearest THEN/THENL to the HOL process,
;encapsulated by ``expand(...);;''"
;  (interactive)
;  (let ((beg (point))
;	(end 0))
;    (save-excursion
;      (search-forward "THEN")
;     (backward-char 4)
;     (setq end (point))
;     (hol-send-string
;       (concat "expand(" (buffer-substring beg end) ");;")))
;    (goto-char (+ end 5))))

(defun hol-send-expand-THEN ()
  "Send tactic from cursor to next THEN/THENL to the HOL process,
encapsulated by ``expand(...);;''"
  (interactive)
  (let ((beg (point))
	(end 0))
    (save-excursion
      (forward-sexp 1)
      (while (not (or (string= "THEN" (buffer-substring (- (point) 4) (point)))
		      (string= "THENL" (buffer-substring (- (point) 5) (point)))))
	(forward-sexp 1))
      (backward-sexp 1)
      (setq end (point))
      (hol-send-string
       (concat "expand(" (buffer-substring beg end) ");;")))
    (goto-char end)
    (forward-sexp 1)))

;;; Hol expand region
(defun hol-send-expand-region (beg end)
  "Send tactic in current region to the HOL process,
encapsulated by ``expand(...);;''"
  (interactive "r")
  (hol-send-string (concat "expand(" (buffer-substring beg end) ");;")))

;;; HOL send backup
(defun hol-send-backup ()
  "Send a ``backup();;'' command to HOL"
  (interactive)
  (hol-send-string "backup();;"))

;;; Default hooks
(defvar hol-mode-hook
  '(hol-mode-key-setup)
  "*Set up the hol-mode keys")

(defvar hol-shell-hook
  '(hol-mode-key-setup)
  "*Set up the hol-shell keys")

(defun hol-mode-key-setup ()
  "Set up HOL mode funcktion keys."
  (interactive)
  (if (fboundp 'key)
      (progn
	(local-set-key (key 'F6) 'hol-send-backup)
	(local-set-key (key 'F7) 'hol-send-expression)
	(local-set-key (key 'F8) 'hol-send-setgoal)
	(local-set-key (key 'F9) 'hol-send-expand-region)
	(local-set-key (key 'F10) 'hol-send-expand-THEN)
	(local-set-key (key 'F12) 'hol-send-let))))
