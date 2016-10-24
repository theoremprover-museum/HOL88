; sml-debug.el
;
; Extends Lars Bo Nielson's sml-mode to support Andrew Tolmach's sml debugger.
;
; To install, place the following lines in your .emacs file:
; (setq sml-mode-hook 'sml-debug-mode)
; (setq sml-shell-hook 'sml-debug-shell)
;
; Adam T. Dingle
; atd@cs.princeton.edu
;
; Version 1.0

;; Functions of general utility

(defun match-text (n)
; Returns the text that matched a subexpression in a regular expression search.
  (let ((match-b (match-beginning n))
	(match-e (match-end n)))
    (and match-b (buffer-substring match-b match-e))))

(defun looking-back-at-string (s)
; Returns t if the given string precedes point in the current buffer.
  (if (> (point) (length s))
      (string= s (buffer-substring (- (point) (length s)) (point)))
    nil))

; Make a list of all elements of a list that satisfy a given predicate.
(defun select (select_f select_l)
  (if (null select_l) nil
    (if (funcall select_f (car select_l))
	(cons (car select_l) (select select_f (cdr select_l)))
      (select select_f (cdr select_l)))))

;; Label code (from label.el)

; This package allows small markers called labels to be placed temporarily
; on the screen.  A label is not intended to be part of the text in the
; buffer that it marks, and vanishes from the buffer as soon as the label
; vanishes from the screen.  This package was developed to help provide
; visual support for the sml debugger in emacs, but may be of more general
; use as well.
;
; While labels are present in a buffer, the buffer is placed into a minor
; mode called Label mode; while in that mode, the buffer is made read-only
; and should not be modified until all labels have been deleted from it.
; When in Label mode, the key sequence C-x C-q is bound to the command
; abort-label-mode, which removes all labels from the buffer and restores it
; to its unlabeled state.
;
; While in Label mode, a buffer is set to be visiting no file; that ensures
; that labels will not be saved to a file if emacs is exited.  The function
; label-visiting can be used to retrieve the name of the file that a
; labeled buffer was visiting before it was labeled.
;
; If a buffer is visiting a file, it must be unmodified (i.e. must have been
; saved to the file) before it can be labelled; that is so that if Emacs is
; exited while the buffer is still labelled, no information will be lost.
; Consequently, set-label-mode saves an unmodified buffer before entering
; label mode for that buffer.
;
; Adam Dingle
; atd@cs.princeton.edu

(provide 'label)

; Ensure that the epoch::version variable, which tells us whether we are
; running epoch, is set.
(defvar epoch::version nil)

(if epoch::version
    (defvar inverse-attribute (reserve-attribute)))

(make-variable-buffer-local 'label-mode)
(make-variable-buffer-local 'label-list)
(make-variable-buffer-local 'label-was-read-only)
(make-variable-buffer-local 'label-was-visiting)
(make-variable-buffer-local 'label-was-ctlx-ctlq)
(make-variable-buffer-local 'label-was-auto-save)

(or (assq 'label-mode minor-mode-alist)
    (setq minor-mode-alist
	  (cons '(label-mode " Label") minor-mode-alist)))

(defun set-label-mode ()
  (if (and (buffer-modified-p) buffer-file-name) (save-buffer))
     ; Only save if the buffer has been modified, to avoid the "No
     ; changes need to be saved" message.
  (setq label-mode t)
  (setq label-was-read-only buffer-read-only)
  (setq buffer-read-only t)
  (setq label-was-visiting buffer-file-name)
  (set-visited-file-name nil)
  (setq label-was-ctlx-ctlq (local-key-binding "\C-x\C-q"))
  (local-set-key "\C-x\C-q" 'abort-label-mode)
  (setq label-was-auto-save buffer-auto-save-file-name)
  (setq buffer-auto-save-file-name nil)
  (set-buffer-modified-p (buffer-modified-p))  ; redisplay mode line
  )

(defun reset-label-mode ()
  (setq label-mode nil)
  (setq buffer-read-only label-was-read-only)
  (set-visited-file-name label-was-visiting)
  (local-unset-key "\C-x\C-q")
  (if label-was-ctlx-ctlq
      (local-set-key "\C-x\C-q" label-was-ctlx-ctlq))
  (setq buffer-auto-save-file-name label-was-auto-save)
  (set-buffer-modified-p nil)
     ; Since it wasn't modified when we entered label mode, it hasn't been
     ; modified now (although Emacs thinks it has).
  )

(defun abort-label-mode ()
  (interactive)
  (mapcar				; delete labels
   (function (lambda (l)
	       (let ((pos (nth 0 l))
		     (str (nth 1 l)))
		 (un-label pos str)))) label-list)
  (reset-label-mode))

(defun compute-offset (l)
  ; used to convert a position in the source buffer to a position in the
  ; labelled buffer.
  ; apply me to each (position string) pair.
  ; dynamic scope warning: be careful about how you name variables!
  (let ((mypos (nth 0 l))
	(mystr (nth 1 l)))
    (if (or (> pos mypos) (and (= pos mypos) (string< mystr str)))
	(setq offset (+ offset (length mystr))))))

(defun label-cpos (c)
; Given a character position in a possibly labeled buffer, return what the
; position would be if the buffer were not labeled.  If the character
; position falls inside a label, the returned value will be the character
; position at which the label was inserted.
; Reverses the functionality of compute-offset.
; Sorts label-list as a side effect; this should not affect other functions.
  (let ((offset 0))
    (setq label-list
     (sort label-list
	   (function (lambda (a b)
		       (let ((a-pos (nth 0 a))
			     (a-str (nth 1 a))
			     (b-pos (nth 0 b))
			     (b-str (nth 1 b)))
			 (if (< a-pos b-pos) t
			   (if (> a-pos b-pos) nil
			     (string< a-str b-str))))))))
    (mapcar
     (function (lambda (l)
		 (let ((pos (+ offset (nth 0 l)))
		       (strlen (length (nth 1 l))))
		   (setq offset (+ offset (max 0 (min strlen (- c pos))))))))
     label-list)
    (- c offset)))

(defun label (pos str cursor)
  ; Place a label named (str) into the current buffer at character position
  ; (pos).  (pos) corresponds to a character position in the unlabelled
  ; buffer.  If several labels are inserted at the same position, they will
  ; appear in alphabetical order; this is not only cute, but allows us to
  ; find a marker easily to delete it.
  ; The buffer will be placed into label mode if it was not already in that
  ; mode.
  ; If cursor is t, point will be moved to the beginning of the label;
  ; otherwise, point will remain unchanged.
  (if (not label-mode) (set-label-mode))
  (let ((offset 0))
    (mapcar 'compute-offset label-list)
    (setq label-list (cons (list pos str) label-list))
    (save-excursion
      (goto-char (+ pos offset))
      (let ((buffer-read-only nil))
	(insert str))
      (if epoch::version
	  (epoch::add-button  (+ pos offset) (+ pos offset (length str))
			      inverse-attribute)))
    (if cursor (goto-char (+ pos offset)))))
		 
(defun un-label (pos str)
  ; Remove a label named (str) from the current buffer at character position
  ; (pos).
  ; If this is the last label, the buffer will be taken out of label mode.
  ; returns t on success, nil if no such label
  (let ((offset 0) (elem (list pos str)))
    (if (null (select
	       (function (lambda (x) (equal x elem))) label-list))
	nil
      (setq label-list (select
			(function (lambda (x) (not (equal x elem))))
			label-list))
      (mapcar 'compute-offset label-list)
      (save-excursion
	(goto-char (+ pos offset))
	(if epoch::version
	    (epoch::delete-button-at (point)))
	(let ((buffer-read-only nil))
	  (delete-char (length str))))
      (if (null label-list) (reset-label-mode))
      t)))

(defun label-visiting ()
  (if label-mode label-was-visiting buffer-file-name))

;; End of label package

;; Functions to configure the sml-mode and sml-shell for debugging

(defvar sml-debug-keys
  '(("\M-f" . sml-step)
    ("\M-b" . sml-step-backward)
    ("\M-s" . sml-skip)
    ("\M-r" . sml-skip-backward)
    ("\M-c" . sml-select-current)
    ("\M-n" . sml-select-next)
    ("\M-p" . sml-select-previous)
    ("\M-k" . sml-break)
    ("\C-\M-k" . sml-show-breaktimes)
    ("\M-u" . sml-up-call-chain)
    ("\M-d" . sml-down-call-chain)
    ("\M-t" . sml-goto-time)
    ("\M-l" . sml-variable-value)
    ("\C-\M-f" . sml-proceed-forward)
    ("\C-\M-b" . sml-proceed-backward)
    ("\C-\M-c" . sml-complete))
)

(defun sml-add-debug-keys ()
  (mapcar (function (lambda (l) (local-set-key (car l) (cdr l))))
	  sml-debug-keys))

(defun sml-debug-mode ()
; Should be hooked to sml-mode.
  (sml-add-debug-keys)
  (local-set-key "\M-e" 'sml-select-near)
; This binding doesn't seem to be added at all the appropriate times...
; BUG BUG
  (local-set-key "\C-c\C-d" 'sml-abort)
  (local-set-key "\C-c\C-\M-u" 'sml-save-buffer-uselive-file)
  (local-set-key "\C-c\C-\M-f" 'sml-usedbg-on-file)
  (local-set-key "\C-c\C-\M-c" 'sml-send-region-uselive)
  (local-set-key "\C-c\C-\M-b" 'sml-send-buffer-uselive)

; Mouse buttons.  Mouse support is handled elegantly under Epoch.
; Under vanilla Emacs, mouse support is awkward: the mouse map is global,
; so this might interfere with other modes which define mouse functions.
  (if epoch::version
      (progn
	(local-set-mouse mouse-left mouse-meta 'sml-mouse-variable-value)
	(local-set-mouse mouse-middle  mouse-meta 'sml-mouse-select-near))
  (define-key mouse-map x-button-m-left 'sml-mouse-variable-value)
  (define-key mouse-map x-button-m-middle 'sml-mouse-select-near))
; Use full pathnames, since the inferior SML process might cd.
  (setq sml-strip-path nil)
)

; sml-process-feed is used to feed text to the sml process, waiting
; until the process is ready to receive the text before we
; send it, so that we can echo the text in a clean way.
; If sml-process-feed-echo is set, then the fed text will be echoed even
; when sml-echo-emacs-commands is false.
(defvar sml-process-feed nil)
(defvar sml-process-feed-echo nil)

(defvar sml-consume nil)       ; used to delete "val it = () : unit" lines

(defun sml-debug-shell ()
; Should be hooked to sml-shell.
  (sml-add-debug-keys)
  (set-process-filter (get-process sml-process-name) 'sml-debug-filter)
; We tell the inferior process to cd to the current directory, although
; it will already be there, so that the currentWD reference is initialized.
  (setq sml-process-feed
	(concat "emacsInit (); cd \"" default-directory "\";\n"))
  (setq sml-process-feed-echo t)
  (display-buffer (concat "*" sml-process-name "*")))

;; Debugging commands that are attached to key sequences.

;; Following are copied wholesale from sml-mode 

(defun sml-usedbg-on-file (file)
  "Send a usedbg FILE to the inferior shell running sml."
  (interactive "FUsedbg file: ")
  (sml-shell)
  (setq file (expand-file-name file))
  (if sml-strip-path
      (if (string= (substring file 0 (string-match "[^/]*$" file))
		   sml-shell-working-dir)
	  (setq file (substring file (string-match "[^/]*$" file)
				(string-match "$" file)))))
  (save-some-buffers)
  (sml-skip-errors)
  (send-string sml-process-name
	       (concat "usedbg " sml-use-left-delim file
		       sml-use-right-delim ";\n")))

(defun sml-save-buffer-uselive-file ()
; Save the buffer, and send a `uselive file' to the inferior shell
; running sml.
  (interactive)
  (let (file)
    (if (setq file (buffer-file-name))	; Is the buffer associated
	(progn				; with file ?
	  (save-buffer)
	  (sml-shell)
	  (sml-skip-errors)
	  (if sml-strip-path
	      (if (string= (substring file 0 (string-match "[^/]*$" file))
			   sml-shell-working-dir)
		  (setq file (substring file (string-match "[^/]*$" file)
					(string-match "$" file)))))
	  (message
	   (concat "uselive " sml-use-left-delim file sml-use-right-delim))
	  (send-string sml-process-name
		       (concat "uselive " sml-use-left-delim
			       file
			       sml-use-right-delim ";\n")))
      (error "Buffer not associated with file."))))

(defun sml-simulate-send-region-uselive (point1 point2)
  "Simulate send region. As send-region only can handle what ever the
system sets as the default, we have to make a temporary file.
Updates the list of temporary files (sml-tmp-files-list)."
  (let ((file (expand-file-name
	       (make-temp-name (concat sml-tmp-template sml-tmp-bug)))))
    ;; Remove temporary files when we leave emacs
    (if (not sml-simulate-send-region-called-p)
	(progn
	  (setq sml-old-kill-emacs-hook kill-emacs-hook)
	  (setq kill-emacs-hook 'sml-remove-tmp-files)
	  (setq sml-simulate-send-region-called-p t)))
    ;; As make-temp-name can only make 26 unique file names with the
    ;; same template (bug in Un*x function mktemp), we add a new
    ;; letter to sml-tmp-template.
    (if (zerop (% (1+ (length sml-tmp-files-list)) 25))
	(setq sml-tmp-bug (concat sml-tmp-bug "A")))
    (save-excursion
      (goto-char point1)
      (setq sml-tmp-files-list
	    (cons (list file
			(buffer-file-name)
			(save-excursion	; Calculate line no.
			  (beginning-of-line)
			  (1+ (count-lines 1 (point)))))
		  sml-tmp-files-list)))
    (write-region point1 point2 file nil 'dummy)
    (sml-shell)
    (message "Using temporary file: %s" file)
    (send-string
     sml-process-name
     ;; string to send: use file;
     (concat "uselive " sml-use-left-delim file sml-use-right-delim ";\n"))))

(defun sml-send-region-uselive ()
  "Send region to inferior shell running sml."
  (interactive)
  (sml-shell)
  (sml-skip-errors)
  (let (start end)
    (save-excursion
      (setq end (point))
      (exchange-point-and-mark)
      (setq start (point)))
    (sml-simulate-send-region-uselive start end)))

(defun sml-send-function-uselive ()
  "Does *not* send the function, but the paragraph, to inferior shell
running sml (sorry)."
  (interactive)
  (sml-shell)
  (sml-skip-errors)
  (let (start end)
    (save-excursion
      (condition-case ()
	  (progn
	    (backward-paragraph)
	    (setq start (point)))
	(error (setq start (point-min))))
      (condition-case ()
	  (progn
	    (forward-paragraph)
	    (setq end (point)))
	(error (setq end (point-max)))))
    (sml-simulate-send-region-uselive start end)))

(defun sml-send-buffer-uselive ()
  "Send the buffer, to inferior shell running sml."
  (interactive)
  (sml-shell)
  (sml-skip-errors)
  (sml-simulate-send-region-uselive (point-min) (point-max)))

(defun sml-step () (interactive) (sml-debug-command "ss();\n"))

(defun sml-step-backward () (interactive) (sml-debug-command "ssb();\n"))

(defun sml-skip () (interactive) (sml-debug-command "sk();\n"))

(defun sml-skip-backward () (interactive) (sml-debug-command "skb();\n"))

(defun sml-select-current () (interactive)
  (sml-debug-command "selectCurrent();\n"))

(defun sml-select-next () (interactive) (sml-debug-command "selectNext();\n"))

(defun sml-select-previous () (interactive)
  (sml-debug-command "selectPrev();\n"))

(defun sml-break (arg) (interactive "P")
  (if arg				; prefix was specified
      (let ((u (prefix-numeric-value arg)))
	(if (>= u 0)
	    (sml-debug-command (concat "breakWhen " (int-to-string u) ";\n"))
	  (sml-debug-command "clearBreaks ();\n")))
    (sml-debug-command "toggleBreak();\n")))

(defun sml-up-call-chain () (interactive)
  (sml-debug-command "upCall();\n"))

(defun sml-down-call-chain () (interactive)
  (sml-debug-command "downCall();\n"))

(defun sml-goto-time (a) (interactive "P")
  (if a					; prefix was specified
      (let ((u (prefix-numeric-value a)))
	(if (>= u 0)			; sensible numeric value
	    (sml-debug-command
	     (concat "jump " (int-to-string u) ";\n"))))
    (sml-debug-command "jumpTrace();\n")))

(defun sml-variable-value (v) (interactive "sVariable: ")
  (sml-debug-command (concat "emacsShowVal \"" v "\";\n")))


(defun sml-proceed-forward () (interactive)
  (sml-debug-command "forward();\n"))

(defun sml-proceed-backward () (interactive)
  (sml-debug-command "backward();\n"))

(defun sml-abort () (interactive)
  (sml-debug-command "abort();\n"))

(defun sml-complete () (interactive)
  (sml-debug-command "complete();\n"))

(defun sml-select-near () (interactive)
  (sml-debug-command
   (concat "selectNear \"" (or (label-visiting) (buffer-name)) "\" "
	   (int-to-string (label-cpos (point)))
	   ";\n")))

;; mouse commands

(defun x-mouse-buffer-char (arg)
; Given a descriptor passed to a mouse function, return the Emacs
; buffer the mouse is in, and the mouse's character position within
; that window.  This is easy in Epoch, and awkward in plain Emacs.
  (if epoch::version
      (list (nth 1 arg) (nth 0 arg))
    (let ((start-w (selected-window))
	  (done nil)
	  (w (selected-window))
	  (rel-coordinate nil))
; Cycle through all windows on the screen, looking for the one containing
; the mouse.  (Could this possibly be done more elegantly?)
      (while (and (not done)
		  (null (setq rel-coordinate
			      (coordinates-in-window-p arg w))))
	(setq w (next-window w))
	(if (eq w start-w)
	    (setq done t)))
; Now we have found the window that the mouse is in, and have the
; mouse coordinates relative to the window.  We need to find the character
; position determined by those coordinates.
      (let* ((b (window-buffer w))
	    (rel-x (nth 0 rel-coordinate))
	    (rel-y (nth 1 rel-coordinate))
	    (retval (list b
			  (progn
			    (select-window w)
			    (save-excursion
			      (move-to-window-line rel-y)
			      (move-to-column (+ rel-x (current-column)))
			      (point))))))
	(select-window start-w)
	retval))))

(defun sml-goto-mouse (arg)
; Move to the buffer and character indicated by the given argument.
  (let ((bc (x-mouse-buffer-char arg)))
    (set-buffer (nth 0 bc))
    (goto-char (nth 1 bc))))

(defun sml-mouse-select-near (arg)
  (save-excursion
    (sml-goto-mouse arg)
    (sml-select-near)))

(defun sml-mouse-word (arg)
; Return the text word that contains the given mouse position.
  (save-excursion
    (sml-goto-mouse arg)
    (while (and (preceding-char)
		(string-match "[A-Za-z0-9_']"
			      (char-to-string (preceding-char))))
      (backward-char))
    (let ((m (match-data)))
      (unwind-protect
	  (if (looking-at "\\([A-Za-z0-9_']+\\)")
	      (match-text 1)
	    (error "%s" "Point to a variable"))
	(store-match-data m)))))

(defun sml-mouse-variable-value (arg)
  (sml-variable-value (sml-mouse-word arg)))

(defun sml-show-breaktimes () (interactive)
  (sml-debug-command "showBreakTimes ();\n"))

(defvar sml-echo-emacs-commands nil
"Whether to echo commands sent to and from the sml debugger.
Useful for debugging.")

(defvar sml-prompt "\n- ")

(defun sml-debug-command (s)
   (sml-send-command s))

(defun sml-send-command (s)
; Echo a command in the SML window, and send it to the sml process.
; Changes the cursor position in the SML window if that window is on-screen.
; If the user is in the process of typing a command, we ignore the command.
  (let ((buf (current-buffer)))
    (unwind-protect
	(progn
	  (set-buffer (concat "*" sml-process-name "*"))
	  (goto-char (point-max))
;	  (if (looking-back-at-string sml-prompt)
	      (progn			; user has typed no input
		(insert-string (if sml-echo-emacs-commands s "\n"))
		(if (not sml-echo-emacs-commands)
		    (setq sml-consume "val it = () : unit\n"))
		(set-marker (process-mark (get-process sml-process-name))
			    (point))
		(send-string sml-process-name s))
;	    (error "%s" "sml-debug: Incomplete command on command line"))
	  )
      (set-buffer buf))))

;; Functions that process the output from the sml process and execute
;; emacs commands requested by SML.  Commands are optionally deleted as
;; they are seen.

(defun sml-debug-filter (proc str)
; Process all output that comes from the sml process, looking for
; emacs commands.
; Changes the cursor position in the SML window if that window is on-screen.
  (set-buffer (concat "*" sml-process-name "*"))
  (goto-char (point-max))
  (let ((pos (point)))
    (insert str)
    (goto-char pos))
  (beginning-of-line)
  (sml-process-commands)
  (set-marker (process-mark proc) (point-max)))

(defun sml-process-commands ()
; Move forward through the text of the current buffer, evaluating
; Emacs commands of the form (one per line)
; (emacs <emacs-command>)
; Commands are optionally deleted as they are executed.
; If sml-consume is matched at the end of the buffer, it is deleted, along
; with the character (assumed newline) preceding it.
; Point is left at the end of the buffer.
  (let ((mdata (match-data)))
    (if (re-search-forward "(emacs \\(.+\\))$" nil t)
	(let ((command (read (match-text 1))))
	  (store-match-data mdata)
	  (save-excursion
	    (eval command))
	  (if (not sml-echo-emacs-commands)
             ; Delete the command from the output buffer
	      (let ((pos (point)))
		(beginning-of-line)
		(delete-region (point) (1+ pos))))
	  (sml-process-commands))
      (if (and sml-consume (search-forward sml-consume nil t))
	  (progn
	    (delete-region (point) (- (point) (length sml-consume)))
	    ; Delete the extra prompt, so that the cursor does not move when
            ; keystroke commands are executed.
	    (if (looking-back-at-string (concat sml-prompt "\n"))
		(delete-region (point) (- (point) (length sml-prompt))))
	    (setq sml-consume nil)))
      (goto-char (point-max))
      (if (and sml-process-feed (looking-back-at-string sml-prompt))
	  (progn
	    (let ((sml-echo-emacs-commands
		   (or sml-echo-emacs-commands sml-process-feed-echo)))
	      (sml-send-command sml-process-feed))
	    (setq sml-process-feed nil)))
      (store-match-data mdata))))

; support for commands that SML will ask us to execute

(defun sml-buffer (buffer)
; Find the buffer that displays the given source file name or buffer name
; (such as *sml-debug-command*).  find-file-noselect will not find an
; existing buffer that is labeled, since a labeled buffer is visiting no file,
; so we look for the buffer by filename before calling find-file-noselect.
; This will cause problems if two source files have the same name (which
; is conceivable if they live in different directories.
  (or (get-buffer (file-name-nondirectory buffer))
      (if (file-readable-p buffer)
	  (find-file-noselect buffer)
	(message "Source is unavailable for %s" buffer)
	nil)))

(defun sml-label-buffer (buffer position string cursor)
 ; Place a label in a buffer at a given position.
 ; If cursor is t, move the cursor to the beginning of the label.
  (let ((cur (selected-window))
	(buf (sml-buffer buffer)))
    (if buf
	(progn
 ; Temporarily select the window so that we can change its visible
 ; cursor position.
	  (pop-to-buffer buf)
	  (label position string cursor)
	  (select-window cur)))))

(defun sml-unlabel-buffer (buffer position string)
  (let ((buf (sml-buffer buffer)))
    (if buf
	(progn
	  (set-buffer buf)
	  (display-buffer (current-buffer))
	  (un-label position string)))))

(defun sml-create-buffer (buffer initial)
  (set-buffer (get-buffer-create buffer))
  (sml-mode)
  (auto-save-mode nil)   ; this is just a temporary buffer
  (erase-buffer)	   ; just in case there was something there before
  (insert initial)
  (display-buffer (current-buffer)))

(defun sml-kill-buffer (buffer)
  (kill-buffer buffer)
; If the following line is not present, the cursor will sometimes be
; left after the kill-buffer command in the inferior window, instead of
; being left at the end of the buffer where it should be.  I'm not exactly sure
; why this happens; perhaps point is being left in a strange position or in
; another buffer after the kill-buffer call.
  (pop-to-buffer (concat "*" sml-process-name "*")))

(defun sml-good-bye () (interactive)
  (process-send-eof sml-process-name))

(defun sml-error (s)
  (message s)
  (beep))

