; Initializations for sml-mode and sml-debug; these should be invoked
; from your .emacs file by a line of the form
;
; (load-library "sml-init")
;
; Adam Dingle, atd@cs.princeton.edu

; sml-mode

; Automatically enter sml-mode for any file whose name ends in ".sml".
(setq auto-mode-alist (cons '("\\.sml$" . sml-mode) auto-mode-alist)) 

(autoload 'sml-mode "sml-mode" "Major mode for editing SML." t)
(autoload 'sml-shell "sml-mode" "Inferior shell invoking SML." t)


(defun smld () (interactive)
  ; Like sml-shell, but we display the sml process window after invoking it;
  ; this will bring it up even if it has already been started.
  ; Also, "sml" is shorter to type than "sml-shell".
  ; Set name of the sml executable that supports debugging.
  (setq sml-prog-name "smld")
  (sml-shell)
  (pop-to-buffer (concat "*" sml-process-name "*")))

; sml-debug

(setq sml-mode-hook 'sml-debug-mode)
(setq sml-shell-hook 'sml-debug-shell)
(autoload 'sml-debug-mode "sml-debug")
(autoload 'sml-debug-shell "sml-debug")

