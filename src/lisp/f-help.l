;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-help.l                                            ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      On-line help system                                 ;;;
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
   (special %search-path %help-search-path))

;;; Keyword facility deleted: should be replaced by a more sophisticated 
;;; method of looking things up.                     [TFM 90.09.08]
;;;
;;; (dml |keyword| 1 ml-keyword (|string| -> |void|))
;;;
;;; (defun ml-keyword (tok)
;;;    (let
;;;      ((file (fileexists 'kwic "hol")))
;;;      (if file
;;;         (keyword-search tok file)
;;;         (failwith "Could not find HOL keyword file"))))

;;; The variable %help-search-path is the search path for help information.
;;; It is set in Makefile.
;;; Added by MJCG on 7 Dec 1989
;;; Revised by TFM 90.12.01 (made available in ML)

;;; Initialized to nil
(setq %help-search-path nil)

;;; TFM 90.12.01 for version 1.12
;;; dml-ed function to return the help search path
(defun ml-help_search_path () %help-search-path)
(dml |help_search_path| 0 ml-help_search_path (|void| -> (|string| |list|)))

;;; TFM 90.12.01 HOL88 version 12
;;; dml-ed function for setting the help search path from ML
(defun ml-set_help_search_path (new-path) 
   (progn %help-search-path (setq %help-search-path new-path) nil))
(dml |set_help_search_path| 1  ml-set_help_search_path 
   ((|string| |list|) -> |void|))


;;; %help-search-path now set in Makefile. (note %hol-dir no longer used)
;;; (defun set-help-search-path ()
;;;  (setq 
;;;   %help-search-path 
;;;   (list (concat %hol-dir '|/help/Reference/RULES/|)
;;;         (concat %hol-dir '|/help/Reference/TACTICS/|)
;;;         (concat %hol-dir '|/help/Reference/GENFNS/|)
;;;         (concat %hol-dir '|/help/Reference/LOGFNS/|)
;;;         (concat %hol-dir '|/help/Reference/LIBRARIES/|))))

(dml |help| 1 ml-help (|string| -> |void|))

;;; Help system changed to search %help-search-path.
;;; .doc files are looked for first and if found processed
;;; with the sed script help/Reference/doc-to-help.sed.
;;; If no .doc file is found then a .jac file is searched for
;;; and if found processed with help/Reference/jac-to-help.sed
;;; MJCG 7 December 1989

;;; Old code:
;;; (defun ml-help (tok)
;;;   (let
;;;      ((file (fileexists 'help tok)))
;;;      (if file
;;;         (display-file file)
;;;         (msg-failwith "help" "No information available on " tok))))

;;; Chaneged to allow for alias for whacky help files (eg '/.doc') by using an
;;; association list. [JVT 17 March 1991].
;;; .hat association list entry added [TFM 17.03.91]

(defun ml-help (tok)
   (let ((%search-path %help-search-path)
         (isothername (assoc tok '((|/| |.div|)(|^| |.hat|)))))
       (let ((realname (if (null isothername) tok (cadr isothername))))
           (let ((doc-file (fileexists 'doc realname)))
                (if doc-file
                    (display-file doc-file '|doc|)
                    (let ((jac-file (fileexists 'jac realname)))
                         (if jac-file
                             (display-file jac-file '|jac|)
                             (msg-failwith
                               "help"
                               "No information available on " tok))))))))

