;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-iox-stand.l                                       ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      ML I/O and flags                                    ;;;
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
;;;   REVISION HISTORY: Original code: din,iox (lisp 1.6) part of Edinburgh ;;;
;;;                     LCF by M. Gordon, R. Milner and C. Wadsworth (1978) ;;;
;;;                     Transported by G. Huet in Maclisp on Multics, Fall  ;;;
;;;                     1981                                                ;;;
;;;                                                                         ;;;
;;; V1.4: nextch imported from F-parser, digitp,etc. exported to F-parser   ;;;
;;;                                                                         ;;;
;;; V2.2: part 4 imported from F-tml                                        ;;;
;;;       local variables in and lcferror                                   ;;;
;;;                                                                         ;;;
;;; |%undisch_defs-flag| deleted [TFM 90.12.01]                             ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (special %flags %search-path |%prompt-flag| |%print_load-flag| %directory
            %library-search-path |%print_lib-flag|)
   (*lexpr concat uconcat))


;;; print on an output file, setting output parameters properly
;;; use channel %outport
(defun hol-print-file (x)
   (let ((*print-level* nil) (*print-length* nil)
         (*print-escape* t) (*print-pretty* nil)
         (prinlevel nil) (prinlength nil)
         (#+franz poport #-franz *standard-output* %outport))
      (llprint x)
      (llterpri)))                  ; hol-print-file


;;;  Part 2: Predicates on tokens

(defun idenp (tok)
   (let ((l (exploden tok)))
      (and l
         (letterp (car l))
         (forall 'alphanump (cdr l)))))     ;idenp

(defun nump (tok)
   (can (function ml-int_of_string) (list tok)))       ;nump

;;;                Part 3 : terminal input

;;; MJCG 30/11/88 for HOL88
;;; List of settable flags
;;; |%undisch_defs-flag| deleted [TFM 90.12.01]
;;; |%read_sexpr-flag| added [JVT 90.13.12]
;;; |%print_fasl-flag| added [TFM 91.01.20]
(setq %flags 
   '(|%theory_pp-flag| |%prompt-flag| |%show_types-flag| |%type_error-flag|
      |%timing-flag| |%sticky-flag| |%interface_print-flag| 
      |%abort_when_fail-flag|
      |%print_top_val-flag| |%print_top_types-flag| |%print_list-flag| 
      |%print_set-flag| |%print_cond-flag| |%print_infix-flag| 
      |%print_load-flag|
      |%print_quant-flag| |%print_restrict-flag| |%print_let-flag| 
      |%print_uncurry-flag| |%print_lettypes-flag| |%print_lib-flag| 
      |%compile_on_the_fly-flag| |%file_load_msg-flag| |%preterm-flag|
      |%read_sexpr-flag| |%print_fasl-flag|
      |%pp_sexpr-flag| |%print_sexpr-flag| |%print_parse_trees-flag|))

(setq |%print_lib-flag| nil)
(setq |%print_load-flag| t)
;;; (setq |%undisch_defs-flag| t) deleted [TFM 90.12.01]
(setq |%preterm-flag| nil)
(setq |%print_fasl-flag| nil)

;;; MJCG 28/11/88 for HOL88
;;; dml-ed function for setting Lisp flags from ML
;;; special case for print_fasl-flag
(defun ml-set_flag (flag val)
   (let
      ((pflag (concat '|%| (canonise-case-symbol flag) '|-flag|)))
      (if (equal pflag '|%print_fasl-flag|)
          (prog1 (eval pflag) (set-fasl-flag val))
          (if (memq pflag %flags)
              (prog1 (eval pflag) (set pflag val))
              (failwith (concat flag " not a settable flag"))))))

(dml |set_flag| 2 ml-set_flag ((|string| |#| |bool|) -> |bool|))

;;; MJCG 13/10/89 for HOL88
;;; dml-ed function for creating new Lisp flags from ML
(defun ml-new_flag (flag val)
   (let
      ((pflag (concat '|%| (canonise-case-symbol flag) '|-flag|)))
      (if(memq pflag %flags)
         (failwith (concat flag " is already a flag"))
         (prog () 
               (setq %flags (cons pflag %flags))
               (set pflag val) 
               (return nil)))))

(dml |new_flag| 2 ml-new_flag ((|string| |#| |bool|) -> |void|))

;;; MJCG 5/2/89 for HOL88
;;; dml-ed function for accessing the value of a settable flag from ML
(defun ml-get_flag_value (flag) 
   (let
      ((pflag
            (concat '|%| (canonise-case-symbol flag) '|-flag|)))
      (if (memq pflag %flags)
         (eval pflag)
         (failwith (concat flag " not a settable flag")))))

(dml |get_flag_value| 1 ml-get_flag_value (|string| -> |bool|))

;;; MJCG 13/10/89 for HOL88
;;; dml-ed function for getting list of flags
;;; Bugfix for CL. MJCG 23/11/90: cdddddr expanded out
;;; (since not defined in CL)
(defun ml-flags ()
  (reverse
    (mapcar
      (function
;    (lambda (x) (imploden (reverse(cdddddr(reverse(cdr(exploden x))))))))
       (lambda (x)
         (imploden
          (reverse(cdr(cdr(cdr(cdr(cdr(reverse(cdr(exploden x))))))))))))
     %flags)))

(dml |flags| 0 ml-flags (|void| -> (|string| |list|)))


;;; MJCG 29/11/88 for HOL88
;;; |%prompt-flag| determines whether to output a prompt
(setq |%prompt-flag| t)
(defun nextcn ()
   (if (null inputstack)
      (cond
         (fin-ligne 
            (if |%prompt-flag| (princ %prompt-string))
            (setq fin-ligne nil))))
   (let ((c (llreadcn)))
      (if (null c) (throw-from eof nil))
      ;; Modification J.Joyce Apr 87 - prompt also on cr character
      (if (or (= c lf) (= c cr))
         (setq fin-ligne t))    ;newline: arm prompt
      c))                                       ;nextch

;;; MJCG 28/11/88 for HOL88
;;; dml-ed function for setting |%prompt-flag|
(defun ml-prompt (x) (prog1 |%prompt-flag| (setq |%prompt-flag| x)))
(dml |prompt| 1 ml-prompt (|bool| -> |bool|))


;;;  Part 4:  file token handling and file opening, closing, etc

;;; MJCG 12/10/88 for HOL88
;;; %search-path holds the HOL users search path. It is initialized to nil.

(setq %search-path nil)

;;; MJCG 13/10/88 for HOL88
;;; dml-ed function for getting search path from ML
(defun ml-search_path () %search-path)
(dml |search_path| 0 ml-search_path (|void| -> (|string| |list|)))

;;; MJCG 13/10/88 for HOL88
;;; dml-ed function for setting search path from ML
;;; (old search path returned)
;;; MJCG 26/9/89 for HOL88
;;; () returned 
(defun ml-set_search_path (new-path) 
   (progn %search-path (setq %search-path new-path) nil))
(dml |set_search_path| 1  ml-set_search_path 
   ((|string| |list|) -> |void|))


;;; =====================================================================
;;; TFM 23.11.91 for version 2.01
;;; %library-search-path holds the HOL users library search path. 
;;; It is initialized to nil.
;;; =====================================================================

(setq %library-search-path nil)

;;; dml-ed function for getting library search path from ML
(defun ml-library_search_path () %library-search-path)
(dml |library_search_path| 0 ml-library_search_path
     (|void| -> (|string| |list|)))

;;; dml-ed function for setting library search path from ML
(defun ml-set_library_search_path (new-path) 
   (progn %library-search-path (setq %library-search-path new-path) nil))
(dml |set_library_search_path| 1  ml-set_library_search_path 
   ((|string| |list|) -> |void|))

;;; MJCG 312/10/88 for HOL88
;;; Split a file into its name and extension

(defun dest-file-name (tok)
   (prog (chars ext)
      (setq chars (reverse (exploden tok)))
      (setq ext nil)
      loop (if (null chars) (return (cons tok nil)))
      (cond
         ((or (not (= (car chars) #/.)) (null (cdr chars)))
            (setq ext (cons (car chars) ext))
            (setq chars (cdr chars))
            (go loop))
         ((= (cadr chars) #/.)   ; we have the unix '..' directory idiom
            (return (cons tok nil)))
         (t
            (return 
               (cons (imploden (reverse (cdr chars))) (imploden ext)))))))


(defun file-name (tok) (car (dest-file-name tok)))
(defun file-ext  (tok) (cdr (dest-file-name tok)))    


;;; MJCG 12/10/88 and 31/10/88 for HOL88
;;; (find-file name) returns name if it exists on the current directory, 
;;; otherwise it returns the first piname that exists, where
;;; %search-path = (p1 ... pn).
;;; If no such pi exists then name (prepended with %directory) is returned 
;;; (for compatability with old code).
;;; If the file name has the form `name.m*` then find-file
;;; searches each directory first for `name_ml.o` and then `name.ml`
;;; (this hack is for code compatibility).

(defun find-file (tok)
   (let*
      ((name-and-type (dest-file-name tok))
         (name (car name-and-type))
         (exts
            (if (eq (cdr name-and-type) '|m*|)
               (list "_ml.o" ".ml")
               (list
                  (if (cdr name-and-type) (catenate "." (cdr name-and-type))
                     ""))))
         (found nil)
         (pre-directory
            ;; JAC 19.06.92 for pc - prepend empty string if filename
            ;; is already completely specified (i.e. contains :) - was
            ;; (or (and (boundp '%directory) (symbol-value '%directory)) "")
            (or
               (and (boundp '%directory)
                  #+pc (not (find (schar ":" 0) (string tok)))
                  (symbol-value '%directory))
               "")))
      (do
         ((search-path
               (nconc (if (exploden pre-directory) (list pre-directory))
                  (or %search-path (list "")))
               (cdr search-path)))
         ((null search-path)
            (catenate pre-directory tok))
         (setq found
            (find-file1 (car search-path) name exts))
         (if found (return found)))))

;;; JVT 11/03/93 for HOL88 V2.02
;;; Some common lisps do not support automatic expansion of "~" into
;;; the user's home directory when loading files.  A change was made to
;;; find-file1 to ensure that the file returned (if found) by find-file1
;;; has a fully expanded pathname.

(defun find-file1 (dir name exts)
   (do
      ((exts exts (cdr exts))
         (file nil))
      ((null exts) nil)
      (setq file (catenate dir name (car exts)))
      (let ((fle (probe-file file)))
           (if fle #+franz (return file) #-franz (return (namestring fle))))))

;;; MJCG 13/10/88 for HOL88
;;; dml-ed versions of find-file; failure if files can't be found
;;; (N.B. Lisp find-file doesn't fail)

(defun ml-find_file (name)
   (let
      ((file (find-file name)))
      (if (probe-file file) file (failwith '|find_file|))))

(dml |find_file| 1 ml-find_file (|string| -> |string|))


(defun ml-find_ml_file (name)
   (let
      ((file
            (find-file
               (if (ends-in-ml name) name (catenate name '|.m*|)))))
      (if (probe-file file) file (failwith '|find_file|))))

(dml |find_ml_file| 1 ml-find_ml_file (|string| -> |string|))


(defun ml-find_theory (name)
   (or (fileexists 'theory name) (failwith '|find_file|)))

(dml |find_theory| 1 ml-find_theory (|string| -> |string|))


;;; MJCG 12/10/88 for HOL88
;;; find-file wrapped around fileof

(defun fileexists (kind tok)
   (let ((file (find-file (fileof kind tok))))
      (if (probe-file file) file)))
