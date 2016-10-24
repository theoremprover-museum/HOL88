;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-tml.l                                             ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Top level ML read-eval-print loop                   ;;;
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
;;;   REVISION HISTORY: Original code: tml (lisp 1.6) part of Edinburgh     ;;;
;;;                     LCF by M. Gordon, R. Milner and C. Wadsworth (1978) ;;;
;;;                     Transported by G. Huet in Maclisp on Multics, Fall  ;;;
;;;                     1981                                                ;;;
;;;                                                                         ;;;
;;;                     V2.1 : begin and end renamed as ml-begin and ml-end ;;;
;;;                                                                         ;;;
;;;                     V2.2 : errset and err replaced with tag and new-exit;;;
;;;                         top1, ctrlgfn no more used                      ;;;
;;;                                                                         ;;;
;;;                     V2.3 : compiler added  July 82   GH                 ;;;
;;;                                                                         ;;;
;;;                     V3.1 : optimization of lisp code L. Paulson         ;;;
;;;                                                                         ;;;
;;;                     V3.2 : compatibility VAX-Unix/Multics               ;;;
;;;                                                                         ;;;
;;;                     V4.2 : message functions gone                       ;;;
;;;                                                                         ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile) 
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (special %char-buffer %parse-tree-buffer |%abort_when_fail-flag| %turnstile
      |%print_lib-flag| %prompt-string %libraries |%print_load-flag|
      |%compile_on_the_fly-flag| |%file_load_msg-flag| %lib-dir
      %pt1 |%print_parse_trees-flag| 
      %search-path %help-search-path %library-search-path))


#+franz
(declare
   (localf top%f
      istmlop
      isdefty
      isdecl
      istydecl
      okpass
      typechpt
      tranpt
      evalpr
      tmlloop
      extend-env
      setbindings
      updatevalues
      printresults
      printtime
      ml-begin
      ml-end
      compiloop
      parseml0))

;;;  Uses Manifests:  eof  [iox/din]
;;;                   nullty  [typeml]
;;;                   nill  [tran]

;;;  Sets Manifests:  initsection, initenv, nosecname

;;;  Uses Globals:  %f
;;;                 %emt, %temt  [typeml]
;;;                 |%print_load-flag|  [System load]
;;;                 ibase, base, *nopoint , %prompt-string [lisp/tml]
;;;  Globals:  %pt, %pt1, %ty, %pr, %val  [in top1/okpass]
;;;                 %sections, %dump

;;;  Specials:  %p, %thisdec, %thistydec, tenv


(eval-when (compile load eval)
   (defconstant initsection '%mustbeatom)
   (defconstant initenv (cons initsection nill))
   (defconstant nosecname '|<noname>|))         ; Value printed by begin/end

(eval-when (load)
   (when initial%load                              ;  Globals
      (setq global%env ())
      (setq %f nil)
      (setq %sections ())
      (setq %dump ())
      (setq |%timing-flag| nil)
      (setq %outport nil)
      (setq |%print_parse_trees-flag| nil)
      (setq |%abort_when_fail-flag| t)
      (setq |%compile_on_the_fly-flag| nil)))

;;;                  Error and message functions

;;; Added by MJCG on 7/4/1987

(defun hol-err (x) (throw-from tmllooptag "System"))

(defun lcferror (x)
   (let (#+franz (poport nil) #-franz (*standard-output* *terminal-io*))
      (llterpri) 
      (llprinc "Error in HOL system, please report it.")
      (llterpri)
      (llprinc (list "Diagnostic:" x))
      (llterpri)
      #+franz (baktrace)
      (hol-err %f)))                            ;lcferror

;;;                  Top level of ml interpreter

(defun top%f () (memq %f '(() load compile)))   ;top%f

(defun istmlop () (memq %head '(mk-begin mk-end)))      ;istmlop

(defun isdefty () (eq %head 'mk-deftype))               ;isdefty

(defun isdecl ()
   (memq %head
      '(mk-let mk-letref mk-letrec mk-abstype mk-absrectype))) ;isdecl

(defun istydecl ()
   (memq %head '(mk-type mk-rectype)))         ;isdecl

;;; MJCG 10.12.90 for Centaur:
;;; The parse tree in %pt seems to get corrupted destructively
;;; So a copy of the original is retained in %pt1
(defun okpass (pass)
   (catch-throw okpass  ; must be catch since throw may come from inside errset
      (let
         ((b
               (errortrap #'(lambda (errtok) "lisp error")
                  (case pass
                     (parse
                        (catch-throw parse
                           (setq %pt (parseml0))
                           (if |%print_parse_trees-flag| ; for Centaur!
                               (setq %pt1 (copy-tree %pt))) ; for Centaur!
                           (throw-from okpass nil)))
                     (typecheck
                        (catch-throw typecheck
                           (setq %ty (typechpt)) (throw-from okpass nil)))
                     (translation
                        (catch-throw translation
                           (setq %pr (tranpt)) (throw-from okpass nil)))
                     (evaluation
                        (catch-throw evaluation
                           (setq %val (evalpr)) (throw-from okpass nil)))
                     (evtmlop
                        (catch-throw evaluation
                           (setq %val (evtmlop %pt)) (throw-from okpass nil)))
                     (t (lcferror (cons pass '(unknown pass))))))))
         ;;; Fall through here if pass failed
         (llprinc
            (case pass
               (parse "parse")
               (typecheck "typecheck")
               (translation "translation")
               (evaluation "evaluation")
               (evtmlop "evaluation")))
         (llprinc " failed     ")
         (if b (llprinc b))
         (llterpri)
         (cond
            ((memq %f '(load compile))
               ;; Propagate failure if performing load or compile
               (putprop lastvalname () 'mlval)        ;to prevent abscope type
               (putprop lastvalname nullty 'mltype)   ;fix for automatic ending
               (throw-from loaderror nil))
            (|%abort_when_fail-flag|
               (quit 1))                              ; to abort when building
            (t (throw-from tmllooptag %f))))))


;;; Redefined below to cope with ML generated declarations
;;; (defun parseml0 () (gnt) (parseml 0))               ;parsml0

(defun typechpt () (typecheck %pt))             ;typechpt

(defun tranpt () (let ((%p ())) (tran %pt)))    ;tranpt


(defun evalpr ()
   (mapc #'eval %compfns)    ; perform the definitions
   ;; Compile the functions - unless the eval has compiled them already
   ;; No in-core compiler in franz
   #-franz
   (if (and %compfns |%compile_on_the_fly-flag|)
      (compile-functions-if-needed %compfns))
   ;; Retain compatibility with old franz versions. Do proper thing for CL
   #+franz (funcall `(lambda (%e) ,%pr) nil)
   #-franz
   (funcall
      ;; may not attempt to compile already-compiled functions in ANSI
      ;; standard CL. Check added - JAC 19.06.92
      (if (and (not (compiled-function-p %pr)) |%compile_on_the_fly-flag|)
         (compile nil %pr)
         %pr)
      nil))


;;; MJCG 29/11/88 for HOL88
;;; ML function for setting prompt string

(setq %prompt-string '|#|)

(defun ml-set_prompt (s)
   (prog1 %prompt-string (setq %prompt-string s)))

(dml |set_prompt| 1 ml-set_prompt (|string| -> |string|))


;;; MJCG 4/1/89 for HOL88
;;; ML function for changing theorem printing character (|-)

(setq %turnstile "|- ")
   
(defun ml-set_turnstile (s)
   (prog1 %turnstile (setq %turnstile s)))

(dml |set_turnstile| 1 ml-set_turnstile (|string| -> |string|))


;;; MJCG 5/2/89 for HOL88
;;; Function to load in hol-init.ml
;;; Sticks loadt`hol-init.ml` in the input buffer

(defun load-hol-init ()
   (let ((file (find-file "hol-init.ml")))
      (if (probe-file file)
         (setq
            %parse-tree-buffer 
            (list '(mk-appn (mk-var |loadt|) (mk-tokconst |hol-init|)))))))

;;; JVT 29/5/92 for HOL88
;;; read-HOLPATH reads in the environment variable HOLPATH (if present)
;;; to get a new root directory for the system without recourse to hol-init
;;; or a rebuild.

(defun read-HOLPATH ()
   #+unix (let ((varble #+franz (getenv 'HOLPATH)
                        #+kcl   (system:getenv "HOLPATH")
                        #+lucid (environment-variable "HOLPATH")
                        #+allegro (system:getenv "HOLPATH")))
               (cond ((or (eq varble '||) (null varble)) nil)
                     (t (setq %hol-dir varble)
                        (setq %lib-dir (concat varble "/Library"))
                        (setq %search-path (list '|| '|~/| (concat varble "/theories/")))
                        (setq %library-search-path (list (concat varble "/Library/")))
                        (setq %help-search-path (list (concat varble "/help/ENTRIES/")))))) 
                        
   #-unix nil
)

;;; Top-level entry to ML
;;; Sets time stamp to allow the generation of symbols unique to this session
;;; Necessary to avoid conflict when loading ML code
;;;    compiled in different sessions
;;; MJCG 29/11/88 for HOL88
;;; Made prompt the global %prompt-string, rather than local hard-wired #
;;; MJCG 5/2/89 for HOL88
;;; Added load-hol-init
;;; JVT 29/5/92 for HOL88
;;; Added read-HOLPATH

(defun tml ()
   (let ((base 10)
         (ibase 10)
         (*nopoint t)
         (%timestamp (mod (clock) 10000)))
      (setq fin-ligne t)
      (init-io)
      (banner)
      (incf %symcount (mod %timestamp 100))
      (read-HOLPATH)
      (load-hol-init)
      (catch-throw eof (tmlloop))
      (finalize-tml)))          ; before exiting from tml command loop


;;; Drop out of tml or a load back to tml - useful if you can't send eofs

(defun ml-dropout () (throw-from eof nil))

(dml |dropout| 0 ml-dropout (|void| -> |void|))


(dml |quit| 0 quit (|void| -> |void|))            ; quit


(defun tmlloop ()                                       ; Also used by load
   (while t (ml-read-eval-print)))


(defun ml-read-eval-print ()
   (errortrap
      #'(lambda (errtok) errtok)
      (catch-throw tmllooptag
         (and |%print_load-flag| (top%f) (llterpri))
         (let ((%thisdec ()) (%thistydec ()))
            (initlean)
            (okpass 'parse)
            (setq %head (car %pt))
            (if (istmlop)
               (okpass 'evtmlop)
               (progn
                  (okpass 'typecheck)
                  (okpass 'translation)
                  (let ((init-time (runtime10th))
                        (init-thms %thm-count))
                     (okpass 'evaluation)
                     (let ((final-time (runtime10th))
                           (final-thms %thm-count))
                        (updatetypes)    ;Uses %thisdec, %thistydec [typeml]
                        (updatevalues)
                        (printresults)
                        (printtime 
                           final-time init-time final-thms init-thms)))
                  ))))))                        ;tmlloop


;;; Insert new (mlname . lispname) pairs onto an alist
;;; For extending global environment

(defun extend-env (bvs lbpat env)
   (if (atom bvs)
      (if (eq bvs '%con)
         env
         (cons (cons bvs lbpat) env))
      (extend-env (cdr bvs) (cdr lbpat) 
         (extend-env (car bvs) (car lbpat) env))))      ;extend-env

;;; Execute set's to maintain top-level environment

(defun setbindings (newlb val)
   (if (atom newlb)
      (ifn (eq newlb '%con) (set newlb val))
      (progn
         (setbindings (car newlb) (car val))
         (setbindings (cdr newlb) (cdr val))))) ;setbindings

;;; Enter bindings in environment and store values in their Lisp atoms
;;; MJCG 9 November 1992. 
;;; Added check to suppress binding of "it" if it has been let-bound.

(defun updatevalues ()
   (cond
      ((isdefty))
      ((isdecl)
         (setq global%env (extend-env (car %val) new%%lb global%env))
         (setbindings new%%lb (cdr %val)))
      ((not(get-lisp-binding lastvalname))
         (putprop lastvalname %val 'mlval)
         (putprop lastvalname %ty 'mltype))))   ;updatevalues

;;; MJCG 11 May 1992. Eliminated third argument (ty) of prlet.
;;; This fixes a bug discovered by JG.
;;; prlet is defined in f-writml.l.
(defun printresults ()
   (cond
      ((not |%print_load-flag|)
         (unless %outport (llprinc '|.|)))
      ((isdefty) (prdefty %thistydec))
      ((istydecl) (prconstrs (cdr %thisdec)))
      ((isdecl) (prlet (car %val) (cdr %val)))
      (t (prvalty %val %ty))))          ;printresults

;;; Print runtime and GC time if |%timing-flag|

(defun printtime (final-times init-times final-thms init-thms)  
   (when |%print_load-flag|
      (let ((runtime (- (car final-times) (car init-times)))
            (gctime (- (cdr final-times) (cdr init-times))))
         (let ((seconds (truncate runtime 10)))
            (when |%timing-flag|
               (llprinc "Run time: ") (llprinc seconds)
               (llprinc ".") (llprinc (- runtime (* seconds 10)))
               (llprinc "s") (llterpri)))
         (ifn (zerop gctime)
            (let ((seconds (truncate gctime 10)))
               (when |%timing-flag|
                  (llprinc "Garbage collection time: ")
                  (llprinc seconds)
                  (llprinc ".") (llprinc (- gctime (* seconds 10)))
                  (llprinc "s") (llterpri))))
         (let ((thms (- final-thms init-thms)))
            (cond
               ((and |%timing-flag| (not (zerop thms)))
                  (llprinc "Intermediate theorems generated: ")
                  (llprinc thms)
                  (llterpri))))))) ; printtime

(defun evtmlop (pt)
   (case (car pt)
      (mk-begin (ml-begin (if (cdr pt) (cadr pt) nosecname)))
      (mk-end
         (ml-end
            (cond
               ((null (cdr pt))
                  (if %dump (car %dump)
                     (msg-failwith '|end| " not in a section")))
               ((assoc-equal (cadr pt) %dump))
               (t (msg-failwith '|end| "no section " (cadr pt))))))
      (t (lcferror (cons (car pt) '(not a tmlop))))))   ;evtmlop

(defun ml-begin (tok)
   (push (list tok %sections global%env %emt %temt %dump) %dump)
   (setq %sections t)
   (ifn %outport
      (when |%print_load-flag|
         (llprinc '|Section |) (llprinc tok)
         (llprinc '| begun|) (llterpri))))  ;ml-begin

(defun ml-end (x)
   (let
      ((tok (car x))
         (new-sections (cadr x))
         (new-global-env (caddr x))
         (new-emt (cadddr x))
         (new-temt (cadddr (cdr x)))
         (new-dump (cadddr (cddr x)))
         (tenv ()))
      (setq tenv new-temt)                    ;  for absscopechk
      (unless
         (catch-throw typecheck (typescopechk (get lastvalname 'mltype)))
         (failwith '|end|))     ; prevents result of section of local type
      (setq %sections new-sections)
      (setq global%env new-global-env)
      (setq %emt new-emt)
      (setq %temt new-temt)
      (setq %dump new-dump)
      (ifn %outport
         (when |%print_load-flag|
            (llprinc '|Section |) (llprinc tok)
            (llprinc '| ended|) (llterpri)))
      ))                                    ;ml-end


;;; MJCG 31/10/88 for HOL88
;;; Test whether a file name ends in `.ml`

(defun ends-in-ml (tok)
   (let ((l (nreverse (exploden tok))))
      (and (> (length l) 2)
         (= (car l) #/l)
         (= (cadr l) #/m)
         (= (caddr l) #/.))))


;;; Load one ml file. If there exists a compiled version, it will load
;;; it rather than the source version.
;;; Caution: even if the source is more recent.
;;;
;;; MJCG 31/10/88 for HOL88
;;; (fileexists '|m*| tok) case added
;;; find-file wrapped around fileof
;;; code to support loadt`foo.ml` added
;;; the resulting definition is inefficient, but disturbs the original
;;; code as little as possible (may optimise later)
;;; MJCG 10/2/90 for HOL88.1.12
;;; Test on |%file_load_msg-flag| added.

(setq |%file_load_msg-flag| t)

;;; Old version. Replaced on 6 April 1991 by
;;; Mark van der Voort's bugfix to handle .s in file names
;;; (See below)
;;; (defun ml-load (tok |%print_load-flag|)
;;;    (let
;;;       ((initial-nesting (length inputstack)) (%f 'load) (%dump ()))
;;;       (catch-throw eof
;;;          (catch-throw loaderror               ; catch failures inside load
;;;             (cond
;;;                ((not (filetokp 'ml tok))
;;;                   (msg-failwith '|load| tok " cannot be file name"))
;;;                ((and (not (ends-in-ml tok)) 
;;;                      (eq (file-ext (fileexists '|m*| tok)) '|o|))
;;;                   (throw-from eof
;;;                      (load (find-file (fileof 'code tok)))))
;;;                ((or (fileexists 'ml tok)
;;;                      (and (ends-in-ml tok)
;;;                         (fileexists 'ml (file-name tok))))
;;;                   (let ((%pt ()) (%ty ()) (%pr ()) (%val ()) (%head ()))
;;;                      (infilepush (find-file (fileof 'ml (file-name tok))))
;;;                      (tmlloop)))
;;;                (t
;;;                   (msg-failwith '|load| tok " ml file not found"))))
;;;          ;; an error occurred (before eof encountered) during file load
;;;          (if (> (length inputstack) initial-nesting) (infilepop))
;;;          (if %dump (ml-end (car (last %dump)))) ;close dangling sections
;;;          (msg-failwith '|load| tok))
;;;       ;; reached end of file without errors
;;;       (if %dump (ml-end (car (last %dump))))    ;close dangling sections
;;;       (if (> (length inputstack) initial-nesting) (infilepop))
;;;       (when (and |%print_load-flag| |%file_load_msg-flag|)
;;;          (llterpri) (llprinc "File ") (llprinc tok)
;;;          (llprinc " loaded") (llterpri))))     ;ml-load

;;; Following bugfix installed by MJCG for HOL88.1.13 (6 April 1991)
;;; Revised code supplied by Mark van der Voort.

;;; MvdV 04/02/91 for HOL88.1.11
;;; whenever a extensionless filename is given
;;; at the end of a path containing dots
;;; file-name will destruct this path instead of 
;;; delivering the whole file-name
;;;
;;; So the last two cases in the cond have been split

(defun ml-load (tok |%print_load-flag|)
   (let
      ((initial-nesting (length inputstack)) (%f 'load) (%dump ()))
      (catch-throw eof
         (catch-throw loaderror                 ; catch failures inside load
            (cond
	     ((not (filetokp 'ml tok))
	        (msg-failwith '|load| tok " cannot be file name"))
	     ((and (not (ends-in-ml tok)) 
              (eq (file-ext (fileexists '|m*| tok)) '|o|))
           (throw-from eof
              ;; tidied up conditional code and added :print nil and
              ;; :verbose nil to load - JAC 19.06.92
              #+lucid
              (let ((*load-binary-pathname-types*
                       (cons "o" *load-binary-pathname-types*)))
                 (fasload (find-file (fileof 'code tok))))
              #-lucid
              #-franz (load (find-file (fileof 'code tok)) :print nil :verbose nil)
              #+franz (load (find-file (fileof 'code tok)))
              ))
	     ((fileexists 'ml tok)
	         (let ((%pt ()) (%ty ()) (%pr ()) (%val ()) (%head ()))
		      (infilepush (find-file (fileof 'ml tok)))
;;;			                                ^place of bug
		      (tmlloop)))
	     ((and (ends-in-ml tok)
		   (fileexists 'ml (file-name tok)))
	         (let ((%pt ()) (%ty ()) (%pr ()) (%val ()) (%head ()))
		      (infilepush (find-file (fileof 'ml (file-name tok))))
		      (tmlloop)))
	     (t
	      (msg-failwith '|load| tok " ml file not found"))))
         ;; an error occurred (before eof encountered) during file load
         (if (> (length inputstack) initial-nesting) (infilepop))
         (if %dump (ml-end (car (last %dump)))) ;close dangling sections
         (msg-failwith '|load| tok))
      ;; reached end of file without errors
      (if %dump (ml-end (car (last %dump))))    ;close dangling sections
      (if (> (length inputstack) initial-nesting) (infilepop))
      (when |%print_load-flag|
         (llterpri) (llprinc "File ") (llprinc tok)
         (llprinc " loaded") (llterpri))))     ;ml-load

(dml |load| 2 ml-load ((|string| |#| |bool|) -> |void|))        ;load


;;; Boolean argument restored V5-1 GH.
;;; Changed for HOL88 by MJCG to return old value

(defun ml-timer (flag)
   (prog1 |%timing-flag| (setq |%timing-flag| flag)))       ;ml-timer

(dml |timer| 1 ml-timer (|bool| -> |bool|))     ;timer


(defun ml-lisp (tok)
   (errortrap
      #'(lambda (errtok) (msg-failwith '|lisp| errtok))
      (eval
         #+franz (readlist (explodec tok))
         #-franz (read-from-string (string tok)))))   ;ml-lisp

(dml |lisp| 1 ml-lisp (|string| -> |void|))             ;lisp


;;; Compiler

(dml |compile| 2 ml-compile ((|string| |#| |bool|) -> |void|))  ;compile

;;; MJCG 31/10/88 for HOL88
;;; find-file wrapped around fileof
;;; name-ext added and following let
;;; MJCG 10/2/90 for HOL88.1.12
;;; Test on |%file_load_msg-flag| added.

(defun ml-compile (tok |%print_load-flag|)
   (let ((%f 'compile)
         (%dump ())
         ($gcprint ())
         (name-ext (dest-file-name (find-file (fileof 'ml tok)))))
      (let ((filename (fileof 'lisp (car name-ext))))
         (catch-throw eof 
            (catch-throw loaderror
               (cond
                  ((not (filetokp 'ml tok))
                     (msg-failwith '|compile| tok " cannot be file name"))
                  ((fileexists 'ml tok)
                     (let ((%pt ()) (%ty ()) (%pr ()) (%val ()) (%head ())) 
                        (infilepush (find-file (fileof 'ml tok)))
                        (setq %outport (outfile filename))
                        ;; Franz compiler cannot know about any specials
                        #+franz (hol-print-file '(declare (special %vtyl)))
                        (compiloop)))
                  (t
                     (msg-failwith '|compile| tok " ml file not found"))))
            ;; an error occurred (before eof happened) during compilation
            (infilepop)
            (close %outport)
            (setq %outport nil)
            (when %dump (ml-end (car (last %dump)))) ;close dangling sections
            (msg-failwith '|compile| tok))
         ;; no error occurred
         (infilepop)
         (close %outport)
         (setq %outport nil)
         (when %dump (ml-end (car (last %dump))))  ;close dangling sections
         (compile-lisp filename)        ;call Lisp compiler
         (when (and |%print_load-flag| |%file_load_msg-flag|)
            (llterpri) (llprinc "File ") (llprinc tok)
            (llprinc " compiled") (llterpri)))))       ;ml-compile

;;; lisp function compiloop: 
;;; llprint at line labelled "***" changed to hol-print-file [TFM 90.06.01] 

(defun compiloop ()
   (while t
      (let ((%thisdec ()) (%thistydec ()))
         (and |%print_load-flag| (top%f) (llterpri))
         (initlean)
         (okpass 'parse)
         (setq %head (car %pt))
         (cond
            ((istmlop)
               (okpass 'evtmlop) (hol-print-file `(evtmlop ',%pt)))  ; ***
            ;; this ugly special case should disappear soon
            (t 
               (okpass 'typecheck)
               (okpass 'translation)
               (okpass 'evaluation)
               (updatetypes)
               (updatevalues)
               (printresults)
               (mapc
                  #'(lambda (form)
                     (hol-print-file `(eval-when (load) ,form)))
                  %compfns)
               (hol-print-file 
                  `(eval-when (load)
                     (execute
                        ',%ty ',%thisdec ',%thistydec ',%head ',new%%lb
                        ;; Retain compatibility with old franz versions.
                        ;; Do proper thing for CL
                        #+franz ',%pr
                        #-franz (function ,%pr))))
               )))))                    ;compiloop


;;; Evaluate an expression and also write it onto %outport
;;; For example, the putprops used to store abstract type information

(defun eval-remember (x)
   (when %outport (hol-print-file `(eval-when (load) ,x)))
   (eval x))                                    ;eval-remember


;;; Execute a compiled ML statement

(defun execute (%ty %thisdec %thistydec %head new%%lb %pr)
   (and |%print_load-flag| (top%f) (llterpri))
   (let ((init-time (runtime10th))
         (init-thms %thm-count))
      (okpass 'evaluation)
      (let ((final-time (runtime10th))
            (final-thms %thm-count))
         (updatetypes)
         (updatevalues)
         (printresults)
         (printtime final-time init-time final-thms init-thms)))) ;execute


;;; NEW  Saves a core image of a session
;;;
;;; caution: this should be invoked only from top-level of ml, and never from
;;; load/mlin (otherwise %f = load, and ml errors are not trapped properly).
;;; ml-save is system-dependent

(dml |save| 1 ml-save (|string| -> |void|))


;;; The code that follows supports ML generated top-level declarations
;;; of the form:  let x = f[`t1`;...;`tn`]. This works by maintaining
;;; pending declarations in the list %parse-tree-buffer. The top-level read
;;; loop checks to see if anything is in the buffer before reading from
;;; the input stream (see parsml0 below).

;;; (setq %parse-tree-buffer nil) 
;;; Now set in F-parsml.l (MJCG 5/2/89 for HOL88)

;;; The function parsml0 was previously defined by
;;; (defun parseml0 () (gnt) (parseml 0))
;;; MJCG 5/2/89 for HOL88
;;; Modified to return the front of %parse-tree-buffer

(defun parseml0 () 
   (prog (pt (*standard-input* *standard-input*))
      (if %parse-tree-buffer (go exit))
      (gnt)
      (setq pt (parseml 0))
      (setq %parse-tree-buffer
         (append %parse-tree-buffer (list pt)))
      exit (return
         (prog1 (car %parse-tree-buffer) 
            (setq %parse-tree-buffer (cdr %parse-tree-buffer))))))


;;; Make an object corresponding to the parse tree for `let mlname = fn tokl'.

(defun mk-let (mlname fn tokl)
   `(mk-let 
      ((mk-var ,mlname)
         mk-appn 
         (mk-var ,fn)
         ,(cons
            'mk-list
            (mapcar
               (function (lambda (x) (list 'mk-tokconst x))) tokl)))))


;;; and put it on the end of %parse-tree-buffer.
;;; The ML function let_after can be used to put it on at the beginning.

(dml |let_after| 3 ml-let_after
   ((|tok| |#| (|tok| |#| (|tok| |list|))) -> |void|))

(defun ml-let_after (mlname fn tokl)
   (prog (ob)
      (setq ob (mk-let mlname fn tokl))
      (setq %parse-tree-buffer
         (append %parse-tree-buffer (list ob)))
      (return '(mk-empty))))


;;; ml-let_before and let_before are like ml-let_after and let_after, except that
;;; the generated parse tree is put on the front of %parse-tree-buffer

(defun ml-let_before (mlname fn tokl)
   (prog (ob)
      (setq ob (mk-let mlname fn tokl))
      (setq %parse-tree-buffer (cons ob %parse-tree-buffer))
      (return '(mk-empty))))

(dml |let_before| 3 ml-let_before
   ((|tok| |#| (|tok| |#| (|tok| |list|))) -> |void|))


;;; MJCG 5/2/89 for HOL88
;;; (ml-autoload s fn (s1 ... sn) primes a string s so that if it is parsed
;;; as a variable (see the function mk-var-fun in F-parser.l) then the 
;;; autoload action fn[s1; ... ;sn] is put into %parse-tree-buffer
;;; The hol-autoload property has the form (eval . <ML parse tree>)

(defun ml-autoload (name fn args)
   (putprop 
      name 
      `(eval . (mk-appn 
            (mk-var ,fn)
            ,(cons
               'mk-list
               (mapcar (function (lambda (x) (list 'mk-tokconst x))) args))))
      'hol-autoload))

(dml |autoload| 3 ml-autoload
   ((|tok| |#| (|tok| |#| (|tok| |list|))) -> |void|))

;;; MJCG 5/2/88 for HOL88
;;; Functions to remove autoload actions

(defun ml-undo_autoload (name)
   (not (null (remprop name 'hol-autoload))))

(dml |undo_autoload| 1 ml-undo_autoload (|string| -> |bool|))


;;; MJCG 6/2/89 for HOL88
;;; Code for autoloading axioms, definitions and theorems.
;;; autoload takes a dotted pair whose car is
;;; a sort ('eval, 'axiom, 'definition or 'theorem)
;;; and whose cdr is either an ML parse tree (in the case of 'eval)
;;; or a theory-name pair in the other three cases.
;;; It then returns the parse tree to be put at the front
;;; of %parse-tree-buffer.
;;; In the 'eval case this tree is just the cdr of the argument; 
;;; in the other cases it is constructed using mk-let.

(defun autoload (p)
   (if (eq (car p) 'eval)
      (cdr p)
      (let ((sort (car p))
            (thy  (cadr p))
            (name (cddr p)))
         (case sort 
            (|axiom|
               (mk-let name '|axiom_msg_lfn| (list thy name)))
            (|definition|
               (mk-let name '|definition_msg_lfn| (list thy name)))
            (|theorem|
               (mk-let name '|theorem_msg_lfn| (list thy name)))
            (t (failwith '|autoload|))))))


;;; MJCG 6/2/89 for HOL88
;;; Function to set up hol-autoload properties for theory retrieval

(defun ml-autoload_theory (sort thy name)
   (cond ((memq sort '(|axiom| |definition| |theorem|))
         (putprop name (cons sort (cons thy name)) 'hol-autoload)
         nil)
      (t (failwith (concat "autoload: " sort)))))

(dml |autoload_theory|
   3
   ml-autoload_theory
   ((|string| |#| (|string| |#| |string|)) -> |void|))


;;; The code that follows enables ML functions to inject sequences of ascii
;;; characters onto the front of the input character stream.
;;; It works by concatenating onto the front of %char-buffer.

(defun inject-input (l) (setq %char-buffer (append l %char-buffer)))

(dml |inject_input| 1 inject-input ((|int| |list|) -> |void|))


;;; MJCG 2/3/89 for HOL88.1.01
;;; Function for loading a library
;;; %libraries holds the libraries already loaded

(setq %libraries nil)

;;; ml-load-library takes a print flag [no longer, see below] 
;;; and a library name.
;;; MJCG 23/3/89 for HOL88.1.02
;;; Instead of an explicit print flag argument, the printing
;;; during library loading is now controlled by the
;;; ML setable flag |%print_lib-flag|.

;;; load_library now sets up the search path. 

;;; (defun ml-load_library (tok)
;;;    (cond ((memq tok %libraries)
;;;          (princ (concat tok " already loaded"))
;;;          (terpri))
;;;       (t (princ (concat "Loading library `" tok "` ..."))
;;;          (terpri)
;;;          (let
;;;             ((dir-sep
;;;                   ;; guess a reasonable directory separator char
;;;                   (if (member #// (exploden %lib-dir)) "/"  ":")))
;;;             (ml-load
;;;                (catenate %lib-dir dir-sep tok dir-sep tok)
;;;                |%print_lib-flag|))
;;;          (setq %libraries (cons tok %libraries))
;;;          (terpri)
;;;          (princ (concat "Library `" tok "` loaded."))
;;;          (terpri)
;;;          nil)))

;;; New implementation of load_library for version 2.01:
;;;
;;;    * finds library using %library-search-path
;;;    * multi-section libraries:
;;;        - load_library `foo` loads <path>/foo/foo.ml
;;;        - load_library `foo:bar` loads <path>/foo/bar.ml
;;;
;;; Auxiliary functions:
;;;
;;;    * get-path : return the library pathname
;;;    * mk-fname : make load file name
;;;    * look-for-lib : search for library loadfile.
;;;
;;; [TFM 91.11.27]

(defun get-path (path sep)
  (let ((snum (car (exploden sep))))
   (prog (chars found)
      (setq chars (reverse (exploden path)))
      (setq found nil)
      loop
      (if (null chars) (return ""))
      (if found
	  (cond ((= (car chars) snum)
		 (return (imploden (reverse (cdr chars)))))
		(t (setq chars (cdr chars)) (go loop)))
	   (cond ((= (car chars) snum)
		  (setq found t) (setq chars (cdr chars)) (go loop))
		 (t (setq chars (cdr chars)) (go loop)))))))

(defun mk-fname (tok dir-sep)
   (prog (chars ext)
      (setq chars (reverse (exploden tok)))
      (setq ext nil)
      loop
       (if (null chars) (return(catenate tok dir-sep tok)))
       (cond
         ((not (= (car chars) colon))
            (setq ext (cons (car chars) ext))
            (setq chars (cdr chars))
            (go loop))
         (t (return
             (catenate
	       (imploden (reverse (cdr chars)))
	       dir-sep
	       (imploden ext)))))))

(defun look-for-lib (name tok)
   (let
      ((file
            (find-file
               (if (ends-in-ml name) name (catenate name '|.m*|)))))
      (if (probe-file file) file
	(failwith (catenate '|load_library: | tok '| not found|)))))


(defun ml-load_library (tok)
   (cond ((memq tok %libraries)
	  (princ (concat tok " already loaded"))
	  (terpri))
	 (t (let
             ((dir-sep
                  ;; guess a reasonable directory separator char
                  ;; JAC 19.02.92 for pc - was
                  ;; (if (member #// (exploden %lib-dir)) "/"  ":")
                  #+(or franz unix) "/"
                  #+pc "\\"
                  #-(or franz unix pc) ":"))
	     (let ((loadfile (mk-fname tok dir-sep)))
	     (let ((pathfile
		    (let ((%search-path %library-search-path))
		      (look-for-lib loadfile tok))))
             (princ (concat "Loading library " tok " ..."))
             (terpri)
	     (let ((%lib-dir (get-path pathfile dir-sep)))
                 (ml-load (catenate %lib-dir dir-sep loadfile)
			  |%print_lib-flag|)))))
         (setq %libraries (cons tok %libraries))
         (terpri)
         (princ (concat "Library " tok " loaded."))
         (terpri)
         nil)))

(dml |load_library| 1 ml-load_library (|string| -> |void|))

(defun ml-libraries () %libraries)

(dml |libraries| 0 ml-libraries (|void| -> (|string| |list|)))


;;; Go from ML to Lisp - was previously in Makefile

(dml |lsp| 0 ml-break (|void| -> |void|))


;;; Reset %hol-dir and %lib-dir from ML (used in install)
;;; no longer used
;;; (defun ml-set_hol_lib_dir (s)
;;; (setq %hol-dir s)
;;; (setq %lib-dir (concat s "/Library"))
;;; nil)
;;;(dml |set_hol_lib_dir| 1 ml-set_hol_lib_dir (|string| -> |void|))

;;; Return the library pathname. 	[TFM 90.12.01]
(defun ml-library_pathname () %lib-dir)
(dml |library_pathname| 0 ml-library_pathname (|void| -> |string|))

;;; Return the pathname to the HOL system directory. 	[TFM 91.05.17]
(defun ml-hol_pathname () %hol-dir)
(dml |hol_pathname| 0 ml-hol_pathname (|void| -> |string|))

