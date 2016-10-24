;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-dml.l                                             ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Various DML'ed ML functions                         ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-franz.l (or f-cl.l), f-macro.l, f-constants.l     ;;;
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
;;;   REVISION HISTORY: Original code: dml (lisp 1.6) part of Edinburgh LCF ;;;
;;;                     by M. Gordon, R. Milner and C. Wadsworth   (1978)   ;;;
;;;                     Transported by G. Huet in Maclisp on Multics, Fall  ;;;
;;;                     1981                                                ;;;
;;;                                                                         ;;;
;;; V4.3: Added fast arithmetic (smallnums)  GC                             ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-macro")
   (include "lisp/f-constants")
   (special %display-function)
   (*lexpr concat))


#+franz (declare (localf ml-isl trymlinfix))

(setq infixables
   (list '\\ '|#| '|*| '|+| '|-| '|<| '|=| '|>| '|?| '|@|
      '|^| '|<<|))


;;;  Part 1: Representation of strings
;;;    In general an ml string value tok is represented by
;;;  the lisp atom tok. Beware in the old Edinburg LCF we had
;;;  two special cases:
;;;      (a) the empty string, returned by implode[], is special
;;;      (b) the string nil is non-interned (to avoid a stanford
;;;          lisp problem that reentering a core image destroys
;;;          additional properties we might have given to nil).
;;;    In effect, the functions here determine string as an abstract
;;;  type with explode, implode, tok_of_int, and int_of_tok as primitive
;;;  operations.

;;; tok_of_int and int_of_tok now called tok_of_string and string_of_tok. 

;;;  Sets Manifests:  tokempty
;;; 
;;;  Convention inter-lisps for coercions atoms-ascii codes
;;;  We follow the Lelisp convention of manipulating ascii codes rather
;;;  than atomic character objects. We use mainly:
;;;     imploden : takes as argument a list of ascii codes and returns an
;;;             atomic symbol whose pname is the corresponding string of
;;;             characters.
;;;     exploden : inverse of imploden.

(defun ml-explode (tok)
   (mapcar #'(lambda (ch) (ascii ch)) (exploden tok)))             ;ml-explode

(defun ml-implode (l)
   (if (forall #'(lambda (x) (= (length (exploden x)) 1)) l)
      (concatl l)
      (failwith '|implode|)))                   ;ml-implode


;;;  PART 2: functions to set up lisp definitions in ml

;;; define an ML function in terms of a Lisp function of n arguments
(defun declare-ml-fun (ml-fn n lisp-fn mty)
   (putprop ml-fn (cons lisp-fn n) 'numargs)
   (putprop ml-fn (makety mty) 'mltype)
   ml-fn)                                      ;declare-ml-fun


;;; define an ML constant in terms of a Lisp constant
(defun declare-ml-const (id exp mty)
   (putprop id (eval exp) 'mlval)
   (putprop id (makety mty) 'mltype)
   id)                                         ; declare-ml-const


;;;  PART 3: defining ml primitives

;;;  Uses manifests:  tokempty  [Part 1]
;;;                   initenv  [tml]
;;;  SETS manifests:  infixables, mlreserved
;;;  Sets global:  tracelist

(defun intdiv (x y)
   (if (zerop y)
      (failwith '|div|)
      (#+franz quotient #-franz floor x y)))                  ;intdiv

(dml |*| 2 #+franz times #-franz * ((|int| |#| |int|) -> |int|))
(dml |/| 2 intdiv ((|int| |#| |int|) -> |int|))
(dml |+| 2 #+franz plus #-franz + ((|int| |#| |int|) -> |int|))
(dml |-| 2 #+franz difference #-franz - ((|int| |#| |int|) -> |int|))

(dml |=| 2 equal ((%A |#| %A) -> |bool|))
(dml |<| 2 #+franz lessp #-franz < ((|int| |#| |int|) -> |bool|))
(dml |>| 2 #+franz greaterp #-franz > ((|int| |#| |int|) -> |bool|))
(dml |%-| 1 #+franz minus #-franz - (|int| -> |int|))

;;; If you want fast arithmetic with smallnums instead of bignums,
;;; then use fast_arith

(dml |fast_arith| 1 ml-fast (|bool| -> |.|))

(defun ml-fast (bool)
   (cond
      (bool
         (putprop '|*| '(|*| . 2) 'numargs)
         (putprop '|/| '(#+franz |/| #-franz floor . 2) 'numargs)
         (putprop '|+| '(|+| . 2) 'numargs)
         (putprop '|-| '(|-| . 2) 'numargs)
         (putprop '|<| '(|<| . 2) 'numargs)
         (putprop '|>| '(|>| . 2) 'numargs))
      (t
         (putprop '|*| '(#+franz times #-franz * . 2) 'numargs)
         (putprop '|/| '(intdiv . 2) 'numargs)
         (putprop '|+| '(#+franz plus #-franz + . 2) 'numargs)
         (putprop '|-| '(#+franz difference #-franz - . 2) 'numargs)
         (putprop '|<| '(#+franz lessp #-franz < . 2) 'numargs)
         (putprop '|>| '(#+franz greaterp #-franz > . 2) 'numargs))))  ;ml-fast


(dml |%&| 2 and ((|bool| |#| |bool|) -> |bool|))
(dml |%or| 2 or ((|bool| |#| |bool|) -> |bool|))
(dml |@| 2 append (((%A |list|) |#| (%A |list|)) -> (%A |list|)))
(dml |.| 2 cons ((%A |#| (%A |list|)) -> (%A |list|)))

(dml |not| 1 not (|bool| -> |bool|))
(dml |null| 1 null ((%A |list|) -> |bool|))
(dml |fst| 1 car ((%A |#| %B) -> %A))
(dml |snd| 1 cdr ((%A |#| %B) -> %B))

(dml |do| 1 ml-do (%A -> |void|))

(defun ml-do (x)
   x                                           ;unused
   nil)                                        ;ml-do

(dml |hd| 1 ml-hd ((%A |list|) -> %A))

(defun ml-hd (x)
   (if x
      (car x)
      (failwith '|hd|)))                      ;ml-hd

(dml |tl| 1 ml-tl ((%A |list|) -> (%A |list|)))

(defun ml-tl (x)
   (if x
      (cdr x)
      (failwith '|tl|)))                      ;ml-tl

(dml |isl| 1 car ((%A |+| %B) -> |bool|))

;;; for Lisp code that handles sums
(defun ml-isl (x) (car x))                              ; ml-isl

;;; this slow version is only good for debugging the system
;;; may use instead of car in ml-outl and ml-outr
;;; t = left, nil = right
;;;(defun ml-isl  (x)
;;; (if (and (not (atom x)) (memq (car x) '(t nil)))
;;;     (car x)
;;;     (lcferror (cons x '(bad mlsumtype)))
;;; ))  ;ml-isl

(dml |outl| 1 ml-outl ((%A |+| %B) -> %A))
(defun ml-outl (x)
   (if (car x)
      (cdr x)
      (failwith '|outl|)))                    ;ml-outl

(dml |outr| 1 ml-outr ((%A |+| %B) -> %B))
(defun ml-outr (x) 
   (if (car x)
      (failwith '|outr|)
      (cdr x)))                                  ;ml-outr

(dml |inl| 1 ml-inl (%A -> (%A |+| %B)))
(defun ml-inl (x)
   (cons t x))                                 ;ml-int

(dml |inr| 1 ml-inr (%B -> (%A |+| %B)))
(defun ml-inr (x)
   (cons nil x))                               ;ml-inr

(dml |explode| 1 ml-explode (|string| -> (|string| |list|)))
(dml |implode| 1 ml-implode ((|string| |list|) -> |string|))

(dml |string_of_int| 1 concat (|int| -> |string|))

;;; Superseded by string_of_int.			[TFM 90.05.06]	
;;; (dml |tok_of_int| 1 concat (|int| -> |string|)) 			

(dml |int_of_string| 1 ml-int_of_string (|string| -> |int|))

;;; Superseded by int_of_string.			[TFM 90.05.06]
;;; (dml |int_of_tok| 1 ml-int_of_string (|string| -> |int|))

;;; Franz bug: (readlist (exploden '|;|)) goes into a loop
;;; this makes the original definition of ml-int_of_string (given below)
;;; dangerous (e.g. new_constant(`;`, ...) crashes HOL).
;;;
;;; (defun ml-int_of_string (s)
;;;    (errortrap #'(lambda (x) (failwith "int_of_string"))
;;;       (let ((n (readlist (exploden s))))
;;;          (unless (fixp n) (failwith "int_of_string"))
;;;            n)))
;;; 
;;; (defun ml-int_of_string (s)
;;;    (if (numconstp s) 
;;;       (readlist (exploden s))
;;;       (failwith "int_of_string")))

;;; Modified TFM 88.04.20 
;;; to include bug fix in franz for (readlist (exploden |;|))... which loops
;;; Modified JVT 90.01.08
;;; to fix problem with (exploden |\||)... which loops

(defun ml-int_of_string (s)
   (let
      ((n
            #+franz
            (errortrap
               #'(lambda (x) (failwith '|int_of_string|))
               (if (or (eq s (ascii 124)) (eq s '|,|) (eq s '|;|)) t 
                 (readlist (exploden s))))
            #-franz
            (parse-integer (string s) :junk-allowed t)
            ))
      (if (integerp n) n (failwith '|int_of_string|))))


;;; The following trace functions are relics from the old days of Edinburgh LCF
;;; 
;;; (defvar tracelist nil)
;;; 
;;; (defun checktraceable (F)
;;;     (cond
;;;       ((atom (cdr F))
;;;        (llprinc '|closure not traceable: |)
;;;        (llprinc (cdr F))
;;;        (llterpri)
;;;        (exit-from evaluation 'TRACE))
;;;       (t F)))                                       ;checktraceable
;;; 
;;; (dml |TRACE| 1 ml-TRACE
;;;      (((%A -> %B) -> ((%A -> %B) |#| %C)) -> ((%A -> %B) -> %C)))
;;; 
;;; (defun ml-TRACE (phi)
;;;     (cons
;;;       (function
;;;     (lambda (%e)
;;;       (let ((F (checktraceable (car %e)))
;;;             (Fcopy (cons nil nil))
;;;             (phi (cadr %e)))
;;;         (dis-place Fcopy F)
;;;         (let ((x (ap phi Fcopy)))
;;;           (dis-place F (car x))
;;;           (push (cons F Fcopy) tracelist)
;;;           (cdr x)))))
;;;       (cons phi initenv)))                  ;ml-TRACE
;;; 
;;; (dml |UNTRACE| 1 ml-UNTRACE ((%A -> %B) -> |bool|))
;;; 
;;; (defun ml-UNTRACE  (F)
;;;     (let ((x (assoc-equal F tracelist)))
;;;       (if (null x)
;;;       nil
;;;       (setq tracelist (outq x tracelist))
;;;       (dis-place F (cdr x))
;;;       t)))                                  ;ml-UNTRACE

;;; MJCG 3/3/1992 Added legalconstants to mlinfixables
(defun trymlinfix (fun tok sort)
   (when (or (memq tok mlreserved)
         (not (or (idenp tok) (memq tok infixables) (memq tok legalconsts))))
      (ptoken |can't infix |)
      (ml-print_tok tok)
      (pnewline)
      (failwith fun))
   (mlinfix2 tok sort)) ;trymlinfix

(dml |ml_paired_infix| 1 ml-ml_paired_infix (|string| -> |.|))

(defun ml-ml_paired_infix  (tok)
   (trymlinfix '|ml_paired_infix| tok 'paired))  ;ml-ml_paired_infix

(dml |ml_curried_infix| 1 ml-ml_curried_infix (|string| -> |.|))

(defun ml-ml_curried_infix  (tok)
   (trymlinfix '|ml_curried_infix| tok 'curried))        ;ml-ml_curried_infix

;;; MJCG 19/2/91
;;; ML function for detecting ML infixes 
;;; (built-in and user defined)

(defun ml-is_ml_infix (x) 
 (and (get x 'ml2)
      (memq (car (get x 'ml2)) 
            '(mlcinf-rtn mlinf-rtn appl-rtn))))

(dml |is_ml_infix| 1 ml-is_ml_infix (|string| -> |bool|))

;;; MJCG 01.02.94
;;; Make a HOL variables infixed
;;; olvarinfix defined in f-parsol.l

(dml |infix_variable| 1 olvarinfix (|string| |->| |void|))

;;; RJB 4/3/91
;;; ML function for detecting user defined curried ML infixes 

(defun ml-is_ml_curried_infix (x)
 (and (get x 'ml2)
      (eq (car (get x 'ml2)) 'mlcinf-rtn)))

(dml |is_ml_curried_infix| 1 ml-is_ml_curried_infix (|string| -> |bool|))

;;; RJB 4/3/91
;;; ML function for detecting user defined paired ML infixes 

(defun ml-is_ml_paired_infix (x)
 (and (get x 'ml2)
      (eq (car (get x 'ml2)) 'mlinf-rtn)))

(dml |is_ml_paired_infix| 1 ml-is_ml_paired_infix (|string| -> |bool|))

;;; Return ascii code of a non-empty string. Fail on an empty one.
;;; MJCG 19/2/91

(defun ml-ascii_code (x)
  (if (eq x '||) (failwith '|ascii_code|) (cascii x))) 
 
;;; gives the ascii code of the first char of its arg
(dml |ascii_code| 1 ml-ascii_code (|string| -> |int|))

;;; gives the unit string consisting of the char with ascii code its arg
(dml |ascii| 1 ml-ascii (|int| -> |string|))

(defun ml-ascii (n)
   (if (or (< n 0) (> n 127)) (failwith '|ascii|) (ascii n)))  ; ml-ascii


;;; MJCG 14/11/88 for HOL88
;;; dml-ed versions of some Unix dependent commands
;;; defined in F-unix.l


(dml |system| 1 exec-system-command (|string| -> |int|))

(dml |getenv| 1 ml-getenv (|string| -> |string|))

(dml |host_name| 0 ml-host_name (|void| -> |string|))

(dml |link| 2 ml-link ((|string| |#| |string|) -> |void|))

(dml |unlink| 1  ml-unlink (|string| -> |void|))


(dml |openi| 1 ml-openi (|string| -> |string|))
(dml |openw| 1 outfile (|string| -> |string|))
(dml |append_openw| 1 ml-append_openw (|string| -> |string|))
(dml |read| 1 readc (|string| -> |string|))
(dml |write| 2 write-and-drain ((|string| |#| |string|) -> |void|))
(dml |tty_read| 0 readc (|void| -> |string|))
(dml |tty_write| 1 tty-write-and-drain (|string| -> |void|))
(dml |close| 1 close (|string| -> |void|))

;;; MJCG 2/3/89 for HOL88.1.01
;;; ML function to compute address of a value
;;; Deleted [04.03.91 JVT]
;;; (dml |address| 1 maknum (|*| -> |int|))

;;; MJCG 2/3/89 for HOL88.1.01
;;; ML funtion to compare values

;;; Lexical ordering of lists

(defun ml-ord (l1 l2)
   (if (atom l1)
      (if (null l1)
         (not(null l2))
         (or (listp l2)
            (if (numberp l1)
               (and (numberp l2) (lessp l1 l2))
               (or (numberp l2) (alphalessp l1 l2)))))
      (and (consp l2)
         (if (equal (car l1) (car l2))
            (ml-ord (cdr l1) (cdr l2))
            (ml-ord (car l1) (car l2))))))

(dml |<<| 2 ml-ord ((|*| |#| |**|) -> |bool|))

;;; MJCG 2/3/89 for HOL88.1.01
;;; ML function to return the HOL88 version number
;;; (as an integer less than 1000)
;;;
;;; changed 100 to 100.001 to compensate for
;;; Franz rounding error [TFM 92.06.26]

(defun ml-version ()
   (fix
      (times
         #+franz (readlist (exploden %version))
         #-franz (read-from-string %version)
         100.001)))

(dml |version| 0 ml-version (|void| -> |int|))

;;; Set %display-function, the system utility used to dislay help files.
;;; Default "cat" set in f-system.l.
;;; MJCG 12/11/90

(defun ml-set_help (x) (prog1 %display-function (setq %display-function x)))

(dml |set_help| 1 ml-set_help (|string| -> |string|))

