;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-format.l                                          ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Pretty printer for ML and OL values and types       ;;;
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
;;;   REVISION HISTORY: Created by L. Paulson in unix version 3.1           ;;;
;;;                                                                         ;;;
;;; V4.1 added "inconsistent breaks", record macros, depth limit,           ;;;
;;;     hypenated some names                                                ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; method based on
;;; Oppen, Derek C., "Pretty Printing",
;;;      Technical report STAN-CS-79-770, Stanford University, Stanford, CA.
;;;      Also in ACM TOPLAS, October 1980, P. 465.

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-macro")
   (include "lisp/f-constants")
   (special %max-depth %margin %output-buffer))

#+franz
(declare
   (localf push-print-stack
      print-blanks
      break-new-line
      break-same-line
      clear-scan-stack
      scan-push
      scan-pop
      scan-empty
      scan-top
      clear-queue
      enqueue
      advance-left
      setsize
      enqueue-string
      pbegin-block))


;;; constant definitions

(eval-when (compile load)
   (defconstant %infinity 999999))        ;large value for default token size


;;; global variables (default changed from 30 to 500 by mjcg for hol)
;;; Buffer output (makes printing quicker in some implementations)
;;; - flush on newline

(setq %max-depth 500)                         ;max be re-set by user
(setq %margin 72)                             ;right margin
(setq %output-buffer nil)


;;; %space              ; space remaining on this line
;;; %left-total         ; total width of tokens already printed
;;; %right-total                ; total width of tokens ever put in queue
;;; %pstack             ; printing stack with indentation entries
;;; %prettyon           ; indicates if pretty-printing is on
;;; %curr-depth         ; current depth of "begins"
;;; %max-depth          ; max depth of "begins" to print

;;; data structures
;;; a token is one of
;;;    ('string  text)
;;;    ('break   width  offset)
;;;    ('begin   indent  [in]consistent )
;;;    ('end)

(eval-when (compile)
   (defmacro tok-class (tok) `(car ,tok))
   (defmacro get-string-text (tok) `(cadr ,tok))
   (defmacro get-break-width (tok) `(cadr ,tok))
   (defmacro get-break-offset (tok) `(caddr ,tok))
   (defmacro get-block-indent (tok) `(cadr ,tok))
   (defmacro get-block-break (tok) `(caddr ,tok)))


;;; the Scan Stack
;;; each stack element is (left-total . qi)
;;;   where left-total the value of %left-total when element was entered
;;;   and qi is the queue element whose size must later be set 

(eval-when (compile)
   (defmacro make-ss-elem (left qi) `(cons ,left ,qi))
   (defmacro get-left-total (x) `(car ,x))
   (defmacro get-queue-elem (x) `(cdr ,x)))


;;; the Queue
;;; elements (size token len)   

(eval-when (compile)
   (defmacro make-queue-elem (size tt len) `(list ,size ,tt ,len))
   (defmacro get-queue-size (q) `(car ,q))
   (defmacro get-queue-token (q) `(cadr ,q))
   (defmacro get-queue-len (q) `(caddr ,q))
   (defmacro put-queue-size (q size) `(rplaca ,q ,size)))


;;; the Printing Stack, %pstack 
;;;  each element is (break . offset)

(eval-when (compile)
   (defmacro get-print-break (x) `(car ,x))
   (defmacro get-print-indent (x) `(cdr ,x)))


(defun push-print-stack (break offset)
   (push (cons break offset) %pstack))


(defun flush-output-buffer nil
   ;; Some data types (e.g. streams) cannot be catenated in franz, so
   ;; print out items in buffer separately. 
   #+franz (mapc #'llprinc (nreverse %output-buffer))
   #-franz (llprinc (apply #'catenate (nreverse %output-buffer)))
   (setq %output-buffer nil))


;;; print n blanks
(defun print-blanks (n)
   (do ((i n (1- i))) ((zerop i)) (push " " %output-buffer)))


;;; print a token
(defun print-token (tt size)
   (case (tok-class tt)
      (string
         (push (get-string-text tt) %output-buffer)
         (decf %space size))
      (begin
         (let ((offset (- %space (get-block-indent tt)))
               (brtype (if (and %prettyon (> size %space)) 
                     (get-block-break tt)
                     'fits)))
            (push-print-stack brtype offset)))
      (end (pop %pstack))
      (break
         (case (get-print-break (car %pstack))
            (consist (break-new-line tt))
            (inconsist
               (if (> size %space) (break-new-line tt) (break-same-line tt)))
            (fits (break-same-line tt))
            (t (lcferror '|bad break in pretty printer|))))
      (t (lcferror (cons tt '(bad print-token type))))))  ; print-token


;;; print a break, indenting a new line
(defun break-new-line (tt)
   (setq %space (- (get-print-indent (car %pstack)) (get-break-offset tt)))
   (flush-output-buffer)
   (llterpri)
   (print-blanks (- %margin %space)))          ; break-new-line

;;; print a break that fits on the current line
(defun break-same-line (tt)
   (let ((width (get-break-width tt)))
      (decf %space width)
      (print-blanks width)))                      ; break-same-line

;;; routines for scan stack
;;; determine sizes of blocks

(defun clear-scan-stack ()
   (setq %scan-stack (list (make-ss-elem -1 nil))))    ; clear-scan-stack

(defun scan-push ()
   (push (make-ss-elem %right-total (car %qright)) %scan-stack)
   nil)        ; scan-push

;;; Pop scan stack and return its value of %qright
(defun scan-pop () (get-queue-elem (pop %scan-stack)))  ; scan-pop

;;; test if scan stack contains any data that is not obsolete
(defun scan-empty  ()
   (< (get-left-total (car %scan-stack)) %left-total))  ; scan-empty

;;; return the kind of token pointed to by the top element of the scan stack
(defun scan-top ()
   (tok-class (get-queue-token (get-queue-elem (car %scan-stack)))))   ; scan-top

;;; the queue
;;; size is set when the size of the block is known
;;; len is the declared length of the token

(defun clear-queue ()
   (setq %left-total 1)
   (setq %right-total 1)
   (setq %qleft nil)
   (setq %qright nil))         ; clear-queue

;;; perhaps should use a dummy list header so %qleft is never nil
(defun enqueue (tt size len)
   (incf %right-total len)
   (let ((newcell (list (make-queue-elem size tt len))))
      (if %qleft (rplacd %qright newcell) (setq %qleft newcell))
      (setq %qright newcell)))                 ; enqueue


;;; Print if token size is known or printing is lagging
;;; Size is known if not negative
;;; Printing is lagging if the text waiting in the queue requires
;;;   more room to print than exists on the current line
(defun advance-left ()
   (while (and %qleft
         (or (not (< (get-queue-size (car %qleft)) 0))
            (> (- %right-total %left-total) %space)))
      (let* ((listsizetokenlen (pop %qleft))
            (size (car listsizetokenlen))
            (token (cadr listsizetokenlen))
            (len (caddr listsizetokenlen)))
         (print-token token (if (< size 0) %infinity size))
         (incf %left-total len))))        ; advance-left

;;; set size of block on scan stack
(defun setsize (tok)
   (cond ((scan-empty) (clear-scan-stack))
      ((eq (scan-top) tok)
         (let ((qi (scan-pop)))
            (put-queue-size qi (+ %right-total (get-queue-size qi))))))
   nil)                                          ; setsize


;;; *************************************************************
;;; procedures to control prettyprinter from outside

;;; the user may set the depth bound %max-depth
;;; any text nested deeper is printed as the character &


;;; print a literal string of given length
(defun pstringlen (str len)
   (if (< %curr-depth %max-depth) (enqueue-string str len)))    ; pstringlen

(defun enqueue-string (str len)
   (enqueue `(string ,str) len len)
   (advance-left))             ; enqueue-string

;;; print a string
(defun pstring (str)
   (pstringlen str (flatsize2 str))); pstring

;;; open a new block, indenting if necessary
(defun pbegin-block (indent break)
   (incf %curr-depth)
   (cond ((< %curr-depth %max-depth)
         (enqueue `(begin ,indent ,break) (- 0 %right-total) 0)
         (scan-push))
      ((= %curr-depth %max-depth)
         (enqueue-string '& 1))))  ; pbegin-block

;;; special cases: consistent, inconsistent
(defun pbegin (indent) (pbegin-block indent 'consist))  ; pbegin
(defun pibegin (indent) (pbegin-block indent 'inconsist))  ; pibegin

;;; close a block, setting sizes of its subblocks
(defun pend ()
   (when (< %curr-depth %max-depth)
      (enqueue '(end) 0 0)
      (setsize 'break)
      (setsize 'begin))
   (decf %curr-depth))           ; pend

;;; indicate where a block may be broken
(defun pbreak (blankspace offset)
   (when (< %curr-depth %max-depth)
      (enqueue `(break ,blankspace ,offset)
         (- 0 %right-total)
         blankspace)
      (setsize 'break)
      (scan-push)))  ; pbreak

;;; Initialize pretty-printer.
(defun pinit ()
   (clear-queue)
   (clear-scan-stack)
   (setq %curr-depth 0)
   (setq %space %margin)
   (setq %prettyon t)
   (setq %pstack nil)
   (pbegin 0)) ; pinit

;;; Turn formatting on or off
;;;   prevents the signalling of line breaks
;;;   free space is set to zero to prevent queuing of text
(defun setpretty (pp)
   (setq %prettyon pp)
   (if pp (setq %space %margin)
      (setq %space 0)))  ; setpretty

;;; Print a new line after printing all queued text
(defun pnewline ()
   (pend)
   (setq %right-total %infinity)
   (advance-left)
   (flush-output-buffer)
   (llterpri)
   (pinit)) ; pnewline

;;; Print all remaining text in queue.
;;; Reinitialize (or turn off) prettyprinting
(defun ml-set_prettymode (pp)
   (pnewline)
   (setpretty pp))  ; ml-set_prettymode

(eval-when (load)
   (pinit)
   (setpretty t))


;;; Added 16/10/89 by MJCG
(defun ml-set_margin (n)
   (prog1 %margin (setq %margin n)))              ; ml-set_margin

(dml |set_margin| 1 ml-set_margin (|int| -> |int|))

;;; changed by mjcg for hol to return old %max-depth
(defun ml-max_print_depth (md)
   (prog1 %max-depth (setq %max-depth md)))              ; ml-max_print_depth

(dml |max_print_depth| 1 ml-max_print_depth (|int| -> |int|))

;;; Deleted for HOL88 by MJCG (30/11/88)
;;; turn on pretty-printing of theories (useful for ftp etc.)
;;;(defun ml-prettyprint_theories (x)
;;;  (prog1 |%theory_pp-flag| (setq |%theory_pp-flag| x)))          

;;;(dml |prettyprint_theories| 1 ml-prettyprint_theories (|bool| -> |bool|))

(dml |set_pretty_mode| 1 ml-set_prettymode (|bool| -> |void|))
(dml |print_newline| 0 pnewline (|void| -> |void|))
(dml |print_begin| 1 pbegin (|int| -> |void|))
(dml |print_ibegin| 1 pibegin (|int| -> |void|))
(dml |print_end| 0 pend (|void| -> |void|))
(dml |print_break| 2 pbreak ((|int| |#| |int|) -> |void|))
