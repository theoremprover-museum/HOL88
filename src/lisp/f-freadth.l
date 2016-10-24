;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-freadth.l                                         ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Fast theory read in CL (except Lucid).  NOTE THAT   ;;;
;;;                     THIS CODE IS ONLY FOR COMMON LISP HOL AND NOT FRANZ ;;;
;;;                     LISP HOL                                            ;;;
;;;   AUTHOR:           John Carroll, University of Cambridge (May 1990)    ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-cl.l, f-macro.l                                   ;;;
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

;;; *** Patch to lisp/f-thyfns.l

(eval-when (load eval)
   (warn "lisp/f-freadth.l is redefining function THY-READ"))

(eval-when (compile) (include "lisp/f-macro"))

(defun thy-read (thy #+franz piport #-franz *standard-input*)
   (second     ; to ignore the (quote ...)
      (third   ; to ignore the (setq %theorydata ...)
         (errortrap
            #'(lambda (ertok) (msg-failwith %failtok thy " theory damaged"))
            ;; Franz-compatible theory reader only applicable in
            ;; CL - also not much use on non-unix architectures
            ;; added PC to exclusions (JAC 19.06.92)
            #+(or franz :macintosh pc lucid) (llread)
            #-(or franz :macintosh pc lucid) (fast-read-theory *standard-input*))
         )))

;;; *** End of patch to lisp/f-thyfns.l


;;; Following are symbols within theory data to make sure end up in
;;; upper case, to agree with their casing in rest of HOL CL code

(defvar *fast-read-upper-case*
   (make-hash-table :size 40 :test #'equal))

(eval-when (load eval)
   (mapc
      '(lambda (str)
           (setf (gethash str *fast-read-upper-case*)
              (intern (string-upcase str))))
      '("%t" "abs" "comb" "const" "pred" "var")))


;;; Minimal 'readtable' just for reading in theory files

(defvar *fast-read-char-vector*
   (make-array 256 :initial-element :constituent))

(eval-when (load eval)
   (mapc
      '(lambda (char)
           (setf (svref *fast-read-char-vector* (char-int char))
              nil)) ; whitespace
      '(#\space #\newline #\tab #\linefeed))
   (mapc
      '(lambda (char)
           (setf (svref *fast-read-char-vector* (char-int char))
              :non-constituent))
      '(#\( #\)))

   (setf (svref *fast-read-char-vector* (char-int #\\))
      :single-escape)
   (setf (svref *fast-read-char-vector* (char-int #\|))
      :multiple-escape)
   (setf (svref *fast-read-char-vector* (char-int #\"))
      :string-quote))


;;;

(eval-when (compile load eval)
   (defmacro eq-chars (x y)
      `(char= (the character ,x) (the character ,y))))


(defun fast-peek-skipping (stream)
   ;; the same as (peek-char t ,stream nil nil)
   (declare (optimize (speed 3) (safety 0)))
   (let ((char (read-char stream nil nil)))
      #+(or kcl akcl) (declare (object char))
      (loop
         (unless char (return))
         (when
            (svref (the simple-vector *fast-read-char-vector*)
               (the fixnum (char-int (the character char))))
            (unread-char char stream)
            (return))
         (setq char (read-char stream nil nil)))))

   
;;;

(defun fast-read-theory (stream) 
   (fast-peek-skipping stream)
   (fast-read-expr stream (read-char stream) 1))


(defun fast-read-expressions (stream level)
   (declare (optimize (speed 3) (safety 0)))
   (let ((exps nil) (char nil))
      (loop
         (setq char (read-char stream))
         (cond
            ((eq-chars char #\))
               (fast-peek-skipping stream)
               (return (nreverse exps)))
            ((eq-chars char #\.)
               (fast-peek-skipping stream)
               (let ((res (nreverse exps))) 
                  (rplacd (last res)
                     (fast-read-expr stream (read-char stream) level))
                  ;; assume followed immediately by right parenthesis
                  (read-char stream)
                  (fast-peek-skipping stream)
                  (return res)))
            (t
               (push (fast-read-expr stream char level)
                  exps))))))


(defun fast-read-expr (stream char level)
   (declare (optimize (speed 3) (safety 0)))
   (cond
      ((eq-chars char #\')
         ;; assume no whitespace after quote
         (list 'quote (fast-read-expr stream (read-char stream) (1+ level))))
      ((eq-chars char #\()
         ;; assume no whitespace after open parenthesis
         (let ((exps (fast-read-expressions stream (1+ level))))
            (when (= level 4)
               (setf (car exps) (intern (string (car exps)))))
            exps))
      (t
         (fast-read-atom stream char))))


;;; Changed buffer from a static string to being held in a special variable
;;; since IBCL choked on it (JAC 19.06.92)

(defvar *fast-read-atom-buffer* (make-string 256))

(defun fast-read-atom (stream char)
   (declare (optimize (speed 3) (safety 0)))
   (let
      ((buffer *fast-read-atom-buffer*)
       (index 0)
       (number-p (digit-char-p (the character char)))
       (string-p nil)
       (multiple-escape-p nil) (escaped-p nil)
       type)
      (declare (fixnum index))
      (loop
         (setq type
            (svref (the simple-vector *fast-read-char-vector*)
                (the fixnum (char-int (the character char)))))
         (cond
            ((eq type :single-escape)
               (setq escaped-p t)
               (setf (schar buffer index) (read-char stream))
               (incf index))
            ((eq type :multiple-escape)
               (setq escaped-p t)
               (setq multiple-escape-p (not multiple-escape-p)))
            ((eq type :string-quote)
               (if string-p (return) (setq string-p t)))
            ((or (eq type :constituent) multiple-escape-p string-p)
               (setf
                  (schar (the string buffer) (the fixnum index))
                  char)
               (setq index (the fixnum (1+ (the fixnum index)))))
            ((null type) ; whitespace
               (fast-peek-skipping stream)
               (return))
            (t ; :non-constituent
               (unread-char char stream)
               (return))
            )
         (setq char (read-char stream)))
      (if number-p
         (parse-integer buffer :end index)
         (do*
            ((res (make-string index))
             (x 0 (the fixnum (1+ (the fixnum x)))))
            ((= (the fixnum x) (the fixnum index))
               (cond
                  (string-p res)
                  (escaped-p (intern res))
                  ((gethash res *fast-read-upper-case*))
                  (t (intern res))))
            (declare (fixnum x))
            (setf (schar (the string res) x)
               (the character (schar (the string buffer) x)))))))


;;; End of file


