;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-macro.l                                           ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Macros for the LCF system                           ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-franz.l (or f-cl.l)                               ;;;
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
   (macros t))


;;; expand a function call
;;;  (function f)    --->    (f arg1 ... argn)
;;;  others           --->    (funcall fun arg1 ... argn)

(defun call-fun (fun args)
   (cond
      ((or (atom fun) (not (member (car fun) '(function quote))))
         `(funcall ,fun ,@args))
      (t `(,(cadr fun) ,@args))))


;;; Print a constant string, computing length at compile-time
;;; for this use flatc rather than flatsize2, 
;;; since flatc is standard Franz while flatsize2 is flatc with a bug fixed
;;; the flatc bug concerns bignums, which do not concern this macro

(defmacro ptoken (str)
   `(pstringlen ',str ,(flatc str)))

(defmacro failwith (tok)
   `(throw-from evaluation ,tok))

(defmacro msg-failwith (tok . msgs)
   ;; fail with appended error message
   `(throw-from evaluation (concat ,tok " -- " . ,msgs)))

(defmacro cond-failwith (tok . code)
   ;; fail if any of the error messages are not nil
   `(let ((msg (or . ,code)))
      (cond
         (msg (throw-from evaluation (concat ,tok " -- " msg))))))

(defmacro failtrap (failfun . trycode)
   ;; ML failure trapping :  trycode ?\tok failfun
   (let ((x (gensym)))
      `((lambda (,x)
            (cond
               ((atom ,x) ,(call-fun failfun (list x)))
               (t (car ,x))))
         (catch-throw evaluation (list (progn . ,trycode))))))

(defmacro errortrap (errorfun . trycode)
   ;; Lisp error trapping 
   (let ((x (gensym)))
      `((lambda (,x)
            (cond ((atom ,x) ,(call-fun errorfun (list x)))
               (t (car ,x))))
         (errset (progn . ,trycode)))))


;;; Apply the function to successive list elements and return the first
;;; non-nil value. If none, return nil

(defmacro exists (fun . lists)
   (let ((vars (mapcar #'(lambda (ignore) (gensym)) lists)))
      (let
         ((inits (mapcar #'(lambda (v l) `(,v ,l (cdr ,v))) vars lists))
            (args (mapcar #'(lambda (v) `(car ,v)) vars)))
         `(do ,inits ((null ,(car vars)) nil)
            (cond (,(call-fun fun args) (return (list ,@args))))))))


(defmacro forall (fun . lists)
   (let ((vars (mapcar #'(lambda (ignore) (gensym)) lists)))
      (let
         ((inits (mapcar #'(lambda (v l) `(,v ,l (cdr ,v))) vars lists))
            (args (mapcar #'(lambda (v) `(car ,v)) vars)))
         `(do ,inits ((null ,(car vars)) t)
            (cond (,(call-fun fun args)) ((return nil)))))))


(defmacro dml (ml-fn n lisp-fn mty)
   `(eval-when (load)
      (declare-ml-fun (quote ,ml-fn) (quote ,n) (quote ,lisp-fn)
         (quote ,mty))))

(defmacro dmlc (id exp mty)
   `(eval-when (load)
      (declare-ml-const (quote ,id) (quote ,exp) (quote ,mty))))
