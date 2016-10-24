;;; NOTE NOTE NOTE *********************************************************;;;
;;; This file deleted from the build sequence for HOL version 1.12          ;;;
;;; [TFM 90.09.09]                                                          ;;;
;;; ************************************************************************;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-obj.l                                             ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      LISP objects                                        ;;;
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
;;;   REVISION HISTORY: Introduced by GH in V4.1                            ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-macro"))


;;; discriminators
(dml |is_string| 1 ml-is_string (|obj| -> |bool|))
(defun ml-is_string (x) (symbolp x))  ;ml-is_string

(dml |is_int| 1 numberp (|obj| -> |bool|))

(dml |is_cons| 1 #+franz dtpr #-franz consp (|obj| -> |bool|))

;;; constructors
(dml |obj_of_string| 1 Id (|string| -> |obj|))

(dml |obj_of_int| 1 Id (|int| -> |obj|))
(defun Id (x) x)  ;Id

;;; ---------------------------------------------------------------
;;; The paired cons function later gets REDEFINED to be a
;;; curried function  (in ml/ml-curry.ml)				   
;;;  --------------------------------------------------------------

(dml |cons| 2 cons ((|obj| |#| |obj|) -> |obj|))

;;; destructors
(dml |string_of_obj| 1 ml-string_of_obj (|obj| -> |string|))
(defun ml-string_of_obj (x)
   (if (ml-is_string x) x (throw-from evaluation '|string_of_obj|)))  ;ml-string_of_obj

(dml |int_of_obj| 1 ml-int_of_obj (|obj| -> |int|))
(defun ml-int_of_obj (x)
   (if (numberp x) x (throw-from evaluation '|int_of_obj|)))  ;ml-int_of_obj

(dml |left| 1 ml-left (|obj| -> |obj|))
(defun ml-left (x)
   (if (consp x) (car x) (throw-from evaluation '|left|)))     ;ml-left

(dml |right| 1 ml-right (|obj| -> |obj|))
(defun ml-right (x)
   (if (consp x) (cdr x) (throw-from evaluation '|right|)))    ;ml-right

;;; ---------------------------------------------------------------
;;; These paired functions: set_left, set_right and eq, later get
;;;  REDEFINED to be curried functions (in ml/ml-curry.ml)
;;;  --------------------------------------------------------------

;;;updators
(dml |set_left| 2 ml-set_left ((|obj| |#| |obj|) -> |obj|))
(defun ml-set_left (x y)
   (if (consp x) (rplaca x y) (throw-from evaluation '|set_left|)))    ;ml-set_left

(dml |set_right| 2 ml-set_right ((|obj| |#| |obj|) -> |obj|))
(defun ml-set_right (x y)
   (if (consp x) (rplacd x y) (throw-from evaluation '|set_rigth|)))   ;ml-set_right

;;;equality
(dml |eq| 2 eq ((|obj| |#| |obj|) -> |bool|))

;;;lisp eval, for communication between lisp and ml
;;;use with caution!
(dml |lisp_eval| 1 eval (|obj| -> |obj|))
