;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-lis.l                                             ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      ML list functions                                   ;;;
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
;;;   REVISION HISTORY: Original code: lis (lisp 1.6) part of Edinburgh LCF ;;;
;;;                     by M. Gordon, R. Milner and C. Wadsworth   (1978)   ;;;
;;;                     Transported by G. Huet in Maclisp on Multics, Fall  ;;;
;;;                     1981                                                ;;;
;;;                                                                         ;;;
;;;                     V3.2: cleaning-up of functions                      ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro"))


#+franz (declare (localf succeeds))



(dml |length| 1 length ((%a |list|) -> |int|) )

(dml |rev| 1 reverse ((%a |list|) -> (%a |list|)))

(dml |flat| 1 ml-flat (((%a |list|) |list|) ->(%a |list|)))

(defun ml-flat (ll) (apply #'append ll))        ;ml-flat

;;; ---------------------------------------------------------------
;;; PAIRED list utilities which later get REDEFINED to be curried 
;;; functions (in ml/ml-curry.ml)				   
;;;  --------------------------------------------------------------

(dml |mem| 2 #+franz member #-franz member-equal-function
   ((%a |#| (%a |list|)) -> |bool|))

#-franz
(defun member-equal-function (x y)
   (member x y :test #'equal))


(dml |map| 2 ml-map  (((%a -> %b) |#| (%a |list|)) -> (%b |list|)))

;;; ap changed to %ap for HOL version 12 [TFM 90.11.11]
(defun ml-map  (%%f l)
   (mapcar #'(lambda (x) (%ap %%f x)) l))       ;ml-map

(dml |exists| 2 ml-exists  (((%a -> |bool|) |#| (%a |list|)) -> |bool|))

;;; ap changed to %ap for HOL version 12 [TFM 90.11.11]
(defun ml-exists  (p l)			 ;ml-exists
   (block found (while l (if (%ap p (pop l)) (return-from found t))) nil))


(dml |forall| 2 ml-forall  (((%a -> |bool|) |#| (%a |list|)) -> |bool|))

;;; ap changed to %ap for HOL version 12 [TFM 90.11.11]
(defun ml-forall  (p l)
   (block found
      (while l (ifn (%ap p (pop l)) (return-from found nil))) t)) ;ml-forall


(dml |find| 2 ml-find  (((%a -> |bool|) |#| (%a |list|)) -> %a))

;;; ap changed to %ap for HOL version 12 [TFM 90.11.11]
(defun ml-find  (p l)
   (block found
      (while l
         (let ((x (pop l))) (if (%ap p x) (return-from found x))))
      (throw-from evaluation '|find|)))             ;ml-find


(dml |tryfind| 2 ml-tryfind (((%a -> %b) |#| (%a |list|)) -> %b))

;;; ap changed to %ap for HOL version 12 [TFM 90.11.11]
(defun ml-tryfind  (%%f %l)
   (block found
      (while %l
         (catch-throw evaluation (return-from found (%ap %%f (pop %l)))))
      (throw-from evaluation '|tryfind|)))           ;ml-tryfind


(dml |filter| 2 ml-filter
   (((%a -> |bool|) |#| (%a |list|)) -> (%a |list|)))

;;; ap changed to %ap for HOL version 12 [TFM 90.11.11]
(defun ml-filter  (p l)
   (let ((r nil))
      (while l (let ((x (pop l))) (if (%ap p x) (push x r))))
      (reverse r)))                             ;ml-filter

(dml |mapfilter| 2 ml-mapfilter
   (((%a -> %b) |#| (%a |list|)) -> (%b |list|)))

;;; ap changed to %ap for HOL version 12 [TFM 90.11.11]
(defun ml-mapfilter (%%f %l)
   (let ((r nil))
      (while %l
         (catch-throw evaluation (push (%ap %%f (pop %l)) r)))
      (reverse r)))                                ;ml-mapfilter


(dml |rev_itlist| 3 ml-rev_itlist
   (((%a -> (%b -> %b)) |#| ((%a |list|) |#| %b)) -> %b))

;;; ap changed to %ap for HOL version 12 [TFM 90.11.11]
(defun ml-rev_itlist  (f l x)
   (while l (setq x (%ap (%ap f (pop l)) x))) x) ;ml-rev_itlist

;;; ap changed to %ap for HOL version 12 [TFM 90.11.11]
(defun succeeds (%%f x)
   (block OK
      (catch-throw evaluation (%ap %%f x) (return-from OK t))
      nil))     ;succeeds

