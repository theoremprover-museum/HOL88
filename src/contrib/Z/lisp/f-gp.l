;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-gp.l                                              ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      General-purpose functions                           ;;;
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
;;;   REVISION HISTORY: Original code: gp (lisp 1.6) part of Edinburgh LCF  ;;;
;;;                     by M. Gordon, R. Milner and C.Wadsworth   (1978)    ;;;
;;;                     Transported by G. Huet in Maclisp on Multics, Fall  ;;;
;;;                     1981                                                ;;;
;;;                                                                         ;;;
;;; V3.1 Unix -- added "uniquesym"                                          ;;;
;;;    Changed "can" to avoid non-local "return" from "tag" (caused looping);;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (*lexpr concat))

#+franz
(declare (localf outq))


(eval-when (compile load eval)
   (defconstant word-sep (cascii '|%|)))         ; word separator for uniquesym


(defun triple (x y z)  (cons x (cons y z)))


;;; A family of "assoc" functions that match the cdr instead of the car

(defun revassoc (x l)
   (block found
      (while l
         (when (equal x (cdar l))
            (return-from found (car l)))
         (setq l (cdr l)))))

(defun revassq (x l)
   (block found
      (while l
         (when (#+franz eq #-franz eql x (cdar l))
            (return-from found (car l)))
         (setq l (cdr l)))))


;;; "assoc" functions that return only the opposite element of the pair found

(defun revassoc1 (x l) (car (revassoc x l)))  ; revassoc1

(defun revassq1 (x l) (car (revassq x l)))  ;revassq1

(defun assq1 (x l)
   (block found
      (while l
         (when (#+franz eq #-franz eql x (caar l))
            (return-from found (cdar l)))
         (setq l (cdr l)))))


(defun assoc1 (x l)
   (block found
      (while l
         (when (#+franz equal #-franz fast-list-equal x (caar l))
            (return-from found (cdar l)))
         (setq l (cdr l)))))

#-franz
(defun fast-list-equal (x y)
   ;; a version of equal that works only for symbols, numbers and lists,
   ;; i.e. ignores vectors, structures etc for speed since they are never
   ;; encountered
   (declare (optimize (speed 3) (safety 0) (space 0)))
   (tagbody loop
      (cond
         ((eql x y) (return-from fast-list-equal t))
         ((and (consp x) (consp y)
               (fast-list-equal (car (the cons x)) (car (the cons y))))
            (setq x (cdr (the cons x)))
            (setq y (cdr (the cons y)))
            (go loop))
         (t (return-from fast-list-equal nil)))))


(defun itlist (fn xl x)
   (let ((rxl (reverse xl)))
      (while rxl (setq x (funcall fn (pop rxl) x)))
      x))                       ; itlist

(defun consprop (i v p)
   (car (putprop i (cons v (get i p)) p)))  ;consprop

(defun itrate (ch n)   
   ;; duplicates ch in a list of length n
   (let ((l nil))
      (while (not (zerop n)) (push ch l) (decf n)) l))  ; itrate


(defun can (fn args)   ;t iff fn[args] does not fail
   (block canit
      (catch-throw evaluation
         (apply fn args) (return-from canit t))
      nil))

(defun inq (x l)
   (if (memq x l) l (cons x l)))  ;inq

(defun outq (x l)
   (when l
      (let ((outtail (outq x (cdr l))))
         (if (#+franz eq #-franz eql x (car l)) 
            outtail (cons (car l) outtail)))))  ; outq

(defun qeval (x) (list 'quote x))  ;qeval


;;; Generates symbols of the form " prefix1 % prefix2 % <number> "
;;; These symbols may be written to the compiler output file,
;;;    thus they should be unique even between sessions of LCF.
;;; The first prefix identifies the class of the symbol
;;; The second prefix should contribute to uniqueness of the symbol
;;; The symbol count is started at a random integer [1..100].

(defun uniquesym (prefix1 prefix2)
   (incf %symcount)
   (concat prefix1 '|%| prefix2 '|%| %symcount))

;;; initialization of uniquesym

(eval-when (load)
   (when initial%load (setq %symcount 0)))


;;; Explode an atom into words separated by the "word-sep"
;;;   "ML % <name> % <count>" --> ("ML" <name> <count>)
;;; Needed to identify different kinds of uniquesyms

(defun explode-word (at)
   (when (atom at)
      (let ((chars (nreverse (cons word-sep (exploden at))))
            (wordlist nil))
         (while chars
            (let ((word nil))
               (while (not (= (car chars) word-sep))
                  (push (pop chars) word))
               (pop chars)
               (push (imploden word) wordlist)))
         wordlist)))    ; explode-word


(defun split (ll)
   (ifn ll (cons nil nil)
      (let* ((consl1l2 (split (cdr ll)))
            (l1 (car consl1l2))
            (l2 (cdr consl1l2)))
         (cons (cons (caar ll) l1) (cons (cdar ll) l2)))))      ; split

(defun binarize (ll tag)
   (if ll 
      (ifn (cdr ll)
         (car ll)
         (list tag (car ll) (binarize (cdr ll) tag))))) ;binarize


(defun dis-place (p1 p2)
   ;;; NOT "displace" which is crazy on the Symbolics
   (rplaca p1 (car p2)) (rplacd p1 (cdr p2)))   ;dis-place


(defun putpropl (l prop)
   (mapcar
      #'(lambda (x) (putprop (car x) (cdr x) prop))
      l))      ;putpropl
