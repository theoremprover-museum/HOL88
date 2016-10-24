;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-mlprin.l                                          ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Prints the ML parse tree to a given depth to report ;;;
;;;                     type errors.  Called only from f-typeml.l           ;;;
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
;;;   REVISION HISTORY: Original code: mlprin (lisp 1.6) part of Edinburgh  ;;;
;;;                     LCF by M. Gordon, R. Milner and C. Wadsworth (1978) ;;;
;;;                     Transported by G. Huet in Maclisp on Multics, Fall  ;;;
;;;                     1981                                                ;;;
;;;                                                                         ;;;
;;;                     V4-5: rewritten by Larry Paulson to avoid calling   ;;;
;;;                           eval                                          ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz")
   (include "lisp/f-constants")
   (include "lisp/f-macro"))


#+franz
(declare
   (localf print-nth
      print-ml-cases
      print-ml-match
      print-ml-funcase
      print-ml1
      print-ml-list
      print-conditional
      print-trap))


;;; macro for printing subtrees
(eval-when (compile load)
   (defun expand-print (x)
      (cond
         ((numberp x) `(print-nth ,x))
         ((atom x) `(llprinc ',x))
         (t x)))
   (defmacro pml #+franz l #-franz (&rest l)
      (cons 'progn (mapcar #'expand-print l))))

(defun print-nth (n)
   (print-ml-cases (car (nthcdr n %ex)) %print-depth))

(defun print-ml-cases (%ex %print-depth)
   (if (atom %ex) (llprinc %ex)
      (case (car %ex)
         (mk-nulltyp (pml |void|))
         (mk-inttyp (pml |int|))
         (mk-booltyp (pml |bool|))
         (mk-toktyp (pml |string|))
         (mk-termtyp (pml |term|))
         (mk-formtyp (pml |form|))
         (mk-typetyp (pml |type|))
         (mk-thmtyp (pml |thm|))
         (mk-vartyp (pml 1))
         (mk-consttyp
            (cond ((null (cddr %ex)) (llprinc (cadr %ex)))
               ((null (cdddr %ex)) (print-ml1 (caddr %ex)) (llprinc (cadr %ex)))
               (t (print-ml-list (cddr %ex) '|(| '|,| '|)| )
                  (llprinc (cadr %ex)))))
         (mk-listtyp (pml 1 |list|))
         (mk-prodtyp (pml |(| 1 |#| 2 |)| ))
         (mk-sumtyp (pml |(| 1 |+| 2 |)| ))
         (mk-funtyp (pml |(| 1 -> 2 |)| ))
         (mk-boolconst (llprinc (if (cadr %ex) '|true| '|false|)))
         (mk-intconst (pml 1))
         (mk-tokconst (pml |`| 1 |`| ))
         (mk-tyquot (pml |": ... "| ))
         (mk-quot (pml |" ... "| ))
         ((mk-var mk-con mk-con0) (pml 1))     ;new
         (mk-wildcard (pml |_|))               ;new
         ;;;       (mk-var (pml 1))
         (mk-fail (pml |fail| ))
         (mk-failwith (pml |failwith| | | 1))
         (mk-empty (pml |()| ))
         (mk-dupl (pml |(| 1 |,| 2 |)| ))
         (mk-list (pml (print-ml-list (cdr %ex) '|[| '|;| '|]| )))
         (mk-straint (pml |(| 1 |:| 2 |)| ))
         (mk-appn (pml |(| 1 | | 2 |)| ))
         (mk-binop (pml |(| 2)
            (llprinc
               (cond ((eq (cadr %ex) '%&) '|&|)
                  ((eq (cadr %ex) '|%or|) '| or |) 
                  (t (cadr %ex))))
            (pml 3 |)| ))
         (mk-unop (cond ((eq (cadr %ex) '|%-|) (llprinc '|-|))
               (t (llprinc (cadr %ex)) (llprinc '| |)))
            (pml 2))
         (mk-do (pml |do| 1))
         (mk-seq  (print-ml-list (append (cadr %ex) (cddr %ex)) '| | '|;| '| |))
         (mk-assign (pml 1 |:=| 2))
         (mk-while (pml |while | 1 | do | 2))
         (mk-test (print-conditional (cdr %ex)))
         (mk-trap 1 (print-trap (cddr %ex)))
         (mk-abstr (pml \(\\ 1 |.| 2 |)| ))
         (mk-fun (pml |fun |) (print-ml-match (cadr %ex)) (pml |)|))
         (mk-case (pml |case | 1 | of |) (print-ml-match (caddr %ex)))
         (mk-in (pml 1 | in | 2))
         (mk-ind (pml 1 | in | 2))
         (mk-ina (pml 1 | in | 2))
         (mk-let (pml |let | 1 | = | 2))
         (mk-letrec (pml |letrec | 1 | = | 2))
         (mk-letref (pml |letref | 1 | = | 2))
         (mk-deftype (pml |lettype ... |))
         (mk-type (pml |type ... |))
         (mk-rectype (pml |rectype ... |))
         (mk-abstype (pml |abstype ... |))
         (mk-absrectype (pml |absrectype ... |))
         (mk-begin (pml |begin | 1))
         (mk-end (pml |end | 1))
         (t (pml | ... |)))))

(defun print-ml-match (funcase-list)
   (print-ml-funcase (car funcase-list))
   (mapc #'(lambda (funcase) (llprinc " | ")(print-ml-funcase funcase))
            (cdr funcase-list)))                  ;print-ml-match
      
(defun print-ml-funcase (funcase)
   (print-ml1 (car funcase))
   (llprinc '| . |)
   (print-ml1 (cdr funcase)))                  ;print-ml-funcase


;;; Entry point, binding %print-depth

(defun print-ml-text (ex %print-depth) 
   (print-ml1 ex))                             ;print-ml-text

(defun print-ml1 (ex)
   (cond ((atom ex) (llprinc ex))
      ((zerop %print-depth) (llprinc '| ... |))
      (t (print-ml-cases ex (sub1 %print-depth))))) ;print-ml1


;;; MJCG for HOL88 9/2/89
;;; Bugfix (] not printed for empty lists before)

(defun print-ml-list (l open sep close)
   (llprinc open)
   (when l                                     ; just brackets if empty list
      (print-ml1 (car l))
      (mapc #'(lambda (x) (llprinc sep) (print-ml1 x)) (cdr l)))
   (llprinc close))                            ;print-ml-list

(defun print-conditional (pt)
   (mapc 
      #'(lambda (x)
         (llprinc '|if |) (print-ml1 (cadr x))
         (llprinc (if (eq (car x) 'once) '| then | '| loop |))
         (print-ml1 (cddr x)))
      (car pt))
   (if (cdr pt)                         ; optional else part
      (let ((opn (caadr pt)) (body (cdadr pt)))
         (llprinc (if (eq opn 'once) '| else | '| loop |))
         (print-ml1 body))))                    ;print-conditional

(defun print-trap (f)
   (mapc 
      #'(lambda (x)
         (llprinc (if (eq (car x) 'once) trapif-then-sym trapif-loop-sym))
         (print-ml1 (cadr x))
         (llprinc '| |) (print-ml1 (cddr x)))
      (car f))
   (if (cdr f)                          ; optional ? or ! part
      (let ((opn (caadr f)) (body (cdadr f)))
         (if (atom opn)
            (llprinc (if (eq opn 'once) trap-then-sym trap-loop-sym))
            (progn
               (llprinc (if (eq (car opn) 'once) trapbind-then-sym trapbind-loop-sym))
               (llprinc (cdr opn))
               (llprinc '| |)))
         (print-ml1 body))))                    ;print-trap
