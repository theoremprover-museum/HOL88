; FILE	       : parse_hacks.l
; DESCRIPTION  : Parser hacks to support programming language
;									
; AUTHOR       : M. Gordon						
; DATE	       : 30 March 1989


(eval-when (compile)
     #+franz (include "f-franz")
     (include "f-constants")
     (include "f-macro")
     (include "f-ol-rec")
     (*lexpr concat)
     (special hoare-begin hoare-end))


; "X+1=x" --> "\s. (s`X`)+1 =x"

(defun trans-term (tm)
 `(MK=ABS
    (MK=TYPED (MK=VAR |s|) (MK=TYPE |fun| (MK=TYPE |string|) (MK=TYPE |num|)))
    ,(trans-term-fn tm)))

; predicate that is true only on lower case atoms

(defun lowp (x)
 (and (atom x) (lessp 96 (cascii x)) (lessp (cascii x) 123)))

(defun add-primes (x) (concat '|`| x '|`|))

(defun trans-term-fn (tm)
 (cond ((atom tm) tm)
       ((and (eq (car tm) 'MK=VAR) (not(lowp (cadr tm))))
        `(MK=COMB (MK=VAR |s|) (MK=CONST ,(add-primes (cadr tm)))))
       (t (cons (trans-term-fn (car tm)) (trans-term-fn (cdr tm))))))

;  "{tm}"  -->  "<translation of tm>"

(setq hoare-begin '|{|)
(setq hoare-end   '|}|)

(eval-when (load)
   (let ((lang1 'ol1) (lang2 'ol2) (langlp 'ollp))
      (unop hoare-begin '(ol-hoare-rtn))))

(putprop hoare-end 5 'ollp)

(defun ol-hoare-rtn ()
 (prog (tm)
       (setq tm (term-check (parse-level 10) '|non term inside { ... }|))
       (check hoare-end nil '|missing } after {|)
       (return (trans-term tm))))


; "while b do c"
; 
; parses via ol-while-rtn to:
; 
; "MK_WHILE(b,c)"

(eval-when (load)
   (let ((lang1 'ol1) (lang2 'ol2) (langlp 'ollp))
      (unop '|while| '(ol-while-rtn))
      (unop '|assert| '(ol-assert-rtn))
      (unop '|invariant| '(ol-invariant-rtn))
      (unop '|variant| '(ol-variant-rtn))
     ))

(putprop '|do| 5 'ollp)
(putprop '|assert| 5 'ollp)
(putprop '|invariant| 5 'ollp)
(putprop '|variant| 5 'ollp)

(defun ol-while-rtn ()
 (prog (b tm)
       (setq b (term-check (parse-level 10) '|non term after while|))
       (check '|do| nil '|missing do after while|)
       (setq tm (term-check (parse-level 10) '|bad term after do|))
       (return `(MK=COMB (MK=CONST MK_WHILE)
                 (MK=COMB (MK=COMB (MK=CONST |,|) ,(trans-term b)) ,tm)))))

(defun ol-assert-rtn ()
 `(MK=COMB 
   (MK=CONST MK_ASSERT)
   ,(term-check (parse-level 10) '|non term after assert|)))

(defun ol-invariant-rtn ()
 `(MK=COMB 
   (MK=CONST MK_INVARIANT)
   ,(term-check (parse-level 10) '|non term after invariant|)))

(defun ol-variant-rtn ()
 `(MK=COMB 
   (MK=CONST MK_VARIANT)
   ,(term-check (parse-level 10) '|non term after variant|)))


; ===================================================================== 
; "if b then c1 else c2"
; 
; parses via ol-if-rtn to:
; 
; "MK_IF2(b,c1,c2)"


(eval-when (load)
   (let ((lang1 'ol1) (lang2 'ol2) (langlp 'ollp))
      (unop '|if| '(ol-if-rtn))))

(putprop '|then| 5 'ollp)
(putprop '|else| 5 'ollp)

(defun ol-if-rtn ()
 (prog (b c1 c2)
       (setq b (term-check (parse-level 10) '|non term after if|))
       (check '|then| nil '|missing then after if|)
       (setq c1 (term-check (parse-level 10) '|bad term after then|))
       (if (not(eq token '|else|))
           (return `(MK=COMB 
                     (MK=CONST MK_IF1)
                     (MK=COMB (MK=COMB (MK=CONST |,|) ,(trans-term b)) 
                              ,c1)))
           (gnt))
       (setq c2 (term-check (parse-level 10) '|non term after else|))
       (return `(MK=COMB 
                 (MK=CONST MK_IF2)
                 (MK=COMB (MK=COMB (MK=CONST |,|) ,(trans-term b))
                          (MK=COMB (MK=COMB (MK=CONST |,|) ,c1) ,c2))))))


; "c1; c2"   parses to "MK_SEQ(c1,c2)"
; "x := e"   parses to "MK_ASSIGN(x,e)"

(eval-when (load)
   (let ((lang1 'ol1) (lang2 'ol2) (langlp 'ollp))
       (binop scolon-sym    
         10 
         '`(MK=COMB 
            (MK=CONST MK_SEQ)
            (MK=COMB (MK=COMB (MK=CONST |,|) ,arg1) ,(parse-level 8))))
       (binop '|:=|
         15 
         '`(MK=COMB 
            (MK=CONST MK_ASSIGN)
            (MK=COMB 
              (MK=COMB (MK=CONST |,|) (MK=CONST ,(add-primes(cadr arg1))))
              ,(trans-term (parse-level 10)))))
     ))



