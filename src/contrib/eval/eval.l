(eval-when (compile)
     #+franz (include "f-franz")
     (include "f-macro")
     (include "f-ol-rec")
     (include "genmacs")
     (special bool-NIL-olval bool-CONS-olval T-olval F-olval
              bool-list-fn-ty bool-list-ty DEST_TRI_l MK_TRI_l 
              AND-tm OR-tm NOT-tm))

#+franz
(declare
 (localf map-term
         map-pred-form
         map-thm
         make-eq
         make-conv
         is-eval-fn
         is-bin-comb
         make-ol-bool-list
         dest-ol-list
         pos-dif
         get-width
         bits-to-num
         bits-to-num-fn
         is-boolconst-list
         make-ol-list-val
         is-num-pair
         word-AND
         word-OR
         word-NOT))

; Lisp code for the ML function rem

(defun intrem (x y) (if (zerop y) (failwith '|rem|) (mod x y)))

; (mk-bin-rep w n) = (b1...bw)  where bi is |0| or |1|

(defun mk-bin-rep (w n)
 (prog (x res)
       (setq res nil)
  loop (cond ((zerop w) (failwith 'mk_bin_rep)))
       (setq x (Divide n 2))
       (setq res (cons (atomify(cadr x)) res))
       (setq n (car x))
       (setq w (sub1 w))
       (cond ((zerop n) (go pad)))
       (go loop)
  pad  (cond ((zerop w) (return res)))
       (setq res (cons '|0| res))
       (setq w (sub1 w))
       (go pad)))
 
; (map-term f tm) maps f over all subterms of term tm

(defun map-term (f tm)
 (cond ((is-comb tm) 
        (apply
         f
         (list
          (make-comb 
           (map-term f (get-rator tm)) 
           (map-term f (get-rand tm))
           (get-type tm)))))
       ((is-abs tm)
        (make-abs 
         (get-abs-var tm)
         (map-term f (get-abs-body tm))
         (get-type tm)))
       (t tm)))

; (map-pred-form f "ASSERT t") maps f over all subterms of term t

(defun map-pred-form (f fm)
  (make-pred-form
   (get-pred-sym fm)
   (map-term f (get-pred-arg fm))))

; (map-thm f thm) maps f over all subterms of the conclusion of thm

(defun map-thm (f thm)
 (make-thm (get-hyp thm) (map-pred-form f (get-concl thm))))

;(make-eq t1 t2) makes a value representing "t1 = t2"

(defun make-eq (t1 t2)
 (make-comb
  (make-comb
   (ml-mk_const '|=| `(|fun| ,(get-type t1) (|fun| ,(get-type t2) (|bool|))))
   t1
   `(|fun| ,(get-type t2) (|bool|)))
  t2
  '(|bool|)))

; (make-conv (f tm)) makes the theorem: |-"^tm = tm'"
; where tm' is got from tm by applying f to all subterms of it

(defun make-conv (f tm)
 (make-thm nil (make-pred-form 'HOL_ASSERT (make-eq tm (map-term f tm)))))

; (is-eval-fn (fnname l)) checks that (explodec fnname) = (append l wl)
; where wl is a list of numerals

(defun is-eval-fn (fnname l)
 (prog (fl)
       (setq fl (exploden fnname))
  loop (cond ((and (null l) (not (null fl)))
              (return
               (test-list-els 
                fl 
                '(#/0 #/1 #/2 #/3 #/4 #/5 #/6 #/7 #/8 #/9))))
             ((or (null fl) (not (eq (cascii (car l)) (car fl))))
               (return nil)))
       (setq l (cdr l))
       (setq fl (cdr fl))
       (go loop)))

; (is-bin-comb tm tok) tests whether tm has the form "tok t1 t2"

(defun is-bin-comb (tm tok)
  (and (is-comb tm)
       (is-comb(get-rator tm))
       (is-const(get-rator(get-rator tm)))
       (eq (get-const-name(get-rator(get-rator tm))) tok)))


(eval-when (load)
   (setq bool-list-ty '(|list| (|bool|)))
   (setq bool-list-fn-ty '(|fun| (|list| (|bool|)) (|list| (|bool|))))
   (setq bool-CONS-olval
      (ml-mk_const 'CONS
         '(|fun| (|bool|) (|fun| (|list| (|bool|)) (|list| (|bool|))))))
   (setq bool-NIL-olval (ml-mk_const 'NIL '(|list| (|bool|))))
   (setq T-olval (ml-mk_const  'T '(|bool|)))
   (setq F-olval (ml-mk_const  'F '(|bool|))))

; (make-ol-bool-list '(|1| |0| |1| |1|)) =  "[T; F; T; T]"

(defun make-ol-bool-list (l)
 (cond ((null l) bool-NIL-olval)
       (t (make-comb
           (make-comb 
             bool-CONS-olval 
             (cond ((eq (car l) '|1|) T-olval) (t F-olval))
             bool-list-fn-ty)
           (make-ol-bool-list (cdr l))
           bool-list-ty))))


;is-ol-list tests whether tm is of the form: 
;       CONS t1 (CONS t2 ... (CONS tn nil) ... )

(defun is-ol-list (tm)
   (or (null-ol-list tm)
       (and (is-ol-cons tm)
            (is-ol-list(tl-ol-list tm)))))

;(dest-ol-list "[e1; ... ;en]") gives (e1 ... en)

(defun dest-ol-list (tm)
   (cond ((null-ol-list tm) nil)
         (t (cons (hd-ol-list tm) (dest-ol-list (tl-ol-list tm))))))



;                 | "[t1;...;tw]" if tm = "BITSw #b1...bw"
;  BITS-eval tm = |
;                 | tm            otherwise

(defun BITS-eval (tm)
 (cond ((and (is-comb tm) 
             (is-const (get-rator tm)) 
             (is-const (get-rand tm))
             (is-eval-fn (get-const-name(get-rator tm)) '(B I T S))
             (wordconstp (get-const-name(get-rand tm))))
        (make-ol-bool-list (cdr(explodec(get-const-name(get-rand tm))))))
       (t tm)))

; (BITS-RULE thm) applies BITS-eval to all subterms of the conclusion of thm
; BITS_CONV is the corresponding formula conversion

(defun BITS-RULE (thm) (map-thm 'BITS-eval thm))
(defun BITS-CONV (fm) (make-conv 'BITS-eval fm))

;                 | "r"     if tm = "m+n" and r=m+n
;   ADD-eval tm = |
;                 | tm       otherwise

; Note that "m+n" is really "+ (($, m) n)"

(defun ADD-eval (tm)
 (cond ((and (is-bin-comb tm '|+|)
             (is-const (get-rand(get-rator tm)))
             (is-const (get-rand tm)))
         (ml-mk_const
          (atomify
           (add
            (atom-to-num(get-const-name(get-rand(get-rator tm))))
            (atom-to-num(get-const-name(get-rand tm)))))
          '(|num|)))
        (t tm)))

; (ADD-RULE thm) applies ADD-eval to all subterms of the conclusion of thm
; ADD-CONV is the corresponding formula conversion

(defun ADD-RULE (thm) (map-thm 'ADD-eval thm))
(defun ADD-CONV (fm) (make-conv 'ADD-eval fm))


;                 | "r"     if tm = "m-n" and r=m-n
;   DIF-eval tm = |
;                 | tm       otherwise

; Note that "m-n" is really "- (($, m) n)"

(defun pos-dif (m n)
 (cond ((lessp m n) 0) (t (diff m n))))

(defun DIF-eval (tm)
 (cond ((and (is-bin-comb tm '|-|)
             (is-const (get-rand(get-rator tm)))
             (is-const (get-rand tm)))
         (ml-mk_const
          (atomify
           (pos-dif
            (atom-to-num(get-const-name(get-rand(get-rator tm))))
            (atom-to-num(get-const-name(get-rand tm)))))
          '(|num|)))
        (t tm)))

; (DIF-RULE thm) applies DIF-eval to all subterms of the conclusion of thm
; DIF-CONV is the corresponding formula conversion

(defun DIF-RULE (thm) (map-thm 'DIF-eval thm))
(defun DIF-CONV (fm) (make-conv 'DIF-eval fm))

;                 | "T"     if tm = "x=x" and x=x
;    EQ-eval tm = | "F"     if tm = "x=y" and x,y are different constants
;                 | tm       otherwise

(defun EQ-eval (tm)
 (cond ((is-bin-comb tm '|=|)
        (let ((left  (get-rand(get-rator tm)))
              (right (get-rand tm)))
              (cond ((equal left right) 
                     T-olval)
                    ((and (is-const left) (is-const right)) 
                     F-olval)
                    (t tm))))
       (t tm)))

; (EQ-RULE thm) applies EQ-eval to all subterms of the conclusion of thm
; EQ-CONV is the corresponding formula conversion

(defun EQ-RULE (thm) (map-thm 'EQ-eval thm))
(defun EQ-CONV (fm) (make-conv 'EQ-eval fm))

;                 | "ti"    if tm = "EL i [tn ; ... ; t0]"
;    EL-eval tm = |
;                 | tm      otherwise

(defun EL-eval (tm)
 (cond ((and (is-comb tm)
             (is-comb (get-rator tm))
             (is-const (get-rator(get-rator tm)))
             (eq (get-const-name(get-rator(get-rator tm))) 'EL)
             (is-const (get-rand(get-rator tm)))
             (is-ol-list (get-rand tm)))
        (word-el
         (atom-to-num (get-const-name(get-rand(get-rator tm))))
         (dest-ol-list (get-rand tm))))
       (t tm)))

; (EL-RULE thm) applies EL-eval to all subterms of the conclusion of thm
; EL-CONV is the corresponding formula conversion

(defun EL-RULE (thm) (map-thm 'EL-eval thm))
(defun EL-CONV (fm) (make-conv 'EL-eval fm))

; (get-width `WORDw) = w

(defun get-width (x)
  (imploden (cddddr (exploden x))))

;                   | "#b1...bw" if tm = "WORDw n"
;    WORD-eval tm = |
;                   | tm         otherwise

(defun WORD-eval (tm)
 (cond ((and (is-comb tm) 
             (is-const(get-rator tm)) 
             (is-const (get-rand tm))
             (is-eval-fn (get-const-name (get-rator tm)) '(W O R D))
             (numconstp (get-const-name (get-rand tm))))
       (ml-mk_const 
        (imploden
          (cons #/#
           (mapcar #'cascii
             (mk-bin-rep 
               (get-width(get-const-name(get-rator tm)))
               (atom-to-num(get-const-name(get-rand tm)))))))
        (list
         (imploden
          (append 
           '(#/w #/o #/r #/d) 
           (exploden(get-width(get-const-name(get-rator tm)))))))))
       (t tm)))

; (WORD-RULE thm) applies WORD-eval to all subterms of the conclusion of thm
; WORD-CONV is the corresponding formula conversion

(defun WORD-RULE (thm) (map-thm 'WORD-eval thm))
(defun WORD-CONV (fm) (make-conv 'WORD-eval fm))

; (bits-to-num '(|1| |0| |1| |1|)) = "11" etc.

(defun bits-to-num (l) 
 (ml-mk_const (atomify (bits-to-num-fn (reverse l))) '(|num|)))

(defun bits-to-num-fn (l)
 (cond ((null l) 0)
       (t (add (atom-to-num(car l)) (times 2 (bits-to-num-fn (cdr l)))))))

;                   | "n"   if tm = "VALw #b1...bw" and b1...bw denotes n
;     VAL-eval tm = |
;                   | tm    otherwise

(defun VAL-eval (tm)
 (cond ((and (is-comb tm) 
             (is-const (get-rator tm)) 
             (is-const (get-rand tm))
             (is-eval-fn (get-const-name(get-rator tm)) '(V A L))
             (wordconstp (get-const-name(get-rand tm))))
        (bits-to-num (cdr(explodec(get-const-name(get-rand tm))))))
       (t tm)))

; (VAL-RULE thm) applies VAL-eval to all subterms of the conclusion of thm
; VAL-CONV is the corresponding formula conversion

(defun VAL-RULE (thm) (map-thm 'VAL-eval thm))
(defun VAL-CONV (fm) (make-conv 'VAL-eval fm))

; test whether a list is a sequence of Ts and Fs

(defun is-boolconst-list (l)
 (or (null l)
     (and (or (equal (car l) T-olval)
              (equal (car l) F-olval))
          (is-boolconst-list (cdr l)))))

;                   | "n"   if tm = "V [b1;...;bm]" and b1...bm denotes n
;       V-eval tm = |
;                   | tm    otherwise


(defun V-eval (tm)
 (cond ((and (is-comb tm) 
             (is-const (get-rator tm)) 
             (eq (get-const-name(get-rator tm)) 'V)
             (is-ol-list (get-rand tm))
             (is-boolconst-list(dest-ol-list (get-rand tm))))
        (bits-to-num 
         (mapcar 
          '(lambda (x) (cond ((equal x T-olval) '|1|) (t '|0|)))
          (dest-ol-list (get-rand tm)))))
       (t tm)))

; (V-RULE thm) applies V-eval to all subterms of the conclusion of thm
; V-CONV is the corresponding formula conversion

(defun V-RULE (thm) (map-thm 'V-eval thm))
(defun V-CONV (fm) (make-conv 'V-eval fm))

;                    | t    if tm "(n,m)" where n,m are constants
; (is-num-pair tm) = |
;                    | nil  otherwise

; (make-ol-list-val (t1...tn) cons-rep ty) makes a value representing
; "[t1;...;tn]", cons-rep and ty are the appropriate cons and ty
; to use - i.e. if ty = el-ty list then cons-rep : el-ty -> ty -> ty


(defun make-ol-list-val (l cons-rep ty)
 (cond ((null l) (ml-mk_const 'NIL ty))
       (t (make-comb
           (make-comb cons-rep (car l) (make-type '|fun| (list ty ty)))
           (make-ol-list-val (cdr l) cons-rep ty)
           ty))))

(defun is-num-pair (tm)
 (and (is-bin-comb tm '|,|)
      (is-const (get-rand(get-rator tm)))
      (numconstp (get-const-name(get-rand(get-rator tm))))
      (is-const (get-rand tm))
      (numconstp (get-const-name(get-rand tm)))))


;                   | "[tj;...;ti]" if tm = "SEG(i,j)[tn;...;t0]"
;     SEG-eval tm = |
;                   | tm            otherwise

(defun SEG-eval (tm)
 (cond ((and (is-comb tm) 
             (is-comb (get-rator tm))
             (is-const (get-rator(get-rator tm)))
             (eq (get-const-name(get-rator(get-rator tm))) 'SEG)
             (is-num-pair (get-rand(get-rator tm)))
             (is-ol-list (get-rand tm)))
         (let ((p  (get-rand(get-rator tm)))
               (ty (get-type tm)))
              (make-ol-list-val
               (word-seg 
                (list 
                 (atom-to-num(get-const-name(get-fst p)))
                 (atom-to-num(get-const-name(get-snd p))))
                (dest-ol-list (get-rand tm)))
               (ml-mk_const
                'CONS
                (make-type 
                 '|fun|
                 (list (cadr ty) (make-type '|fun| (list ty ty)))))
               ty)))
       (t tm)))

; (SEG-RULE thm) applies SEG-eval to all subterms of the conclusion of thm
; SEG-CONV is the corresponding formula conversion

(defun SEG-RULE (thm) (map-thm 'SEG-eval thm))
(defun SEG-CONV (fm) (make-conv 'SEG-eval fm))

; (word-AND '|#a1...aw| '|#b1...bw|) = |#c1...cw|  where ci=ai/\bi

(defun word-AND (w1 w2)
 (imploden
  (cons 
   #/#
   (mapcar
    #'(lambda (a b)
        (cond ((eq a #/1) b) (t #/0)))
    (cdr(exploden w1))
    (cdr(exploden w2))))))

;                   | "#c1...cw" if tm = "#a1...aw AND #b1...bw" and ci=ai/\bi
;     AND-eval tm = |
;                   | tm         otherwise

(defun AND-eval (tm)
 (cond ((and (is-comb tm) 
             (is-comb (get-rator tm))
             (is-const (get-rator(get-rator tm)))
             (is-eval-fn (get-const-name(get-rator(get-rator tm))) '(A N D))
             (is-const (get-rand(get-rator tm)))
             (wordconstp (get-const-name(get-rand(get-rator tm))))
             (is-const (get-rand tm))
             (wordconstp (get-const-name(get-rand tm))))
         (ml-mk_const
          (word-AND
           (get-const-name(get-rand(get-rator tm)))
           (get-const-name(get-rand tm)))
          (get-type tm)))
       (t tm)))

; (AND-RULE thm) applies AND-eval to all subterms of the conclusion of thm
; AND-CONV is the corresponding formula conversion

(defun AND-RULE (thm) (map-thm 'AND-eval thm))
(defun AND-CONV (fm) (make-conv 'AND-eval fm))

; (word-OR '|#a1...aw| '|#b1...bw|) = |#c1...cw|  where ci=ai\/bi

(defun word-OR (w1 w2)
 (imploden
  (cons 
   #/#
   (mapcar
    #'(lambda (a b)
         (cond ((eq a #/0) b) (t #/1)))
    (cdr(exploden w1))
    (cdr(exploden w2))))))

;                   | "#c1...cw" if tm = "#a1...aw OR #b1...bw" and ci=ai\/bi
;      OR-eval tm = |
;                   | tm         otherwise

(defun OR-eval (tm)
 (cond ((and (is-comb tm) 
             (is-comb (get-rator tm))
             (is-const (get-rator(get-rator tm)))
             (is-eval-fn (get-const-name(get-rator(get-rator tm))) '(O R))
             (is-const (get-rand(get-rator tm)))
             (wordconstp (get-const-name(get-rand(get-rator tm))))
             (is-const (get-rand tm))
             (wordconstp (get-const-name(get-rand tm))))
         (ml-mk_const
          (word-OR
           (get-const-name(get-rand(get-rator tm)))
           (get-const-name(get-rand tm)))
          (get-type tm)))
       (t tm)))

; (OR-RULE thm) applies OR-eval to all subterms of the conclusion of thm
; OR-CONV is the corresponding formula conversion

(defun OR-RULE (thm) (map-thm 'OR-eval thm))
(defun OR-CONV (fm) (make-conv 'OR-eval fm))

; (word-NOT '|#a1...aw|) = |#b1...bw|  where bi = ~ai

(defun word-NOT (w)
 (imploden
  (cons 
   #/#
   (mapcar
    #'(lambda (a)
         (cond ((eq a #/0) #/1) (t #/0)))
    (cdr(exploden w))))))

;                    | "#b1...bw" if tm = "NOT #a1...aw" and bi = ~ai
;      NOT-eval tm = |
;                    | tm         otherwise

(defun NOT-eval (tm)
 (cond ((and (is-comb tm) 
             (is-const (get-rator tm))
             (is-eval-fn (get-const-name(get-rator tm)) '(N O T))
             (is-const (get-rand tm))
             (wordconstp (get-const-name(get-rand tm)))
             (is-const (get-rand tm))
             (wordconstp (get-const-name(get-rand tm))))
         (ml-mk_const
          (word-NOT(get-const-name(get-rand tm)))
          (get-type tm)))
       (t tm)))

; (NOT-RULE thm) applies NOT-eval to all subterms of the conclusion of thm
; NOT-CONV is the corresponding formula conversion

(defun NOT-RULE (thm) (map-thm 'NOT-eval thm))
(defun NOT-CONV (fm) (make-conv 'NOT-eval fm))


;                    | "x"        if tm = "(T=>x|y)"
;     COND-eval tm = | "y"        if tm = "(F=>x|y)"
;                    | "z"        if tm = "(t=>z|z)"
;                    | tm         otherwise

(defun COND-eval (tm)
 (cond ((and (is-comb tm) 
             (is-comb (get-rator tm))
             (is-comb (get-rator(get-rator tm)))
             (is-const (get-rator(get-rator(get-rator tm))))
             (eq 
              (get-const-name(get-rator(get-rator(get-rator tm))))
              'COND))
        (let ((test (get-rand(get-rator(get-rator tm))))
              (then-branch (get-rand(get-rator tm)))
              (else-branch (get-rand tm)))
             (cond ((equal test T-olval) then-branch)
                   ((equal test F-olval) else-branch)
                   ((equal then-branch else-branch) then-branch)
                   (t tm))))
       (t tm)))

; (COND-RULE thm) applies COND-eval to all subterms of the conclusion of thm
;  COND-CONV is the corresponding formula conversion

(defun COND-RULE (thm) (map-thm 'COND-eval thm))
(defun COND-CONV (fm) (make-conv 'COND-eval fm))

;               | "x"  if tm = "x Uw FLOATw" or tm = "FLOATw Uw x" or "x Uw x"
;   U-eval tm = |
;               | tm         otherwise

(defun U-eval (tm)
 (cond ((and (is-comb tm) 
             (is-comb (get-rator tm))
             (is-const (get-rator(get-rator tm)))
             (is-eval-fn (get-const-name(get-rator(get-rator tm))) '(U)))
        (let ((left  (get-rand(get-rator tm)))
              (right (get-rand tm)))
             (cond ((and 
                     (is-const left) 
                     (is-eval-fn (get-const-name left) '(F L O A T)))
                    right)
                   ((and 
                     (is-const right) 
                     (is-eval-fn (get-const-name right) '(F L O A T)))
                    left)
                   ((equal left right) left)
                   (t tm))))
       (t tm)))


; (U-RULE thm) applies U-eval to all subterms of the conclusion of thm
; U-CONV is the corresponding formula conversion

(defun U-RULE (thm) (map-thm 'U-eval thm))
(defun U-CONV (fm) (make-conv 'U-eval fm))

;                 | "x"  if tm = "DEST_TRIw(MK_TRIw x)"
;   TRI-eval tm = |
;                 | tm   otherwise

(setq DEST_TRI_l '(D E S T _ T R I))
(setq MK_TRI_l   '(M K _ T R I))

(defun TRI-eval (tm)
 (cond ((and (is-comb tm) 
             (is-const (get-rator tm))
             (is-eval-fn (get-const-name(get-rator tm)) DEST_TRI_l)
             (is-comb (get-rand tm))
             (is-const (get-rator(get-rand tm)))
             (is-eval-fn (get-const-name(get-rator(get-rand tm))) MK_TRI_l))
         (get-rand (get-rand tm)))
        (t tm)))

; (TRI-RULE thm) applies TRI-eval to all subterms of the conclusion of thm
;  TRI-CONV is the corresponding formula conversion

(defun TRI-RULE (thm) (map-thm 'TRI-eval thm))
(defun TRI-CONV (fm) (make-conv 'TRI-eval fm))

; bool-eval does the following simplifications:
; 
;   T /\ x    --->  x
;   F /\ x    --->  F
;   x /\ T    --->  x
;   x /\ F    --->  F
;   T \/  x   --->  T
;   F \/  x   --->  x
;   x \/  T   --->  T
;   x \/  F   --->  x
;   T ==> x   --->  x
;   F ==> x   --->  T
;   x ==> T   --->  T
;     ~ T     --->  F
;     ~ F     --->  T

(eval-when (load)
   (setq AND-tm
      (ml-mk_const '/\\ '(|fun| (|bool|) (|fun| (|bool|) (|bool|)))))
   (setq OR-tm
      (ml-mk_const '\\/ '(|fun| (|bool|) (|fun| (|bool|) (|bool|)))))
   (setq NOT-tm (ml-mk_const '|~|  '(|fun| (|bool|) (|bool|)))))

(defun bool-eval (tm)
 (cond ((and (is-comb tm) 
             (is-const (get-rator tm))
             (eq (get-const-name(get-rator tm)) '|~|))
        (let ((x (get-rand tm)))
             (cond ((equal x T-olval) F-olval)
                   ((equal x F-olval) T-olval)
                   (t tm))))
       ((is-bin-comb tm '/\\)
        (let ((x (get-rand(get-rator tm)))
              (y (get-rand tm)))
             (cond ((equal x T-olval) y)
                   ((equal x F-olval) F-olval)
                   ((equal y T-olval) x)
                   ((equal y F-olval) F-olval)
                   (t tm))))
       ((is-bin-comb tm '\\/)
        (let ((x (get-rand(get-rator tm)))
              (y (get-rand tm)))
             (cond ((equal x T-olval) T-olval)
                   ((equal x F-olval) y)
                   ((equal y T-olval) T-olval)
                   ((equal y F-olval) x)
                   (t tm))))
       ((is-bin-comb tm '|==>|)
        (let ((x (get-rand(get-rator tm)))
              (y (get-rand tm)))
             (cond ((equal x T-olval) y)
                   ((equal x F-olval) T-olval)
                   ((equal y T-olval) T-olval)
                   ((equal y F-olval) (make-comb NOT-tm x '(|bool|)))
                   (t tm))))
       (t tm)))


; (bool-RULE thm) applies bool-eval to all subterms of the conclusion of thm
; bool-CONV is the corresponding formula conversion

(defun bool-RULE (thm) (map-thm 'bool-eval thm))
(defun bool-CONV (fm) (make-conv 'bool-eval fm))

