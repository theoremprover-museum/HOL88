;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-ol-net.l                                          ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Descrimination nets for rewriting                   ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-franz.l (or f-cl.l), f-constants.l, f-marco.l,    ;;;
;;;                     f-ol-rec.l                                          ;;;
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
   (include "lisp/f-constants")
   (include "lisp/f-macro")
   (include "lisp/f-ol-rec"))


#+franz
(declare
   (localf keylist exec-deferred update-net-fm update-alist
      combine-tips traverse-link))


;;; Discrimination net program like that in
;;;     Charniak, Riesbeck, McDermott.  "Artificial Intelligence Programming",
;;;        Lawrence Erlbaum Associates, Inc., Hillsdale, NJ

;;; Unlike book version, table updating is purely constructive

;;; These networks are indexed by PPLAMBDA terms and formulas, 
;;;    for fast rewriting.
;;; Abstract syntax only is stored, and no types
;;;    thus networks take up less space than the terms themselves
;;; ALL variables are considered pattern variables
;;; If you store "X" using the index p=>r|s, then any conditional 
;;;    will retrieve "X", and possibly other elements
;;; Lookup retrieves all possible matches, and some impossible ones.
;;; Since matching is approximate, stored data should include a proper matching
;;;    function for the term index


;;; a-list nodes -- keys with entries

(eval-when (compile)
   (defmacro get-key (link) `(car ,link))
   (defmacro get-entry (link) `(cdr ,link))
   (defmacro make-link (key entry) `(cons ,key ,entry)))

;;; tips of nets

(eval-when (compile)
   (defmacro get-tiplist (x) `(cdr ,x))
   (defmacro is-tip (x) `(eq (car ,x) '*tip*))
   (defmacro make-tip (x) `(cons '*tip* ,x)))

;;; all the keys of an alist

(defun keylist (alist) (mapcar #'car alist))   ; keylist


;;; apply deferred parts of the formula to the net
;;; if none, enter %elem as a tip node of a net
(defun exec-deferred (net)
   (if %deferred (update-net-fm (pop %deferred) net)
      (make-tip (cons %elem (get-tiplist net))))
   )                              ; exec-deferred

;;; Using a formula (or term) index, add a new element to the network
(defun enter-elem-fm (%elem fm net)
   (let ((%deferred nil))  (update-net-fm fm net))
   )                              ; enter-elem-fm

;;; add the formula (or term) fm to the net, creating a new net.
;;; keep track of deferred parts 
(defun update-net-fm (fm net)
   (let ((class (form-class fm)))
      (let ((child (assq1 class net)))
         (case class
            ((conj disj imp) ; iff deleted [TFM 90.01.20]
               (push (get-right-form fm) %deferred)
               (update-alist net class 
                  (update-net-fm (get-left-form fm) child)))
            ((forall exists)
               (update-alist net class 
                  (update-net-fm (get-quant-body fm) child)))
            (pred
               (let ((pname (get-pred-sym fm)))
                  (let ((pchild (assq1 pname child)))
                     (update-alist net class 
                        (update-alist child pname 
                           (update-net-tm (get-pred-arg fm) pchild))))))
            (t (update-net-tm fm net)))))
   )                              ; update-net-fm



;;; add the formula tm to the net, creating a new net.
;;; build up the continuation 
(defun update-net-tm (tm net)
   (let ((class (term-class tm)))
      (let ((child (assq1 class net)))
         (let ((newchild
                  (case class
                     (var (exec-deferred child))
                     (const
                        (let ((cname (get-const-name tm)))
                           (let ((cchild (assq1 cname child)))
                              (update-alist child cname 
                                 (exec-deferred cchild)))))
                     (comb (push (get-rand tm) %deferred)
                        (update-net-tm (get-rator tm) child))
                     (abs (update-net-tm (get-abs-body tm) child))
                     (t (lcferror 'update-net-tm)))))
            (update-alist net class newchild))))
   )                              ; update-net-tm



;;; update an alist with a new key/entry pair 
;;; does not alter list structure, instead copies when needed
;;; this assumes that there are only a small number of distinct keys
;;; such as conj, disj, imp...
(defun update-alist (alist key entry)
   (if (assq key alist)
      (let ((newrest  (update-alist (cdr alist) key entry)))
         (if (#+franz eq #-franz eql key (get-key (car alist))) newrest
            (cons (car alist) newrest)))
      (cons (make-link key entry) alist))
   )                              ; update-alist


;;; merge two nets into one, sharing whenever possible
(defun ml-merge_nets (net1 net2)
   (cond
      ((null net1) net2)
      ((null net2) net1)
      ((is-tip net1)
         (make-tip (append (get-tiplist net1) (get-tiplist net2))))
      (t (mapcar #'(lambda (key)
               (make-link key (ml-merge_nets (assq1 key net1)
                     (assq1 key net2))))
            (union (keylist net1) (keylist net2)))))
   )                              ; ml-merge_nets



;;; Look up an item in the net, indexed by a term
(defun lookup-elem-tm (net tm)
   (combine-tips (follow-tm tm net)))



;;; Look up an item in the net, indexed by a formula
(defun lookup-elem-fm (net fm)
   (combine-tips (follow-fm fm net)))



;;; Combine results from nondeterministic search
(defun combine-tips (tiplist)
   (if tiplist 
      (append (get-tiplist (car tiplist))
         (combine-tips (cdr tiplist))))
   )                              ; combine-tips



;;; Follow preorder expansion of index formula in the net
;;; Nondeterministic, since matching of terms is.
(defun follow-fm (fm net)
   (if net
      (case (form-class fm)
         (pred (follow-tm (get-pred-arg fm)
               (assq1 (get-pred-sym fm) 
                  (assq1 'pred net))))
         ((conj disj imp) ; iff deleted [TFM 90.01.20]
            (mapcan #'(lambda (link2)  (follow-fm (get-right-form fm) link2))
               (follow-fm (get-left-form fm) (assq1 (get-conn fm) net))))
         ((forall exists)
            (follow-fm (get-quant-body fm) 
               (assq1 (get-quant fm) net)))
         (t (lcferror 'follow-fm))))
   )                              ; follow-fm



;;; Follow preorder expansion of index term in the net
;;; A nondeterministic matcher:
;;;     since pattern variables match anything, returns a list of subnets 
(defun follow-tm (tm net)
   (nconc
      (if net
         (case (term-class tm)
            (var nil)
            (const
               (traverse-link (get-const-name tm) (assq1 'const net)))
            (abs
               (follow-tm (get-abs-body tm) (assq1 'abs net)))
            (comb
               (mapcan #'(lambda (link2)  (follow-tm (get-rand tm) link2))
                  (follow-tm (get-rator tm) (assq1 'comb net))))
            (t (lcferror 'follow-tm))))
      (list (assq1 'var net)))
   )                              ; follow-tm



;;; Follow down one link in the net
;;; This is deterministic but returns a list anyway, for consistency with
;;;     follow-tm and follow-fm
(defun traverse-link (key net)
   (let ((link (assq1 key net)))  (if link (list link)))
   )                              ; traverse-link


;;; ML functions used only to define abstract types 

(dml |merge_nets_rep| 2 ml-merge_nets
   (((* |list|) |#| (* |list|)) -> (* |list|)))

(dml |enter_term_rep| 3 enter-elem-fm
   ((* |#| (|term| |#| (* |list|))) -> (* |list|)))

(dml |lookup_term_rep| 2 lookup-elem-tm (((* |list|) |#| |term|) -> (* |list|)))

(dml |enter_form_rep| 3 enter-elem-fm
   ((* |#| (|form| |#| (* |list|))) -> (* |list|)))

(dml |lookup_form_rep| 2 lookup-elem-fm (((* |list|) |#| |form|) -> (* |list|)))

