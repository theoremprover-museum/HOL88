
%------------------------------------------------------------------%
%                                                                  %
%     lisp_pt.ml          - functions to create a print tree       %
%                           structure from lisp parse tree         %
%                                                                  %
%                 richard boulton, for the prooftree library       %
%                                                                  %
%------------------------------------------------------------------%


lisp `
(defmacro dml (ml-fn n lisp-fn mty)
   \`(declare-ml-fun (quote ,ml-fn) (quote ,n) (quote ,lisp-fn) (quote ,mty)))
`;;


lisp `
(defun ml-is_ml_curried_infix (x)
 (and (get x 'ml2)
      (memq (car (get x 'ml2))
            '(mlcinf-rtn))))
`;;


lisp `
(dml |is_ml_curried_infix| 1 ml-is_ml_curried_infix (|string| -> |bool|))
`;;


lisp `
(defun ml-is_ml_paired_infix (x)
 (and (get x 'ml2)
      (memq (car (get x 'ml2))
            '(mlinf-rtn))))
`;;


lisp `
(dml |is_ml_paired_infix| 1 ml-is_ml_paired_infix (|string| -> |bool|))
`;;


lisp `
(defun ml-wrap_pairs (s)
   (cond ((atom s) s)
         ((and (atom (cdr s)) (not (null (cdr s))))
             (cons (list 'PAIR (ml-wrap_pairs (car s)) (cdr s)) nil))
         (t (cons (ml-wrap_pairs (car s)) (ml-wrap_pairs (cdr s))))))
`;;
 

lisp `
(defun ml-lisp_to_print_tree (s)
   (let ((ws (ml-wrap_pairs s)))
   (cond ((atom ws) \`(|Print_node| ,ws))
         ((eq (car ws) 'PAIR)
             (cons '|Print_node|
                (cons 'PAIR
                   (mapcar #'ml-lisp_to_print_tree (cdr ws)))))
         (t (cons '|Print_node|
               (cons 'LIST
                  (mapcar #'ml-lisp_to_print_tree ws)))))))
`;;


lisp `
(defun ml-get_last_parse_tree (s) (ml-lisp_to_print_tree %pt))
`;;


lisp `
(dml |get_last_parse_tree| 1 ml-get_last_parse_tree (|void| -> |print_tree|))
`;;


let get_last_parse_tree = get_last_parse_tree : void -> print_tree;;

lisp `
(defun ml-if_franz (s) #+franz t #-franz nil)
` ;;

lisp `
(dml |if_franz| 1 ml-if_franz (|void| -> |bool|))
` ;;

let first_arg pt =
   case pt
   of (Print_node (`LIST`,ptl)) . ((hd o tl o tl) ptl)
    | (_) . failwith `first_arg`;;

%
let print_lisp_pt x =
   pretty_print 79 0 lisp_tree_rules_fun `` []
      (first_arg (get_last_parse_tree ()));;
%

letrec transform_pt pt =
   case pt
   of (Print_node (`LIST`,((Print_node (op,[])).args))) .
         (Print_node (op,(map transform_pt args)))
    | (Print_node (op,ptl)) . (Print_node (op,map transform_pt ptl))
    | (_) . pt;;


letrec transform_once pt =
   case pt
   of (Print_node (`once`,((Print_node (op,[])).ptl))) .
         (Print_node (`once`,[transform_once (Print_node (op,ptl))]))
    | (Print_node (`once`,(pt1.(Print_node (op,[])).ptl))) .
         (Print_node
             (`once`,
              ((transform_once pt1).[transform_once (Print_node (op,ptl))])))
    | (Print_node (op,ptl)) . (Print_node (op,map transform_once ptl))
    | (_) . pt;;


letrec transform_quot pt =
   case pt
   of (Print_node (op,ptl)) .
         (let op' = case op
                    of `MK=CONST`   . `CONST`
                     | `MK=VAR`     . `VAR`
                     | `MK=COMB`    . `COMB`
                     | `MK=ABS`     . `ABS`
                     | `MK=TYPE`    . `OP`
		     | `MK=LIST`    . `LIST`
                     | `MK=VARTYPE` . `VAR`
		     | `MK=APPN`    . `APPN`
                     | `mk-quot`    . `term`
                     | `mk-tyquot`  . `type`
                     | (_)          . op
          in  Print_node (op',map transform_quot ptl));;


letrec upper_case pt =
   case pt
   of (Print_node (op,ptl)) .
         (let op' = case op
                    of `mk-empty`   . `MK-EMPTY`
                     | `mk-boolconst` . `MK-BOOLCONST`
                     | `mk-intconst` . `MK-INTCONST`
                     | `mk-tokconst` . `MK-TOKCONST`
                     | `mk-var` . `MK-VAR`
		     | `mk-con` . `MK-CON`
                     | `mk-con0` . `MK-CON0`
		     | `mk-unop` . `MK-UNOP`
                     | `mk-binop` . `MK-BINOP`
                     | `mk-appn` . `MK-APPN`
                     | `mk-list` . `MK-LIST`
                     | `mk-dupl` . `MK-DUPL`
                     | `mk-test` . `MK-TEST`
                     | `mk-letrec` . `MK-LETREC`
                     | `mk-let` . `MK-LET`
                     | `mk-in` . `MK-IN`
                     | (_)          . op
          in  Print_node (op',map upper_case ptl));;

