% ptree.ml                                                                    %
%-----------------------------------------------------------------------------%


%  Datatype for parse-trees used by pretty-printer.  %

%  A node can have any number of children. Leaf nodes are nodes with no  %
%  children.                                                             %

rectype print_tree = Print_node of string # print_tree list;;


%  Function to extract name of root node of a parse-tree.  %

let print_tree_name pt =

   % : (print_tree -> string) %

   case pt of (Print_node (s,_)) . s;;


%  Function to extract the children of the root node of a parse-tree.  %

let print_tree_children pt =

   % : (print_tree -> print_tree list) %

   case pt of (Print_node (_,l)) . l;;


%-----------------------------------------------------------------------------%
