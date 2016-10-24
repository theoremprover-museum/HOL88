% rewrite.ml  

  I got sick and tired of conversion-based rewriting, so I wrote my own. 
  For the application of KB completion, it was quite successful:

      For each test, the first row is the one done with standard HOL tools:
      PURE_REWRITE_RULE and TOP_DEPTH_CONV. The second is done with the new
      rewriting tools. In test1, the third line corresponds to the use of
      the new rewriting tools plus a rewriting lemma cache. The fourth line 
      is the new rewriting tools plus a critical pair cache. The fifth line
      shows how far we have to go; it is the time taken by a naive nonlogical 
      implementation in SML.

          TEST      THEOREMS   RUN TIME    GC TIME     TOTAL TIME
         --------------------------------------------------------
          test1     17436      180.8s      140.2s
                    1731       169.8s      49.1s
                    1636       233.6s      68.8s
                    1720       183.0s      47.1s
                               7s
         --------------------------------------------------------
          test3     44517      437.1s      690.6s
                    3199       387.5s      138.8s
         --------------------------------------------------------
          test4     1070       12.5s       20.6s
                    178        9.4s        0s
         --------------------------------------------------------
          test5a    28591      309.1s      632.9s
                    2653       273.9s      105.7s
         --------------------------------------------------------
          test5b    28779      314.1s      807.4s
                    2686       276.7s      112.7s
         --------------------------------------------------------
          test6     2297       24.5s       64.9s
                    306        15.9s       4.1s
         --------------------------------------------------------
          test12    22972      227.3s      666.7s
                    1752       214.5s      85.0s
         --------------------------------------------------------
          test16    HOL system ran out of space -- crashed
                    13716      2435.5s     1067.9s
         --------------------------------------------------------

The rewriting is parallel-disjoint redex rewriting. Conversion based rewriting
only gets one redex at a time and thus has to maintain a lot of nodes on the
stack, which is my guess why test16 failed using conversion based rewriting.
%
letrec first_success f alist = 
   if (null alist) 
   then failwith `no success`
   else (f (hd alist)) ? first_success f (tl alist);;

letref global_rewrite_list = ([] : (thm#term) list);;

let basic_match ob pat_th = 
   let tm_subst = fst (match (lhs (concl pat_th)) ob)
   and v = genvar (type_of ob)
   in
   let pat_th' = INST tm_subst pat_th
   in
   ( global_rewrite_list := (pat_th',v).(global_rewrite_list);
     v);;

let node_match pats ob = first_success (basic_match ob) pats;;

% Constructs a "disjoint redex"-template, i.e., it finds as
  many redexes as possible that do not interfere with each other.
  The aim is to make each SUBST do as much work as possible.
%
let make_template pats =
   letrec mk_tmp ob =
      (node_match pats ob)
       ? mk_comb (mk_tmp (rator ob), mk_tmp (rand ob))
       ? ob
   in
   mk_tmp;;


% PSUB stands for Parallel Substitute.
%
let PSUB eq_thms ob_thm = 
   global_rewrite_list := [];
   let temp = make_template eq_thms (concl ob_thm)
   in
   SUBST global_rewrite_list temp ob_thm;;


% Loops until no rewrites possible.
%
let PSUB_ALL eq_thms ob_thm =
   letref result = PSUB eq_thms ob_thm
   in
   ( while not (null global_rewrite_list)
     do result := PSUB eq_thms result;
     result);;


let PSUB_CONV eq_thms ob = 
   global_rewrite_list := [];
   let temp = make_template eq_thms ob
   in
   SUBST_CONV global_rewrite_list temp ob;;

let PSUB_ALL_CONV eq_thms ob =
   letref result = PSUB_CONV eq_thms ob
   in
   ( while not (null global_rewrite_list)
     do result := TRANS result (PSUB_CONV eq_thms 
                                         ((snd o dest_eq o concl) result));
     result);;

let RW_LHS_FULLY R th =
   let (l,r) = dest_eq (concl th)
   in
   let l' = PSUB_ALL_CONV R l
   and v = genvar (type_of l)
   in
   SUBST [(l',v)] (mk_eq (v,r)) th;;

let RW_RHS_FULLY R th =
   let (l,r) = dest_eq (concl th)
   in
   let r' = PSUB_ALL_CONV R r
   and v = genvar (type_of r)
   in
   SUBST [(r',v)] (mk_eq (l,v)) th;;


let MATCH_SUBST_TAC rewrites =
  let conv = PSUB_ALL_CONV rewrites
  in
  \(A,t):goal. 
   let th = conv t
   in
   let (),right = dest_eq(concl th)
   in
   if right="T" 
   then ([], \[]. EQ_MP (SYM th) TRUTH)
   else ([A,right], \[th']. EQ_MP (SYM th) th');;


