% Syntactic type for processes with denotational semantics.		%
% 									%
% FILE		  : csp_syntax.ml 					%
% 									%
% READS FILES	  : process.th			          		%
% LOADS LIBRARIES : sets, string		          		%
% WRITES FILES    : csp_syntax.th					%
%									%
% AUTHOR	  : Albert J Camilleri					%
% AFFILIATION     : Hewlett-Packard Laboratories, Bristol		%
% DATE		  : 89.03.15						%
% REVISED	  : 91.10.01						%

load_library `sets`;;
load_library `string`;;

new_theory `csp_syntax`;;               

new_parent `process`;;

new_type_abbrev (`environment`, ":string -> (event + process)");;

let Event = define_type `Event` `Event = econst string | evar string`;;

let Event_INDUCT  = prove_induction_thm Event;;
let Event_ONE_ONE = prove_constructors_one_one Event;;
let Event_DISTINCT = prove_constructors_distinct Event;;

let ES =
    new_recursive_definition
       false
       Event
       `ES`
       "((ES (econst s) (E:environment)) = s) /\
        ((ES (evar s) E) = OUTL (E s))";;

let CSP =
    define_type
       `CSP`
       `CSP = stop alphabet |
              run alphabet |
              var string |
              pref Event CSP |
              Choice string alphabet CSP |
              par CSP CSP |
              after CSP trace |
              mu string alphabet CSP |
              cond Event Event CSP CSP`;;

let Bnd =
    new_definition
       (`Bnd`,
        "Bnd s exp (env: environment) = \s'. (s' = s) => exp | (env s)");;

let TS =
    new_recursive_definition
       false
       CSP
       `TS`
       "((TS (stop A) E) = STOP A) /\
        ((TS (run A) E) = RUN A) /\
        ((TS (var s) E) = OUTR (E s)) /\
        ((TS (pref a P) E) = ((ES a E) --> (TS P E))) /\
        ((TS (Choice s A P) E) =
         (choice A (\x:event. TS P (Bnd s (INL x) E)))) /\
        ((TS (par P Q) E) = (TS P E) PAR (TS Q E)) /\
        ((TS (after P tr) E) = (TS P E) / tr) /\
        ((TS (mu s A P) E) =
         (MU A (\x:process. TS P (Bnd s (INR x) E)))) /\
        ((TS (cond e1 e2 P Q) E) =
         ((ES e1 E = ES e2 E) => TS P E | TS Q E))";;

let CSP_INDUCT = prove_induction_thm CSP;;

close_theory ();;
