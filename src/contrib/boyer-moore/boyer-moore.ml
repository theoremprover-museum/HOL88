let path = (hol_pathname ()) ^ `/contrib/boyer-moore/`
in  map (\st. loadf (path ^ st))
        [`support`;
         `struct_equal`;
         `shells`;
         `environment`;
         `clausal_form`;
         `waterfall`;
         `rewrite_rules`;
         `definitions`;
         `terms_and_clauses`;
         `equalities`;
         `generalize`;
         `irrelevance`;
         `induction`;
         `main`];;
