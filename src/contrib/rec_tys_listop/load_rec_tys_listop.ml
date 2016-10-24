( print_string `loading the "rec_tys_listop" extended type definition package`;
  print_newline () ;
  let pack_path = (hol_pathname () ^ `/contrib/rec_tys_listop/`) in 
        map (loadf o ($^ pack_path))
            [ `rt_lop_tydefs`
            ; `rt_lop_prim_rec`
            ; `rt_lop_tyfns` ]) ;;
