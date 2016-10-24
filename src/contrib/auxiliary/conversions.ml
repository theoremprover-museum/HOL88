%<We name the theorems needed,
  so compilation will not be confused>%

% LHS_CONV conv "OP t1 t2" applies conv to t1				%
let LHS_CONV = RATOR_CONV o RAND_CONV ;;

% BINDER_CONV conv "B x. tm[x]" applies conv to tm[x]			%
let BINDER_CONV conv =  (RAND_CONV (ABS_CONV conv));;

PRODUCT_FORALL_THM;;

PRODUCT_EXISTS_THM;;

BASE_CHANGE_SURJ_FORALL;;

BASE_CHANGE_ISO_FORALL;;

BASE_CHANGE_ONTO_EXISTS;;

BASE_CHANGE_ISO_EXISTS;;

BASE_CHANGE_EXISTS_UNIQUE;;
        

%<PROD_CONV transforms "!x.P", where x is a product-type,
  into !x1 x2 ....xn.P((x1,x2,.....,xn)/x)>%

let is_product ty = 
       let name,tylist = dest_type ty ? `not_prod`,[ty] in
       name = `prod`;;

letrec dest_prod ty = 
       let name,tylist = dest_type ty ? `not_construct`,[ty] in
       if not ( name = `prod` ) then [ty]
       else (hd tylist).(dest_prod (el 2 tylist));;  

let mk_prod_names x varlist = 
        letrec mk_list n = if n = 0 then []
                           else ((mk_list (n-1))@[n]) 
        in 
        let name,ty = dest_var x
        in 
        let tylist = dest_prod ty 
        in
        let mk_numbered (n,ty) = mk_primed_var(name ^ (string_of_int n),ty)
        in
        let num_ty_list = combine (mk_list(length tylist),tylist)
        in
        if length tylist = 1 then [x]
        else  
          let prelist = map mk_numbered num_ty_list in
          map (variant varlist) prelist;; 

letrec LIST_GEN_ALPHA_CONV tmlist =
         let l = length tmlist in 
            if l = 0 then ALL_CONV
            if l > 0 then ((BINDER_CONV (LIST_GEN_ALPHA_CONV (tl tmlist))) THENC
                            GEN_ALPHA_CONV (hd tmlist))
            else fail;;

let SIMPLE_PROD_CONV thm tm = 
        let derbndr,x,body = ((I # dest_abs) o dest_comb) tm in  
        if is_product (type_of x) then 
             (let tyi = snd(match "x:*1#*2" x) in
              let th2 = INST_TYPE tyi (GEN_ALL thm) in 
              let th3 = SPEC (mk_abs(x,body)) th2 in
              let th4 = (CONV_RULE (LHS_CONV(BINDER_CONV BETA_CONV))) th3 in 
              let th5 = (CONV_RULE (LHS_CONV (GEN_ALPHA_CONV x))) th4 in
              (CONV_RULE (RAND_CONV(BINDER_CONV(BINDER_CONV BETA_CONV)))) th5)
        else ALL_CONV tm;; 

let PROD_CONV tm =
        let derbndr,x,body = ((I # dest_abs) o dest_comb) tm in  
        let tok = fst(dest_const derbndr) in
        let th1 = 
            (if tok = `!` then PRODUCT_FORALL_THM
             if tok = `?` then PRODUCT_EXISTS_THM
             else fail) in
        let prod_vars = mk_prod_names x [] in
        letrec pre_prod_conv trml =
            if ((length trml) = 0) then ALL_CONV
            else ((SIMPLE_PROD_CONV th1) THENC
                  (BINDER_CONV (pre_prod_conv (tl trml)))) in
        let thm' = pre_prod_conv prod_vars tm in
        (CONV_RULE (RAND_CONV (LIST_GEN_ALPHA_CONV prod_vars))) thm';;


%<The following conversion allows for change of base:
  for proving quantified formulas.
  Note that it depends on 5 theorems, which
  first must be proved in theorems.ml>%

let BASE_CHANGE_CONV =
set_fail `BASE_CHANGE_CONV`
(\thm tm.
let derbndr,x,body = ((I # dest_abs) o dest_comb) tm in 
let tok = fst(dest_const derbndr) in
let thmtype,fnc = (((fst o dest_const) # I) o dest_comb o concl) thm in 
if   
     not((mem tok [`!`;`?`;`?!`])) or
     not((mem thmtype [`ONTO`;`ISO`])) or
     (not(thmtype = `ISO`) & (tok = `?!`)) then fail 
else
     let tyi = snd(match "f:*->**" fnc) in
     let quant_ty = el 2 (snd(dest_type (type_of fnc))) in
     let tyi' = snd(match "x:^quant_ty" x) in
     let th1 = 
        (if ((tok = `!`) & (thmtype = `ONTO`)) then
                       BASE_CHANGE_SURJ_FORALL
         if ((tok = `!`) & (thmtype = `ISO`)) then 
                       BASE_CHANGE_ISO_FORALL
         if ((tok = `?`) & (thmtype = `ONTO`)) then
                       BASE_CHANGE_ONTO_EXISTS
         if ((tok = `?`) & (thmtype = `ISO`)) then
                       BASE_CHANGE_ISO_EXISTS
         if (tok = `?!`) then 
                       BASE_CHANGE_EXISTS_UNIQUE
         else fail) in
     let th2 = INST_TYPE tyi th1 in
     let th3 = INST_TYPE tyi' (SPEC fnc th2) in 
     let th4 = SPEC (mk_abs(x,body)) th3 in 
     let th5 = MP th4 (INST_TYPE tyi' thm) in
     let th6 = (CONV_RULE (LHS_CONV(BINDER_CONV BETA_CONV))) th5 in  
     let th7 = (CONV_RULE (LHS_CONV (GEN_ALPHA_CONV x))) th6 in
     (CONV_RULE (RAND_CONV(BINDER_CONV BETA_CONV))) th7);;










       

 






