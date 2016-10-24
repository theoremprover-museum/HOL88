RRbool_eq [REFL "T";REFL "F"];;
RRbool_eq [REFL "x:bool";REFL "T"];;

RRnot [REFL "T"];;
RRnot [it];;

RRand [REFL "F";REFL "x:bool"];;
RRand [REFL "x:bool";REFL "F"];;
RRand [REFL "T";REFL "x:bool"];;
RRand [REFL "x:bool";REFL "T"];;
RRand [REFL "T";Rnot ["F"]];;

RRor [REFL "F";REFL "x:bool"];;
RRor [REFL "x:bool";REFL "F"];;
RRor [REFL "T";REFL "x:bool"];;
RRor [REFL "x:bool";REFL "T"];;
RRor [REFL "T";RRnot [REFL "F"]];;
RRor [REFL "T";Rnot ["F"]];;

RRcond [Rnot ["F"];Rnot ["F"];REFL "F"];;
RRcond [Rnot ["F"];REFL "x:bool";REFL "T"];;

RRnum_eq [CONJUNCT1 PRE;SYM(SPEC "0" ADD1)];;
RRnum_eq [REFL "2";ISPECL["`b`";"2"] SND];;
RRcond [Rnot["F"];CONJUNCT1 PRE;SYM(SPEC "0" ADD1)];;
RRcond [REFL "x:bool";CONJUNCT1 PRE;SYM(SPEC "0" ADD1)];;
RRnum_eq [REFL "x:num";REFL "0"];;

RRstring_eq [REFL "`b`";REFL "`b`"];;
RRstring_eq [REFL "`a`";REFL "`b`"];;
RRstring_eq [REFL "`a`";REFL "x:string"];;

RRprod_eq [REFL "`a`,0";REFL "`b`,0"];;
RRprod_eq [REFL "`a`,x:*";REFL "`b`,x:*"];;
RRprod_eq [REFL "`b`,x:*";REFL "`b`,y:*"];;
RRprod_eq [REFL "`a`,x:*";REFL "`b`,y:*"];;
RRprod_eq [REFL "`a`,x:*,0";REFL "`a`,y:*,0"];;

RRfst [REFL "`a`,0"];;
RRfst [REFL "x:*,0"];;

RRsnd [REFL "`a`,0"];;
RRsnd [REFL "x:*,0"];;

Rsndsnd ["`a`,0,T"];;
RRsndsnd [REFL "(x:*,0),(1,`b`)"];;

RRlist_eq [REFL "[1;0;2]";REFL "[0;1;2]"];;
RRlist_eq [REFL "[1;x;2]";REFL "[1;x;2]"];;
RRlist_eq [REFL "[0;x;2]";REFL "[1;x;2]"];;
Rlist_eq ["[x;0]";"[y;0]"];;
RRlist_eq [REFL "[x;0]";REFL "[y;0]"];;
RRlist_eq [REFL "[x:*]";REFL "[y:*]"];;
RRlist_eq [REFL "[x:num]";REFL "[y:num]"];;
RRlist_eq [REFL "[1;x]";REFL "[1;y]"];;

Rhd ["[1;2]"];;
RRhd [REFL "[0;1;2]"];;

Rtl ["[1;2]"];;
RRtl [REFL "[0;1;2]"];;

Rlength ["[1;2]"];;
RRlength [REFL "[0;1;2]"];;

Rlappend["CONS [1;2](CONS [3] [])"];;
RRlappend[REFL "CONS [1;2](CONS [3] [])"];;

Rmap Rnot ["$~";"[T;x:bool;F]"];;
RRmap Rnot [REFL "$~";REFL "[T;x:bool;F]"];;

Rxmap2 Ror ["$\/";"[F;T]";"[T;F]"];;
Rxmap2 Rand ["$/\";"[]:bool list";"[]:bool list"];;
RRxmap2 Ror (map REFL ["$\/";"[F;T;F]";"[T;F;F]"]);;

Revery Rnot ["$~";"[F;F]"];;
Revery Rnot ["$~";"[]:bool list"];;
RRevery Rnot (map REFL ["$~";"[F;T;F]"]);;

Revery2 Ror ["$\/";"[F;T]";"[T;F]"];;
Revery2 Rand ["$/\";"[]:bool list";"[]:bool list"];;
RRevery2 Ror (map REFL ["$\/";"[F;T;F]";"[T;F;F]"]);;

Rmem ["0";"[1;2]"];;
RRmem [REFL "2";REFL "[1;2]"];;
RRmem [REFL "2";REFL "[x;2]"];;
RRmem [REFL "1";REFL "[x;2]"];;
RRmem [REFL "y:num";REFL "[x;2]"];;

Rmem1 ["`b`";"[`a`,1;`b`,2]"];;

Rmem2 ["0";"[`a`,1;`b`,2]"];;
Rmem2 ["2";"[`a`,1;`b`,2]"];;
RRmem2 [REFL "2";REFL "[`b`,2]"];;
RRmem2 [REFL "2";REFL "[`a`,1;`b`,2]"];;
RRmem2 [REFL "2";REFL "[a:*,x;b:*,2]"];;
RRmem2 [REFL "1";REFL "[`a`,x;`b`,2]"];;
RRmem2 [REFL "y:num";REFL "[`a`,x;`b`,2]"];;

Rcorr2 ["0";"[`a`,1;`b`,2]"];;
Rcorr2 ["2";"[`a`,1;`b`,2]"];;
RRcorr2 [REFL "2";REFL "[a:*,x;b:*,2]"];;
RRcorr2 [REFL "1";REFL "[`a`,2;`b`,x]"];;
RRcorr2 [REFL "y:num";REFL "[`a`,x;`b`,2]"];;

Rcorr1 ["`b`";"[`a`,1;`b`,2]"];;
Rcorr1 ["`b`";"[`a`,2;`b`,x]"];;
RRcorr1 [REFL "`a`";REFL "[`a`,2;`b`,x]"];;

Rlmem ["[1;0]";"[2;0;1]"];;
RRlmem [REFL "[1;2]";REFL "[x:num]"];;

Rlor ["[F;F;F;T;F]"];;
RRlor [REFL "[F]"];;

Rland ["[F;F;F;T;F]"];;
RRland [REFL "[F]"];;

Rnocontr["[0,`a`;1,`b`;1,`c`]"];;
Rnocontr["[0,`a`;1,`b`;1,`a`]"];;
RRnocontr[REFL "[0,`a`;0,`b`]"];;

Rsubset["{1,2,1}";"{2,4,1}"];;
Rsubset["{0}";"{x:num}"];;
RRsubset[REFL "{0}";REFL "{4,1}"];;

Rset_eq["{1,2,1}";"{2,1}"];;
RRset_eq[REFL "{0}";REFL "{x:num}"];;

Rin["1";"{2,1,4,1}"];;
RRin[REFL "0";REFL "{4,1}"];;

Rdelete["{2,1,4,1}";"1"];;
RRdelete[REFL "{4,1}";REFL "0"];;

Runion["{1,3,1}";"{2,4,1}"];;
Runion["{0}";"{x:num}"];;
RRunion[REFL "{0}";REFL "{4,1}"];;

Rsevery Rnot ["$~";"{F,F}"];;
RRsevery Rnot (map REFL ["$~";"{F,T,F}"]);;

Rlunion["[{2,0};{};{2}]"];;
RRlunion[REFL "[{2,0};{};{2}]"];;

Rcard["{2,1,4,1}"];;
RRcard[REFL "{4,1}"];;

% ------------------------------------------------------ %

RType_eq["Tyop `fun` [Tyop `bool` [];Tyvar `a`]";
         "Tyop `fun` [Tyop `bool` [];Tyvar `a`]"];;
RType_eq["Tyop `fun` [Tyop `bool` [];Tyvar `a`]";
         "Tyop `fun` [Tyop `bool` [];Tyvar `b`]"];;
RType_eq["Tyop `fun` [Tyop `bool` [];Tyop `fun` [Tyvar `a`;Tyvar `b`]]";
         "Tyop `fun` [Tyop `bool` [];Tyvar `a`]"];;
RRType_eq[REFL "Tyvar `b`";REFL "Tyop `fun` [Tyop `bool` [];Tyvar `a`]"];;

RIs_Tyvar ["Tyvar `*`"];;
RIs_Tyvar ["Tyop `x` [Tyop `bool` [];Tyvar `x`]"];;

RIs_Tyop ["Tyvar `*`"];;
RIs_Tyop ["Tyop `x` [Tyop `bool` [];Tyvar `x`]"];;

RTyvar_nam ["Tyvar `*`"];;
RTyvar_nam ["Tyop `x` [Tyop `bool` [];Tyvar `x`]"];;

RTyop_nam ["Tyvar `*`"];;
RTyop_nam ["Tyop `x` [Tyop `bool` [];Tyvar `x`]"];;

RTyop_tyl ["Tyvar `*`"];;
RTyop_tyl ["Tyop `x` [Tyop `bool` [];Tyvar `x`]"];;

RType_OK["[(`fun`,2);(`bool`,0);(`prod`,2);(`ind`,0)]";
         "Tyop `fun`[Tyvar ``;Tyop `prod`[Tyop `bool`[];Tyvar `a`]]"];;
RRType_OK[REFL "[(`fun`,2);(`bool`,0)]";
         REFL "Tyop `fun` [Tyop `bool` [];Tyvar `a`]"];;

RType_replace["[(Tyop `bool` [],`a`);(Tyvar `a`,`b`)]";
         "Tyop `fun`[Tyvar `a`;Tyvar `b`]"];;
RType_replace["[(Tyvar `b`,`a`);(Tyvar `a`,`b`)]";
         "Tyop `fun`[Tyvar `a`;Tyvar `b`]"];;
RType_replace["[(Tyop `bool` [],`a`);(Tyvar `a`,`b`)]";
         "Tyop `fun`[Tyvar `a`;Tyop `prod`[Tyop `bool`[];Tyvar `b`]]"];;
RRType_replace[REFL"[(Tyvar `b`,`a`);(Tyvar `a`,`b`)]";
         REFL"Tyop `fun`[Tyvar `a`;Tyvar `b`]"];;

RType_compat["Tyop `bool` []";"Tyvar `a`"];;
RType_compat["Tyop `bool` []";"Tyop `a` []"];;
RType_compat["Tyop`fun`[Tyop`bool`[];Tyvar`a`]";"Tyop`fun`[Tyvar`a`;Tyvar`b`]"];;
RRType_compat(map REFL ["Tyop `bool` []";"Tyop`a`[]"]);;

RType_instl["Tyop `bool` []";"Tyvar `a`"];;
RType_instlx["Tyvar `a`";"Tyop `bool` []"];;
RType_instl["Tyop `bool` []";"Tyop `a` []"];;
RType_instl["Tyop`fun`[Tyop`bool`[];Tyvar`a`]";"Tyop`fun`[Tyvar`a`;Tyvar`b`]"];;
RRType_instl(map REFL ["Tyop `bool` []";"Tyop`a`[]"]);;


RPterm_eq["Var (`x`,Tyvar `a`)";"Var (`x`,Tyvar `a`)"];;
RPterm_eq["Var (`y`,Tyvar `a`)";"Var (`x`,Tyvar `a`)"];;
RPterm_eq["Var (`x`,Tyvar `a`)";"Var (`x`,Tyvar `b`)"];;
RPterm_eq["Var (`x`,Tyvar `a`)";"Const `x` (Tyop `bool` [])"];;
RPterm_eq["Const `x` (Tyop `bool` [])";"Var (`x`,Tyvar `a`)"];;
RPterm_eq["Lam (`x`,Tyvar `a`) (Var (`x`,Tyvar `a`))";
          "Lam (`x`,Tyvar `a`) (Var (`x`,Tyvar `b`))"];;
RPterm_eq["App (Var(`x`,Tyop `fun` [Tyvar `a`;Tyvar `b`])) (Var (`z`,Tyvar `a`))";
          "Lam (`x`,Tyvar `a`) (Var (`x`,Tyvar `b`))"];;
RPterm_eq["Lam (`x`,Tyvar `a`) (Var (`x`,Tyvar `b`))";
          "App (Var(`x`,Tyop `fun` [Tyvar `a`;Tyvar `b`])) (Var (`z`,Tyvar `a`)) (Tyvar `b`)"];;
RRPterm_eq[REFL "Var (`x`,Tyvar `a`)";REFL "Var (`x`,Tyvar `b`)"];;

RIs_Const ["Const `=` (Tyop`bool`[])"];;
RIs_Const ["Lam(`x`,(Tyop`bool`[]))(Const `=`(Tyop`bool`[]))(Tyop`bool`[])"];;

RIs_Var ["Const `=` (Tyop`bool`[])"];;
RIs_Var ["Lam(`x`,(Tyop`bool`[])) (Const `=` (Tyop`bool`[])) (Tyop`bool`[])"];;

RIs_App ["Const `=` (Tyvar`a`)"];;
RIs_App ["App (Var(`x`,(Tyvar`a`))) (Const `=` (Tyvar`a`)) (Tyvar`a`)"];;

RIs_Lam ["Const `=` (Tyvar`a`)"];;
RIs_Lam ["Lam (`x`,(Tyvar`a`)) (Const `=` (Tyvar`a`)) (Tyvar`a`)"];;

RConst_nam ["Const `=` (Tyvar`a`)"];;
RConst_nam ["Lam (`x`,(Tyvar`a`)) (Const `=` (Tyvar`a`)) (Tyvar`a`)"];;

RConst_ty ["Const `=` (Tyvar`a`)"];;
RConst_ty ["Lam (`x`,(Tyvar`a`)) (Const `=` (Tyvar`a`)) (Tyvar`a`)"];;

RVar_var ["Var (`x`,(Tyvar`a`))"];;
RVar_var ["Lam (`x`,(Tyvar`a`)) (Const `=` (Tyvar`a`)) (Tyvar`a`)"];;

RApp_fun ["Var (`x`,(Tyvar`a`))"];;
RApp_fun ["App (Var (`x`,(Tyvar`a`))) (Const `=` (Tyvar`a`)) (Tyvar`a`)"];;

RApp_arg ["Var (`x`,(Tyvar`a`))"];;
RApp_arg ["App (Var (`x`,(Tyvar`a`))) (Const `=` (Tyvar`a`)) (Tyvar`a`)"];;

RLam_var ["Var (`x`,(Tyvar`a`))"];;
RLam_var ["Lam (`x`,(Tyvar`a`)) (Const `=` (Tyvar`a`)) (Tyvar`a`)"];;

RLam_bod ["Var (`x`,(Tyvar`a`))"];;
RLam_bod ["Lam (`x`,(Tyvar`a`)) (Const `=` (Tyvar`a`)) (Tyvar`a`)"];;

RPtype_of["Const `imp` (Tyop `fun` [Tyop `bool` [];Tyop `fun` [Tyop `bool` [];Tyop `bool` []]])"];;
RPtype_of["Var (`x`,Tyvar `a`)"];;
RRPtype_of[REFL "Var (`x`,Tyvar `a`)"];;

RPboolean [tm_trans "x==>y"];;
RRPboolean [REFL (tm_trans "x==>(y=x)")];;

let Typl = "[(`bool`,0);(`fun`,2)]";;
let Conl = "[(`T`,Tyop `bool` []);
             (`F`,Tyop `bool` []);
             (`=`,^(ty_trans":**->**->bool"));
             (`==>`,^(ty_trans":bool->bool->bool"))]";;

RPwell_typed [Typl;Conl;"Var (`x`,Tyvar `a`)"];;
RPwell_typed[Typl;Conl;"Const `T` (Tyop `bool` [])"];;
RPwell_typed[Typl;Conl;"Const `=` ^(ty_trans":bool->bool->bool")"];;
RPwell_typed[Typl;Conl;tm_trans "(f:*->**)x"];;
RPwell_typed [Typl;Conl;tm_trans "x==>y"];;
RPwell_typed [Typl;Conl;tm_trans "x\/y"];;
RPwell_typed[Typl;Conl;"Const `T`(Tyvar `a`)"];;
RPwell_typed [Typl;Conl;tm_trans "\x:bool.x"];;
RRPwell_typed[REFL Typl;REFL Conl;REFL (tm_trans "(f:*->**)x")];;


RPfree["(`x`,Tyop `bool` [])";tm_trans "x==>y"];;
th_back (RPfree["(`x`,Tyop `bool` [])";tm_trans "x==>y"]);;
RPfree["(`x`,Tyop `bool` [])";tm_trans"\x.x==>y"];;
RPfree["(`x`,Tyop `bool` [])";tm_trans"(\x.x/\y)x"];;
RRPfree[REFL "(`x`,Tyop `bool` [])";REFL(tm_trans "x==>y")];;

RPbound["(`x`,Tyop `bool` [])";tm_trans "x==>y"];;
th_back (RPbound["(`x`,Tyop `bool` [])";tm_trans "x==>y"]);;
RPbound["(`x`,Tyop `bool` [])";tm_trans"\x.x==>y"];;
RPbound["(`x`,Tyop `bool` [])";tm_trans"(\x.x/\y)x"];;
RRPbound[REFL "(`x`,Tyop `bool` [])";REFL(tm_trans "x==>y")];;

th_back (RPoccurs["(`x`,Tyop `bool` [])";tm_trans"(\x.x==>y)z"]);;

RPlnotfree["[(`x`,Tyop `bool` [])]";tm_trans "\y.y==>z"];;

RPlnotbound["[(`x`,Tyop `bool` [])]";tm_trans "\y.y==>z"];;

RPlnotoccurs["[(`x`,Tyop `bool` [])]";tm_trans "\y.y==>z==>T"];;

RPallnotfree["(`x`,Tyop `bool` [])";"{^(tm_trans "\y.y==>z")}"];;
RRPallnotfree[REFL "(`x`,Tyop `bool` [])";REFL "{^(tm_trans "\y.y==>z")}"];;

RPlallnotfree["[(`x`,Tyop `bool` [])]";"{^(tm_trans "\y.y==>z")}"];;
RRPlallnotfree[REFL "[(`x`,Tyop `bool` [])]";REFL "{^(tm_trans "\y.y==>z")}"];;

RPalreplace1
  ["Var (`x`,Tyop `bool` [])"
  ;"[]:((string#Type)#(string#Type))list"
  ;"[]:(Pterm#string#Type)list"
  ;"Var (`x`,Tyop `bool` [])"];;
RPalreplace1["Var (`y`,Tyop `bool` [])"
     ;"[]:((string#Type)#(string#Type))list"
     ;"[]:(Pterm#string#Type)list"
     ;"Var (`x`,Tyop `bool` [])"];;
RPalreplace1[tm_trans "\(x:bool).x"
          ;"[]:((string#Type)#(string#Type))list"
          ;"[(Var(`y`,Tyop `bool` []),`x`,Tyop `bool` [])]"
          ;tm_trans "\(x:bool).x"];;
RPalreplace1[tm_trans "\(y:bool).x:bool"
          ;"[]:((string#Type)#(string#Type))list"
          ;"[(Var(`x`,Tyop `bool` []),`y`,Tyop `bool` [])]"
          ;tm_trans "\(y:bool).y:bool"];;
RPalreplace1[tm_trans "\(z:bool).y==>y"
          ;"[]:((string#Type)#(string#Type))list"
          ;"[(Var(`y`,Tyop `bool` []),`x`,Tyop `bool` [])]"
          ;tm_trans "\(z:bool).x==>y"];;

RPalreplace1[tm_trans "\z.a==>z"
          ;"[]:((string#Type)#(string#Type))list"
        ;"[]:(Pterm#(string#Type))list"
        ;tm_trans "\x:bool.a==>x"];;
RPalreplace1[tm_trans "\z.\z.a==>z"
          ;"[]:((string#Type)#(string#Type))list"
        ;"[]:(Pterm#(string#Type))list"
        ;tm_trans "\x:bool.\y.a==>y"];;
RPalreplace1[tm_trans "\z.\z.z==>z"
          ;"[]:((string#Type)#(string#Type))list"
        ;"[]:(Pterm#(string#Type))list"
        ;tm_trans "\x:bool.\y.x==>y"];;

RPalreplace[tm_trans "\(z:bool).y==>y"
          ;"[(Var(`y`,Tyop `bool` []),`x`,Tyop `bool` [])]"
          ;tm_trans "\(z:bool).x==>y"];;

RPalpha[tm_trans "\z.a==>z"
        ;tm_trans "\x:bool.a==>x"];;
RPalpha[tm_trans "\z.\z.z==>z"
        ;tm_trans "\x.\y.x==>y"];;
RPalpha[tm_trans "\z.\z.z==>a"
        ;tm_trans "\x:bool.\y:bool.y==>a"];;
RPalpha[tm_trans "\z.\z.z==>a"
        ;tm_trans "\x:bool.\y:bool.x==>a"];;

th_back(RPalpha[tm_trans "\x'.\y'.x'==>y'";tm_trans "\x.\y.x==>y"]);;

RPsubst_triples
  ["[Var(`y`,Tyop `bool`[]),Var(`x`,Tyop `bool`[]),`t`,Tyop `bool`[]]"];;
RRPsubst_triples (map REFL
  ["[Var(`y`,Tyop `bool`[]),Var(`x`,Tyop `bool`[]),`t`,Tyop `bool`[]]"]);;

Rlist13 ["[1,T,`a`]"];;
RRlist13 [REFL "[(1,T,`a`);(0,x,y)]"];;

RPsubst [Typl;Conl;"Var(`y`,Tyop `bool`[])"
         ;"[Var(`y`,Tyop `bool`[]),Var(`x`,Tyop `bool`[]),`t`,Tyop `bool`[]]"
         ;"Var(`t`,Tyop `bool`[])"
         ;"Var(`x`,Tyop `bool`[])"];;
RPsubst [Typl;Conl;tm_trans "\z'.x==>(z'==>(y==>z))"
         ;tm_trans "[(y==>z),(x:bool),`t`,Tyop`bool`[]]"
         ;tm_trans "\z.x==>(z==>t)"
         ;tm_trans "\z.x==>(z==>x)"];;
th_back it;;

RPbeta [tm_trans "z==>y"
       ;"`x`,Tyop `bool`[]"
       ;tm_trans "x==>y"
       ;"Var(`z`,Tyop `bool`[])"];;
RPbeta [tm_trans "\y'.y==>y'"
       ;"`x`,Tyop `bool`[]"
       ;tm_trans "\y.x==>y"
       ;"Var(`y`,Tyop `bool`[])"];;
th_back it;;

BETA_CONV "(\x.(\y.x==>(\x.x==>y)z))y";;
th_back (RPbeta [tm_trans "\y'.y==>(\x.x==>y')z"
       ;"`x`,Tyop `bool`[]"
       ;tm_trans "\y.x==>(\x.x==>y)z"
       ;"Var(`y`,Tyop `bool`[])"]);;

RType_occurs["`*`";"Tyvar `*`"];;
RType_occurs["`*`";"Tyop `bool`[]"];;
RType_occurs["`**`";"Tyop `fun` [Tyvar `*`;Tyop `bool`[]]"];;
RRType_occurs[REFL"`*`";REFL"Tyop `fun` [Tyvar `*`;Tyop `bool`[]]"];;

RPty_occurs["`*`";tm_trans"=:**->**->bool"];;
RPty_occurs["`*`";tm_trans"x:bool"];;
RPty_occurs["`*`";tm_trans"\y:bool.(f:*->**)x"];;

RPty_snotoccurs["`*`";"{^(tm_trans"x:bool"),^(tm_trans"x==>y")}"];;
RPty_snotoccurs["`*`";"{^(tm_trans"x:**"),^(tm_trans"\(z:*).x==>y")}"];;
RRPty_snotoccurs[REFL "`*`";
      REFL "{^(tm_trans "\(x:**).x"),^(tm_trans "\x.x==>y")}"];;

RPlty_snotoccurs["[`*`;`a`]";"{^(tm_trans"x:*b"),^(tm_trans"\(z:*).x==>y")}"];;

RPnewfree1["Var(`x`,Tyvar`a`)";"[]:(string#Type)list";"Var(`y`,Tyvar`b`)"];;
RPnewfree1[tm_trans"\x.x==>y";"[]:(string#Type)list";tm_trans"\y.y==>z"];;

RPnewfree[tm_trans "\x.x==>y";tm_trans "\y.y==>x"];;
RPnewfree[tm_trans "x==>y";tm_trans "y==>z"];;
RPnewfree[tm_trans "x==>y";tm_trans "y==>x"];;
RPnewfree[tm_trans "x==>y";tm_trans "y==>y"];;
RPnewfree[tm_trans "\x:bool.(y:bool)";tm_trans(mk_abs("x:*","x:bool"))];;

RPtyinst1[tm_trans"x:bool";"[]:((string#Type)#string#Type)list";
          "[]:((string#Type)#string#Type)list";
          "[Tyop`bool`[],``]";tm_trans"x:*"];;
RPtyinst1[tm_trans"\(x:bool).x:bool";"[]:((string#Type)#string#Type)list";
          "[]:((string#Type)#string#Type)list";
          "[Tyop`bool`[],``]";tm_trans(mk_abs("x:*","x:bool"))];;
RPtyinst1[tm_trans"\(x:bool).x:bool";"[]:(^ty1)list";
          "[]:((string#Type)#string#Type)list";
          "[Tyop`bool`[],``]";tm_trans(mk_abs("x:bool","x:*"))];;
RPtyinst1[tm_trans"\(x:bool).y:bool";"[]:(^ty1)list";
          "[(`y`,Tyop `bool`[]),`x`,Tyop `bool`[]]";
          "[Tyop`bool`[],``]";tm_trans(mk_abs("x:*","x:bool"))];;

RPtyinst["{}:(Pterm)set"
        ;tm_trans"\(x:bool).y:bool"
        ;"[Tyop`bool`[],``]"
        ;tm_trans(mk_abs("x:*","x:bool"))];;
RPtyinst["{}:(Pterm)set"
        ;tm_trans"\(x:bool).x:bool"
        ;"[Tyop`bool`[],``]"
        ;tm_trans(mk_abs("x:*","x:bool"))];;


RPsequent_eq ["Pseq {} (Var(`x`,Tyop`bool`[]))";
              "Pseq {} (Var(`x`,Tyop`bool`[]))"];;
RPsequent_eq ["Pseq {Var(`x`,Tyop`bool`[])} (Var(`x`,Tyop`bool`[]))";
              "Pseq {} (Var(`x`,Tyop`bool`[]))"];;
RRPsequent_eq (map REFL
       ["Pseq {Var(`x`,Tyop`bool`[])} (Var(`x`,Tyop`bool`[]))";
        "Pseq {} (Var(`x`,Tyop`bool`[]))"]);;

RPseq_assum ["Pseq {} (Var(`x`,Tyop`bool`[]))"];;

RPseq_concl ["Pseq {} (Var(`x`,Tyop`bool`[]))"];;

RPEQ[tm_trans"x:*";tm_trans"x:*"];;
RPEQ[tm_trans"x==>y";tm_trans"x==>y"];;

RPIMP[tm_trans"x:bool";tm_trans"y:bool"];;

RIs_EQtm[tm_trans"(x:*)=y"];;
RIs_EQtm [tm_trans "(x:bool)=y"];;

RPseq_boolean ["Pseq {} (Var(`x`,Tyop`bool`[]))"];;
RPseq_boolean ["Pseq {Var(`x`,Tyop`bool`[])} (Var(`x`,Tyop`bool`[]))"];;

RPseq_well_typed[Typl;Conl;"Pseq {} (Var(`x`,Tyop`bool`[]))"];;
RPseq_well_typed [Typl;Conl;
    "Pseq {Var(`x`,Tyop`bool`[])} (Var(`x`,Tyop`bool`[]))"];;

RPASSUME [Typl;Conl;
          "Pseq {Var(`x`,Tyop `bool` [])}(Var(`x`,Tyop `bool` []))";
          "Var(`x`,Tyop `bool` [])"];;
RRPASSUME (map REFL [Typl;Conl;
          "Pseq {Var(`x`,Tyop `bool` [])}(Var(`x`,Tyop `bool` []))";
          "Var(`x`,Tyop `bool` [])"]);;

RPREFL[Typl;Conl;"Pseq {} ^(tm_trans "(x:bool)=x")";tm_trans "x:bool"];;
th_back (RIs_refl [Typl;Conl;tm_trans "(x==>y)=(x==>y)"]);;
RRPREFL(map REFL[Typl;Conl;"Pseq {} ^(tm_trans "(x:bool)=x")";tm_trans "x:bool"]);;

RPBETA_CONV [Typl;Conl;"Pseq {} ^(tm_trans "(\x:bool.x)z=z")";
  tm_trans "(\x:bool.x)z"];;
RPBETA_CONV [Typl;Conl;"Pseq {} ^(tm_trans "(\x:bool.(y:bool))z=y")";
  tm_trans "(\x:bool.(y:bool))z"];;
RPBETA_CONV [Typl;Conl;"Pseq {} ^(tm_trans "(\x:bool.(y:bool))z=z")";
  tm_trans "(\x:bool.(y:bool))z"];;
RPBETA_CONV [Typl;Conl;"Pseq {} ^(tm_trans "(\x:bool.\y.x==>y)y=(\z.y==>z)")";
  tm_trans "(\x:bool.\y.x==>y)y"];;

RPsubst_newlist ["[]:(Psequent#string#Type)list"];;
RPsubst_newlist 
  ["[Pseq {} ^(tm_trans"(x:bool)=y"),`t`,Tyop `bool` []]"];;
RRPsubst_newlist [REFL "[]:(Psequent#string#Type)list"];;

RPSUBST [Typl;Conl;"Pseq {} ^(tm_trans "y==>x")"
        ;"[Pseq {} ^(tm_trans"(x:bool)=y"),`p`,Tyop `bool` []]"
        ;tm_trans "p==>x"
        ;"Pseq {} ^(tm_trans "x==>x")" ];;

RPABS[Typl;Conl;
      "Pseq {} ^(tm_trans "(\x:bool.(y:bool))=(\x.z)")";
      "Var(`x`,Tyop`bool`[])";
      "Pseq {} ^(tm_trans "(y:bool)=z")" ];;
RPABS[Typl;Conl;
      "Pseq {^(tm_trans "(y:bool)=z")} 
            ^(tm_trans "(\x:bool.(y:bool))=(\x.z)")";
      "Var(`x`,Tyop`bool`[])";
      "Pseq {^(tm_trans "(y:bool)=z")} ^(tm_trans "(y:bool)=z")" ];;
RPABS[Typl;
      "Pseq {^(tm_trans "(y:bool)=z")} 
            ^(tm_trans "(\y:bool.(y:bool))=(\y.z)")";
      "Var(`y`,Tyop`bool`[])";
      "Pseq {^(tm_trans "(y:bool)=z")} ^(tm_trans "(y:bool)=z")" ];;

RPINST_TYPE[Typl;
      "Pseq {} ^(tm_trans "(x:bool)=y")";
      "[Tyop`bool`[],``]";
      "Pseq {} ^(tm_trans "(x:*)=y")" ];;
RPINST_TYPE[Typl;
      "Pseq {^(tm_trans "(x:*)=y")} ^(tm_trans "(x:bool)=y")";
      "[Tyop`bool`[],``]";
      "Pseq {^(tm_trans "(x:*)=y")} ^(tm_trans "(x:*)=y")" ];;

RPDISCH[Typl;Conl;"Pseq {} ^(tm_trans "x==>y")"
       ;"Var(`x`,Tyop `bool` [])"
       ;"Pseq {} (Var(`y`,Tyop `bool` []))" ];;
RPDISCH [Typl;Conl;"Pseq {} ^(tm_trans "x==>y==>z")"
        ;"Var(`x`,Tyop `bool` [])"
        ;"Pseq {} ^(tm_trans "y==>z")"];;

RPMP["Pseq {} (Var(`y`,Tyop `bool` []))"
    ;"Pseq {} ^(tm_trans "x==>y")"
    ;"Pseq {} (Var(`x`,Tyop `bool` []))" ];;
RPMP["Pseq {} ^(tm_trans "y==>x")"
    ;"Pseq {} ^(tm_trans "x==>y==>x")"
    ;"Pseq {} (Var(`x`,Tyop `bool` []))" ];;

RInf_concl["AS_inf (Pseq {Var(`x`,Tyop `bool` [])} (Var(`x`,Tyop `bool` [])))
                   (Var(`x`,Tyop `bool` []))"];;
RInf_concl[
  "SU_inf (Pseq {Var(`a`,Tyop`bool`[]),Var(`b`,Tyop`bool`[])}^(tm_trans "(x:bool)==>y"))
  [Pseq {Var(`b`,Tyop`bool`[])} ^(tm_trans"(x:bool)=y"),`p`,Tyop`bool`[]]
  ^(tm_trans"x==>p")
  (Pseq {Var(`a`,Tyop`bool`[])}^(tm_trans "(x:bool)==>x"))"];;

RInf_hyps[
  "SU_inf (Pseq {Var(`a`,Tyop`bool`[]),Var(`b`,Tyop`bool`[])}^(tm_trans "(x:bool)==>y"))
  [Pseq {Var(`b`,Tyop`bool`[])} ^(tm_trans"(x:bool)=y"),`p`,Tyop`bool`[]]
  ^(tm_trans"x==>p")
  (Pseq {Var(`a`,Tyop`bool`[])}^(tm_trans "(x:bool)==>x"))"];;

let Axil = "[]:(Psequent)list";;
ROK_Inf[Typl;Conl;Axil;
        "AS_inf (Pseq {Var(`x`,Tyop `bool` [])} (Var(`x`,Tyop `bool` [])))
                (Var(`x`,Tyop `bool` []))"];;
ROK_Inf[Typl;Conl;Axil;
  "RE_inf (Pseq {} ^(tm_trans "(x:bool)=x")) (Var(`x`,Tyop`bool`[]))"];;
ROK_Inf[Typl;Conl;Axil;
  "BE_inf (Pseq {} ^(tm_trans "(\(x:bool).x)y=y"))
      ^(tm_trans "(\(x:bool).x)y")"];;
ROK_Inf[Typl;Conl;Axil;
 "SU_inf (Pseq {Var(`a`,Tyop`bool`[]),Var(`b`,Tyop`bool`[])}^(tm_trans "(x:bool)==>y"))
         [Pseq {Var(`b`,Tyop`bool`[])} ^(tm_trans"(x:bool)=y"),`p`,Tyop`bool`[]]
         ^(tm_trans"x==>p")
         (Pseq {Var(`a`,Tyop`bool`[])}^(tm_trans "(x:bool)==>x"))"];;
ROK_Inf[Typl;Conl;Axil;
 "AB_inf (Pseq {Var(`a`,Tyop `bool` [])} ^(tm_trans "(\(x:bool).x)=(\x.y)"))
         (Var(`x`,Tyop`bool`[]))
         (Pseq {Var(`a`,Tyop `bool` [])} ^(tm_trans "(x:bool)=y"))"];;
ROK_Inf[Typl;Conl;Axil;
  "IN_inf (Pseq {Var(`a`,Tyop `bool` [])} ^(tm_trans "(x:bool)=x"))
          [Tyop`bool`[],``]
          (Pseq {Var(`a`,Tyop `bool` [])} ^(tm_trans "(x:*)=x"))"];;
ROK_Inf[Typl;Conl;Axil;
  "DI_inf (Pseq {Var(`a`,Tyop `bool`[])} ^(tm_trans "(x:bool)==>y"))
          (Var(`x`,Tyop`bool`[]))
          (Pseq {Var(`a`,Tyop `bool`[]),Var(`x`,Tyop`bool`[])}
                (Var(`y`,Tyop `bool`[])))"];;
ROK_Inf[Typl;Conl;Axil;
  "MP_inf (Pseq {Var(`a`,Tyop`bool`[]),Var(`b`,Tyop`bool`[])}
                (Var(`y`,Tyop`bool`[])))
          (Pseq {Var(`a`,Tyop`bool`[])} ^(tm_trans"x==>y"))
          (Pseq {Var(`b`,Tyop`bool`[])} (Var(`x`,Tyop`bool`[])))"];;

RIs_proof [Typl;Conl;Axil;
  "[RE_inf (Pseq {} ^(tm_trans "(x:bool)=x")) (Var(`x`,Tyop`bool`[]))]"];;

RIs_proof [Typl;Conl;Axil;
  "[DI_inf
        (Pseq {} ^(tm_trans "((y:bool)=y)==>((x:bool)=x)"))
        ^(tm_trans "(y:bool)=y")
        (Pseq {} ^(tm_trans "(x:bool)=x"))
   ;RE_inf (Pseq {} ^(tm_trans "(x:bool)=x")) (Var(`x`,Tyop`bool`[]))]"];;

th_back(RIs_proof [Typl;Conl;Axil;
  "[MP_inf
     (Pseq {^(tm_trans "(y:bool)=y")} ^(tm_trans "(x:bool)=x"))
     (Pseq {} ^(tm_trans "((y:bool)=y)==>((x:bool)=x)"))
     (Pseq {^(tm_trans "(y:bool)=y")} ^(tm_trans "(y:bool)=y"))
   ;AS_inf
     (Pseq {^(tm_trans "(y:bool)=y")} ^(tm_trans "(y:bool)=y"))
     ^(tm_trans "(y:bool)=y")
   ;DI_inf
     (Pseq {} ^(tm_trans "((y:bool)=y)==>((x:bool)=x)"))
     ^(tm_trans "(y:bool)=y")
     (Pseq {} ^(tm_trans "(x:bool)=x"))
   ;RE_inf 
     (Pseq {} ^(tm_trans "(x:bool)=x"))
     (Var(`x`,Tyop`bool`[]))
   ]"] );;

% result:
|- Is_xproof
   [MP_Xinf
    (Xseq {y = y} (x = x))
    (Xseq {} ((y = y) ==> (x = x)))
    (Xseq {y = y} (y = y));
    AS_Xinf (Xseq {y = y} (y = y)) (y = y);
    DI_Xinf (Xseq {} ((y = y) ==> (x = x))) (y = y) (Xseq {} (x = x));
    RE_Xinf (Xseq {} (x = x)) x] =
   T
%
