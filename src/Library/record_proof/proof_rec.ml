%=============================================================================%
%                               HOL 88 Version 2.1                            %
%                                                                             %
%     FILE NAME:        proof_rec.ml                                          %
%                                                                             %
%     DESCRIPTION:      function for recording and transforming proofs        %
%                                                                             %
%     AUTHOR:           Mike Gordon, Wai Wong                                 %
%                                                                             %
%     USES FILES:       hol-syn.ml                                            %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        University of Edinburgh                               %
%     COPYRIGHT:        University of Cambridge                               %
%     COPYRIGHT:        INRIA                                                 %
%                                                                             %
%=============================================================================%

%< --------------------------------------------------------------------------
Proof recording:

When proff recording is enabled,  every inference step performed by
the system will be recorded in a list whose elements are of type step.
The low level functions for managing this feature are in the file
hol-syn.ml. They are reproduced below for easy reference.
 The step list is then processed by the function MakeProof to become a
line list. This list can then be save into a disk file. 

% We hide the flag and the list in local variables. Four functions are
provided for the users to control the recording of proof %

begin_section `record_proof`;;

letref steplist = [] : step list;;
letref record_proof_flag = false;;
letref suspended = false;;

let is_recording_proof (():void) = record_proof_flag;;

let record_proof b = 
    (if b then (steplist := [];()); 
     record_proof_flag := b; ()) ;;

let suspend_recording () = 
    if record_proof_flag
     then (record_proof_flag := false;
       	   suspended := true; ());;

let resume_recording () =
    if (suspended & (not record_proof_flag))
     then (record_proof_flag := true;
    	   suspended := false; ());;

let RecordStep step =
    if  record_proof_flag
     then (steplist := (step.steplist); ());;

let get_steps (():void) = steplist;;

(record_proof,is_recording_proof,RecordStep,get_steps,
 suspend_recording,resume_recording);;
end_section `record_proof`;;

let (record_proof,is_recording_proof,RecordStep,get_steps,
     suspend_recording,resume_recording) = it;;
---------------------------------------------------------------------------->%

%----------------------------------------------------------------------------%
% Proof lines                                                                %
%----------------------------------------------------------------------------%

type justification =
   Hypothesis
 | Assume of term
 | Refl of term
 | Subst of (int#term)list # term # int
 | BetaConv of term
 | Abs of term # int
 | InstType of (type#type)list # int
 | Disch of term # int
 | Mp of int # int
 | MkComb of int # int
 | MkAbs of int
 | Alpha of term # term
 | AddAssum of term # int
 | Sym of int
 | Trans of int # int
 | ImpTrans of int # int
 | ApTerm of term # int
 | ApThm of int # term
 | EqMp of int # int
 | EqImpRuleR of int
 | EqImpRuleL of int
 | Spec of term # int
 | EqtIntro of int
 | Gen of term # int
 | EtaConv of term
 | Ext of int
 | Exists of (term # term) # int
 | Choose of (term # int) # int
 | ImpAntisymRule of int # int
 | MkExists of int
 | Subs of int list # int
 | SubsOccs of (int list # int) list # int
 | SubstConv of (int # term) list # term # term
 | Conj of int # int
 | Conjunct1 of int
 | Conjunct2 of int
 | Disj1 of int # term
 | Disj2 of term # int
 | DisjCases of int # int # int
 | NotIntro of int
 | NotElim of int
 | Contr of term # int
 | Ccontr of term # int
 | Inst of (term # term) list # int
 | StoreDefinition of string # term
 | Definition of string # string
 | DefExistsRule of term
 | NewAxiom of string # term
 | Axiom of string # string
 | Theorem of string # string
 | NewConstant of string # type
 | NewType of int # string
 | NumConv of term;;


type line = Line of (int # thm # justification);;

%-------------------------------------------------------------------%
% MakeProof converts a step list into a line list.		    %
%-------------------------------------------------------------------%
let MakeProof steplst =
 letref steps  = rev steplst
 and    proof     = [] : line list
 and    hyplist   = [] : (int # thm) list
 and    thmlist   = [] : (int # thm) list
 and    linecount = 1
 and    hypcount  = 0
 and    thmcount  = thm_count ()
 in
 let Pos th =
  fst(rev_assoc th thmlist)
  ? fst(rev_assoc th hyplist)
  ? (hypcount := hypcount-1;
     hyplist := (hypcount,th).hyplist;
     hypcount)
 and AddLine just th =
  (proof := Line(linecount,th,just).proof; 
   thmlist := (linecount,th).thmlist;
   linecount := linecount+1)
 and AddHypLines () =
  (proof := rev proof;
   itlist (\(n,th) l. Line(n,th,Hypothesis).l)  hyplist proof)
 in
 (suspend_recording (); 
  while not(null steps)
  do ((case (hd steps) of
        AssumeStep w . 
         AddLine (Assume w) (ASSUME w)
      | ReflStep t . 
         AddLine (Refl t) (REFL t)
      | SubstStep(thvars,w,lhsthm) . 
         AddLine (Subst(map (Pos # I) thvars, w, Pos lhsthm)) 
         (SUBST thvars w lhsthm)
      | BetaConvStep t .
         AddLine (BetaConv t) (BETA_CONV t)
      | AbsStep(x,th) .
         AddLine (Abs(x,Pos th)) (ABS x th)
      | InstTypeStep(inst_tylist,th) . 
         AddLine (InstType(inst_tylist,Pos th)) 
         (INST_TYPE inst_tylist th)
      | DischStep(w,th) . 
         AddLine (Disch(w,Pos th)) (DISCH w th)
      | MpStep(thi,th) .
         AddLine (Mp(Pos thi,Pos th)) (MP thi th)
      | MkCombStep(funth,argth) .
         AddLine (MkComb(Pos funth,Pos argth)) (MK_COMB(funth,argth))
      | MkAbsStep th.
         AddLine (MkAbs(Pos th)) (MK_ABS th)
      | AlphaStep(t1,t2) . 
          AddLine (Alpha(t1,t2)) (ALPHA t1 t2)
      | AddAssumStep(t,th) .
          AddLine (AddAssum(t,Pos th)) (ADD_ASSUM t th)
      | SymStep th .
         AddLine (Sym(Pos th)) (SYM th)
      | TransStep(th1,th2) .
         AddLine (Trans(Pos th1,Pos th2)) (TRANS th1 th2)
      | ImpTransStep(th1,th2) .
         AddLine (ImpTrans(Pos th1,Pos th2)) (IMP_TRANS th1 th2)
      | ApTermStep(tm,th) .
         AddLine (ApTerm(tm,Pos th)) (AP_TERM tm th)
      | ApThmStep(th,tm) .
         AddLine (ApThm(Pos th,tm)) (AP_THM th tm)
      | EqMpStep(th1,th2) .
         AddLine (EqMp(Pos th1,Pos th2)) (EQ_MP th1 th2)
      | EqImpRuleStep th .
         (AddLine (EqImpRuleR(Pos th)) (fst(EQ_IMP_RULE th));
          AddLine (EqImpRuleL(Pos th)) (snd(EQ_IMP_RULE th)))
      | SpecStep(t,th) .
         AddLine (Spec(t,Pos th)) (SPEC t th)
      | EqtIntroStep th .
         AddLine (EqtIntro(Pos th)) (EQT_INTRO th)
      | GenStep(x,th) .
         AddLine (Gen(x,Pos th)) (GEN x th)
      | EtaConvStep tm .
         AddLine (EtaConv tm) (ETA_CONV tm)
      | ExtStep th .
         AddLine (Ext(Pos th)) (EXT th)
      | ExistsStep((w,t),th) .
         AddLine (Exists((w,t),Pos th)) (EXISTS (w,t) th)
      | ChooseStep((v,th1),th2) .
         AddLine (Choose((v,Pos th1),Pos th2)) (CHOOSE (v,th1) th2)
      | ImpAntisymRuleStep(th1,th2) .
         AddLine (ImpAntisymRule(Pos th1,Pos th2)) 
         (IMP_ANTISYM_RULE th1 th2)
      | MkExistsStep bodyth .
         AddLine (MkExists(Pos bodyth)) (MK_EXISTS bodyth)
      | SubsStep(ths,th) .
         AddLine (Subs(map Pos ths,Pos th)) (SUBS ths th)
      | SubsOccsStep(nlths,th) .
         AddLine (SubsOccs(map (I # Pos) nlths,Pos th)) 
         (SUBS_OCCS nlths th)
      | SubstConvStep(thvars,template,tm) .
         AddLine (SubstConv(map (Pos # I) thvars, template, tm)) 
         (SUBST_CONV thvars template tm)
      | ConjStep(th1,th2) .
         AddLine (Conj(Pos th1,Pos th2)) (CONJ th1 th2)
      | Conjunct1Step th .
         AddLine (Conjunct1(Pos th)) (CONJUNCT1 th)
      | Conjunct2Step th .
         AddLine (Conjunct2(Pos th)) (CONJUNCT2 th)
      | Disj1Step(th,w) .
         AddLine (Disj1(Pos th,w)) (DISJ1 th w)
      | Disj2Step(w,th) .
         AddLine (Disj2(w,Pos th)) (DISJ2 w th)
      | DisjCasesStep(dth,ath,bth) .
         AddLine (DisjCases(Pos dth,Pos ath,Pos bth)) 
         (DISJ_CASES dth ath bth)
      | NotIntroStep th .
         AddLine (NotIntro(Pos th)) (NOT_INTRO th)
      | NotElimStep th .
         AddLine (NotElim(Pos th)) (NOT_ELIM th)
      | ContrStep(w,fth) .
         AddLine (Contr(w,Pos fth)) (CONTR w fth)
      | CcontrStep(w,fth) .
         AddLine (Ccontr(w,Pos fth)) (CCONTR w fth)
      | InstStep(inst_list,th) .
         AddLine (Inst(inst_list,Pos th)) (INST inst_list th)
      | StoreDefinitionStep(name,t) .
         AddLine (StoreDefinition(name,t)) (definition(current_theory()) name)
      | DefinitionStep(thy,ax) .
         AddLine (Definition(thy,ax)) (definition thy ax)
      | DefExistsRuleStep tm .
         AddLine (DefExistsRule tm) (DEF_EXISTS_RULE tm)
      | NewAxiomStep(tk,tm) .
         AddLine (NewAxiom(tk,tm)) (new_axiom(tk,tm))
      | AxiomStep(thy,ax) .
         AddLine (Axiom(thy,ax)) (axiom thy ax)
      | TheoremStep(thy,factname) .
         AddLine (Theorem(thy,factname)) (theorem thy factname)
      | NewConstantStep(s,ty) .
         AddLine (NewConstant(s,ty)) (TRUTH)
      | NewTypeStep(arity,tok) .
         AddLine (NewType(arity,tok)) (TRUTH)
      | NumConvStep tm .
        AddLine (NumConv tm) (num_CONV tm));
     steps := tl steps);
  resume_recording(); set_thm_count thmcount;
  AddHypLines());;

% let ShowProof() = MakeProof (get_steps());; %

%-------------------------------------------------------------------%
% The functions below are for outputting proof lines to a disk file %
%-------------------------------------------------------------------%
begin_section `output_proof`;;

let output_strings port sl =   % : (string -> string list -> void) %
   do (map (\s. (write(port,s); write(port, `\L`))) sl);;


let write_pair port (fl,fr) =
    \(l,r). (write(port, `{`);
    	     (fl port l);
    	     (fr port r);
    	     write(port, `}`));;

let write_list port fn l =
    (write(port, `[`);
     (map (fn port) l);
     write(port, `]`));;

letrec write_type port ty =
    if (is_vartype ty)
    then (write (port, (`(v `));
    	  write(port, (dest_vartype ty));
    	  write(port, `)`))
    else (
      let tyop,tyl = dest_type ty in
      if null tyl
      then (write (port, (`(c `));
    	    write (port, tyop);
            write (port, `)`))
      else (write (port, (`(o `));
    	    write (port, tyop);
            write_list port write_type tyl;
            write (port, `)`)));;

letrec write_term port tm =
    let opt_delim s =
        let lastchar s = (last o explode) s in
        if (is_alphanum(lastchar s)) then () else write(port,` `)  in
    if (is_var tm)
    then (let v,ty = dest_var tm in
    	  (write(port, (`(V `));
    	   write(port, (v)); opt_delim v;
    	   write_type port ty;
    	   write(port, `)`)))
    else if (is_const tm)
    then (let v,ty = dest_const tm in
    	  (write(port, (`(C `));
    	   write(port, (v)); opt_delim v;
    	   write_type port ty;
    	   write(port, `)`)))
    else if (is_comb tm)
    then (let ro,ra = dest_comb tm in
    	  (write(port, (`(A `));
           write_term port ro; write_term port ra;
           write(port, `)`)))
    else (let ro,ra = dest_abs tm in
    	  (write(port, (`(L `));
           write_term port ro; write_term port ra;
           write(port, `)`)));;

let write_thm port thm =
    (write_term port (concl thm);
     write(port, `\L`));;

let write_all_thm port thm =
    let asml,con = dest_thm thm in
    (write(port, `(THM `);
     write_list port write_term asml;
     write_term port con;
     write(port, `)\L`));;

let write_int port i =
    (write(port, ` `);
     write(port, (string_of_int i)));;

let write_just port j =
    case j of
    Hypothesis .
    	 write(port, `(Hypothesis)`)
 | (Assume tm) . 
    	(write(port, `(Assume `);
    	 write_term port tm;
    	 write(port, `)`))
 | (Refl tm) .
    	(write(port, `(Refl `);
    	 write_term port tm;
    	 write(port, `)`))
 | (Subst (itl,tm,i)) .
    	(write(port, `(Subst `);
    	 write_list port (\p. write_pair p (write_int,write_term)) itl;
    	 write_term port tm;
    	 write_int port i;
    	 write(port, `)`))
 | (BetaConv tm) .
    	(write(port, `(BetaConv `);
    	 write_term port tm;
    	 write(port, `)`))
 | (Abs (tm,i)) .
    	(write(port, `(Abs `);
    	 write_term port tm;
    	 write_int port i;
    	 write(port, `)`))
 | (InstType (tyl,i)) .
    	(write(port, `(InstType `);
    	 write_list port (\p. write_pair p (write_type,write_type)) tyl;
         write_int port i;
    	 write(port, `)`))
 | (Disch (tm,i)) .
    	(write(port, `(Disch `);
    	 write_term port tm;
    	 write_int port i;
    	 write(port, `)`))
 | (Mp (i1,i2)) .
    	(write(port, `(Mp `);
    	 write_int port i1;
    	 write(port, ` `);
    	 write_int port i2;
    	 write(port, `)`))
 | (MkComb (i1,i2)) .
    	(write(port, `(MkComb `);
    	 write_int port i1;
    	 write(port, ` `);
    	 write_int port i2;
    	 write(port, `)`))
 | (MkAbs i) .
    	(write(port, `(MkAbs `);
    	 write_int port i;
    	 write(port, `)`))
 | (Alpha (tm1,tm2)) .
    	(write(port, `(Alpha `);
    	 write_term port tm1;
    	 write_term port tm2;
    	 write(port, `)`))
 | (AddAssum (tm,i)) .
    	(write(port, `(AddAssum `);
    	 write_term port tm;
    	 write_int port i;
    	 write(port, `)`))
 | (Sym i) .
    	(write(port, `(Sym `);
    	 write_int port i;
    	 write(port, `)`))
 | (Trans (i1,i2)) .
    	(write(port, `(Trans `);
    	 write_int port i1;
    	 write(port, ` `);
    	 write_int port i2;
    	 write(port, `)`))
 | (ImpTrans (i1,i2)) .
    	(write(port, `(ImpTrans `);
    	 write_int port i1;
    	 write(port, ` `);
    	 write_int port i2;
    	 write(port, `)`))
 | (ApTerm (tm,i)) .
    	(write(port, `(ApTerm `);
    	 write_term port tm;
    	 write_int port i;
    	 write(port, `)`))
 | (ApThm (i,tm)) .
    	(write(port, `(ApThm `);
    	 write_int port i;
    	 write_term port tm;
    	 write(port, `)`))
 | (EqMp (i1,i2)) .
    	(write(port, `(EqMp `);
    	 write_int port i1;
    	 write(port, ` `);
    	 write_int port i2;
    	 write(port, `)`))
 | (EqImpRuleR i).
    	(write(port, `(EqImpRuleR `);
    	 write_int port i;
    	 write(port, `)`))
 | (EqImpRuleL i).
    	(write(port, `(EqImpRuleL `);
    	 write_int port i;
    	 write(port, `)`))
 | (Spec (tm,i)) .
    	(write(port, `(Spec `);
    	 write_term port tm;
    	 write_int port i;
    	 write(port, `)`))
 | (EqtIntro i) .
    	(write(port, `(EqtIntro `);
    	 write_int port i;
    	 write(port, `)`))
 | (Gen (tm,i)) .
    	(write(port, `(Gen `);
    	 write_term port tm;
    	 write_int port i;
    	 write(port, `)`))
 | (EtaConv tm) .
    	(write(port, `(EtaConv `);
    	 write_term port tm;
    	 write(port, `)`))
 | (Ext i) . 
    	(write(port, `(Ext `);
    	 write_int port i;
    	 write(port, `)`))
 | (Exists (tm,i)) .
    	(write(port, `(Exists `);
    	 write_pair port (write_term,write_term) tm;
    	 write_int port i;
    	 write(port, `)`))
 | (Choose (tmi,i)) .
    	(write(port, `(Choose `);
    	 write_pair port (write_term,write_int) tmi;
    	 write_int port i;
    	 write(port, `)`))
 | (ImpAntisymRule (i1,i2)) .
    	(write(port, `(ImpAntisymRule `);
    	 write_int port i1;
    	 write(port, ` `);
    	 write_int port i2;
    	 write(port, `)`))
 | (MkExists i) .
    	(write(port, `(MkExists `);
    	 write_int port i;
    	 write(port, `)`))
 | (Subs (il,i)) .
    	(write(port, `(Subs `);
    	 write_list port write_int il;
    	 write_int port i;
    	 write(port, `)`))
 | (SubsOccs (il,i)) . 
    	(write(port, `(SubsOccs `);
    	 write_list port 
    	 (\p (ill,ii). (write(p,`(`); 
            	        write_list p write_int ill;
    	    	    	write_int p ii;
    	    	        write(p,`)`))) il;
    	 write_int port i;
    	 write(port, `)`))
 | (SubstConv (itl, tm1, tm2)) .
    	(write(port, `(SubstConv `);
    	 write_list port (\p. write_pair p (write_int,write_term)) itl;
    	 write_term port tm1;
    	 write_term port tm2;
    	 write(port, `)`))
 | (Conj (i1,i2)) .
    	(write(port, `(Conj `);
    	 write_int port i1;
    	 write(port, ` `);
    	 write_int port i2;
    	 write(port, `)`))
 | (Conjunct1 i) .
    	(write(port, `(Conjunct1 `);
    	 write_int port i;
    	 write(port, `)`))
 | (Conjunct2 i) . 
    	(write(port, `(Conjunct2 `);
    	 write_int port i;
    	 write(port, `)`))
 | (Disj1 (i,tm)) .
    	(write(port, `(Disj1 `);
    	 write_int port i;
    	 write_term port tm;
    	 write(port, `)`))
 | (Disj2 (tm,i)) .
    	(write(port, `(Disj2 `);
    	 write_term port tm;
    	 write_int port i;
    	 write(port, `)`))
 | (DisjCases (i1,i2,i3)) .
    	(write(port, `(DisjCases `);
    	 write_int port i1;
    	 write(port, ` `);
    	 write_int port i2;
    	 write(port, ` `);
    	 write_int port i3;
    	 write(port, `)`))
 | (NotIntro i) .
    	(write(port, `(NotIntro `);
    	 write_int port i;
    	 write(port, `)`))
 | (NotElim i) . 
    	(write(port, `(NotElim `);
    	 write_int port i;
    	 write(port, `)`))
 | (Contr (tm,i)) .
    	(write(port, `(Contr `);
    	 write_term port tm;
    	 write_int port i;
    	 write(port, `)`))
 | (Ccontr (tm,i)) .
    	(write(port, `(Ccontr `);
    	 write_term port tm;
    	 write_int port i;
    	 write(port, `)`))
 | (Inst (ttl,i)) . 
    	(write(port, `(Inst `);
    	 write_list port (\p. write_pair p (write_term,write_term)) ttl;
    	 write_int port i;
    	 write(port, `)`))
 | (StoreDefinition (s,tm)) . 
    	(write(port, (`(StoreDefinition `^s));
    	 write_term port tm;
    	 write(port, `)`))
 | (Definition (s1,s2)) .
    	(write(port, (`(Definition `^s1^` `^s2^`)`)))
 | (DefExistsRule tm) .
    	(write(port, (`(DefExistsRule `));
    	 write_term port tm;
    	 write(port, `)`))
 | (NewAxiom (s,tm)) . 
    	(write(port, (`(NewAxiom `^s));
    	 write_term port tm;
    	 write(port, `)`))
 | (Axiom (s1,s2)) .
    	(write(port, (`(Axiom `^s1^` `^s2^`)`)))
 | (Theorem (s1,s2)) .
    	(write(port, (`(Theorem `^s1^` `^s2^`)`)))
 | (NewConstant (s,ty)) . 
    	(write(port, (`(NewConstant `^s));
    	 write_type port ty;
    	 write(port, `)`))
 | (NewType (i,s)) .
    	(write(port, (`(NewType `));
    	 write_int port i;
    	 write(port, (` `^s^`)`)))
 | (NumConv tm) .
    	(write(port, `(NumConv `);
    	 write_term port tm;
    	 write(port, `)`));;

let write_line port (Line (ct, thm, just)) =
    (write(port, `(LINE `);
     write(port, (string_of_int ct));
     write_just port just;
     write(port,`\L`);
     write_all_thm port thm;
     write(port, `)\L\L`));;

let write_tyconst port (arity,tyname) =
    (write_pair port ((\p s.write(p,s)), write_int) (tyname, arity));;

let write_sig port (cname, cty) =
    (write_pair port ((\p s.write(p,s)), write_type) (cname, cty));;

let write_env ofile =
    let holthy = `HOL` . (ancestors `HOL`) in
    let thisthy = current_theory() in
    let allthy = thisthy . (ancestors thisthy) in
    let ths = subtract allthy holthy in
    let tylst = flat (map types ths)
    and conlst = map dest_const (flat (map constants ths)) in
    (write(ofile, `(ENV `);
     write(ofile, thisthy);
     write_list ofile write_tyconst tylst;
     write_list ofile write_sig conlst;
     write(ofile, `)\L`));;

let write_thm_list port thml = write_list port write_all_thm thml;;

(write_line,write_thm_list,write_env);;
end_section `output_proof`;;
let (write_line,write_thm_list,write_env) = it;;

%-------------------------------------------------------------------%
% The functions below are the user level functions for recording    %
% proofs    	    	    %
%-------------------------------------------------------------------%

begin_section `proof_interface`;;

let format_version = `(VERSION PRF FORMAT 1.0 EXTENDED)\L`;;

let write_proof_add_to =
    let format_name = (explode format_version) in
    let read_line port =
    	letref ls = [] in
        letref c = read port in
    	(if (c = `nil`) then (c := ``; ())
         if not(c = `\L`) loop (ls := (c. ls); c := read port);
    	 (ls := c.ls); 
         rev ls) in
    let check_file fname = 
        let path = search_path() in
    	(set_search_path [``] ; 
         let fname' = find_file fname ? 
            (let ofile = openw fname in
    	     (write(ofile, format_version);
    	      write_env ofile;
    	      close ofile; fname)) in
         let ifile = openi fname' in
         let fformat = read_line ifile in
    	 (set_search_path path;
          (fformat  = format_name))) in
  \file name thms prf.
    if check_file file then
      (let ofile = append_openw file in
       (write(ofile, (`\L(PROOF `^name^`\L`));
        write_thm_list ofile thms;
    	write(ofile, `\L[\L`);
        map (write_line ofile) prf;
        write(ofile, `])\L`);
        close ofile))
    else failwith 
        (`write_proof_add_to: ` ^file ^ ` not in the correct format`);;

let write_proof_to file pname thms prf =
    let ofile = openw file in
    (write(ofile, format_version);
     write_env ofile;
     write(ofile, (`(PROOF `^pname^`\L`));
     write_thm_list ofile thms;
     write(ofile, `\L[\L`);
     map (write_line ofile) (prf);
     write(ofile, `])\L`);
     close ofile);;

letref proof_file_name = ``;;
letref proof_file_port = ``;;
letref proof_name = ``;;
letref proof_count = 0;;
letref current_goals = []:thm list;;

let write_last_proof =
  \name thms.
    (if (proof_file_port = ``) then failwith `no proof file`
     else (
    	write(proof_file_port, (`\L(PROOF `^name^`\L`));
     	write_thm_list proof_file_port thms;
        write(proof_file_port, `\L[\L`);
     	map (write_line proof_file_port) (MakeProof (get_steps()));
     	write(proof_file_port, `])\L`)))
    ?\s failwith (`write_last_proof: `^s);;

let current_proof_file (():void) = proof_file_name;;
let current_proof (():void) = proof_name;;

let close_proof_file (():void) =
    (close proof_file_port;
     proof_file_port := ``;
     let c  = system (`gzip `^ proof_file_name) in
     if not(c = 0) then
       tty_write(`WARNING: cannot compress proof file (gzip error `^
    	    	 (string_of_int c) ^`)`)
     else ();
     proof_file_name := ``; 
     proof_count := 0; ());;

let new_proof_file name = 
    (if not(proof_file_name = ``) then(
    	close_proof_file();
    	failwith `a proof file is already opened`)
     else(
         proof_file_name := name;
    	 proof_count := 0;
         let ofile = openw proof_file_name in
    	     (write(ofile, format_version);
    	      write_env ofile);
         proof_file_port := ofile; ()))
    ?\s failwith (`new_proof_file: `^s);;

let begin_proof name =
    (if not(proof_name = ``) then failwith (`last proof is not saved yet`)
     else (proof_name := name; 
    	proof_count := proof_count + 1;
        current_goals := [];
    	record_proof true; ()))
    ?\s failwith (`begin_proof: `^s);;

let end_proof name =
    (if (proof_name = ``) then ()
     else
      (write_last_proof proof_name current_goals;
       record_proof false;
       proof_name := ``;
       current_goals := []; ()))
    ?\s failwith (`end_proof: `^s);;
     
%-------------------------------------------------------------------%
% The functions below are the user level functions for recording    %
% tactical proofs    	    	    %
%-------------------------------------------------------------------%
let sanitise str =
    let sps = explode `.;,:"!@#$^&*()|\\` in
    let c' = `_` in
    let san c = if (mem c sps) then c' else c in
    letrec sani sl =
    	if (null sl) then []
    	else let h = san (hd sl) in (h . (sani (tl sl))) in
     implode (sani (explode str));;

let TAC_PROOF (gl,tac) =
    (let thm = TAC_PROOF(gl,tac) in
     	(current_goals := (mk_thm gl) . current_goals;
     	 thm));;
     
let PROVE (tm,tac) =
    (let thm = PROVE(tm,tac) in
     (current_goals := (mk_thm([],tm)) . current_goals;
      thm));;

let prove = \(t,tac). TAC_PROOF(([],t), tac);;

let prove_thm (name,tm,tac) =
    (let thm = prove_thm(name,tm,tac) in
     	(current_goals := (mk_thm([],tm)) . current_goals;
         thm));;

(write_proof_add_to, write_proof_to, write_last_proof,
 current_proof, current_proof_file,
 new_proof_file, close_proof_file, begin_proof, end_proof,
 TAC_PROOF, PROVE, prove, prove_thm);;
 
end_section `proof_interface`;;
let (write_proof_add_to, write_proof_to, write_last_proof,
 current_proof, current_proof_file,
 new_proof_file, close_proof_file, begin_proof, end_proof,
 TAC_PROOF, PROVE, prove, prove_thm) = it;;


