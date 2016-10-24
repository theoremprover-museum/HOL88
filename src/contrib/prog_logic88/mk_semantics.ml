
new_theory `semantics`;;


% Needed for HOL88 %

load_library `string`;;

new_type_abbrev(`state`, ":string -> num");;

new_type_abbrev(`command`, ":state#state->bool");;

% A deterministic command is one that is single values 
  (i.e. a partial function).
%

new_definition
 (`DET`,
  "DET(c:command) = !s s1 s2. c(s,s1) /\ c(s,s2) ==> (s1=s2)");;

% Skip and Abort commands %

new_definition
 (`MK_SKIP`,
  "MK_SKIP (s:state,s') = (s=s')");;

new_definition
 (`MK_ABORT`,
  "MK_ABORT (s:state,s':state) = F");;

% MK_ASSIGN : tok # (state -> num) -> command

     MK_ASSIGN (x,f) (s,s')  =  (s' = s[f s/x])
%

% BND : num -> tok -> state -> state

     BND n x s = s[n/x]
%

new_definition
 (`BND`,
  "BND n x (s:state)  =  \z. ((z=x) => n | s z)");;

new_definition
 (`MK_ASSIGN`,
  "MK_ASSIGN (x,f) (s:state,s')  =  (s' = BND (f s) x s)");;

% MK_IF1 : (state->bool) # command -> command

     MK_IF1 (p,c) (s,s')  =  (p s => c(s,s') | (s=s'))
%

new_definition
 (`MK_IF1`,
  "MK_IF1(p,c) (s:state,s')  =  (p s => c(s,s') | (s=s'))");;

% MK_IF2 : (state->bool) # command # command  -> command

     MK_IF2 (p,c1,c2) (s,s')  =  (p s => c1(s,s') | c2(s,s'))
%

new_definition
 (`MK_IF2`,
  "MK_IF2 (p,c1,c2) (s:state,s':state) :bool  =
    (p s => c1(s,s') | c2(s,s'))");;

% MK_SEQ : command # command -> command

     MK_SEQ (c1,c2) (s,s')  =  ?s''. c1(s,s'') /\ c2(s'',s')
%

new_definition
 (`MK_SEQ`,
  "MK_SEQ (c1,c2) (s:state,s':state)  = 
    ?s'':state. c1(s,s'') /\ c2(s'',s')");;

% MK_SEQL : command list -> command

     MK_SEQL[c1;c2; ... ;cn]  =  
      MK_SEQ(c1,MK_SEQ(c2, ... ,(MK_SEQ(c[n-1],cn)) ... )
%

new_list_rec_definition
 (`MK_SEQL`,
  "(MK_SEQL []           =  \(s,s').(s=s')) /\
   (MK_SEQL (CONS c cl)  =  MK_SEQ(c, MK_SEQL cl))");;

% MK_FINITE_WHILE : num -> (state->bool) # command -> command

     MK_FINITE_WHILE 0 (p,c) (s,s')        =  F

     MK_FINITE_WHILE (SUC n) (p,c) (s,s')  =  
      MK_IF1(p, MK_SEQ(c, MK_FINITE_WHILE n (p,c)))
%

new_prim_rec_definition
 (`MK_FINITE_WHILE`,
  "(MK_FINITE_WHILE 0       = \(p,c) (s,s'). F) /\
   (MK_FINITE_WHILE (SUC n) = \(p,c).
      MK_IF1(p, MK_SEQ(c, MK_FINITE_WHILE n (p,c))))");;

new_definition
 (`MK_WHILE`,
  "MK_WHILE (p,c) (s,s') = ?n. MK_FINITE_WHILE n (p,c) (s,s')");;

% Version using fixedpoints:

     MK_WHILE : (state->bool) # command -> command

     MK_WHILE (p,c) (s,s')  =  MK_IF1(p, MK_SEQ(c, MK_WHILE(p,c)))

     new_definition
      (`MK_WHILE`,
       "MK_WHILE (p,c)  =  FIX(\f. MK_IF1(p, MK_SEQ(c, f)))");;
%

% {p}c{q} is represented by MK_SPEC(p,c,q) %

new_definition
 (`MK_SPEC`,
  "MK_SPEC(p,c,q) = !(s1 s2:state). p s1 /\ c(s1,s2) ==> q s2");;

% An assertion, invariant or variant in a program is represented as 
  a partial identity relation. This meaning is not currently used.
%

new_definition
 (`MK_ASSERT`,
  "MK_ASSERT (p:state->bool) (s1,s2) = p s1 /\ (s1 = s2)");;

new_definition
 (`MK_INVARIANT`,
  "MK_INVARIANT (p:state->bool) (s1,s2) = p s1 /\ (s1 = s2)");;

new_definition
 (`MK_VARIANT`,
  "MK_VARIANT (p:state->num) (s1,s2) = (p s1 > p s2) /\ (s1 = s2)");;

close_theory();;


