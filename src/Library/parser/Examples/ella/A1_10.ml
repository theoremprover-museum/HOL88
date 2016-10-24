
% A1.10 SEQUENCES %
sequence:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`sequence`,expected,WORD);
   
    if WORD = `BEGIN` then
        (let (sequence_BE_0 , result_list , prev, lst) = sequence_BE lst whitespace whitespace result_list FIRST_CHARS CHARS `END` in
         let result_list = push sequence_BE_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `END` WORD lst `sequence` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `sequence` WORD lst expected)
    else
         fail
  ?
    if WORD = `(` then
        (let (sequence_br_0 , result_list , prev, lst) = sequence_br lst whitespace whitespace result_list FIRST_CHARS CHARS `)` in
         let result_list = push sequence_br_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `sequence` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `sequence` WORD lst expected)
    else
         fail
  ? fail;;

sequence_BE:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`sequence_BE`,expected,WORD);
   
    if WORD = `SEQ` then
        (let (poss_seq_step_0 , result_list , prev, lst) = poss_seq_step lst whitespace whitespace result_list FIRST_CHARS CHARS `OUTPUT` in
         let result_list = push poss_seq_step_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `OUTPUT` WORD lst `sequence_BE` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (unit_1 , result_list , prev, lst) =  unit  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
         let tmp_3 = MK_two(`sequence_BEGINEND`,unit_1,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `sequence_BE` prev lst `nil`)
    else
         fail
  ? fail;;

sequence_br:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`sequence_br`,expected,WORD);
   
    if WORD = `SEQ` then
        (let (poss_seq_step_0 , result_list , prev, lst) = poss_seq_step lst whitespace whitespace result_list FIRST_CHARS CHARS `OUTPUT` in
         let result_list = push poss_seq_step_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `OUTPUT` WORD lst `sequence_br` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (unit_1 , result_list , prev, lst) =  unit  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
         let tmp_3 = MK_two(`sequence_brackets`,unit_1,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `sequence_br` prev lst `nil`)
    else
         fail
  ? fail;;

poss_seq_step:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`poss_seq_step`,expected,WORD);
   
    (let (sequencestep_0 , result_list , prev, lst) =  sequencestep  lst whitespace  WORD  result_list FIRST_CHARS CHARS `;` in
     let tmp_1 = MK_one(`sequencestep`,sequencestep_0) in
     let result_list = push tmp_1 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `;` WORD lst `poss_seq_step` in
     let TOKENS = explode WORD in
     let (more_seq_steps_1 , result_list , prev, lst) = more_seq_steps lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push more_seq_steps_1 result_list in
     do_return result_list whitespace `poss_seq_step` prev lst `nil`)
  ?
    (let tmp_0 = MK_zero(`sequencestep`) in
     let result_list = push tmp_0 result_list in
     do_return result_list whitespace `poss_seq_step` WORD lst expected);;

more_seq_steps:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_seq_steps`,expected,WORD);
   
    (let (sequencestep_0 , result_list , prev, lst) =  sequencestep  lst whitespace  WORD  result_list FIRST_CHARS CHARS `;` in
     let tmp_1 = MK_one(`sequencestep`,sequencestep_0) in
     let result_list = push tmp_1 result_list in
     let (result_list,pop_list) = chop_off 2 [] result_list in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let tmp_3 = add_to_list(POP_1,POP_2) in
     let result_list = push tmp_3 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `;` WORD lst `more_seq_steps` in
     let TOKENS = explode WORD in
     let (more_seq_steps_3 , result_list , prev, lst) = more_seq_steps lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push more_seq_steps_3 result_list in
     do_return result_list whitespace `more_seq_steps` prev lst `nil`)
  ?
    (do_return result_list whitespace `more_seq_steps` WORD lst expected);;

sequencestep:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`sequencestep`,expected,WORD);
   
    if WORD = `LET` then
        (let (letitem_0 , result_list , prev, lst) = letitem lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push letitem_0 result_list in
         let (more_letitems_1 , result_list , prev, lst) = more_letitems lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_letitems_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`step_LET`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `sequencestep` prev lst `nil`)
    else
         fail
  ?
    if WORD = `VAR` then
        (let (varitem_0 , result_list , prev, lst) = varitem lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push varitem_0 result_list in
         let (more_varitems_1 , result_list , prev, lst) = more_varitems lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_varitems_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`sequencestep_VAR`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `sequencestep` prev lst `nil`)
    else
         fail
  ?
    if WORD = `STATE` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `VAR` WORD lst `sequencestep` in
         let TOKENS = explode WORD in
         let (statevaritem_0 , result_list , prev, lst) = statevaritem lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
         let result_list = push statevaritem_0 result_list in
         let (more_statevaritems_1 , result_list , prev, lst) = more_statevaritems lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_statevaritems_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`sequencestep_STATEVAR`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `sequencestep` prev lst `nil`)
    else
         fail
  ?
    if WORD = `PVAR` then
        (let (statevaritem_0 , result_list , prev, lst) = statevaritem lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push statevaritem_0 result_list in
         let (more_statevaritems_1 , result_list , prev, lst) = more_statevaritems lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_statevaritems_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`sequencestep_PVAR`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `sequencestep` prev lst `nil`)
    else
         fail
  ?
    if WORD = `PRINT` then
        (let (printitem_0 , result_list , prev, lst) = printitem lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push printitem_0 result_list in
         let (more_printitems_1 , result_list , prev, lst) = more_printitems lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_printitems_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`step_PRINT`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `sequencestep` prev lst `nil`)
    else
         fail
  ?
    if WORD = `FAULT` then
        (let (faultitem_0 , result_list , prev, lst) = faultitem lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push faultitem_0 result_list in
         let (more_faultitems_1 , result_list , prev, lst) = more_faultitems lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_faultitems_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`step_FAULT`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `sequencestep` prev lst `nil`)
    else
         fail
  ?
    (let (declaration_0 , result_list , prev, lst) = declaration lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push declaration_0 result_list in
     do_return result_list whitespace `sequencestep` prev lst `nil`)
  ?
    (let (statement_0 , result_list , prev, lst) = statement lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push statement_0 result_list in
     do_return result_list whitespace `sequencestep` prev lst `nil`);;

varitem:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`varitem`,expected,WORD);
   
    (let (name_0 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `:=` in
     let result_list = push name_0 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `:=` WORD lst `varitem` in
     let TOKENS = explode WORD in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (unit_2 , result_list , prev, lst) =  unit  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_3 = MK_two(`varitem`,POP_1,unit_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `varitem` prev lst `nil`);;

more_varitems:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_varitems`,expected,WORD);
   
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (varitem_1 , result_list , prev, lst) =  varitem  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let tmp_2 = add_to_list(POP_0,varitem_1) in
     let result_list = push tmp_2 result_list in
     let (more_varitems_2 , result_list , prev, lst) = more_varitems lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_varitems_2 result_list in
     do_return result_list whitespace `more_varitems` prev lst `nil`)
  ?
    (do_return result_list whitespace `more_varitems` WORD lst expected);;

statevaritem:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`statevaritem`,expected,WORD);
   
    (let (name_0 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push name_0 result_list in
     let (init_or_other_1 , result_list , prev, lst) = init_or_other lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push init_or_other_1 result_list in
     do_return result_list whitespace `statevaritem` prev lst `nil`);;

init_or_other:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`init_or_other`,expected,WORD);
   
    if WORD = `INIT` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (const1_1 , result_list , prev, lst) =  const1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_two(`statevaritem_INIT`,POP_0,const1_1) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`statevaritem`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `init_or_other` prev lst `nil`)
    else
         fail
  ?
    if WORD = `::=` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (const1_1 , result_list , prev, lst) =  const1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_two(`statevaritem`,POP_0,const1_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `init_or_other` prev lst `nil`)
    else
         fail
  ? fail;;

more_statevaritems:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_statevaritems`,expected,WORD);
   
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (statevaritem_1 , result_list , prev, lst) =  statevaritem  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let tmp_2 = add_to_list(POP_0,statevaritem_1) in
     let result_list = push tmp_2 result_list in
     let (more_statevaritems_2 , result_list , prev, lst) = more_statevaritems lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_statevaritems_2 result_list in
     do_return result_list whitespace `more_statevaritems` prev lst `nil`)
  ?
    (do_return result_list whitespace `more_statevaritems` WORD lst expected);;

statement:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`statement`,expected,WORD);
   
    if WORD = `IF` then
        (let (boolean_0 , result_list , prev, lst) = boolean lst whitespace whitespace result_list FIRST_CHARS CHARS `THEN` in
         let result_list = push boolean_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `THEN` WORD lst `statement` in
         let TOKENS = explode WORD in
         let (statement_1 , result_list , prev, lst) = statement lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
         let result_list = push statement_1 result_list in
         let (poss_ifseq_else_2 , result_list , prev, lst) = poss_ifseq_else lst whitespace prev result_list FIRST_CHARS CHARS `FI` in
         let result_list = push poss_ifseq_else_2 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `FI` WORD lst `statement` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `statement` WORD lst expected)
    else
         fail
  ?
    if WORD = `CASE` then
        (let (unit_0 , result_list , prev, lst) = unit lst whitespace whitespace result_list FIRST_CHARS CHARS `OF` in
         let result_list = push unit_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `OF` WORD lst `statement` in
         let TOKENS = explode WORD in
         let (seqchoices_1 , result_list , prev, lst) = seqchoices lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
         let result_list = push seqchoices_1 result_list in
         let (poss_caseseq_else_2 , result_list , prev, lst) = poss_caseseq_else lst whitespace prev result_list FIRST_CHARS CHARS `ESAC` in
         let result_list = push poss_caseseq_else_2 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `ESAC` WORD lst `statement` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `statement` WORD lst expected)
    else
         fail
  ?
    if WORD = `[` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `INT` WORD lst `statement` in
         let TOKENS = explode WORD in
         let (name_0 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `=` in
         let result_list = push name_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `=` WORD lst `statement` in
         let TOKENS = explode WORD in
         let (int_1 , result_list , prev, lst) = int lst whitespace WORD result_list FIRST_CHARS CHARS `..` in
         let result_list = push int_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `..` WORD lst `statement` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let (int_4 , result_list , prev, lst) =  int  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
         let (statement_5 , result_list , prev, lst) =  statement  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_6 = MK_four(`statement_INT`,POP_2,POP_3,int_4,statement_5) in
         let result_list = push tmp_6 result_list in
         do_return result_list whitespace `statement` prev lst `nil`)
    else
         fail
  ?
    if WORD = `(` then
        (let (statement_0 , result_list , prev, lst) = statement lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push statement_0 result_list in
         let (more_statements_1 , result_list , prev, lst) = more_statements lst whitespace prev result_list FIRST_CHARS CHARS `)` in
         let result_list = push more_statements_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `statement` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`statements`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `statement` WORD lst expected)
    else
         fail
  ?
    (let (varname_0 , result_list , prev, lst) =  varname  lst whitespace  WORD  result_list FIRST_CHARS CHARS `:=` in
     let tmp_1 = MK_one(`varname`,varname_0) in
     let result_list = push tmp_1 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `:=` WORD lst `statement` in
     let TOKENS = explode WORD in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (unit_2 , result_list , prev, lst) =  unit  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_3 = MK_two(`statement_assign`,POP_1,unit_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `statement` prev lst `nil`);;

poss_ifseq_else:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`poss_ifseq_else`,expected,WORD);
   
    if WORD = `ELSE` then
        (let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (statement_2 , result_list , prev, lst) =  statement  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_3 = MK_three(`statement_cond`,POP_0,POP_1,statement_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `poss_ifseq_else` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 2 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let tmp_2 = MK_two(`statement_cond`,POP_0,POP_1) in
     let result_list = push tmp_2 result_list in
     do_return result_list whitespace `poss_ifseq_else` WORD lst expected);;

poss_caseseq_else:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`poss_caseseq_else`,expected,WORD);
   
    if WORD = `ELSE` then
        (let tmp_0 = MK_zero(`statement_ELSEOF`) in
         let result_list = push tmp_0 result_list in
         let (result_list,pop_list) = chop_off 3 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (statement_3 , result_list , prev, lst) =  statement  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_4 = MK_four(`statement_case`,POP_0,POP_1,POP_2,statement_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `poss_caseseq_else` prev lst `nil`)
    else
         fail
  ?
    if WORD = `ELSEOF` then
        (let (seqchoices_0 , result_list , prev, lst) = seqchoices lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push seqchoices_0 result_list in
         let (more_seq_elseofs_1 , result_list , prev, lst) = more_seq_elseofs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_seq_elseofs_1 result_list in
         do_return result_list whitespace `poss_caseseq_else` prev lst `nil`)
    else
         fail
  ?
    (let tmp_0 = MK_zero(`statement_ELSEOF`) in
     let result_list = push tmp_0 result_list in
     let (result_list,pop_list) = chop_off 3 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let tmp_3 = MK_three(`statement_case`,POP_0,POP_1,POP_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `poss_caseseq_else` WORD lst expected);;

more_seq_elseofs:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_seq_elseofs`,expected,WORD);
   
    if WORD = `ELSEOF` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (seqchoices_1 , result_list , prev, lst) =  seqchoices  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,seqchoices_1) in
         let result_list = push tmp_2 result_list in
         let (more_seq_elseofs_2 , result_list , prev, lst) = more_seq_elseofs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_seq_elseofs_2 result_list in
         do_return result_list whitespace `more_seq_elseofs` prev lst `nil`)
    else
         fail
  ?
    if WORD = `ELSE` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let tmp_1 = MK_one(`statement_ELSEOF`,POP_0) in
         let result_list = push tmp_1 result_list in
         let (result_list,pop_list) = chop_off 3 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let (statement_4 , result_list , prev, lst) =  statement  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_5 = MK_four(`statement_case`,POP_1,POP_2,POP_3,statement_4) in
         let result_list = push tmp_5 result_list in
         do_return result_list whitespace `more_seq_elseofs` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_one(`statement_ELSEOF`,POP_0) in
     let result_list = push tmp_1 result_list in
     let (result_list,pop_list) = chop_off 3 [] result_list in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let (POP_3 , pop_list ) = (pop pop_list) in
     let tmp_4 = MK_three(`statement_case`,POP_1,POP_2,POP_3) in
     let result_list = push tmp_4 result_list in
     do_return result_list whitespace `more_seq_elseofs` WORD lst expected);;

more_statements:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_statements`,expected,WORD);
   
    if WORD = `;` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (statement_1 , result_list , prev, lst) =  statement  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,statement_1) in
         let result_list = push tmp_2 result_list in
         let (more_statements_2 , result_list , prev, lst) = more_statements lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_statements_2 result_list in
         do_return result_list whitespace `more_statements` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `more_statements` WORD lst expected);;

seqchoices:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`seqchoices`,expected,WORD);
   
    (let (seqchoice_0 , result_list , prev, lst) = seqchoice lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push seqchoice_0 result_list in
     let (more_seqchoices_1 , result_list , prev, lst) = more_seqchoices lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_seqchoices_1 result_list in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let tmp_3 = MK_one(`seqchoices`,POP_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `seqchoices` prev lst `nil`);;

seqchoice:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`seqchoice`,expected,WORD);
   
    (let (choosers_0 , result_list , prev, lst) = choosers lst whitespace WORD result_list FIRST_CHARS CHARS `:` in
     let result_list = push choosers_0 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `:` WORD lst `seqchoice` in
     let TOKENS = explode WORD in
     let (poss_statement_1 , result_list , prev, lst) = poss_statement lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push poss_statement_1 result_list in
     do_return result_list whitespace `seqchoice` prev lst `nil`);;

poss_statement:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`poss_statement`,expected,WORD);
   
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (statement_1 , result_list , prev, lst) =  statement  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_2 = MK_two(`seqchoice`,POP_0,statement_1) in
     let result_list = push tmp_2 result_list in
     do_return result_list whitespace `poss_statement` prev lst `nil`)
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_one(`seqchoice`,POP_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `poss_statement` WORD lst expected);;

more_seqchoices:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_seqchoices`,expected,WORD);
   
    if WORD = `,` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (seqchoice_1 , result_list , prev, lst) =  seqchoice  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,seqchoice_1) in
         let result_list = push tmp_2 result_list in
         let (more_seqchoices_2 , result_list , prev, lst) = more_seqchoices lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_seqchoices_2 result_list in
         do_return result_list whitespace `more_seqchoices` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `more_seqchoices` WORD lst expected);;

varname:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`varname`,expected,WORD);
   
    (let (name_0 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push name_0 result_list in
     let (rest_of_varname_1 , result_list , prev, lst) = rest_of_varname lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push rest_of_varname_1 result_list in
     do_return result_list whitespace `varname` prev lst `nil`);;

rest_of_varname:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`rest_of_varname`,expected,WORD);
   
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (name_1 , result_list , prev, lst) =  name  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let tmp_2 = MK_two(`varname`,POP_0,name_1) in
     let result_list = push tmp_2 result_list in
     let (rest_of_varname_2 , result_list , prev, lst) = rest_of_varname lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push rest_of_varname_2 result_list in
     do_return result_list whitespace `rest_of_varname` prev lst `nil`)
  ?
    if WORD = `[` then
        (let (var_brackets_0 , result_list , prev, lst) = var_brackets lst whitespace whitespace result_list FIRST_CHARS CHARS `\]` in
         let result_list = push var_brackets_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `rest_of_varname` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `rest_of_varname` WORD lst expected)
    else
         fail
  ?
    (do_return result_list whitespace `rest_of_varname` WORD lst expected);;

var_brackets:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`var_brackets`,expected,WORD);
   
    if WORD = `[` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (unit_1 , result_list , prev, lst) =  unit  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `\]` in
         let tmp_2 = MK_two(`varname_unit`,POP_0,unit_1) in
         let result_list = push tmp_2 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `var_brackets` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `var_brackets` WORD lst expected)
    else
         fail
  ?
    (let (int_0 , result_list , prev, lst) = int lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push int_0 result_list in
     let (var_int_stuff_1 , result_list , prev, lst) = var_int_stuff lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push var_int_stuff_1 result_list in
     do_return result_list whitespace `var_brackets` prev lst `nil`);;

var_int_stuff:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`var_int_stuff`,expected,WORD);
   
    if WORD = `..` then
        (let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (int_2 , result_list , prev, lst) =  int  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_3 = MK_three(`varname_int_range`,POP_0,POP_1,int_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `var_int_stuff` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 2 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let tmp_2 = MK_two(`varname_int`,POP_0,POP_1) in
     let result_list = push tmp_2 result_list in
     do_return result_list whitespace `var_int_stuff` WORD lst expected);;

