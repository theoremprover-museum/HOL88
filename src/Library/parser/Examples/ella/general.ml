letref FAIL_LIST = []:(string#string#string) list;;

letref FIRST_CHARS = []:string list;;
letref CHARS = []:string list;;

let pg_failwith symb prdn =
    FAIL_LIST := append FAIL_LIST [(`*`,prdn,symb)]; fail;;

let push item lst = (item . lst);;

let pop lst = 
    if null lst then failwith `can't pop null list`
    else (hd lst,tl lst);;

let write_string str file =
   if file = `nil` then tty_write str else write(file,str);;

let read_char file =
   if file = `nil` then tty_read() else (read file);;

let close_file file =
   if file = `nil` then ()
   else close file;;

let open_file direction filename =
   if filename = `nil` then `nil` 
   else if mem direction [`in` ; `input` ; `i`] then
      openi filename
   else if mem direction [`out`; `output`; `o`] then
      openw filename
   else 
      failwith (concat `can't open ` 
               (concat filename 
               (concat ` in direction ` direction)));;

letrec e_w_s file chr whitespace =
   if mem chr whitespace then e_w_s file (read_char file) whitespace
   else if chr = `nil` then failwith `unexpected eof`
   else chr;;

letrec e_w_s_ok file chr whitespace =
   if mem chr whitespace then e_w_s_ok file (read_char file) whitespace
   else if chr = `nil` then `nil`
   else chr;;

let determine_lst ch follow white =
    if follow = white then
       mem ch white
    else
       not (mem ch follow);;

letrec get_word2 ch lst file white seps =
    if ch = `nil` then
       (lst,`nil`)
    else if can (assoc ch) seps then
       (lst,ch)
    else if mem ch white then
       (lst,e_w_s_ok file (read_char file) white)
    else
       get_word2 (read_char file) (append lst [ch]) file white seps;;

letrec get_word1 ch lst file follow white =
    if ch = `nil` then
       (lst,`nil`)
    else if not (mem ch follow) then
       (lst,e_w_s_ok file ch white)
    else
       get_word1 (read_char file) (append lst [ch]) file follow white;;

let complete_separator thing file white seps =
    if can (assoc thing) seps then
       let follow = snd (assoc thing seps) in
           if null follow then
              (thing,e_w_s_ok file (read_char file) white)
           else
              let (wrd,sep) = get_word1 (read_char file) [thing] file 
                                        follow white in
                  (implode wrd,sep)
    else 
       let (wrd,sep) = get_word2 (read_char file) [thing] file white seps in
           (implode wrd,sep);;

let get_word file white last seps sep =
    if mem last white then
       failwith `Generated Parser Error, please report it.`
    else if not (mem sep white) then
       (last,sep)
    else if last = `nil` then
       (`nil`,`nil`)
    else
       complete_separator last file white seps;;

letrec read_input file lst white seps prev =
   let (WORD,sep) = get_word file white prev seps (hd white) in
   let lst = append lst [WORD] in
       if WORD = `nil` then
          (close_file file; lst)
       else
          read_input file lst white seps sep;;
 

let gnt lst white WORD =
    if WORD = `nil` then
       if null lst then
          (`nil`,[])
       else failwith `Unexpected end of term.`
    else if WORD = white then
       (hd lst,tl lst)
    else
       (WORD,lst);;

let eat_terminal token WORD lst prdn = 
   if WORD = token then
      if WORD = `nil` then
         if null lst then
            (`nil`,[])
         else failwith `Unexpected end of term.`
      else
         (hd lst,tl lst)
   else 
       pg_failwith WORD prdn (concat `expected "`
                             (concat token `".`));;

letrec chop_off ctr pop_list result_list =
   if ctr = 0 then (result_list,pop_list)
   else chop_off (ctr-1) ((hd result_list) .  pop_list) (tl result_list);;

let do_return_1 res_list white prdn thing lst expect =
    if thing = white then
       (FAIL_LIST := append FAIL_LIST [(`<`,prdn,``)];
        (hd res_list, tl res_list, (hd lst), (tl lst)))
    else if thing = expect then
       (FAIL_LIST := append FAIL_LIST [(`<`,prdn,``)];
        (hd res_list, tl res_list, thing, lst))
    else
       (FAIL_LIST := append FAIL_LIST [(`*`,prdn,thing)];
        fail);;

let do_return res_list white prdn prev lst expect =
    if expect = `nil` then
       (FAIL_LIST := append FAIL_LIST [(`<`,prdn,``)];
        (hd res_list, tl res_list, prev, lst))
    else
       do_return_1 res_list white prdn prev lst expect;;

letrec write_tabs tab =
    if tab = 0 then () 
    else (write_string ` ` `nil`;write_tabs (tab-1));;

letrec backtrace lst tab =
    if null lst then
       write_string `\L` `nil`
    else
       let (dir,prdn,symb) = hd lst in
           if dir = `>` then
              (write_tabs (tab+2);
               write_string (`>> `^prdn^`: "`^symb^`"\L`) `nil`;
               backtrace (tl lst) (tab+2))
           else if dir = `<` then
              (write_tabs tab;
               write_string (`<< `^prdn^`\L`) `nil`;
               backtrace (tl lst) (tab-2))
           else
              (write_tabs tab;
               write_string (`** `^prdn^`: "`^symb^`" (FAIL)\L`) `nil`;
               backtrace (tl lst) (tab-2));;

let evaluation_failed lst = 
    write_string `\L\LERROR: unrecognisable input.\L` `nil`;
    write_string `    -- TRACE: \L` `nil`;
    backtrace lst 3;
    FAIL_LIST := [];
    fail;;
  
