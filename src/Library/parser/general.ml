
letref FIRST_CHARS = []:string list
and CHARS = []:string list
and DEBUG = false
and IGNORE = []:(string#string)list
and USEFUL = []:(string#string)list;;

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

letrec get_word2 ch lst file white seps ignore useful =
    if ch = `nil` then
       (lst,`nil`)
    else if can (assoc ch) seps then
       (lst,ch)
    else if can (assoc ch) ignore then
       (lst,ch)
    else if can (assoc ch) useful then
       (lst,ch)
    else if mem ch white then
       (lst,e_w_s_ok file (read_char file) white)
    else
       get_word2 (read_char file) (append lst [ch]) file 
                 white seps ignore useful;;

letrec get_word1 ch lst file follow white =
    if ch = `nil` then
       (lst,`nil`)
    else if not (mem ch follow) then
       (lst,e_w_s_ok file ch white)
    else
       get_word1 (read_char file) (append lst [ch]) file follow white;;

let complete_separator thing file white seps ignore useful =
    if can (assoc thing) seps then
       let follow = snd (assoc thing seps) in
           if null follow then
              (thing,e_w_s_ok file (read_char file) white)
           else
              let (wrd,sep) = get_word1 (read_char file) [thing] file 
                                        follow white in
                  (implode wrd,sep)
    else 
       let (wrd,sep) = get_word2 (read_char file) [thing] file 
                                 white seps ignore useful in
           (implode wrd,sep);;

let get_word file white last seps sep ignore useful =
    if mem last white then
       failwith `Generated Parser Error, please report it.`
    else if not (mem sep white) then
       (last,sep)
    else if last = `nil` then
       (`nil`,`nil`)
    else if can (assoc last) useful then
       (last,read_char file)
    else if can (assoc last) ignore then
       (last,read_char file)
    else
       complete_separator last file white seps ignore useful;;

letrec useful_stuff ch finish file ch_lst =
   if ch = finish then
      (implode ch_lst,finish)
   if ch = `nil` then
      failwith `Unexpected EOF`
   else
      useful_stuff (read_char file) finish file (append ch_lst [ch]);;

letrec ignore_stuff ch finish file white =
    if ch = finish then
       e_w_s_ok file (read_char file) white
    else if ch = `nil` then
       failwith `unexpected EOF`
    else ignore_stuff (read_char file) finish file white;;

letrec read_input file lst white seps prev ignore useful =
   let (WORD,sep) = get_word file white prev seps (hd white) ignore useful in
       if can (assoc WORD) ignore then
          read_input file lst white seps 
                          (ignore_stuff sep (snd (assoc WORD ignore)) 
                                        file white) ignore useful
       else
          let lst = append lst [WORD] in
              if WORD = `nil` then
                 (close_file file; lst)
              else if can (assoc WORD) useful then
                 let block,final = useful_stuff sep (snd (assoc WORD useful)) 
                                                file [] in
                     read_input file (append lst [block;final]) white seps 
                                (e_w_s_ok file (read_char file) white) 
                                ignore useful
              else
                 read_input file lst white seps sep ignore useful;;
 
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
       fail;;

letrec chop_off ctr pop_list result_list =
   if ctr = 0 then (result_list,pop_list)
   else chop_off (ctr-1) ((hd result_list) .  pop_list) (tl result_list);;

let debug_return state prdn =
    if DEBUG then
       write_string (state ^ ` prdn "` ^ prdn ^`".\L`) `nil`
    else
       ();;

let do_return_1 res_list white prdn thing lst expect =
    if thing = white then
       (debug_return `EXITING` prdn;
        (hd res_list, tl res_list, (hd lst), (tl lst)))
    else if thing = expect then
       (debug_return `EXITING` prdn;
        (hd res_list, tl res_list, thing, lst))
    else
       (debug_return `FAILING` prdn;
        fail);;

let do_return res_list white prdn prev lst expect =
    if expect = `nil` then
       (debug_return `EXITING` prdn;
        (hd res_list, tl res_list, prev, lst))
    else
       do_return_1 res_list white prdn prev lst expect;;

let debug_enter(prdn,expect,wrd) =
    if DEBUG then
       write_string (`ENTERING prdn "`^prdn^
                     `": Curr. Token = "`^wrd^
                     `"; Expected = "`^expect^`".\L`) `nil`
    else ();;

let debug_on() = let D = DEBUG in DEBUG := true;D
and debug_off() = let D = DEBUG in DEBUG := false;D;;

