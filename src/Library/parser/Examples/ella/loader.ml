% Generated parser load file

  First load some basic definitions: %
loadf `/usr/groups/hol/hol_12/Library/parser/general`;;

loadf `PP_printer`;;
loadf `full-ella`;;
loadf `PP_command`;;

% Insert any other files you want loaded here: %
loadf `v1_help`;;

% Now load the declarations: %
loadf `A1_1_decls`;;
loadf `A1_2_decls`;;
loadf `A1_3_decls`;;
loadf `A1_4_decls`;;
loadf `A1_5_decls`;;
loadf `A1_6_decls`;;
loadf `A1_7_decls`;;
loadf `A1_8_decls`;;
loadf `A1_9_decls`;;
loadf `A1_10_decls`;;
loadf `A1_11_decls`;;

% Finally load in the function definitions: %
loadf `A1_1`;;
loadf `A1_2`;;
loadf `A1_3`;;
loadf `A1_4`;;
loadf `A1_5`;;
loadf `A1_6`;;
loadf `A1_7`;;
loadf `A1_8`;;
loadf `A1_9`;;
loadf `A1_10`;;
loadf `A1_11`;;

let SEPS = [(`;`,[]);(`|`,[]);(`:`,[`=`]);(`,`,[]);(`(`,[]);(`)`,[]);
            (`}`,[]);(`{`,[]);(`+`,[]);(`-`,[`>`]);(`*`,[]);(`#`,[]);(`%`,[]);
            (`=`,[]);(`/`,[`/`;`=`]);(`>`,[`=`]);(`<`,[`=`]);(`.`,[`.`]);
            (`[`,[]);(`]`,[]);(`&`,[])];;

let ELLA_text thing = hd (PARSE_text(thing,[],SEPS)) and
    ELLA_file thing = hd (PARSE_file(thing,[],SEPS));;

new_syntax_block(`BEGIN_ELLA`,`END_ELLA`,`ELLA_text`);;
