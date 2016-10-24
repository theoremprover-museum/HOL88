% Generated parser load file

  First load some basic definitions: %
loadf `/anfs/bigdisc/jvt/fake12/Library/parser/general`;;

% Insert any other files you want loaded here: %
loadf `/anfs/bigdisc/jvt/fake12/Library/parser/Examples/HOL/term_help`;;

% Now load the declarations: %
loadf `/anfs/bigdisc/jvt/fake12/Library/parser/Examples/HOL/type_decls`;;
loadf `/anfs/bigdisc/jvt/fake12/Library/parser/Examples/HOL/term_decls`;;

% Finally load in the function definitions: %
loadf `/anfs/bigdisc/jvt/fake12/Library/parser/Examples/HOL/type`;;
loadf `/anfs/bigdisc/jvt/fake12/Library/parser/Examples/HOL/term`;;

let SEPS = [(`[`,[]);(`]`,[]);(`(`,[]);(`)`,[]);(`+`,[]);(`*`,[]);
            (`:`,[]);(`=`,[`=`;`>`]);(`\\`,[`/`]);(`/`,[`\\`]);
            (`<`,[`=`]);(`>`,[`=`]);(`-`,[`>`]);(`#`,[]);(`~`,[]);
            (`.`,[]);(`,`,[])];;

let parse thing = preterm_to_term (PARSE_text(thing,[],SEPS));;

set_string_escape 0;;

new_syntax_block(`<<`,`>>`,`parse`);;
