% Generated parser load file

  First load some basic definitions: %
loadf `/usr/users/jvt/HOL/CHEOPS/Parser/ml/general`;;

% Insert any other files you want loaded here: %
loadf `types_help`;;

% Now load the declarations: %
loadf `types_decls`;;

% Finally load in the function definitions: %
loadf `types`;;

let SEPS = [(`(`,[]);(`)`,[]);(`#`,[]);(`-`,[`>`]);(`+`,[]);(`,`,[])];;

let parse thing = hd (PARSE_text(thing,[],SEPS));;

new_syntax_block(`<<`,`>>`,`parse`);;
