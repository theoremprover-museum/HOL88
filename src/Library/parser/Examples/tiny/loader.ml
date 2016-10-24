% Generated parser load file

  First load some basic definitions: %
loadf `/usr/groups/hol/hol_12/Library/parser/general`;;

% Insert any other files you want loaded here: %
loadf `tiny_help`;;

% Now load the declarations: %
loadf `tiny_decls`;;

% Finally load in the function definitions: %
loadf `tiny`;;

let SEPS =
 [(`(`,[]);(`)`,[]);(`]`,[]);(`[`,[]);(`{`,[]);(`}`,[]);(`+`,[]);(`-`,[]);
  (`*`,[]);(`;`,[]);(`:`,[`=`]);(`=`,[`=`;`>`]);(`<`,[`=`;`>`]);(`>`,[`=`]);
  (`~`,[]);(`/`,[`\\`]);(`\\`,[`/`])];;

let MK_NICE thing = PARSE_text(thing,[],SEPS);;

