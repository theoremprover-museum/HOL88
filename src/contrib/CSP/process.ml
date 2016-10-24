load_library `sets`;;
load_library `string`;;

new_theory `process`;;

map new_parent [`prefix`; `run`; `choice`; `parallel`; `after`; `mu`];;

close_theory ();;
