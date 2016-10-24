
prettyprinter printgoal =

rules

'goal'::goal(*topterm) -> [<h 0> 'term'::*topterm] ;

'goal'::goal(*topterm, **asl) -> [<v 6,0> 'term'::*topterm
				[<h 0> "[" 'dotted'::**asl "]" ]] ;

'fullgoal'::goal(*topterm, **asl) -> [<v 6,0> 'term'::*topterm
				**[<h 0> "[" 'term'::**asl "]" ]] ;

'dotted'::term(*term) -> [<h 0> "."] ;

end rules

end prettyprinter

