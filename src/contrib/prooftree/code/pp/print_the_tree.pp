
prettyprinter printproof =

rules

'proof'::unexp(*flag,*what) -> [<hov 1,1,0> 'fullgoal'::*what ] ;

'proof'::unexp(*what) -> [<h 0> 'goal'::*what] ;

'proof'::exp(*gl,*tac,**kids) -> [<v 3,0> 'goal'::*gl
					[<h 1>  'ml'::*tac]
					**kids] ;

'proof'::proved(*thrm, *tac) -> [<v 3,0> [<h 1> 'thm'::*thrm]
					[<h 1>  'ml'::*tac]] ;

'proof'::proved(*thrm,*tac,**kids) -> [<v 3,0>
					[<h 1> 'thm'::*thrm]
					[<h 1>  'ml'::*tac]
					**kids] ; 

'finaltac'::unexp(*what) -> [<h 1> "THEN" "----"] ;

'firstfinaltac'::unexp(*what) -> [<h 0> "----"] ;

'firstfinaltac'::exp(*gl,*tac,*kid) ->
	[<v 1,0> 'ml'::*tac <0,0> [<h 1> 'finaltac'::*kid ]] ;


'finaltac'::exp(*gl,*tac,*kid) ->
	[<v 0,0> [<h 1> "THEN" 'ml'::*tac] *kid ] ;


'finaltac'::exp(*gl,*tac,**kids,*kid) ->
	[<v 0,0> [<h 1> "THEN" 'ml'::*tac]
	 "THENL"
          [<h 1> "[" [<v 0,0> **[<h 0> 'firstfinaltac'::**kids ";"]
					'firstfinaltac'::*kid ] "]" ]] ; 

'firstfinaltac'::exp(*gl,*tac,**kids,*kid) ->
	[<v 0,0> 'ml'::*tac
	 "THENL"
          [<h 1> "[" [<v 0,0> **[<h 0> 'firstfinaltac'::**kids ";"]
					'firstfinaltac'::*kid ] "]" ]] ; 

'finaltac'::proved(*gl, *tac) ->
	[<hov 2,1,0> "THEN" 'ml'::*tac ] ;

'finaltac'::proved(*gl, *tac, *onechild) ->
	[<v 0,0> [<h 1> "THEN" 'ml'::*tac] *onechild ] ;

'finaltac'::proved(*gl,*tac,**kids,*kid) ->
	[<v 0,0> [<h 1> "THEN" 'ml'::*tac]
	 "THENL"
          [<h 1> "[" [<v 0,0> **[<h 0> 'firstfinaltac'::**kids ";"]
					'firstfinaltac'::*kid ] "]" ]] ; 

'firstfinaltac'::proved(*gl, *tac) ->
	[<hov 2,1,0> 'ml'::*tac ] ;

'firstfinaltac'::proved(*gl, *tac, *onechild) ->
	[<v 0,0> 'ml'::*tac [<h 1> 'finaltac'::*onechild] ] ;

'firstfinaltac'::proved(*gl,*tac,**kids,*kid) ->
	[<v 0,0> 'ml'::*tac
	 "THENL"
          [<h 1> "[" [<v 0,0> **[<h 0> **kids ";"] *kid ] "]" ]] ; 

end rules

end prettyprinter



