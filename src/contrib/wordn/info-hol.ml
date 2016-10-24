RE: n-bit word package for HOL.
===============================

As some of you know, there has been a prototype n-bit word package around
for several years now (it exists in several versions).  This is intended
as a direct replacement for the old (axiomatized) :wordn types, which are
presently resident in the eval library.

Last summer, Graham Birtwistle and I did some work on the new package, in
order to prepare a polished version for the library.  The following script
shows the current status of the work.  Note that the programs illustrated
below are ready to release; they are optimized and of "production quality".
The only thing that may change will be some of their names.

The main function in the package is 

     define_wordn_type : (string -> int -> thm)

This takes a name under which the resulting definition is stored and
the width of the wordn type to be defined. It works as follows:

     #let word4 = define_wordn_type `word4` 4;;
     word4 = 
     |- (!w. WORD4(BITS4 w) = w) /\
        (!l. (LENGTH l = 4) = (BITS4(WORD4 l) = l))

This automatically defines the type :word4 and the constants:

     BITS4 : word4 -> (bool)list
     WORD4 : (bool)list -> word4

with the property shown above. All further reasoning about :word4
can proceed based only on this theorem.

There is then a collection of functions for proving that the constants
BITSn and WORDn and one-to-one and onto, in an appropriate sense.  These
work as follows:

     #prove_BITS_one_one word4;;
     |- !w' w. (BITS4 w = BITS4 w') ==> (w = w')

     #prove_BITS_onto word4;;
     |- !l. (LENGTH l = 4) ==> (?w. BITS4 w = l)

     #prove_WORD_one_one word4;;
     |- !l l'.
        (LENGTH l = 4) /\ (LENGTH l' = 4) ==>
        (WORD4 l = WORD4 l') ==>
        (l = l')

     #prove_WORD_onto word4;;
     |- !w. ?l. (LENGTH l = 4) /\ (WORD4 l = w)

A futher theorem is that BITSn gives you a list of length n:

     #prove_LENGTH_BITS_thm word4;;
     |- !w. LENGTH(BITS4 w) = 4

A slightly less trivial proof is that you can (uniquely) define a function
over :wordn by defining it in terms of the n bits that are the components 
of any n-bit word:

     #let fndef = prove_function_defn_thm word4;;
     fndef = 
     |- !f. ?! fn. !b0 b1 b2 b3. fn(WORD4[b0;b1;b2;b3]) = f b0 b1 b2 b3

A degenerate `induction' theorem over :wordn also follows:

     #let ind = prove_wordn_induction_thm fndef;;
     ind = |- !P. (!b0 b1 b2 b3. P(WORD4[b0;b1;b2;b3])) ==> (!w. P w)

And so does a theorem for doing case analysis on the bits:

     #let cases = prove_wordn_cases_thm ind;;
     cases = |- !w. ?b0 b1 b2 b3. w = WORD4[b0;b1;b2;b3]

For n-bit words denoted by constants, we have a wordn_CONV (analogous 
to num_CONV):

     #wordn_CONV "#1101";;
     |- #1101 = WORD4[T;T;F;T]

There is also a decision procedure for equality of n-bit word constants:

     #wordn_EQ_CONV word4 "#1100 = #1101";;
     |- (#1100 = #1101) = F

Finally, for those really nasty case analyses, we have:

     #let ccases = prove_wordn_const_cases cases;;
     ccases = 
     |- !w.
         ((((w = #0000) \/ (w = #0001)) \/ (w = #0010) \/ (w = #0011)) \/
          ((w = #0100) \/ (w = #0101)) \/
          (w = #0110) \/
          (w = #0111)) \/
         (((w = #1000) \/ (w = #1001)) \/ (w = #1010) \/ (w = #1011)) \/
         ((w = #1100) \/ (w = #1101)) \/
         (w = #1110) \/
         (w = #1111)

I have tested this last function up to :word12 (or something) but it is
not really recommended for n larger than four or so.


In addition to the programs shown above, there are others still under
development (when I get around to them).  They include a program for
defining functions over :wordn based on the theorem returned by
prove_function_defn_thm (see above), as well as packages for abstracting
to the natural numbers and the integers (complete with theorems about
modulo-n arithmetic). 

All this is fairly trivial and a bit boring, but slightly tricky to get
to run fast. I don't know when I'll have time to finish the package; but
if there is enough interest, I could release what I have so far.

Tom


