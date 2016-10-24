;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                             HOL 88 Version 2.0                          ;;;
;;;                                                                         ;;;
;;;   FILE NAME:        f-constants.l                                       ;;;
;;;                                                                         ;;;
;;;   DESCRIPTION:      Various constants (aka LISP specials) in the system ;;;
;;;                                                                         ;;;
;;;   USES FILES:       f-franz.l (or f-cl.l)                               ;;;
;;;                                                                         ;;;
;;;                     University of Cambridge                             ;;;
;;;                     Hardware Verification Group                         ;;;
;;;                     Computer Laboratory                                 ;;;
;;;                     New Museums Site                                    ;;;
;;;                     Pembroke Street                                     ;;;
;;;                     Cambridge  CB2 3QG                                  ;;;
;;;                     England                                             ;;;
;;;                                                                         ;;;
;;;   COPYRIGHT:        University of Edinburgh                             ;;;
;;;   COPYRIGHT:        University of Cambridge                             ;;;
;;;   COPYRIGHT:        INRIA                                               ;;;
;;;                                                                         ;;;
;;;   REVISION HISTORY: (none)                                              ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when (compile)
   #+franz (include "lisp/f-franz"))


(eval-when (compile load)
   (special

           poport                      ;output stream
           piport                      ;input stream
           outfiles                    ;set of output files 
           inputstack                  ;stack of input streams
           %directory                  ;directory where input file found
           %debug                      ;t iff compiler lisp sources files kept

;;; f-gp
           prop                        ;holder of property for putpropl
           initial%load                ;t iff initial loading of the system
           %symcount                   ;counter for internal gensym
           %timestamp                  ;time stamp

;;; site
           %hol-dir                    ;path of hol directory
           %lib-dir                    ;path of library
           %liszt                      ;path to liszt (TFM)
           %version                    ;current version (TFM)
           %build-date                 ;date 
           %system-name                ;LCF, ML, or what have you
           experimental                ;obsolete

;;; f-parser f-parsml
           spec-toks
           eq-tok
           token                       ;current token
           tokchs                      ;list of chars of next tokens
           toktyp                      ;type of current token
           %char-buffer 
           %special-letters 
           %special-alphanums 
           %special-table 
           %ch                         ; last ascii character read
           hol-char                    ;current char
           ptoken                      ;previous
           ptokchs                     ;previous 
           ptoktyp                     ;previous
           pchar                       ;previous
           cflag                       ;glitch to recognize vartypes
           parsedepth                  ;depth of parse recursion
           arg1                        ;global used to feed a parse function its arg
           lang1                       ;code of unary operator in current language
           lang2                       ;code of binary operator in current language
           langlp                      ;code of operator precedence in current language
           atom-rtn                    ;lisp code of atom recognizer in current language
           juxtlevel                   ;level of juxt nesting 
           juxt-rtn                    ;lisp code of juxt operator in current language

           toklist                     ;acc of string chars 
           metaprec


;;; typeml
           %mlprindepth                ;max depth of printing for ML
           %vartypes                   ;list of vartypes
           env                         ;local environnement
           tenv                        ;local type environnement
           asscheck                    ;check for assignment
           structcheck                 ;check for structs
           glassl                      ;global assigned vars list
           %l                          ;dummy for list
           %env                        ;dummy for env
           %id                         ;dummy for identifiers
           %star                       ;number of stars in vartypes
           nonloc                      ;t if not local
           type%errors                 ;type errors

           nullty                      ;null type
           boolty                      ;booleen type
           intty                       ;integer type
           tokty                       ;string type
;;;        objty                       ;lisp object type[deleted TFM 90.09.09]
           typety                      ;ol type type
           termty                      ;ol term type
           formty                      ;ol formula type
           thmty                       ;ol theorem type

           %thisdec                    ;t if ML declaration
           %thistydec                  ;t if ML type declaration
           %deftypes                   ;types defined in current exprs
           %emt                        ;global environnement
           %temt                       ;global type environnement
           %sections                   ;stack of sections
           
;;; f-mlprint
           %print-depth                ;depth of printing
           %ex                         ;

;;; f-DML
           infixables
           tracelist

;;; f-TRAN
           msg1                        ;error message for multiple occs of vars in structs
           msg2                        ;used instead of msg1 when mult occs allowed

           %compfns
           %p
           global%env
           new%%lb
           rec%env
           %loop
           %test
           %timestamp

;;; f-FORMAT
           %space                      ;space remaining on this line
           %left-total                 ;total width of tokens already printed
           %right-total                ;total right of tokens ever put in queue
           %pstack                     ;printing stack with indentation entries
           %scan-stack                 ;
           %qleft                      ;
           %qright                     ;
           %prettyon                   ;indicates if pretty-pretting is on
           %curr-depth                 ;current depth of "begins"
           %max-depth                  ;max depth of "begins" to print

;;; f-IOX-STAND
           %%%fn
           %%%args
           fin-ligne
           %prompt-string
           inputstack
           prinlevel
           prinlength

;;; f-TML
           %f
           %dev
           %pt
           %ty
           %pr
           %val
           new%%lb
           %compfns
           global%env
           %sections
           %dump
           %emt
           %temt
           %lb
           %thisdec
           %thistydec
           tenv
           %head
           new%lb
           |%timing-flag|        ; Changed from %time for HOL88 (30/11/88)
           %timestamp
           %symcount
           %outport
           |%print_load-flag|
           ibase
           base
           *nopoint
           instack
           msgflag
           eof
           nullty
           %char-buffer
           %parse-tree-buffer 
           |%abort_when_fail-flag| 
           %turnstile
           %prompt-string
           %libraries

;;; f-LIS
;;;        %%F                         ; deleted 19/11/91 JAC

           %theorydata
           %falsity                    ;ol-syntax
           %vtyl                       ;ol-syntax
           %thm-count                  ;ol-syntax
           term-constrs                ;parsol
           form-constrs                ;
           olinprec
           %mk=antiquot 
           %empty                      ;F-typeol
           %stickylist
           %canonlist
           %tyvars
           %linkcount
           |%show_types-flag|            ;F-writol (HOL88)
           %varpairs                   ;F-subst
           %all
           %vars
           %newvars
           %oldtys                     ;F-inst
           %tyvl
           %used-varnames
           %changed-types
           %renames
           dash                        ;F-thyfns
           legalconsts
           %current
           %ancestry
           %kind
           %loading-thy
           olreserved
           legalconst
           %newconsts
           %date
           %theory-data
           %theorems
           %failtok
           %newtypes
           %current
           %thy-cache
           %new-ancestors
           %sharetypes
           %sharecount
           %elem                       ;F-ol-net
           %deferred
           %substl                     ;F-simpl
           %insttyl
           %bv-pairs
           %type-matches
           |%theory_pp-flag|))


;;; f-parser

(defconstant cr 13) ;carriage return
(defconstant lf 10) ;line feed
(defconstant ff 12) ;form feed
(defconstant tab 9) ;tab
(defconstant cmntchr #/%) 
(defconstant hol-space #/ )
(defconstant lparen #/()
(defconstant rparen #/))
(defconstant period #/.)
(defconstant comma #/,)
(defconstant colon #/:)
(defconstant scolon #/;)
(defconstant lbrkt #/[)
(defconstant rbrkt #/])
(defconstant multiply #/*)
(defconstant tokqt #/`)
#+franz (defconstant escape #/\)
#-franz (defparameter escape #/\)
(defconstant cmnt-start #/<)
(defconstant cmnt-end #/>)
(defconstant endcnrtok '|"|)
(defconstant anticnr-tok '|^|)
(defconstant condl-tok '|=>|)
(defconstant else-tok '\|)
(defconstant lambda-tok '\\)
(defconstant ineq-tok '|<<|)
(defconstant neg-tok '|~|)
(defconstant conj-tok '/\\)
(defconstant disj-tok '\\/)
(defconstant imp-tok '|==>|)
; (defconstant iff-tok '|<=>|)         no longer used [TFM 90.01.20]
(defconstant forall-tok '|!|)
(defconstant exists-tok '|?|)
(defconstant restrict-tok '|::|)  ;;; MJCG 24.1.91
(defconstant arrow-tok '|->|)
(defconstant sum-tok '|+|)
(defconstant prod-tok '|#|)

(defconstant cr-sym (imploden (list cr))) ;carriage return
(defconstant lf-sym (imploden (list lf))) ;line feed
(defconstant ff-sym (imploden (list ff))) ;form feed
(defconstant tab-sym (imploden (list tab))) ;tab
(defconstant tml-sym '|;;|)
(defconstant tokqt-sym '|`|)
(defconstant escape-sym '\\)
(defconstant exfix-sym '|$|)
(defconstant neg-sym '|not|)
(defconstant arrow-sym '|->|)
(defconstant prod-sym '|#|)
(defconstant sum-sym '|+|)
(defconstant list-sym '|list|)  
(defconstant null-sym '|void|)
(defconstant cnr-sym '|"|)
(defconstant endcnr-sym '|"|)
(defconstant mul-sym '|*|)
(defconstant div-sym '|/|)
(defconstant plus-sym '|+|)
(defconstant mns-sym '|-|)
(defconstant conc-sym '|@|)
(defconstant eq-sym '|=|)
(defconstant lt-sym '|<|)
(defconstant gt-sym '|>|)
(defconstant conj-sym '|&|)
(defconstant disj-sym '|or|)  
(defconstant condl-sym '|=>|)
(defconstant lam-sym '\\)
(defconstant assign-sym '|:=|)
(defconstant wildcard-sym '|_|)
(defconstant case-sym '\|)
(defconstant else-sym '\|)
(defconstant trap-then-sym '|?|)
(defconstant trapif-then-sym '|??|)
(defconstant trapbind-then-sym '?\\)
(defconstant trap-loop-sym '|!|)
(defconstant trapif-loop-sym '|!!|)
(defconstant trapbind-loop-sym '!\\)
(defconstant cmntchr-sym '|%|)
(defconstant space-sym '| |)
(defconstant lparen-sym '|(|)
(defconstant rparen-sym '|)|)
(defconstant period-sym '|.|)
(defconstant comma-sym '|,|)
(defconstant colon-sym '|:|)
(defconstant scolon-sym '|;|)
(defconstant lbrkt-sym '|[|)
(defconstant rbrkt-sym '|]|)

(defconstant trap-syms
    (list trap-then-sym trap-loop-sym trapif-then-sym trapif-loop-sym
          trapbind-then-sym trapbind-loop-sym))

(defconstant spec-syms
      (list* div-sym else-sym escape-sym trapbind-then-sym trapbind-loop-sym
             '(|:| |(|  |)|  |#|  |->|  |,|  |.|  |[|  |]|  |;|  |;;|  |:=| |"|
               |%|  |$|  |`| |``| |*|  |+|  |-|  |@|  |=|  |<|  |>|  |&|
               |=>| |?| |??| |!| |!!| )))

(defconstant rsvdwds '(|let| |letref| |letrec| |and| |with| |in|
                       |typeabbrev| |deftype| |lettype| |abstype| 
                       |absrectype| |type| |rectype|
                       |where| |whereref| |whererec|
                       |wheretype| |whererectype| |wheretypeabbrev| 
                       |whereabstype| |whereabsrectype|
                       |fail| |failwith| |begin| |end| |do| |it| |or|
                       |not| |true| |false|
                       |if| |then| |loop| |else| |while|))

(defconstant declnconstrs '(mk-let mk-letrec mk-letref mk-deftype
                            mk-abstype mk-absrectype
                            mk-type mk-rectype))

(defconstant exprconstrs '(mk-boolconst mk-intconst mk-tokconst mk-var 
                           mk-wildcard mk-case mk-while mk-fun
                           mk-appn mk-abstr mk-dupl mk-empty
                           mk-fail mk-binop mk-unop
                           mk-assign mk-list mk-seq mk-trap mk-test
                           mk-straint mk-in mk-ind mk-quot mk-tyquot))

(defconstant tokflag '|<string>|)


;;; f-parsml f-gnt

(defconstant bastypes '(|int| |bool| |string| |token| |tok| |.|
                           |void| |term| |form| |type| |thm|))


;;; f-dml

(defconstant tokempty '|``|)
(defconstant mlreserved (append '(|=| |?|) rsvdwds))


;;; f-tml f-typeml

(defconstant lastvalname '|it|)


;;; f-tran, f-tml, f-writml

(defconstant nill '%nil)
(defconstant empty '%empty)
