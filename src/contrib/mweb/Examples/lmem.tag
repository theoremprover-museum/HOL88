@t LMEM_DEF
\THM (\FORALL x\DOT \CONST{LMEM} \,x \,\NIL  = \CONST{F}) \AND 
     (\FORALL x \,h \,t\DOT \CONST{LMEM} \,x \,(\CONST{CONS} \,h \,t) =
                               (x = h) \OR  \CONST{LMEM} \,x \,t)
@e 
@t NULL_NOT_LMEM
\THM \FORALL x \,l\DOT \CONST{NULL} \,l \IMP  \NOT \CONST{LMEM} \,x \,l
@e 
