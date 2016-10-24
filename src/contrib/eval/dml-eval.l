(eval-when (compile)
     #+franz (include "f-franz")
     (include "f-macro")
     (include "f-ol-rec")
     (include "genmacs"))

#+franz (declare (localf))


(dml |div| 2 intdiv ((|int| |#| |int|) -> |int|))

(dml |rem| 2 intrem ((|int| |#| |int|) -> |int|))

(dml |mk_bin_rep| 2 mk-bin-rep ((|int| |#| |int|) -> (|tok| |list|)))


(dml |BITS_RULE| 1 BITS-RULE (|thm| -> |thm|))
(dml |BITS_CONV| 1 BITS-CONV (|term| -> |thm|))

(dml |ADD_RULE| 1 ADD-RULE (|thm| -> |thm|))
(dml |ADD_CONV| 1 ADD-CONV (|term| -> |thm|))

(dml |DIF_RULE| 1 DIF-RULE (|thm| -> |thm|))
(dml |DIF_CONV| 1 DIF-CONV (|term| -> |thm|))

(dml |EQ_RULE| 1 EQ-RULE (|thm| -> |thm|))
(dml |EQ_CONV| 1 EQ-CONV (|term| -> |thm|))

(dml |EL_RULE| 1 EL-RULE (|thm| -> |thm|))
(dml |EL_CONV| 1 EL-CONV (|term| -> |thm|))

(dml |WORD_RULE| 1 WORD-RULE (|thm| -> |thm|))
(dml |WORD_CONV| 1 WORD-CONV (|term| -> |thm|))

(dml |VAL_RULE| 1 VAL-RULE (|thm| -> |thm|))
(dml |VAL_CONV| 1 VAL-CONV (|term| -> |thm|))

(dml |V_RULE| 1 V-RULE (|thm| -> |thm|))
(dml |V_CONV| 1 V-CONV (|term| -> |thm|))

(dml |SEG_RULE| 1 SEG-RULE (|thm| -> |thm|))
(dml |SEG_CONV| 1 SEG-CONV (|term| -> |thm|))

(dml |AND_RULE| 1 AND-RULE (|thm| -> |thm|))
(dml |AND_CONV| 1 AND-CONV (|term| -> |thm|))

(dml |OR_RULE| 1 OR-RULE (|thm| -> |thm|))
(dml |OR_CONV| 1 OR-CONV (|term| -> |thm|))

(dml |NOT_RULE| 1 NOT-RULE (|thm| -> |thm|))
(dml |NOT_CONV| 1 NOT-CONV (|term| -> |thm|))

(dml |COND_RULE| 1 COND-RULE (|thm| -> |thm|))
(dml |COND_CONV| 1 COND-CONV (|term| -> |thm|))

(dml |U_RULE| 1 U-RULE (|thm| -> |thm|))
(dml |U_CONV| 1 U-CONV (|term| -> |thm|))

(dml |TRI_RULE| 1 TRI-RULE (|thm| -> |thm|))
(dml |TRI_CONV| 1 TRI-CONV (|term| -> |thm|))

(dml |bool_RULE| 1 bool-RULE (|thm| -> |thm|))
(dml |bool_CONV| 1 bool-CONV (|term| -> |thm|))

