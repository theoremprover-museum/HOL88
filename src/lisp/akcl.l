;----------------------------------------------------------------------------;
;                                                                            ;
; AKCL initialisation for speed.                                             ;
;                                                                            ;
; FILE:    hol-init.ml                                                       ;
;                                                                            ;
; AUTHOR:  John Van Tassel                                                   ;
; ADDRESS: University of Cambridge Computer Laboratory                       ;
;          New Museums Site                                                  ;
;          Pembroke Street                                                   ;
;          Cambridge CB2 3QG                                                 ;
;          ENGLAND                                                           ;
; E-MAIL:  jvt@cl.cam.ac.uk                                                  ;
; TEL.     +44 223 334729                                                    ;
;                                                                            ;
;----------------------------------------------------------------------------;

#+akcl
     #+sun (progn ()
               (allocate 'cons 900)
               (allocate 'string 100)
               (system:allocate-relocatable-pages 100)
               (system:set-hole-size 2048))
     #+mips (progn ()
               (allocate 'cons 2048)
               (allocate 'string 100)
               (system:allocate-relocatable-pages 100)
               (system:set-hole-size 2048))
     #+hp9000-800 (progn ()
               (allocate 'cons 2024)
               (allocate 'string 100)
               (system:allocate-relocatable-pages 100)
               (system:set-hole-size 2048))
     #-(or sun mips hp9000-800) ()

#-akcl ()

