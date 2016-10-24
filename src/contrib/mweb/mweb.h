/*
  FILE: mweb.h --- header file for mweave and mtangle
  DATE: 29 May 1992 
  AUTHER: Wai Wong

Copyright (C) 1992, 1993 Wai Wong

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2, or (at your option)
any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.  

char headerVersion[] = "3.0";
*/


#ifndef MWEB

#define MWEB

#define MAXNAMELEN 40
#define MAXFNAMELEN 80
#define MAXOUTLEN 240
#define MAXNOLINE 400
#define MAXLINELEN 160
#define MAXNOTAGS 200
#define MAXNOTEXT 2000
#define MAXNOPARAS 200

#define WARNING 1
#define ERROR 2
#define FATAL 3

#define FALSE  0
#define TRUE   1

#ifndef EXTERN
#define EXTERN extern
#endif

#define Pchar_cmd		0
#define Pchar_old               1
#define Pchar_new               2
#define Pchar_begin_sec         3
#define Pchar_end_sec           4
#define Pchar_begin_star_sec    5
#define Pchar_begin_para        6
#define Pchar_end_para          7
#define Pchar_begin_tag         8
#define Pchar_end_tag           9
#define Pchar_incl_file         10
#define Pchar_para_def          11
#define Pchar_str_quote         12
#define Pchar_ml_sec            13
#define Pmac_sec                14
#define Pmac_star_sec           15
#define Pmac_sec_default        16
#define Pmac_line               17
#define Pmac_begin_env          18
#define Pmac_end_env            19
#define Pmac_filler             20
#define Pmac_changed            21
#define Pmac_before_tag         22
#define Pmac_after_tag          23
#define Poutsuffixmweave        24
#define Poutsuffixmtangle       25
#define Poutsuffixwinnow        26
#define Pinsuffix               27
#define Pml_comm_begin          28
#define Pml_comm_end            29
#define Pstr_blank              30
#define Pml_only                31
#define Pml_line_length         32
#define Pml_line_count          33
#define Pfilter_mode            34
#define Pdoc_only_mode          35
#define Pmac_begin_arg          36
#define Pmac_end_arg            37
#define Pmac_begin_doc          38
#define Pmac_end_doc            39
#define Pmac_end_sec            40
#define Pchar_anon_sec          41
#define Pchar_str_esc           42
#define Pparallel_mode          43
#define Pmac_begin_other        44
#define Pmac_end_other          45
#define Pmac_begin_native       46
#define Pmac_end_native         47
#define Praw_text_mode          48
#define Pspec_chars             49
#define Pmac_spec_char          50
#define Pmac_other_line         51
#define Pmac_native_line        52
#define Ptab_spaces		53
#define Pline_mode		54
#define Pchar_lang		55
#define Ptangle_lang		56
#define Pmac_begin_lang         57
#define Pmac_end_lang           58

#define TANGLE    0
#define WEAVE     1
#define WINNOW    2

typedef struct ptab
{
    char pname[MAXNAMELEN];
    char pval[MAXLINELEN];
}PTAB;

EXTERN PTAB paratab[];

EXTERN char *str_blank;

EXTERN char *char_cmd;
EXTERN char *char_old;
EXTERN char *char_new;
EXTERN char *char_begin_sec;
EXTERN char *char_end_sec;
EXTERN char *char_begin_star_sec;
EXTERN char *char_begin_para;
EXTERN char *char_end_para;
EXTERN char *char_begin_tag;
EXTERN char *char_end_tag;
EXTERN char *char_incl_file;
EXTERN char *char_para_def;
EXTERN char *char_ml_sec;
EXTERN char *char_anon_sec;
EXTERN char *char_str_esc;
EXTERN char *char_lang;

EXTERN char *tangle_lang;

EXTERN char *mac_sec;
EXTERN char *mac_star_sec;
EXTERN char *mac_sec_default;
EXTERN char *mac_line;
EXTERN char *mac_begin_env;
EXTERN char *mac_end_env;
EXTERN char *mac_filler;
EXTERN char *mac_changed;
EXTERN char *mac_before_tag;
EXTERN char *mac_after_tag;
EXTERN char *mac_begin_arg;
EXTERN char *mac_end_arg;
EXTERN char *mac_begin_doc;
EXTERN char *mac_end_doc;
EXTERN char *mac_end_sec;
EXTERN char *mac_other_line;
EXTERN char *mac_native_line;
EXTERN char *mac_begin_lang;
EXTERN char *mac_end_lang;

EXTERN int program;
EXTERN int verbflag;
EXTERN int filtermode;
EXTERN int mlonlymode;
EXTERN int doconlymode;
EXTERN int parallelmode;
EXTERN int rawtextmode;
EXTERN int linemode;

EXTERN int linecount;
EXTERN int seccount;
EXTERN int filecount;
EXTERN char prog[MAXFNAMELEN];
EXTERN char inbuf[MAXLINELEN];
EXTERN char langname[MAXNAMELEN];

EXTERN void proginit();
EXTERN void proc_incl_file();
EXTERN char *proc_tagname();
EXTERN char *get_para();
EXTERN char *proc_str();

EXTERN char basefilename[MAXFNAMELEN];

EXTERN char *outsuffix;

#define isblank(c) (strchr(str_blank,(c)) != NULL)

/* structure for storing tagged text block */

typedef struct tln{
    int nxt;
    char s[MAXLINELEN];
}   LINE;

EXTERN LINE tags[MAXNOTAGS];
EXTERN LINE incltext[MAXNOTEXT];
EXTERN int tagptr, textptr;

EXTERN char infname[MAXFNAMELEN];

#endif
