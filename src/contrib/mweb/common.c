/*
  FILE: common.c --- common to both mtangle and mweave
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
Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.  */


char Version[] = "Version 3.0";

#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include "patchlevel.h"

#define EXTERN /* */
#include "mweb.h"

PTAB paratab[MAXNOPARAS] = {
    "char_cmd",             "@",     /* 0 */
    "char_old",             "O",
    "char_new",             "N",
    "char_begin_sec",       " ",
    "char_end_sec",         "-",
    "char_begin_star_sec",  "*",    /* 5 */
    "char_begin_para",      "{",
    "char_end_para",        "}",
    "char_begin_tag",       "t",
    "char_end_tag",         "e",
    "char_incl_file",       "I",   /* 10 */
    "char_para_def",        "D",
    "char_str_quote",       "\"",
    "char_ml_sec",          "M",
    "mac_sec",              "\\subsect",
    "mac_star_sec",         "\\sect",     /* 15 */
    "mac_sec_default",      "\\subsect{}",
    "mac_line",             "\\pline",
    "mac_begin_env",        "\\begin{paralines}",
    "mac_end_env",          "\\end{paralines}\n",
    "mac_filler",           "\n",          /* 20 */
    "mac_changed",          "[c]\n",
    "mac_before_tag",       "\\begin{verbatim}\n",
    "mac_after_tag",        "\\end{verbatim}\n",
    "outsuffixmweave",      ".tex",
    "outsuffixmtangle",     ".ml",      /* 25 */
    "outsuffixwinnow",      ".m",
    "insuffix",             ".m",
    "ml_comm_begin",        "%-",
    "ml_comm_end",          "-%",
    "str_blank",            "\n\t ",	/* 30 */
    "ml_only",              "",	
    "ml_line_length",       "80",
    "ml_line_count",        "200",
    "filter_mode",          "",
    "doc_only_mode",        "",        /* 35 */
    "mac_begin_arg",        "{",
    "mac_end_arg",          "}",
    "mac_begin_doc",        "",
    "mac_end_doc",          "",
    "mac_end_sec",          "\n",     /* 40 */
    "char_anon_sec",        "A",
    "char_str_esc",         "\\",
    "parallel_mode",        "TRUE",
    "mac_begin_other",      "\\begin{other}\n",
    "mac_end_other",        "\\end{other}\n", /* 45 */
    "mac_begin_native",     "\\begin{native}\n",
    "mac_end_native",       "\\end{native}\n",
    "raw_text_mode",        "",
    "spec_chars",           "#$%&~_^{}\\",
    "mac_spec_char",        "\\char\"", /* 50 */
    "mac_other_line",       "\n",
    "mac_native_line",      "\n",
    "tab_spaces",	    "8",
    "line_mode",            "",
    "char_lang",            "L",
    "tangle_lang",          "",
    "mac_begin_lang",       "\\begin",
    "mac_end_lang",         "\\end",
    "", "" };

static int paracount = 59;;

char *str_blank  = paratab[Pstr_blank].pval;

char *char_cmd             = paratab[Pchar_cmd].pval;
char *char_old             = paratab[Pchar_old].pval;
char *char_new             = paratab[Pchar_new].pval;
char *char_begin_sec       = paratab[Pchar_begin_sec].pval;
char *char_end_sec         = paratab[Pchar_end_sec].pval;
char *char_begin_star_sec  = paratab[Pchar_begin_star_sec].pval;
char *char_begin_para      = paratab[Pchar_begin_para].pval;
char *char_end_para        = paratab[Pchar_end_para].pval;
char *char_begin_tag       = paratab[Pchar_begin_tag].pval;
char *char_end_tag         = paratab[Pchar_end_tag].pval;
char *char_incl_file       = paratab[Pchar_incl_file].pval;
char *char_para_def        = paratab[Pchar_para_def].pval;
char *char_str_quote       = paratab[Pchar_str_quote].pval;
char *char_ml_sec          = paratab[Pchar_ml_sec].pval;
char *char_anon_sec        = paratab[Pchar_anon_sec].pval;
char *char_str_esc         = paratab[Pchar_str_esc].pval;
char *char_lang            = paratab[Pchar_lang].pval;

char *tangle_lang          = paratab[Ptangle_lang].pval;

char *mac_sec             = paratab[Pmac_sec].pval;
char *mac_star_sec        = paratab[Pmac_star_sec].pval;
char *mac_sec_default     = paratab[Pmac_sec_default].pval;
char *mac_line            = paratab[Pmac_line].pval;
char *mac_begin_env       = paratab[Pmac_begin_env].pval;
char *mac_end_env         = paratab[Pmac_end_env].pval;
char *mac_filler          = paratab[Pmac_filler].pval;
char *mac_changed         = paratab[Pmac_changed].pval;
char *mac_before_tag      = paratab[Pmac_before_tag].pval;
char *mac_after_tag       = paratab[Pmac_after_tag].pval;
char *mac_begin_arg       = paratab[Pmac_begin_arg].pval;
char *mac_end_arg         = paratab[Pmac_end_arg].pval;
char *mac_begin_doc       = paratab[Pmac_begin_doc].pval;
char *mac_end_doc         = paratab[Pmac_end_doc].pval;
char *mac_end_sec         = paratab[Pmac_end_sec].pval;
char *mac_other_line      = paratab[Pmac_other_line].pval;
char *mac_native_line     = paratab[Pmac_native_line].pval;
char *mac_begin_lang      = paratab[Pmac_begin_lang].pval;
char *mac_end_lang        = paratab[Pmac_end_lang].pval;

char *insuffix            = paratab[Pinsuffix].pval;


int verbflag = TRUE;
int filtermode = FALSE;
int mlonlymode = FALSE;
int doconlymode = FALSE;
int rawtextmode = FALSE;
int parallelmode = TRUE;
int linemode = FALSE;


struct spp 
{
    int pinx;
    int *pflag;
} special_ptab[] = 
{
    Pml_only,  &mlonlymode,
    Pfilter_mode,  &filtermode,
    Pdoc_only_mode, &doconlymode,
    Pparallel_mode, &parallelmode,
    Praw_text_mode, &rawtextmode,
    Pline_mode,  &linemode,
    -1, NULL
    };

EXTERN char inbuf[MAXLINELEN];
EXTERN char langname[MAXNAMELEN];

FILE *instream = stdin;
FILE *outstream = stdout;

char infilename[MAXFNAMELEN] = "";
char outfilename[MAXFNAMELEN] = "";

void error(val,s,cp)
int val;
char *s, *cp;
{
    
    if(linecount <= 0)
	fprintf(stderr,"%s:%s\n", prog,s);
    else
	fprintf(stderr,"%s:%s at line %d\n", prog,s,linecount);

    if(val != WARNING)    exit(val);
    
}

void printusage(n)
{
    fprintf(stderr, "%s [options] [infile] [outfile]\n", prog);
    fprintf(stderr, "The follwoing options are available:\n");
    fprintf(stderr, " -h -H : help---print this message\n");
    fprintf(stderr, " -v : verbose---print process info (default)\n");
    fprintf(stderr, " -s : silent ---no process info\n");
    fprintf(stderr, " -I file: specify an include file\n");
    fprintf(stderr, " -D para=value : set a parameter to value\n");
    fprintf(stderr, " -L lang: specify language for mtangle\n");
    fprintf(stderr, " -m : ---activate ML only mode\n");
    fprintf(stderr, " -f : ---activate filter mode\n");
    fprintf(stderr, " -d : ---activate document only mode\n");
    fprintf(stderr, " -r : ---activate raw text mode\n");
    fprintf(stderr, " -p : ---deactivate parallel mode\n");
    fprintf(stderr, " -l : ---activate line mode\n");

    exit(n);
}

void print_end_sec()
{
    fprintf(stderr,"]");
    if((seccount % 10) == 0)
	fprintf(stderr,"\n");
}

int is_command(pcmd, cmdinx)
char *pcmd;
int cmdinx;
{
    char *cp = paratab[cmdinx].pval;
    int n = 0;

    if(cmdinx >= paracount) 
	error(ERROR, "Unknown command (should not happen)", pcmd);

    while((cp != NULL) && (*cp != '\0'))
	{
	    if (*cp == *pcmd)
		{
		    n++; cp++;
		    pcmd++;
		    if(*cp == '\0') return(n);
		}
	    else return(0);
	}
    return(0);
    
}

char *get_para(paraname)
char *paraname;
{
    int i = 0;
    
    while(paratab[i].pname[0] != '\0')
	{
	    if(strcmp(paraname, paratab[i].pname) == 0)
		return(paratab[i].pval);
	    i++;
	}
    return((char *)NULL);
    
}/* end of get_para() */


int set_para(paraname, paraval)
char *paraname, *paraval;
{
    int i = 0;
    
    while(paratab[i].pname[0] != '\0')
	{
	    if(strcmp(paraname, paratab[i].pname) == 0)
		{
		    strcpy(paratab[i].pval,paraval);
		    return(i);
		}
	    i++;
	}
    if(i >= (MAXNOPARAS -1))
	error(WARNING, "Internal table overflow(paratab)", NULL);
    else
	{
	     strcpy(paratab[i].pname,paraname);
	     strcpy(paratab[i].pval,paraval);
	     paratab[i+1].pname[0] = paratab[i+1].pval[0] = '\0';
	     paracount++; 
	 }
    return(i);
    
}/* end of set_para() */

static char ppname[MAXNAMELEN];
static char ppval[MAXLINELEN];

char *proc_str(sp, pp)
char *sp, *pp;
{
    char cc, c, *cp = sp;
    int n = 0;
    
    if((n  = is_command(cp, Pchar_begin_para)) != 0)
	{ c = *char_end_para; cp += n; }
    else if((n = is_command(cp, Pchar_str_quote)) != 0)
	{ c = *char_str_quote; cp += n; }
    else                        c = ' ';
    
    while(((c != ' ') && (*cp != c)) ||
          ((c == ' ') && (!isblank(*cp)) && (*cp != '=')))
	{
	    cc = *cp++;
	    if(cc == *char_str_esc)
		{   /* proce escape sequence */
		    cc = *cp++;
		    if(cc == 'n')
			cc = '\n';
		    else if(cc == 't')
			cc = '\t';
		    else if(cc == (*char_str_quote))
			cc = *char_str_quote;
		    else if(isdigit(cc) && (cc != '8') && (cc != '9'))
			{
			    if(!isdigit(*cp))
				error(WARNING,"Syntax error in parameter definition",sp);
			    cc = (cc - '0') * 8 + ((*cp++) - '0') ;
			    if(!isdigit(*cp))
				error(WARNING,"Syntax error in parameter definition",sp);
			    cc = cc * 8 + ((*cp++) - '0') ;
			}
		    		    
		}
	    *pp++ = cc;
	    
	    if(cc == '\0') {
		if(c != ' ')
		    error(WARNING,"Syntax error in parameter definition",sp);
		return((char *)NULL);
	    }
	}
    
    *pp = '\0'; 
    return(++cp);
    
}

void set_flag(pflag, pval)
int *pflag;
char *pval;
{
    char *cp;

    cp = pval;    
    *pflag = FALSE;
    
    while((cp != NULL) && (*cp != '\0'))
	{
	    if(isspace(*cp)) cp++;
	    else
		{
		    *pflag = TRUE;
		    return;
		}
	}
    
}


void do_special_para(inx)
int inx;
{
    int i = 0;

    while(special_ptab[i].pinx != -1)
	{
	    if(special_ptab[i].pinx == inx)
		{
		    set_flag(special_ptab[i].pflag, paratab[inx].pval);
		    return;
		    }
	    i++;
	}
    return;
	    
}

void proc_para_def(defstr)
char *defstr;
{
    char *cp = defstr;
    int inx;
    

    while(isblank(*cp)) cp++;
    
    cp = proc_str(cp, ppname);
    
    while(isblank(*cp)) cp++;
    if(*cp == '=') cp++;
    while(isblank(*cp)) cp++;

    cp = proc_str(cp, ppval);

    inx = set_para(ppname, ppval);
    do_special_para(inx);
   
}/* end of proc_para_def() */

void proc_cmd(infile,outfile,line)
FILE *infile, *outfile;
char *line;
{
    char *cp = line,*tp;
    int n = 0;
    
    if(((n = is_command(cp, Pchar_begin_sec)) != 0) ||
       ((n = is_command(cp, Pchar_begin_star_sec)) != 0) ||
       ((n = is_command(cp, Pchar_anon_sec)) != 0) ||
       ((n = is_command(cp, Pchar_ml_sec)) != 0))
	proc_sec(infile,outfile, (cp));
    else if((n = is_command(cp, Pchar_para_def)) != 0)
	{
	    cp += n;
	    if((tp = strrchr(cp, '\n')) != NULL)
		*tp = '\0';
	    proc_para_def(cp);
	}
    else if((n = is_command(cp, Pchar_incl_file)) != 0)
	{
	    cp += n;
	    proc_incl_file(cp);
	}
    else if ((program == WINNOW) && (filtermode != FALSE))
	{
	    fprintf(outfile,"%s", inbuf);
	}
    else error(ERROR,"Unknown command", cp);
}


void proc_file(infile, outfile)
FILE *infile, *outfile;
{
    char *cp;
    int n;
  
    while((cp = fgets(inbuf, MAXLINELEN, infile)) != NULL)
	{	    
	    linecount++;
	    
	    if((program == TANGLE) && (linemode == TRUE))
		fprintf(outfile, "\n");

	    if((n = is_command(cp, Pchar_cmd)) != 0)
		{
		    cp += n;
		    proc_cmd(infile,outfile,cp);
		}
	    else if ((program != TANGLE) && (filtermode == TRUE))
		{
		    fprintf(outfile, "%s", cp);
		}
	    
	}
}/* end of proc_file() */

void getfilename()
{
    char *cp;

    if(filecount == 1)
	{
	    if((cp = strrchr(infilename, (int)'.')) == NULL)
		{
		    strcpy(outfilename, infilename);
		    strcat(infilename, insuffix);
		    strcat(outfilename, outsuffix);
                    filecount++;
		}
            
	}

    if(filecount >= 1)
	{
	    strcpy(basefilename, infilename);
	    if((cp = strrchr(basefilename, (int)'.')) != NULL)
		{
		    *cp = '\0';
		}
	}
}/* end of getfilename() */

void init()
{
   
    if(verbflag)
	{
	    fprintf(stderr,"%s:(%s) Utility for literate programming in HOL\n",
		    prog, Version);
	    if (patchlevel != 0) 
		fprintf(stderr,"----Patch level %d\n", patchlevel);
	}

    proginit(); /* do initialization specific to each program */

    tagptr = textptr = 1;
    incltext[0].s[0] = tags[0].s[0] = '\0';
    incltext[0].nxt = tags[0].nxt = 0;


}/* end of init() */

void fileinit()
{
    basefilename[0]='\0';
    seccount = linecount = 0;
    getfilename();
    
    if(infilename[0] != '\0')
	{
	    instream = fopen(infilename, "r");
	    if(instream == NULL)
		{
		    sprintf(inbuf, "Cannot open input file %s", infilename);
		    error(ERROR, inbuf, NULL);
		}
	}
    
    if(outfilename[0] != '\0')
	{
	    outstream = fopen(outfilename, "w");
	    if(outstream == NULL)
		{
		    sprintf(inbuf, "Cannot open output file %s", outfilename);
		    error(ERROR, inbuf, NULL);
		}
	}
    
    
}/* end of fileinit() */


main(argc,argv)
int argc;
char *argv[];
{
    int i;

    strcpy(prog,argv[0]);

    init();
    
    i =  1; filecount = 0;
    
    while(argc > 1)
	{
	    if(argv[i][0] == '-'){
		switch(argv[i][1]) {		     
		    case 'v':
		    {
		    verbflag = 1;
		    break;
		    }
		    case 's':
		    {
		    verbflag = 0;
		    break;
		    }
		    case 'i': case'I':
		    {
			if(argv[i][2] == '\0')
			    {
				proc_incl_file(argv[++i]);
				argc--;
			    }
			else
				proc_incl_file(&argv[i][2]);
			break;
		    }
		    case'L':
		    {
			if(argv[i][2] == '\0')
			    {
				set_para("tangle_lang", argv[++i]);
				argc--;
			    }
			else
			    set_para("tangle_lang", (&argv[i][2]));
			break;
		    }
		    case 'm':
		    {
			proc_para_def("ml_only=true");
			break;
		    }
		    case 'f':
		    {
			proc_para_def("filter_mode=true");
			break;
		    }
		    case 'd':
		    {
			proc_para_def("doc_only_mode=true");
			break;
		    }
		    case 'p':
		    {
			proc_para_def("parallel_mode={}");
			break;
		    }
		    case 'r':
		    {
			proc_para_def("raw_text_mode=true");
			break;
		    }
		    case 'l':
		    {
			proc_para_def("line_mode=true");
			break;
		    }
		    case 'D':
		    {
/* fprintf(stderr,"-D(%s)\n",&(argv[i][2])); */
			
			if(argv[i][2] == '\0')
			    {
/* fprintf(stderr,"-D == null\n"); */
				proc_para_def(argv[++i]);
				argc--;
			    }
			else
			    proc_para_def(&(argv[i][2]));
			break;
		    }
		    case 'h': case 'H': case '?':
		    default:
		    {
		    printusage(0);
		    }
		    
		}
		
	    }else {
		if(filecount == 0){
		    strcpy(infilename,argv[i]);
		    filecount++;
		}else if(filecount == 1){
		    strcpy(outfilename,argv[i]);
		    filecount++;
		}else{
		    printusage(1);
		}
	    }
	    
	    i++; argc--;
	    
	}
    
    
    fileinit();

    if(verbflag) 
	{
	    if(filecount == 0)
		fprintf(stderr,"Input file: stdin");
   	    else fprintf(stderr,"Input file: %s ", infilename);
	    if(filecount <= 1)
		fprintf(stderr,"Output file: stdout\n");
   	    else fprintf(stderr,"Output file: %s\n", outfilename);
	}
    
    proc_file(instream,outstream);
    
    if(verbflag)
	fprintf(stderr, "\nTotal lines read: %d\n", linecount);

    exit(0);
    
}/* end of main() */


/* ------------------ process include files ----------------------- */
char tagname[MAXLINELEN];

char *proc_tagname(cp)
char *cp;
{
    char *ccp = tagname;
    int n,para = 0;
    

    /*skip leading blanks */
    while(((*cp) != '\0') && isblank(*cp)) ++cp;

    if(*cp == *char_begin_para)
	{ para = 1; cp++; }
    
    
    /* copy and strip final \n */
    while((*cp) != '\0')
	{
	    if(*cp == *char_end_para)
		{
		    para--;
		    if(para == 0) break;
		}
	    else if(*cp == *char_begin_para) para++;
	    else if(*cp == '\n') break;
	    *ccp++ = *cp++;
	}
    
    *ccp = '\0';
    if(para != 0)
       error(WARNING, "Unbalanced parathesis in name",tagname);
    
    return(tagname);
    
}/* end of proc_tagname() */



#define SKIP 0
#define INTAG 1
char tmpbuf[MAXLINELEN];

void proc_incl_file(fname)
char *fname;
{
    FILE *fp;
    int n,state = SKIP;
    int mainlinecnt = linecount;
    char *ccp, *cp, *tp;
    
    cp = proc_str(fname, infname);
    
    if((fp = fopen(infname, "r")) == NULL)
       {
	   sprintf(tmpbuf, "Cannot open include file %s", infname);
	   error(ERROR, tmpbuf, NULL);
       }

    if(verbflag) fprintf(stderr, "Reading include file %s\n", infname);
        
    linecount = 0;
    
    while((cp = (char *)fgets(tmpbuf, (MAXLINELEN-1), fp)) != (char *)NULL)
	{
	    ++linecount;
	    
	    if((n = is_command(cp, Pchar_cmd)) != 0)
		{
		    cp += n;
		    
		    if((n = is_command(cp, Pchar_begin_tag)) != 0)
			{
			    if(tagptr >= MAXNOTAGS)
				error(ERROR, "internal buffer overflow(tags)",cp);
			    cp += n;
			    cp = proc_tagname(cp);
			    if(strlen(cp) == 0)
				{				    
				   error(WARNING, "Anonymous tag section",NULL);
				   tags[tagptr].s[0] = '\0'; 
				}
			    else strcpy(tags[tagptr].s, cp);
			    if(textptr >= MAXNOTEXT)
				error(ERROR, "internal buffer overflow(incltext)",cp);
			    tags[tagptr++].nxt = textptr;
       			    state = INTAG;
			}
		    else if((n = is_command(cp, Pchar_end_tag)) != 0)
			{
			    if(state != INTAG)
				error(ERROR,"Unexpected command in include file",cp);
			    cp += n;
			    cp = proc_tagname(cp);
			    if(strlen(cp) != 0)
				{
				    if(strcmp(cp, tags[tagptr-1].s))
				       error(WARNING,"tag section end with different name"); 
				}
			    if(textptr == (tags[tagptr-1].nxt))
				tags[tagptr-1].nxt = 0;
			    
			    state = SKIP;
			}
		    else if((n = is_command(cp, Pchar_para_def)) != 0)
			{
			    cp += n;
			    if((tp = strrchr(cp, '\n')) != NULL)
				*tp = '\0';
			    proc_para_def(cp);
			}
		    else
			{
			    error(ERROR,"Unexpected command in include file",cp);
			}
		}
	    else if(state == INTAG)
		{
		    if(textptr >= MAXNOTEXT)
			error(ERROR, "internal buffer overflow(incltext)",cp);

		    strcpy(incltext[textptr].s, cp);
		    if(textptr != tags[(tagptr-1)].nxt)
			incltext[textptr-1].nxt = textptr;
		    incltext[textptr++].nxt = 0;
		}
	    
	}
    
    if(state == INTAG)
	error(ERROR, "Unexpected end of file while in a tag");
    else linecount = mainlinecnt;
    
}/* end of proc_incl_file() */
