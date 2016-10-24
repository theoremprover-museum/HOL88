/*
  FILE: winnow.c --- generate ML output
  DATE: 05 March 1993 
  AUTHORS: Wai Wong & Brian Graham

Copyright (C) 1993 Wai Wong Brian Graham

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




/* ---------------------------------------------------------------------------
   An informal specification for the processing envisioned:
   ---------------------------------------------------------------------------
     input .tex file    -->   output master file   -->	restored file
   ---------------------------------------------------------------------------
      ...		      ... (unchanged)		...

     \beginhol		      \beginhol			\beginhol
     			      @ {<infilename>_##}	
     			      @t{<infilename>_##}	
     			      @N				
     % .... %		      % .... %			%...%
     #new_theory `blat`;;					
			      new_theory `blat`;;	#new_theory `blat`;;
     drivel ...						new drivel ...

     #new_parent `who`;;      new_parent `who`;;	#new_parent `who`;;
							
     drivel ...						new drivel ...
     							
     \endhol		      @-	
			      \endhol			\endhol
			      	
     ...		      ... (unchanged)		...

     \begin{hh}		      \begin{hh}		\begin{hh}
     			      @ {$<infilename>_##}	
     			      @t{$<infilename>_##}	
			      @N				
     timer true;;	      timer true;;		timer true;;

     loadt `who`;;	      loadt `who`;;		loadt `who`;;
     							
     \end{hh}		      @-			
			      \end{hh}			\end{hh}

   ---------------------------------------------------------------------------
*/

char winnowVersion[] = "1.0";

#include <stdio.h>
#include <string.h>

#include "mweb.h"

char tmpbuf[MAXLINELEN];

#define IS_HOL      1
#define IS_HIDE_HOL 2
#define NEW 1
char secbuf[MAXLINELEN];

static int Iout_char_cmd;
static int Iout_begin_sec_cmd;
static int Iout_end_sec_cmd;
static int Iout_char_new_cmd;
static int Iout_ml_sec;
static int Ichar_hol_prompt;
static int Ichar_end_hol_in;
static int Ichar_hol_begin_comment;
static int Ichar_hol_end_comment;
static int Ichar_end_hide;
static int Ichar_hide_indicator;

void proginit()
{
    program = WINNOW;
    set_para("char_cmd",           "\\"       ); /* "\" is new command char     */
    set_para("char_begin_sec",     "beginhol" ); /* "\beginhol" starts a sect   */
    set_para("char_end_sec",       "endhol"   ); /* "\endhol" ends a section    */
    set_para("char_begin_star_sec","\n"       ); /* unused entry to proc_sec    */
    set_para("insuffix",           ".tex"     ); /* infile suffix for winnow    */
    set_para("char_ml_sec",       "begin{hh}"); /* "\begin{hh}" starts ml sect */

    proc_para_def("filter_mode=true");

    Iout_char_cmd           = set_para("out_char_cmd",          "@" );     
    Iout_begin_sec_cmd      = set_para("out_begin_sec_cmd",     " " );
    Iout_end_sec_cmd        = set_para("out_end_sec_cmd",       "-" );  
    Iout_char_new_cmd       = set_para("out_char_new_cmd",      "N" ); 
    Iout_ml_sec             = set_para("out_ml_sec",            "M" );       
    Ichar_hol_prompt        = set_para("char_hol_prompt",       "#" );       
    Ichar_end_hol_in        = set_para("char_end_hol_in",       ";;");       
    Ichar_hol_begin_comment = set_para("char_hol_begin_comment","\%");       
    Ichar_hol_end_comment   = set_para("char_hol_end_comment",  "\%");       
    Ichar_end_hide          = set_para("char_end_hide",         "end{hh}");
    Ichar_hide_indicator    = set_para("char_hide_indicator",   "$");

    outsuffix = paratab[Poutsuffixwinnow].pval;

}


void proc_hidden_sec (infile,outfile)
FILE *infile,*outfile;
{

    char *cp;
    int n;

    fprintf(outfile,"%s%s\n",
	    paratab[Pchar_cmd].pval,
	    paratab[Pchar_ml_sec].pval);
    fprintf(outfile, "%s%s%s%s%s_%d%s\n%s%s%s%s%s_%d%s\n%s%s\n",
	    paratab[Iout_char_cmd].pval,		/* "@" */
	    paratab[Iout_begin_sec_cmd].pval,		/* " " */
	    paratab[Pmac_begin_arg].pval,		/* "{" */
	    paratab[Ichar_hide_indicator].pval,		/* "$" */
	    basefilename,				/* <fname>_# */
	    seccount,				
	    paratab[Pmac_end_arg].pval,			/* "}" */
	    paratab[Iout_char_cmd].pval,		/* "@" */
	    paratab[Pchar_begin_tag].pval,		/* "t" */
	    paratab[Pmac_begin_arg].pval,		/* "{" */
	    paratab[Ichar_hide_indicator].pval,		/* "$" */
	    basefilename,				/* <fname>_# */
	    seccount,				
	    paratab[Pmac_end_arg].pval,			/* "}" */
	    paratab[Iout_char_cmd].pval,		/* "@" */
	    paratab[Iout_char_new_cmd].pval) ;		/* "N" */

    while((cp = fgets(inbuf, MAXLINELEN, infile)) != NULL)
	{
	    linecount++;

	    if((n = is_command(cp, Pchar_cmd)) != 0)
		{
		    cp += n;
		    
		    if ((n = is_command(cp, Ichar_end_hide)) != 0)
			{
			    fprintf(outfile,"%s%s\n",
				    paratab[Iout_char_cmd].pval,
				    paratab[Iout_end_sec_cmd].pval);
			    fprintf(outfile,"%s%s\n",
				    paratab[Pchar_cmd].pval,
				    paratab[Ichar_end_hide].pval);
			    return;
			    
		        }
		    else
			{
			    fprintf(outfile,"%s",inbuf);
			}
		}
	    else fprintf(outfile,"%s",inbuf);
	}
    error(ERROR,"hidden hol section not terminated",cp);

} /* end of proc_hidden_sec */


void proc_example_sec (infile,outfile)
FILE *infile,*outfile;
{

    char *cp;
    int n;

    fprintf(outfile,"%s%s\n",
	    paratab[Pchar_cmd].pval,
	    paratab[Pchar_begin_sec].pval);
    fprintf(outfile, "%s%s%s%s_%d%s\n%s%s%s%s_%d%s\n%s%s\n",
	    paratab[Iout_char_cmd].pval,		/* "@" */
	    paratab[Iout_begin_sec_cmd].pval,		/* " " */
	    paratab[Pmac_begin_arg].pval,		/* "{" */
	    basefilename,				/* <fname>_# */
	    seccount,					
	    paratab[Pmac_end_arg].pval,			/* "}" */
	    paratab[Iout_char_cmd].pval,		/* "@" */
	    paratab[Pchar_begin_tag].pval,		/* "t" */
	    paratab[Pmac_begin_arg].pval,		/* "{" */
	    basefilename,				/* <fname>_# */
	    seccount,					
	    paratab[Pmac_end_arg].pval,			/* "}" */
	    paratab[Iout_char_cmd].pval,		/* "@" */
	    paratab[Iout_char_new_cmd].pval) ;		/* "N" */

    while((cp = fgets(inbuf, MAXLINELEN, infile)) != NULL)
	{
	    linecount++;

	    if((n = is_command(cp, Pchar_cmd)) != 0)
		{
		    cp += n;
		    
		    if ((n = is_command(cp, Pchar_end_sec)) != 0)
			{
			    fprintf(outfile,"%s%s\n",
				    paratab[Iout_char_cmd].pval,
				    paratab[Iout_end_sec_cmd].pval);
			    fprintf(outfile,"%s%s\n",
				    paratab[Pchar_cmd].pval,
				    paratab[Pchar_end_sec].pval);
			    return;
			    
		        }
		}
	    else if ((n = is_command(cp, Ichar_hol_prompt)) != 0)
		{
		    cp += n;

		    while ((strstr(cp, paratab[Ichar_end_hol_in].pval)) == NULL)
			{
			    fprintf(outfile,"%s",cp);
			    if ((cp = fgets(inbuf, MAXLINELEN, infile)) == NULL)
				{
				    error(ERROR,"hol command not terminated",cp);
				}
			    else
				{
				    linecount++;
				}
			}
		    
		    fprintf(outfile,"%s",cp);
		}
	    else if ((n = is_command(cp, Ichar_hol_begin_comment)) != 0)
		{
		    cp += n;
		    while ((strstr(cp, paratab[Ichar_hol_end_comment].pval)) == NULL)
			{
			    fprintf(outfile,"%s",inbuf);
			    if ((cp = fgets(inbuf, MAXLINELEN, infile)) == NULL)
				{
				    error(ERROR,"hol comment not terminated",cp);
				}
			    else
				{
				    linecount++;
				}
			}
		    
		    fprintf(outfile,"%s",inbuf);
		}
	}
    error(ERROR,"hol section not terminated",cp);
} /* end of proc_example_sec */

void proc_sec(infile,outfile,line)
FILE *infile,*outfile;
char *line;
{
    char *cp=line;
    int n;

    ++seccount;
    if(verbflag)
	fprintf(stderr,"[%d", seccount);

    if ((n = is_command(cp, Pchar_begin_sec)) != 0)
	{
	    proc_example_sec(infile, outfile);
	}
    else if ((n = is_command(cp, Pchar_ml_sec)) != 0)
        {
	    proc_hidden_sec(infile, outfile);
	}
    else error (ERROR, "Unknown command", cp);

    if(verbflag)
	print_end_sec();

} /* end of proc_sec */

/* ---------------- copied directly from mweave.c --------------------- */

int search_tag(cp)
char *cp;
{
    int lp = 1;
    
    while(lp < tagptr)
	{
	    if(strcmp(cp,tags[lp].s) == 0)
		return lp;
	    else lp++;
	}
    return(0);
    
}/* end search_tag() */


void proc_tag(tag,outfile)
char *tag;
FILE *outfile;
{
    char *cp;
    int tagp =0, lp = 0;
    

    cp = proc_tagname(tag);
    
    tagp = search_tag(cp);
    
    if(tagp == NULL)
	{
	    sprintf(tmpbuf, "Cannot find tag section %s", cp);
	    error(WARNING, tmpbuf, NULL);
	}
    else
	{
	    fprintf(outfile, "%s\n", mac_before_tag);
	    lp = tags[tagp].nxt;
	    while(incltext[lp].nxt != 0)
		{
		    fprintf(outfile, "%s", incltext[lp].s);
		    lp++;
		}
	    fprintf(outfile, "%s", incltext[lp].s);
	    fprintf(outfile, "%s\n", mac_after_tag);
	}
    
    
}/* end of proc_tag() */
