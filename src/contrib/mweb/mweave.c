/*
  FILE: mweave.c --- generate TeX output
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


char mweaveVersion[] = "2.0";

#include <stdio.h>
#include <string.h>

#include "mweb.h"

char old_buf[MAXNOLINE][MAXLINELEN];
char new_buf[MAXNOLINE][MAXLINELEN];
char tmpbuf[MAXLINELEN];

int oldp,newp;

void proc_tag();

void proginit()
{
    program = WEAVE;
    outsuffix = paratab[Poutsuffixmweave].pval;
}

int store_buf(infile,buf)
FILE *infile;
char buf[][MAXLINELEN];
{
    char *cp;
    int n,count = 0;
    int linelen = atoi(paratab[Pml_line_length].pval);
    int maxnoline = atoi(paratab[Pml_line_count].pval);
    
    while((cp = fgets(buf[count], linelen, infile)) != NULL)
	{
	    linecount++;
	    	    
	    if((n = is_command(cp, Pchar_cmd)) != 0) return(count);
	    else  count++;
	    if(count >= maxnoline)
		error(ERROR, "Internal buffer overflow(secbuf)",NULL);
	}
    error(ERROR, "Unexpected end of file",cp);
    
}/* end of store_buf() */

void ctohex(c,cp)
unsigned char c;
char *cp;
{
    int d;
    
    d = (c >> 4) & 0x0F;
    *cp = (d < 10) ? ('0' + d) : (d + ('A' - 10));
    d = c & 0x0F;
    *(cp+1) = (d < 10) ? ('0' + d) : (d + ('A' - 10));
    
}/* end of ctohex() */

int is_spec(c)
char c;
{
    char *cp = paratab[Pspec_chars].pval;

    while(*cp != '\0')
	if(*cp++ == c) return(1);
    return(0);
}

char *proc_tab(op)
char *op;
{
    /* convert TAB character to spaces */
    int n = atoi(paratab[Ptab_spaces].pval);

    while(n-- > 0)
	{
	    *op++ ='\\'; *op++ =' ';
	}

    return(op);
    
}
/* end of proc_tab */
char charspec[MAXLINELEN];

void proc_buf_line(obuf, inbuf)
char *obuf, *inbuf;
{
    char c,*op = obuf;
    int len;
        
    if(rawtextmode == TRUE)
	{
	    strcpy(obuf, inbuf);
	}
    else
	{
	    
	    len = strlen(paratab[Pmac_spec_char].pval);
	    strncpy(charspec, paratab[Pmac_spec_char].pval, (len + 3));
	    
	    while(*inbuf != '\0')
		{
		    if(is_spec(*inbuf))
			{
			    c = *inbuf++;
			    ctohex(c,&(charspec[len]));
			    op = strcpy(op,charspec);
			    op += len + 2;
			    *op++ = ' ';
			}
		    else if(*inbuf == '\n') inbuf++;
		    else if(*inbuf == '\t')
			{
			    op = proc_tab(op);
			    inbuf++;
			}
		    else if(*inbuf == ' ')
			{
			    *op++ = '\\'; *op++ = ' '; inbuf++;
			}
		    else *op++ = *inbuf++;
		}
	    *op = '\0';
	}
        		    
}/* end of proc_buf_line() */


char *skip(buf, bp, bend, cp)
char buf[][MAXLINELEN];
int *bp, bend;
char *cp;
{
    while(isblank(*cp))
	{
/*	    fprintf(stderr,"(%c)",*cp); */
	    
	    if(*cp == '\0') 
		{
		    *bp += 1;
		    if((*bp) >= bend) return(NULL);
		    else cp = buf[(*bp)];
		}
	    else cp++;
	}
    
    return(cp);
}

char oldstr[MAXOUTLEN],newstr[MAXOUTLEN],langstr[MAXOUTLEN];

void output_p_sec(outfile,old_buf,oldp,new_buf,newp)
FILE *outfile;
char old_buf[][MAXLINELEN],new_buf[][MAXLINELEN];
int oldp,newp;
{
    int op = 0, np = 0;
    char *ocp, *ncp;
    int done= 0, changed = 0;    
    
    /* compare two buffers */
    ocp = old_buf[op];
    ncp = new_buf[np];
    while(!done)
	{
	    ocp = skip(old_buf, &op, oldp, ocp);
	    ncp = skip(new_buf, &np, newp, ncp);
/*	    fprintf(stderr,"OUTPUT_SEC:ocp->%s|ncp->%s\n", ocp, ncp); */
	    
	    if((ocp == NULL) && (ncp == NULL))
		{
		    changed = 0;
		    done = 1;
		}
	    else if((ocp == NULL) || (ncp == NULL))
		{
		    changed = 1;
		    done = 1;
		}
	    else
		{
		    
		    while(!isblank(*ocp) && !isblank(*ncp))
			{
			    if(*ocp != *ncp)
				{
				    changed = 1;
				    goto compared;
				}
			    ocp++;
			    ncp++;
			}
		    if(isblank(*ocp) != isblank(*ncp))
			{
			    changed = 1;
			    done = 1;
			}
		}
	    
	}
    
compared:
    if(verbflag > 1) fprintf(stderr,"*"); 
    fprintf(outfile,"%s%s", mac_begin_env, 
	    (changed ? mac_changed : mac_filler));

    op = np = 0;
    
    while((op < oldp) && (np < newp))
	{
	    proc_buf_line(oldstr,&(old_buf[op++][0]));
	    proc_buf_line(newstr,&(new_buf[np++][0]));	    
	    fprintf(outfile,"%s%s%s%s%s%s%s\n",
		    mac_line,
		    mac_begin_arg,oldstr,mac_end_arg,
		    mac_begin_arg,newstr,mac_end_arg);
	}

    if(op >= oldp)
	{
	    while(np < newp){
		    proc_buf_line(newstr,&(new_buf[np++][0]));	    
		    fprintf(outfile,"%s%s%s%s%s%s%s\n",
			    mac_line,
			    mac_begin_arg,mac_filler,mac_end_arg,
			    mac_begin_arg,newstr,mac_end_arg);
		}
	    }
    else if(np >= newp)
	{
	    while(op < oldp)
		{
		    proc_buf_line(oldstr,&(old_buf[op++][0]));
		    fprintf(outfile,"%s%s%s%s%s%s%s\n",
			    mac_line,
			    mac_begin_arg,oldstr,mac_end_arg,
			    mac_begin_arg,mac_filler,mac_end_arg);
		}
	    
	}

    fprintf(outfile,"%s", mac_end_env);


}/* end of output_p_sec () */

void output_s_sec(outfile,old_buf,oldp,new_buf,newp)
FILE *outfile;
char old_buf[][MAXLINELEN],new_buf[][MAXLINELEN];
int oldp,newp;
{
    int lp = 0;
    
    if(oldp > 0){
	fprintf(outfile,"%s",paratab[Pmac_begin_other].pval);
	while(lp < oldp)
	    {
		proc_buf_line(oldstr, &(old_buf[lp++][0]));
		fprintf(outfile, "%s%s%s%s",
		    mac_other_line,mac_begin_arg,oldstr,mac_end_arg);
	    }
	fprintf(outfile,"%s",paratab[Pmac_end_other].pval);
    }


    if(newp > 0) {
	lp = 0;
	fprintf(outfile,"%s",paratab[Pmac_begin_native].pval);
	while(lp < newp)
	    {
		proc_buf_line(newstr, &(new_buf[lp++][0]));
		fprintf(outfile, "%s%s%s%s",
		    mac_native_line,mac_begin_arg,newstr,mac_end_arg);
	    }
	fprintf(outfile,"%s",paratab[Pmac_end_native].pval);
    }

}/* end of output_s_sec () */

void output_sec(outfile,old_buf,oldp,new_buf,newp)
FILE *outfile;
char old_buf[][MAXLINELEN],new_buf[][MAXLINELEN];
int oldp,newp;
{
    if(parallelmode == TRUE)
	output_p_sec(outfile,old_buf,oldp,new_buf,newp);
    else
	output_s_sec(outfile,old_buf,oldp,new_buf,newp);

}/* end of output_sec() */

void skip_sec(infile, outfile)
FILE *infile, *outfile;
{
    char *cp;
    int n;

    while((cp = fgets(inbuf, MAXLINELEN, infile)) != NULL)
	{
	    linecount++;

	    if((n = is_command(cp, Pchar_cmd)) != 0)
		{
		    cp += n;
		    
		    if((n = is_command(cp, Pchar_end_sec)) != 0)
			{
			    if(verbflag) print_end_sec();
			    return;
			}
		}
	}
    error(ERROR, "Unexpected EOF when skipping ML section",cp);
}

    
#define IN_DOC  1
#define IN_O    2
#define IN_N    3
#define IN_LANG 4

void proc_sec(infile,outfile,line)
FILE *infile,*outfile;
char *line;
{
    char *cp = line;
    int n = 0;
    int status = 0;

    ++seccount;
    if(verbflag) fprintf(stderr,"[%d", seccount);
    oldp = newp = 0;
    
    if((n = is_command(cp, Pchar_ml_sec)) != 0)
	{
	    if(mlonlymode == TRUE)
		{
		    skip_sec(infile, outfile);
		    return;
		}
	    cp += n;
	    if((n = is_command(cp,Pchar_begin_para)) != 0)
		fprintf(outfile,"%s%s\n", mac_sec, cp);
	    else fprintf(outfile,"%s\n", mac_sec_default);

	}
    else if((n = is_command(cp, Pchar_begin_sec)) != 0)
	{
	    cp += n;
	    if((n = is_command(cp, Pchar_begin_para)) != 0)
		fprintf(outfile,"%s%s\n", mac_sec, cp);
	    else fprintf(outfile,"%s\n", mac_sec_default);
	}
    else if((n = is_command(cp, Pchar_begin_star_sec)) != 0)
	{
	    cp += n;
	    if((n = is_command(cp, Pchar_begin_para)) != 0)
		fprintf(outfile,"%s%s\n", mac_star_sec, cp);
	    else error(ERROR, "No name for section",cp);
	}
    /* else it must be char_anon_sec then nothing is output */

    fprintf(outfile, "%s", mac_begin_doc);
    status = IN_DOC;
        
    while((cp = fgets(inbuf, MAXLINELEN, infile)) != NULL){
	linecount++;

	if((n = is_command(cp, Pchar_cmd)) == 0){
	    if(status == IN_DOC){
		fprintf(outfile,"%s", cp);
	    }
	    else if((status == IN_LANG) && (doconlymode != TRUE)){
		proc_buf_line(langstr, cp);
		fprintf(outfile, "%s\n", langstr);
	    }
	}
	else{
	    cp += n;
	    
	    if((n = is_command(cp, Pchar_begin_tag)) != 0){
		proc_tag((cp += n),outfile);
		continue;
	    }
	    
	    if((n = is_command(cp, Pchar_end_sec)) != 0){
		cp += n;
		if(status == IN_DOC)
		    fprintf(outfile,"%s", mac_end_doc);
		else if(status == IN_LANG){
		    if(doconlymode != TRUE)
			fprintf(outfile, "%s%s%s%s\n",
			   mac_end_lang, mac_begin_arg,
			   langname, mac_end_arg);
	        }
		fprintf(outfile,"%s", mac_end_sec);
		if(verbflag) print_end_sec();
		return;
	    }
	    
	    if((n = is_command(cp, Pchar_old)) != 0){
		if(status == IN_LANG){
		   fprintf(outfile, "%s%s%s%s\n",
			   mac_end_lang, mac_begin_arg,
			   langname, mac_end_arg);
	        }else if(status == IN_DOC)
		    fprintf(outfile,"%s", mac_end_doc);
		status = IN_O;
		oldp = store_buf(infile,old_buf);
		cp = &(old_buf[oldp][1]);
	    }
	    
	    if((n = is_command(cp, Pchar_new)) != 0){
		if(status == IN_LANG){
		   fprintf(outfile, "%s%s%s%s\n",
			   mac_end_lang, mac_begin_arg,
			   langname, mac_end_arg);
	        }else if(status == IN_DOC)
		    fprintf(outfile,"%s", mac_end_doc);
		status = IN_N;
		newp = store_buf(infile,new_buf);
		cp = &(new_buf[newp][1]);
	    }

	    if((n = is_command(cp, Pchar_lang)) != 0){
		if(status == IN_LANG){
		    if(doconlymode != TRUE)
			fprintf(outfile, "%s%s%s%s\n",
			   mac_end_lang, mac_begin_arg,
			   langname, mac_end_arg);
	        }else if(status == IN_DOC)
		    fprintf(outfile,"%s", mac_end_doc);
		else if((status == IN_O) || (status == IN_N)){
		    if(doconlymode != TRUE)
			output_sec(outfile,old_buf,oldp,new_buf,newp);
		}
		cp += n;
		while(isblank(*cp)) cp++;
		cp = proc_str(cp, langname);
		
		status = IN_LANG;
		if(doconlymode != TRUE)
		    fprintf(outfile, "%s%s%s%s\n",
			mac_begin_lang, mac_begin_arg,
			langname, mac_end_arg);
	    }
	    else if((n = is_command(cp, Pchar_end_sec)) != 0){
		if(doconlymode != TRUE){
		    if(status == IN_LANG){
			fprintf(outfile, "%s%s%s%s\n",
			   mac_end_lang, mac_begin_arg,
			   langname, mac_end_arg);
		    }
		    output_sec(outfile,old_buf,oldp,new_buf,newp);
	        }
		fprintf(outfile,"%s", mac_end_sec);
		if(verbflag) print_end_sec();
		return;
	    }
	    else error(ERROR, "Unexpected command", cp);
				
	}
    }
    
    error(ERROR, "Unexpected end of file",cp);
    
}/* end of proc_sec() */

int search_tag(cp)
char *cp;
{
    int lp = tagptr;
    
    --lp;
    
    while(lp > 0)
	{
	    if(strcmp(cp,tags[lp].s) == 0)
		return lp;
	    else lp--;
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
	    fprintf(outfile, "%s", mac_before_tag);
	    lp = tags[tagp].nxt;
	    while(incltext[lp].nxt != 0)
		{
		    fprintf(outfile, "%s", incltext[lp].s);
		    lp++;
		}
	    fprintf(outfile, "%s", incltext[lp].s);
	    fprintf(outfile, "%s", mac_after_tag);
	}
    
    
}/* end of proc_tag() */
