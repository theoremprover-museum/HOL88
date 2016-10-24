/*
  FILE: mtangle.c --- generate ML output
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


char mtangleVersion[] = "2.0";

#include <stdio.h>
#include <string.h>

#include "mweb.h"

char *ml_comm_begin = paratab[Pml_comm_begin].pval;
char *ml_comm_end = paratab[Pml_comm_end].pval;

#define NEW 1
#define LANG 2
#define DONENEW 3
#define DONELANG 4

char secbuf[MAXLINELEN];

void proginit()
{
    program = TANGLE;
    outsuffix = paratab[Poutsuffixmtangle].pval ;
}


void proc_sec(infile,outfile,line)
FILE *infile,*outfile;
char *line;
{
    char *cp;
    int status, n;

    strcpy(secbuf,line);
    if((cp = strchr(secbuf, (int)('\n'))) != NULL)
	*cp = '\0'; 
    
    ++seccount;    
    if(verbflag) fprintf(stderr,"[%d", seccount);

    status = NULL;
    langname[0] = '\0';

    while((cp = fgets(inbuf, MAXLINELEN, infile)) != NULL){
	linecount++;

	if((n = is_command(cp, Pchar_cmd)) != 0){
	    cp += n;
		    
	    if ((n = is_command(cp, Pchar_new)) != 0){
		if((status == NEW) || (status == DONENEW))
		    error(ERROR, "Unexpected command: already in a section", cp);
		else if(status == LANG)
		    status = DONELANG;
		else if((status == NULL) && (*tangle_lang == '\0')){
		    status = NEW;
		    fprintf(outfile,"%s %d.%d ",ml_comm_begin, linecount,seccount);
		    if(secbuf[1] == *char_begin_para)
			fprintf(outfile,"%s ", &(secbuf[1]));
		    fprintf(outfile,"%s\n", ml_comm_end);
		}
	    }
	    else if ((n = is_command(cp, Pchar_end_sec)) != 0){
		status = NULL;
		fprintf(outfile,"\n"); 
		if(verbflag) {
		    print_end_sec();
		}
		return;
	    }
	    else if ((n = is_command(cp, Pchar_lang)) != 0){
		cp += n;
		while(isblank(*cp)) cp++;
		cp = proc_str(cp, langname);

		if(status == NEW) status = DONENEW;
		else if(status == LANG) status = DONELANG;
		else if(status == NULL){
		    if((*tangle_lang != '\0') &&
		       (strcmp(langname, tangle_lang) == 0)){
			status = LANG;
			fprintf(outfile,"%s %d.%d ",ml_comm_begin, linecount, seccount);
			if(secbuf[1] == *char_begin_para)
			    fprintf(outfile,"%s ", &(secbuf[1]));
			fprintf(outfile,"%s\n", ml_comm_end);
		    }
		}
	    }
	    else if ((is_command(cp, Pchar_old) == 0) &&
		     (is_command(cp, Pchar_begin_tag) == 0))
		error(ERROR,"Unexpected command: not allowed in a section", cp);
	}
	else if((status == NEW) || (status == LANG))
	    fprintf(outfile,"%s",inbuf);
	else if(linemode == TRUE)
	    fprintf(outfile,"\n");
    }
    
    error(ERROR,"Unexpected end of file",cp);
    
}/* end of proc_sec() */

