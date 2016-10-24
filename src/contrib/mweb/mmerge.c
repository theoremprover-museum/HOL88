/*
  FILE: mmerge.c
  DATE: April 1993
  AUTHOR: Brian Graham (based on RJB's hol_merge pprogram)

Copyright (C) 1993  Brian Graham

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


/* starting from rjb's hol_merge program, this program now is used for the   */
/* putting together of tag files to be used with ww's mtangle, mweave, and   */
/* btg's winnow utilities.                                                   */

/* This program takes the output from running a HOL session and merges it    */
/* with the input file. The result appears exactly as if the input had been  */
/* given to HOL interactively. For example, executing the UNIX commands      */
/*                                                                           */
/*    hol <input.ml >output                                                  */
/*    mmerge input                                                           */
/* assumes the presence of input.ml input.log and produces input.tag         */
/*                                                                           */
/* The program works by detecting any occurrence of the HOL prompt at the    */
/* beginning of a line in `output'. At such an occurrence a line is read     */
/* from `input.ml' and inserted after the prompt. If the first prompt is     */
/* followed immediately by another prompt on the same line, it is treated in */
/* the same way, and so on until a non-prompt is found. The rest of the line */
/* is then copied to the output without modification.                        */
/*                                                                           */
/* The default HOL prompt is '#' and this is what hol_merge looks for unless */
/* told to do otherwise via the -p option on the command line. The argument  */
/* for -p may need to be quoted.                                             */
/*                                                                           */
/* This code can be compiled using the UNIX command                          */
/*                                                                           */
/*    cc -o mmerge mmerge.c                                                  */


#include <stdio.h>
#include <string.h>

#define default_prompt  "#"
#define mlsuffix	".ml"
#define logsuffix	".log"
#define tagsuffix	".tag"
#define eoln 		"\n"
#define holcomment 	"%"
#define hollabcomment 	"%-"
#define hidemark 	"$"
#define startlabel 	"{"
#define finishlabel 	"}"

/* ----------------------new source ----------------------------*/
#define MAXLINELEN 160
#define MAXFNAMELEN 40
/* ----------------------end of new----------------------------*/


int inchar;

/* ----------------------new source ----------------------------*/
char logbuf[MAXLINELEN];
char mlbuf[MAXLINELEN];
char mlinfilename[MAXFNAMELEN] = "";
char lginfilename[MAXFNAMELEN] = "";
char outfilename[MAXFNAMELEN] = "";

void error(s,cp)
char *s, *cp;
{
    fprintf(stderr,"\s\s\n",s,cp);
    exit(2);
}

void debug(m,v)
char *m, *v;
{
    fprintf (stderr, "%s %s\n", m, v);
    return;
}

int is_string_match(s1,s2)
    char *s1, *s2;
{
    int nn = 0;

    while((s2 != '\0') && (s1 != '\0'))
	{
	    if (*s1 == *s2)
		{
		    s1++; s2++; nn++;
		    if(*s2 == '\0') return(nn);
		}
	    else
		return (0);
	}
    return(0);
}



/* ----------------------end of new----------------------------*/


main(argc, argv)
int argc;
char *argv[];
{
     extern int optind;
     extern char *optarg;
/*      FILE *fml, *flg, *fopen();   */
     int errflg, c;

     char *prompt;
/* ----------------------new source ----------------------------*/
     FILE *fml, *flg, *outfile, *fopen();
     char *cp, *lgp, *tp, *mlp;
     int n, m, new, in_comment, hidden, start_flag, hold_blank;
/* ----------------------end of new----------------------------*/

     prompt = default_prompt;
     errflg = 0;
     while ((c = getopt(argc, argv, "?hHp:")) != -1)
          switch (c) {
          case 'p':
               prompt = optarg;
               break;
	     case '?': case 'h': case 'H':
               errflg++;
	     }

     if ((optind) != (argc-1))
	 errflg++;

     if (errflg)
	 {
	     fprintf(stderr,"usage: %s [-p prompt] [-hH] ML_source_file_stem\n", argv[0]);
	     exit(2);
	 }

     strcpy (mlinfilename,argv[optind]);
     if ((cp = strrchr(mlinfilename, (int)'.')) == NULL)
	 {
	     strcpy(lginfilename,mlinfilename);
	     strcpy(outfilename,mlinfilename);
	     strcat(mlinfilename, mlsuffix);
	     strcat(lginfilename, logsuffix);
	     strcat(outfilename, tagsuffix);
	     if ((fml = fopen(mlinfilename,"r")) == NULL)
		 error("cannot open ml input file %s", mlinfilename);
	     if ((flg = fopen(lginfilename,"r")) == NULL)
		 error("cannot open log input file %s", lginfilename);
	     if ((outfile = fopen(outfilename,"w")) == NULL)
		 error("cannot open output file %s", outfilename);

	     fprintf(stderr,"input ml file is  %s\n", mlinfilename);
	     fprintf(stderr,"input log file is %s\n", lginfilename);
	     fprintf(stderr,"output file is    %s\n", outfilename);
	 }
     else
	 {
	     if ((fml = fopen(mlinfilename,"r")) == NULL)
		 error("cannot open ml input file ", mlinfilename);
	     flg = stdin;
	     outfile = stdout;

	     fprintf(stderr,"input ml file is  %s\n", mlinfilename);
	     fprintf(stderr,"input log file is stdin\n");
	     fprintf(stderr,"output file is    stdout\n");
	 }
     




     if ((mlp = fgets(mlbuf, (MAXLINELEN-1), fml)) == NULL)
	 {
	     error("ml file is empty");
	 }
     in_comment = 0;	/* processing multi line comment */
     hidden = 0;	/* processing hidden hol commands */
     start_flag = 1;	/* before doing first tag section */
     hold_blank = 0;	/* blank line from log file pending being outuput */
     
     while ((lgp = fgets(logbuf, (MAXLINELEN-1), flg)) != NULL)
	 {

	     new = 1;

   	     while ((n=is_string_match(lgp,prompt)) != 0)
		 {
		     lgp += n;
		     					/* finishing off comment */
		     if (in_comment)
			 {
			     in_comment = (strstr(mlp,holcomment) == NULL);
			     fprintf(outfile, "%s", mlp);
			     mlp = fgets(mlbuf, (MAXLINELEN-1), fml);
			 }
		     					/* ignoring blank lines */
		     else if ((m=is_string_match(mlp,eoln)) != 0)
			 {
			     mlp = fgets(mlbuf, (MAXLINELEN-1), fml);
			 }
		     					/* source begins a section comment */
		     else if ((m=is_string_match(mlp,hollabcomment)) != 0)
			 {
			     if ((mlp=strstr(mlp,startlabel)) == NULL)
				 error("section command missed `{'");
			     if ((tp = strstr(mlp,finishlabel)) == NULL)
				 error("section command missed `}'");
			     if (start_flag)
				 start_flag = 0;
			     else
				 {
				     fprintf(outfile, "@e\n\n");
				     hold_blank = 0;
				 }
			     hidden = is_string_match((mlp + 1),hidemark);
			     *(++tp) = '\0';
			     fprintf(outfile,"@t%s\n",mlp);
			     mlp = fgets(mlbuf, (MAXLINELEN-1), fml);
			 }
		     					/* ordinary comment starts */
		     else if ((m=is_string_match(mlp,holcomment)) != 0)
			 {
			     if (hold_blank)
				 {
				     hold_blank = 0;
				     fprintf(outfile, eoln);
				 }
			     fprintf(outfile,"%s\n",mlp);
			     in_comment = (strstr(++mlp,holcomment) == NULL);
			     mlp = fgets(mlbuf, (MAXLINELEN-1), fml);

			 }
		     					/* a command */
		     else
			 {
			     if (hold_blank)
				 {
				     hold_blank = 0;
				     fprintf(outfile, eoln);
				 }
			     if (new  && (hidden == 0))
				 {
				     fprintf(outfile,"%s",prompt);
				     new = 0;
				 }
			     fprintf(outfile,"%s",mlp);
			     mlp = fgets(mlbuf, (MAXLINELEN-1), fml);
			 }
		 }
	     					/* system output instead */
	     if (hidden == 0)
		 {
		     if (is_string_match(lgp,eoln))
			 {
			     if (hold_blank)
				 {
				     fprintf(outfile,lgp);
				 }		/* avoid blank in first hidebox */
			     else if (start_flag == 0) hold_blank = 1;
			 }
		     else
			 {
			     if (hold_blank)
				 {
				     fprintf(outfile,eoln);
				     fprintf(outfile,lgp);
				     hold_blank = 0;
				 }
			     else
				 fprintf(outfile,lgp);
			 }
		 }
	 }
			     
     fprintf(outfile, "@e\n");			/* close of the last tag */

     exit(0);	/* automatically calls fclose for all files */
 }
