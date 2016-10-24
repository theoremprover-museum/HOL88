/* hol_merge.c */

/* This program takes the output from running a HOL session and merges it    */
/* with the input file. The result appears exactly as if the input had been  */
/* given to HOL interactively. For example, executing the UNIX commands      */
/*                                                                           */
/*    hol <input.ml >output                                                  */
/*    hol_merge input.ml <output >results                                    */
/*                                                                           */
/* creates a file `output' with the output from the HOL session, but the     */
/* input to HOL does not appear. `results' does contain the input to the     */
/* session.                                                                  */
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
/*    cc -o hol_merge hol_merge.c                                            */


#include <stdio.h>

#define default_prompt "#"


int inchar;


main(argc, argv)
int argc;
char *argv[];
{
     extern int optind;
     extern char *optarg;
     FILE *fp, *fopen();
     int errflg, c;
     char *prompt;

     prompt = default_prompt;
     errflg = 0;
     while ((c = getopt(argc, argv, "?p:")) != -1)
          switch (c) {
          case 'p':
               prompt = optarg;
               break;
          case '?':
               errflg++;
	     }
     if (optind != (argc - 1))
          errflg++;
     if (errflg) {
          (void)fprintf(stderr,
                        "usage: %s [-p prompt] ML_source_file\n", argv[0]);
          exit (2);
	}
     if ((fp = fopen(argv[optind], "r")) == NULL) {
          (void)fprintf(stderr, "%s: can't open %s\n", argv[0], argv[optind]);
          exit (2);
	}
     inchar = '\n';
     while (inchar != EOF) {
          while (matchprompt(prompt))
               while ((c = getc(fp)) != EOF)
                    if (putchar(c) == '\n')
                         break;
          while ((inchar != EOF) && (inchar != '\n'))
               if (putchar(inchar = getchar()) == '\n')
                    break;
	}
     fclose(fp);
   }


matchprompt(s)
char *s;
{
     int l;

     l = 0;
     while (s[l] != '\0') {
          if (inchar != EOF) {
               if (putchar(inchar = getchar()) != s[l++])
                    return(0);
	     }
          else
               return(0);
	}
     return(1);
   }

