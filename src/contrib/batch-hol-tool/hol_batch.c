/* hol_batch.c */

/* This program can be used to run a HOL session in a non-interactive manner */
/* to produce the output which would have appeared on the terminal if the    */
/* same input had been given in an interactive session.                      */
/*                                                                           */
/* A UNIX command of the form                                                */
/*                                                                           */
/*    hol_batch input.ml                                                     */
/*                                                                           */
/* is expanded to                                                            */
/*                                                                           */
/*    (hol <input.ml) | (hol_merge -p '#' input.ml)                          */
/*                                                                           */
/* by this program.                                                          */
/*                                                                           */
/*    hol_batch input.ml results                                             */
/*                                                                           */
/* expands to                                                                */
/*                                                                           */
/*    (hol <input.ml) | (hol_merge -p '#' input.ml >results)                 */
/*                                                                           */
/* If the HOL session uses a prompt other than '#', the prompt used must be  */
/* specified using the -p option to hol_batch. The names of the HOL          */
/* executable and the merge program to be used can also be changed from the  */
/* defaults above using the -h and -m options respectively.                  */
/*                                                                           */
/* If the size of the expanded command line exceeds `command_line_size' the  */
/* program is likely to fail in an unpleasant manner. The code does NOT      */
/* check that the call to allocate storage for the command line succeeded.   */
/*                                                                           */
/* This code can be compiled using the UNIX command                          */
/*                                                                           */
/*    cc -o hol_batch hol_batch.c                                            */


#include <stdio.h>
#include <string.h>

#define main_program       "hol"
#define merge_program      "hol_merge"
#define default_prompt     "#"
#define command_line_size  256


main(argc, argv)
int argc;
char *argv[];
{
     extern int optind;
     extern char *optarg;
     FILE *fp, *fopen();
     int errflg, c;
     char *call, *calloc(), *main, *merge, *prompt;

     main = main_program;
     merge = merge_program;
     prompt = default_prompt;
     errflg = 0;
     while ((c = getopt(argc, argv, "?p:h:m:")) != -1)
          switch (c) {
          case 'p':
               prompt = optarg;
               break;
	  case 'h':
               main = optarg;
               break;
	  case 'm':
               merge = optarg;
               break;
          case '?':
               errflg++;
	     }
     if ((argc > (optind + 2)) || (argc < (optind + 1)))
          errflg++;
     if (errflg) {
          (void)fprintf(stderr,"usage:\n");
          (void)fprintf(stderr,"%s [-p prompt] [-h hol_exec] ", argv[0]);
          (void)fprintf(stderr,"[-m merge_exec] input_file [output_file]\n");
          exit (2);
	}
     if ((fp = fopen(argv[optind], "r")) == NULL) {
          (void)fprintf(stderr,
                        "%s: can't open %s\n", argv[0], argv[optind]);
          exit (2);
        }
     else
          fclose(fp);
     if (argc > (optind + 1)) {
          if ((fp = fopen(argv[optind + 1], "w")) == NULL) {
               (void)fprintf(stderr,
                             "%s: can't open %s\n", argv[0], argv[optind + 1]);
               exit (2);
	     }
          else
               fclose(fp);
	}
     call = calloc(command_line_size,sizeof(char));               
     strcpy(call,"(");
     strcat(call,main);
     strcat(call," <");
     strcat(call,argv[optind]);
     strcat(call,") | (");
     strcat(call,merge);               
     strcat(call," -p '");
     strcat(call,prompt);
     strcat(call,"' ");
     strcat(call,argv[optind]);
     if (argc > (optind + 1)) {
          strcat(call," >");
          strcat(call,argv[optind + 1]);
	}
     strcat(call,")");
     system(call);
     free(call);
   }



