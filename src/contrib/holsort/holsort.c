/* holsort produces alphabetically-ordered versions of files containing
lists of HOL axioms, theorems, definitions, or constants with
associated type declarations.  Useful files for it to sort can be
prepared with the UNIX command script and the HOL commands
print_theory, axioms, theorems, and so on.

Specifically, holsort interprets an input file as a list of items and
produces an output file containing these items separated by blank
lines and in alphabetical order.  It takes an item to be an (optional)
label, followed by text delimited by parentheses or double-quote marks,
followed by (optional) text, followed by a new-line character.  It
takes an (optional) flag argument that determines whether it uses
parentheses (-p) or double-quote marks (-q) as delimiters, using
parentheses if this flag is omitted.  Invoke holsort with

     holsort <filename>
     holsort -p <filename>       or
     holsort -q <filename> .

Under normal conditions, holsort produces a sorted output file having
the name of its input file with ".sort" appended.  If the input file
does not contain a final new-line character, holsort adds one after the
corresponding item in the sorted file.  Under error conditions, holsort
prints a descriptive message to stderr, including the appropriate
line-number in the input file if there is one, but has no further
effect.

Compile holsort with the command: cc -O -o holsort holsort.c  */

static char copyright[] = "Copyright 1992 by ORA Corporation.";

/* Permission to use, copy, modify, and distribute this software and
its documentation for any purpose and without fee is hereby granted,
provided that the above copyright notice appear in all copies.  ORA
Corporation makes no representations about the suitability of this
software for any purpose.  It is provided "as is" without express or
implied warranty.  */

#include <stdio.h>
#define MAXNAME 100

typedef struct item {
  long int
    start;          /* start position of item in file */
  struct item
    *pnext,         /* next element of doubly-linked list */
    *plast;         /* last element of doubly-linked list */
  } ITEM,*PITEM;

static char
  cannotopeninerror[] =
"Unable to open %s for input;  check spelling\n",
  cannotopenmiderror[] =
"Unable to open file for intermediate output\n",
  cannotopenouterror[] =
"Unable to open file for final output\n",
  twoitemsonlineerror[] =
"Two items on one input line, file %s, line number %d\n",
  unexpectedeoferror[] =
"End of file before end of item, file %s\n";

char
  startname[MAXNAME],  /* name of input file */
  midname[MAXNAME],    /* name of intermediate output file */
  endname[MAXNAME];    /* name of final output file */
FILE
  *fin,               /* pointer to inuput file */
  *fmid,              /* pointer to intermediate output file */
  *fout;              /* pointer to final output file */

void tilt();           /* error exit routine */

void main(argc,argv)
int argc;
char *argv[];
{
char
  *flag,               /* -p or -q */
  *strcpy(),
  *strcat();
int
  numberitems,        /* number of items in input file */
  getitems();         /* separates input file into items */
void
  orderitems();       /* sorts file of items */

if(argc == 3) {
  flag = argv[1];
  (void) strcpy(startname,argv[2]);
  }
else {
  flag = "-p";
  (void) strcpy(startname,argv[1]);
  }
(void) strcpy(midname,startname);
(void) strcat(midname,".items");
(void) strcpy(endname,startname);
(void) strcat(endname,".sort");

fin = fopen(startname,"r");
if(fin == NULL) {
  tilt(cannotopeninerror,0);
  }
(void) unlink(midname);
fmid = fopen(midname,"a+");
if(fmid == NULL) {
  tilt(cannotopenmiderror,0);
  }
(void) unlink(endname);
fout = fopen(endname,"w");
if(fmid == NULL) {
  tilt(cannotopenouterror,0);
  }

numberitems = getitems(flag,fin,fmid);  /* produce item file */

(void) rewind(fmid);  /* prepare to read intermediate file */

orderitems(numberitems,fmid,fout);  /* sort item file */

(void) fclose(fin);
(void) fclose(fmid);
(void) unlink(midname);
(void) fclose(fout);
}



/* getitems produces an intermediate file of items separated by blank
lines, ignoring any blank lines or form-feeds in the input.  It takes
an item to be a (possibly empty) initial string of text, an opening
delimiter ("(" or """), a main string of text, a closing delimiter (")"
or """), and a (possibly empty) final string to the next new-line
character or the end of the input.  Its "flag" argument determines what
it takes as the delimiters.  If the input file did not end with a
new-line character, it adds this character to the final item.  It
returns the number of items found. */


int getitems(flag,infile,outfile)
char *flag;
FILE *infile,*outfile;
{
char
  c;                /* last character read */
int
  itemcount = 0,    /* number of items read */
  linenumber = 1,   /* line number in input file */
  startline = 1,    /* whether at start of line */
  startitem = 0,    /* whether start of next item read */
  count = 0;        /* # opening delimiters - # closing delimiters */

while ((c = getc(infile)) != EOF) {
  switch(c) {
  case '\n':
    if(!startline) {
      (void) putc(c,outfile);
      startline = 1;
      if(startitem && !count) {
        itemcount++;
        (void) putc('\n',outfile);  /* second newline before next item */
        count = 0;                  /* reset counts for next item */
        startitem = 0;
        }
      }
    linenumber++;
    break;

  case '(':
    (void) putc(c,outfile);
    startline = 0;
    if(flag[1] == 'p') {
      if(startitem && !count) {
        tilt(twoitemsonlineerror,linenumber);
        }
      startitem = 1;
      count++;
      }
    break;

  case ')':
    (void) putc(c,outfile);
    startline = 0;
    if(flag[1] == 'p') {
      count--;
      }
    break;

  case '\"':
    (void) putc(c,outfile);
    startline = 0;
    if(flag[1] == 'q') {
      if(startitem && !count) {
        tilt(twoitemsonlineerror,linenumber);
        }
      startitem = 1;
      count = 1 - count;
      }
    break;

  case '\f':
    break;

  default:
    (void) putc(c,outfile);
    startline = 0;
    break;
    }
  }
if(!startline) {             /* last line incomplete? */
  if(startitem && !count) {  /* if last item otherwise complete */
    (void) putc('\n',outfile);  /* complete last line */
    (void) putc('\n',outfile);  /* second newline before EOF */
    }
  else {                    /* else unexpected end of file */
    tilt(unexpectedeoferror,linenumber);
    }
  }
else {                      /* last line complete? */
  if(startitem || count) {  /* ready for next item? */
    tilt(unexpectedeoferror,linenumber);  /* if not, error */
    }
  }
return(itemcount);
}



/* orderitems takes a count of items, a pointer to a file containing
this many items separated by blank lines, and a pointer to an output
file.  It copies the input items, with their separating blank lines,
to the output file in alphabetical order. */

void orderitems(itemcount,infile,outfile)
int itemcount;
FILE *infile,*outfile;
{
char
  c,                      /* last character read */
  *malloc();
int
  i,                      /* index temporary */
  newlinecount;           /* count of consecutive '\n's */
PITEM
  itemarray,              /* array of list-element structures */
  ptemp,                  /* item pointer */
  plist,                  /* sublist pointer */
  suborder();             /* subroutine that orders sublist */

               /* create unordered, doubly-linked list of items */

itemarray = (ITEM *) malloc((unsigned) (itemcount*sizeof(ITEM)));

for(i=0; i < itemcount; i++) {             /* link all but ends */
  (itemarray+i)->pnext = itemarray + i + 1;
  (itemarray+i)->plast = itemarray + i - 1;
  }

itemarray->plast = itemarray + itemcount - 1;  /* link ends */
(itemarray+itemcount-1)->pnext = itemarray;

ptemp = itemarray;                 /* fill in file index values */
do {
  ptemp->start = ftell(infile);
  newlinecount = 0;
  while(newlinecount < 2) {
    c = getc(infile);
    if(c == '\n') {
      newlinecount++;
      }
    else {
      newlinecount = 0;
      }
    }
  ptemp = ptemp->pnext;
  } while(ptemp != itemarray);

plist = suborder(0,itemarray,infile);  /* sort list */

ptemp = plist;            /* write sorted list to output file */
do {
  (void) fseek(infile,ptemp->start,0);
  newlinecount = 0;
  while(newlinecount < 2) {
    c = getc(infile);
    (void) putc(c,outfile);
    if(c == '\n') {
      newlinecount++;
      }
    else {
      newlinecount = 0;
      }
    }
  ptemp = ptemp->pnext;
  } while(ptemp != plist);
}



/* suborder performs an alphabetical-order basket sort on the items
in a file given by pointers in a double-linked list. The input "level"
tells how many characters there are from the start of each item to the
letter to next be used to sort the items.  It returns a pointer to the
newly-sorted list. */

PITEM suborder(level,initem,file)
int level;
PITEM initem;
FILE *file;
{
char
  c;  /* character read */
int
  i;  /* integer temporary */
PITEM
  ptemp1,       /* list-element temporary */
  ptemp2,       /* list-element temporary */
  ptemp3,       /* list-element temporary */
  table[256],   /* table of sublists for each ascii character */
  suborder();   /* suborder is a recursive function */

for(i=0; i < 256; i++)
  table[i] = NULL;

ptemp1 = initem;
do {
  ptemp2 = ptemp1->pnext;
  (void) fseek(file, ptemp1->start + level, 0);
  c = getc(file);
  if(c == EOF)
    c = 'z';
  if('A' <= c && c <= 'Z')  /* ignore case */
    c += 32;
  if(table[c] == NULL) {
    table[c] = ptemp1;
    ptemp1->pnext = ptemp1;
    ptemp1->plast = ptemp1;
    }
  else {
    ptemp1->pnext = table[c];
    ptemp1->plast = table[c]->plast;
    (ptemp1->plast)->pnext = ptemp1;
    (ptemp1->pnext)->plast = ptemp1;
    }
  ptemp1 = ptemp2;
  } while(ptemp1 != initem);

ptemp2 = NULL;
for(i=0; i < 256; i++) {
  ptemp1 = table[i];
  if(ptemp1 != NULL) {
    if(ptemp1->pnext != ptemp1)
      ptemp1 = suborder(level+1,ptemp1,file);
    if(ptemp2 == NULL)
      ptemp2 = ptemp1;
    else {
      (ptemp2->plast)->pnext = ptemp1;
      (ptemp1->plast)->pnext = ptemp2;
      ptemp3 = ptemp2->plast;
      ptemp2->plast = ptemp1->plast;
      ptemp1->plast = ptemp3;
      }
    }
  }

return(ptemp2);
}



/* tilt prints out an error message identifying a problem and
(possibly) the line number in the input file at which the problem
arose.  If then closes any open files and deletes any intermediate and
final output files. */

void tilt(problem,linenumber)
char *problem;
int linenumber;
{
void exit();

(void) fprintf(stderr,problem,startname,linenumber);

(void) fclose(fin);
(void) fclose(fmid);
(void) fclose(fout);
(void) unlink(midname);
(void) unlink(endname);
exit(1);
}
