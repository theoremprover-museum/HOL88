

/*       XHOLHELP: THE HOL DOCUMENTATION BROWSER       */
/*                                                     */
/*                           - Sara Kalvala            */
/*                           University of Cambridge   */
/*                           Computer Laboratory       */
/*                           (sk@cl.cam.ac.uk)         */
/*                           August, 1991              */


#include <stdio.h>


#include <X11/Xatom.h>
#include <X11/Intrinsic.h>
#include <X11/StringDefs.h>
#include <X11/Shell.h>


#include <X11/Xaw/AsciiText.h>
#include <X11/Xaw/Box.h>
#include <X11/Xaw/Command.h>
#include <X11/Xaw/Dialog.h>
#include <X11/Xaw/Paned.h>
#include <X11/Xaw/Label.h>
#include <X11/Xaw/List.h>
#include <X11/Xaw/Toggle.h>
#include <X11/Xaw/Form.h>

#include <X11/Xmu/Atoms.h>
#include <X11/Xmu/StdSel.h>


#include <X11/Xaw/Cardinals.h>
#include <X11/cursorfont.h>

#include "xholhelp.h"

void Quit(), doA(), doR(), doT(), Help(), ClearD(), ScrollF(), ScrollB(),
     ShowData(), busyCursor(), unbusyCursor(), PrintOut(), AppendD();


String fallback_resources[] = { 
  "xholhelp.height: 400",
  "xholhelp.width: 600",
  "*showGrip: False",
  "*font: 7x13bold",

/* dialog box */
  "*dialog.label.height: 2",
  "*dialog.label: ",
  "*dialog.value: ",
  "*dialog.value.translations:  #override \\n  <Key>Escape: doR() \\n \
  <Key>Return: doA() \\n <Key>Tab: doT() \\n Ctrl<Key>L: ClearD() \\n \
                Ctrl<Key>V: ScrollF() \\n Ctrl<Key>N: ScrollF() \\n \
                Meta<Key>V: ScrollB() \\n Ctrl<Key>P: ScrollB() \\n",
  "*Dialog.value.width: 350",
  "*Dialog.value.height: 20",

/* command buttons */
  "*Command.height: 20",

/* box for text - default is help */
  "*text*type: file",
  "*text*string: HELPFILE",
  "*text*scrollVertical: always",
  "*text*displayCaret: False",
  "*text*translations: #override  \\n  <Key>Escape: doR() \\n \
                         <Key>Return: doA() \\n <Key>Tab: doT() \\n \
                Ctrl<Key>V:ScrollF() \\n Ctrl<Key>N: ScrollF() \\n \
                Meta<Key>V:ScrollB() \\n Ctrl<Key>P: ScrollB() \\n \
                 Ctrl<Key>L: ClearD() ",
NULL, };

XtActionsRec actionTable[] = {
    {"doA",	doA},
    {"doT",	doT},
    {"doR",	doR},
    {"ScrollF", ScrollF},
    {"ScrollB", ScrollB},
    {"AppendD", AppendD},
    {"ClearD",  ClearD}
};

/*<Btn2Down>: AppendD() \\n*/

  Widget holapropos, outer, dialog, quit, help, apropos, printout,
         entry, theorems, clear, scrollf, scrollb, alltext;
  XtAppContext helptool;



/* ***************************** */
void main (argc, argv)
     int argc;
     char **argv;
{
  Arg args[10];

/* first set up the window */

  holapropos = XtAppInitialize(&helptool, "xholhelp", NULL, ZERO, &argc,
			       argv, fallback_resources, NULL, ZERO);

  outer = XtCreateManagedWidget("frame", panedWidgetClass, holapropos,
				  NULL, ZERO);

/* dialog box and associated buttons */

  dialog = XtCreateManagedWidget("dialog", dialogWidgetClass,
				 outer, NULL, ZERO);

  quit = XtCreateManagedWidget( "quit", commandWidgetClass,
			       dialog, NULL, ZERO);
  XtAddCallback( quit, XtNcallback, Quit, NULL);


  help = XtCreateManagedWidget( "help", commandWidgetClass,
			       dialog, NULL, ZERO);
  XtAddCallback( help, XtNcallback, Help, NULL);


  apropos = XtCreateManagedWidget( "apropos", commandWidgetClass,
				  dialog, NULL, ZERO);
  XtAddCallback( apropos, XtNcallback, doA, NULL);


  entry = XtCreateManagedWidget( "reference", commandWidgetClass,
				dialog, NULL, ZERO);
  XtAddCallback( entry, XtNcallback, doR, NULL);


  theorems = XtCreateManagedWidget( "theorems", commandWidgetClass,
				   dialog, NULL, ZERO);
  XtAddCallback( theorems, XtNcallback, doT, NULL);


  clear = XtCreateManagedWidget( "clear", commandWidgetClass,
				dialog, NULL, ZERO);
  XtAddCallback( clear, XtNcallback, ClearD, NULL);

  scrollf = XtCreateManagedWidget( "forward", commandWidgetClass,
				dialog, NULL, ZERO);
  XtAddCallback( scrollf, XtNcallback, ScrollF, NULL);

  scrollb = XtCreateManagedWidget( "backward", commandWidgetClass,
				dialog, NULL, ZERO);
  XtAddCallback( scrollb, XtNcallback, ScrollB, NULL);

  printout = XtCreateManagedWidget( "print", commandWidgetClass,
				dialog, NULL, ZERO);
  XtAddCallback( printout, XtNcallback, PrintOut, NULL);

/* text box, for output */

  alltext = XtCreateManagedWidget( "text", boxWidgetClass,
				  outer, NULL, ZERO);


/* infinite loop */

  XtAppAddActions(helptool, actionTable, XtNumber(actionTable));
  XtSetKeyboardFocus(outer,dialog);
  XtRealizeWidget(holapropos);
  XtAppMainLoop(helptool);
}


void Quit()
{
  exit(0);
}

void ClearD()
{
  Arg wargs[10];

  XtSetArg(wargs[0], XtNvalue, "");
  XtSetValues(dialog, wargs, 1);
 }

void AppendD()
{
  Arg wargs[10];
char tempdialog[BUFSIZ];
int nbytes;

char *sel_value = XFetchBuffer(XtDisplay(outer), &nbytes, 0);



strcpy(tempdialog,  XawDialogGetValueString(dialog));
strcat(tempdialog,sel_value);

nbytes = strlen(tempdialog);

  XtSetArg(wargs[0], XtNvalue, tempdialog);
  XtSetArg(wargs[1], XtNinsertPosition, nbytes-1);

  XtSetValues(dialog, wargs, 2);

 }

void doA()
{
  char callsed[BUFSIZ], tempd[BUFSIZ];
  FILE *fin, *popen();

strcpy(tempd, XawDialogGetValueString(dialog));

if (strlen(tempd) == 0)
  {Arg wargs[10];
   XtDestroyWidget(alltext);
   XtSetArg(wargs[0], XtNtype, XawAsciiString);
   XtSetArg(wargs[1], XtNstring, (XtArgVal) EMPTY_DIALOG);
   alltext =  XtCreateManagedWidget("text", asciiTextWidgetClass,
				    outer, wargs, 2) ;
   return;
 }

  busyCursor();

  strcpy(callsed, BIN);
  strcat(callsed, "hol_apro ");
  strcat(callsed, tempd);

  if ((fin = popen(callsed,"r")) == NULL)
    {
      fprintf(stderr, "cant run"); exit(1);
    }

  ShowData(fin);

  unbusyCursor();

  if (pclose(fin) == -1) fprintf (stderr, "didnt close\n");

}


void doR()
{
  char callsed[BUFSIZ], tempd[BUFSIZ];
  FILE *fin, *popen();

strcpy(tempd, XawDialogGetValueString(dialog));

if (strlen(tempd) == 0)
  {Arg wargs[10];
   XtDestroyWidget(alltext);
   XtSetArg(wargs[0], XtNtype, XawAsciiString);
   XtSetArg(wargs[1], XtNstring, (XtArgVal) EMPTY_DIALOG);
   alltext =  XtCreateManagedWidget("text", asciiTextWidgetClass,
				    outer, wargs, 2) ;
   return;
 }

  busyCursor();

  strcpy(callsed, BIN);
  strcat(callsed, "hol_ref ");
  strcat(callsed, tempd);

  if ((fin = popen(callsed,"r")) == NULL)
    {
      fprintf(stderr, "cant run"); exit(1);
    }

  ShowData(fin);

unbusyCursor();

  if (pclose(fin) == -1) fprintf (stderr, "didnt close\n");


}

void doT()
{
  char callsed[BUFSIZ];
  FILE *fin, *popen();

  busyCursor();

  strcpy(callsed, BIN);
  strcat(callsed, "hol_thm \"");
  strcat(callsed,  XawDialogGetValueString(dialog));
  strcat(callsed, "\"");

  if ((fin = popen(callsed,"r")) == NULL)
    {fprintf(stderr, "cant run"); return;}

  ShowData(fin);
  unbusyCursor();

  if (pclose(fin) == -1) fprintf (stderr, "didnt close\n");
}

void PrintOut()
{
  char callshell[BUFSIZ];
  FILE *fin, *popen();
  Arg wargs[1];
  char *data;

XtSetArg (wargs[0], XtNstring, &data);
XtGetValues (XawTextGetSource (alltext), wargs, 1);


if (getenv("HOL_PRINT_CMD") != NULL)
  {
    strcpy(callshell, getenv("HOL_PRINT_CMD"));
    if ((fin = popen(callshell,"w")) == NULL)
      {fprintf(stderr, "cant run"); return;}
    fprintf(fin, "%s\n", data);
    if (pclose(fin) == -1)
      fprintf (stderr, "didnt close\n");
  }
}

void Help()
{ Arg wargs[1];

  XtDestroyWidget(alltext);

  XtSetArg(wargs[0], XtNstring, (XtArgVal) HELPFILE);

  alltext = XtCreateManagedWidget("text", asciiTextWidgetClass,
				  outer, wargs, 1) ;
}


void ScrollF()
{
    XtCallActionProc(alltext, "next-page", 0, 0, 0);
    return;
}

void ScrollB()
{
    XtCallActionProc(alltext, "previous-page", 0, 0, 0);
    return;
}

/* **************** Auxiliary Functions ***************** */


void ShowData(file)
FILE *file;
{
  char *data;		/* pointer to the data stored
			   in dynamic memory */
  int num_bufs;
  char eachstring[MAXLEN];
  Arg wargs[10];
/*  char new_data; */

  XtDestroyWidget(alltext);
  XtSetArg(wargs[0], XtNtype, XawAsciiString);

/*
 * Get file size and allocate a chunk of memory for the file to be 
 * copied into.
 */

  if ((data = (char *)malloc(BUFSIZ)) == NULL)
    {
      XtSetArg(wargs[1], XtNstring, (XtArgVal) NOT_ENUF);
      alltext =  XtCreateManagedWidget("text", asciiTextWidgetClass,
				       outer, wargs, 2) ;
      return;
    }

  num_bufs = 1;
  strcpy(data,"");

  while (fgets (eachstring, MAXLEN, file) != NULL)
    {
      if (strlen(data) + strlen(eachstring) > (num_bufs * BUFSIZ))
	if ((data = (char *)realloc(data, (BUFSIZ * ++num_bufs))) == NULL)
	  {
	    XtSetArg(wargs[1], XtNstring, (XtArgVal) NOT_ENUF);
	    alltext =  XtCreateManagedWidget("text", asciiTextWidgetClass,
					     outer, wargs, 2) ;
	    return;
	  }
      strcat(data, eachstring);
    }

/* bug when data is of less than 500 bytes ?!?!?! */
/* strcat(data,"\n");
strcat(data,"   \n");  */

/* if (strlen(data) < BUFSIZ) */

/* new_data = XtNewString(data);  */

  XtSetArg(wargs[1], XtNstring, (XtArgVal)/* new_*/ data);

  alltext =  XtCreateManagedWidget("text", asciiTextWidgetClass,
				   outer, wargs, 2) ;
strcpy(data,"");

}

void busyCursor()
{
  static Cursor busyCursor = (Cursor) 0;
    
  /* define an appropriate busy cursor */
	busyCursor = XCreateFontCursor(XtDisplay(holapropos), XC_watch);

  XDefineCursor(XtDisplay(holapropos), XtWindow(dialog), busyCursor);
  XDefineCursor(XtDisplay(holapropos), XtWindow(alltext), busyCursor);
  XFlush(XtDisplay(holapropos));
    
  return;
}


void unbusyCursor()
{
  static Cursor unBusyCursor = (Cursor) 0;
  static Cursor textCursor = (Cursor) 0;

	unBusyCursor = XCreateFontCursor(XtDisplay(holapropos), XC_left_ptr);
        textCursor = XCreateFontCursor(XtDisplay(holapropos), XC_xterm);

  XDefineCursor(XtDisplay(holapropos), XtWindow(dialog), unBusyCursor);
  XDefineCursor(XtDisplay(holapropos), XtWindow(alltext), textCursor);
  XFlush(XtDisplay(holapropos));
    
  return;
}
