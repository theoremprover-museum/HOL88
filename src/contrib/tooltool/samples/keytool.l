.TH SETWIN 1 "8 December 1988"
.SH NAME
keytool \- terminal emulator with interactively redefineable function keys
.SH SYNOPSIS
\fBkeytool\fP [\fB\(hyi\fP \fIinit_file\fP] \fIcommand\fP [\fIargs\fP]
.SH DESCRIPTION
.LP
\f2Keytool\fP is an interactive terminal emulator built with \f2tooltool\fP(1).
It provides a tty subwindow environment similar to \f2shelltool\fP(1) for executing
interactive commands.  This is very useful for running shell programs both locally
(such as \f2ssh\fP(1)) and remotely (using \f2rlogin\fP(1), or 
\f2telnet\fP(1). 
.LP
\f2Keytool\fP behaves very much like \f2shelltool\fP(1).
Keystrokes typed to \f2keytool\fP are passed to the program specified in \fIcommand\fP.
(\fICommand\fP must specify the full pathname of the program.)
If this program is a shell, it accepts commands and runs programs in the usual way.
Any shelltool-like window arguments may be specified in \fIargs\fP.
These are processed by tooltool and not sent to \fIcommand\fP. Any other \fIargs\fP
are passed to the program.
.LP
\f2Keytool\fP accepts one command line option of its own, \fB\(hyi\fP, and this must be first
in the command line. Its argument, \fIinit_file\fP, specifies the initial filename
\f2keytool\fP will read for function key definitions.  The default is 
~/.keytool if it exists, and /usr/local/lib/keytool.defaults if not.
.LP
\f2Keytool\fP allows definition of the function keys L2-L4, L9-L10, F1-F9, 
and R1-R15 with any combinations of CONTROL, SHIFT, and META.  It also 
allows definition of any shifted combinations of the three mouse buttons 
except for one.  CONTROL-SHIFT-META-RIGHT_MOUSE brings up the \f2keytool\fP
menu that is described below.  The unshifted mouse buttons behave as in any
tty subwindow: select, adjust, and tty subwindow menu.
.LP
\f2Keytool\fP has two complete sets of function key and mouse button 
definitions designated \fBprimary\fP and \fBsecondary\fP.  These
could be used, for example, with one keyset for shell operation and the 
other for an editor.
The \f2keytool\fP menu has entries to select either as the active 
keyset. Also, pressing the CONTROL-SHIFT-META combination of any function 
key that is not otherwise bound will toggle the active keyset, annunciating
a single beep if the primary keyset becomes active and a double beep for 
the secondary. 
.SH KEYTOOL MENU
.LP
The \f2keytool\fP menu invoked by CONTROL-SHIFT-META-RIGHT_MOUSE contains 
these entries:
.IP "\f2Define Keys\fP"
Bring up the \f2keytool\fP \fBkey definition window\fP, descibed below.
.IP "\f2Use Primary\fP"
Designate the primary keyset as active.
.IP "\f2Use Secondary\fP"
Designate the secondary keyset as active.
.IP "\f2Read Init File\fP"
Read the currently active initialization file, redefining all function 
key and mouse button combinations. 
.SH KEY DEFINITION WINDOW
.IP
The \f2keytool\fP \fBkey definition window\fP allows any key to be 
redefined for immediate use.  There is no need to edit ~/.keytool and 
restart the application (as with shelltool and .ttyswrc).  The key 
definition window is activated from the \f2keytool\fP menu described above.
It may be moved around and left open without affecting the operation of the
application window. Thus key definitions can be used or tested out as soon 
as they are typed in.
.IP "\f2Key Definition\fP"
The text entry gadget in the bottom center of the window shows the current 
definition for the selected key.  Directly to its left are choice gadgets 
for selecting the key and shift combination to be defined.  The definition 
can be replaced or altered with any printing or non-printing ascii 
characters (except for the \fBline separator\fP and \fBitem separator\fP 
characters described below). A special font is used so that control characters 
are identifiable. Certain keys have special functions. TAB advances the 
active text gadget within the key definition window. CONTROL-U deletes the 
entire line, and CONTROL-W deletes the last word. DELETE erase the last 
character. To enter one of these characters into a key definition, a 
special button is provided to the right of the text entry gadget. 
.IP
Mouse button definitions may have tooltool \fIformat\fP specifications for 
up to two variables embedded in them. These will be replaced with the
mouse cursor's X and Y character positions using 1,1 as the origin.
For example, the definition "ESC5%c%c" will cause a mouse button to send 
"ESC5", followed by the character with the value of the cursor's X position, 
followed by the character with the value of the cursor's Y position.
.IP "\f2Define Button\fP"
Key definitions do not take effect until the \fBdefine\fP button is 
selected. If the active key is changed without doing so, the definition is 
lost.
.IP "\f2Function Key Buttons\fP"
Surrounding the key definition window, there are buttons for each of the 
definable function keys and the mouse buttons.  The active key for 
definition can be specified by selecting one of these buttons with the 
appropriate shift combination.
.IP "\f2Active Keyset\fP"
This choice gadget allows selection of either the primary or secondary 
keyset for both definition and use.
.IP "\f2Definition File\fP"
This text gadget specifies filename to save or read key definitions from.
The entry may be edited in the normal way (CONTROL-W, CONTROL-U, and DELETE).
It does filename completion when SPACE is pressed.
.IP "\f2Item Separator\fP"
.IP "\f2Line Separator\fP"
Key definitions may contain any ascii characters \f2except\fP for two. 
\f2Keytool\fP needs two special characters to separate definitions within 
the definition file.  The item and line separators may be specified as any
ascii characters that will not be used in key definitions.  The defaults 
are TAB and NEWLINE, respectively.  As with the key definition gadget
a button is provided next to the separator text gadget for entering TAB, 
CONTROL-U, CONTROL-W, or DELETE. Selecting the "\fISeparator\fP" text will 
toggle between the two character definition fields. 
.IP "\f2Save\fP"
The \fBsave\fP button normally saves both keysets to the definition file. 
Shift combinations also allow loading key definitions from a file, copying 
either keyset over the other, and setting the definition file gadget to the
default filename (or the filename specified with the \fB\(hyi\fP command 
line option). This last fuction does \f2not\fP load key definitions.
.IP "\f2Done\fP"
The \fBdone\fP button removes the key definition window from the screen. It
can be reopened from the \f2keytool\fP menu.
.SH AUTHOR
.LP
Ken Laprade
.SH FILES
.LP
.br
~/.keytool
.br
/usr/local/lib/keytool.defaults
.SH "SEE ALSO"
.LP
shelltool (1),
tooltool (1)
.SH BUGS
.LP
Due to the size of the file  that \f2tooltool\fP(1) must parse, 
\f2keytool\fP takes an obnoxiously long time to start up.

