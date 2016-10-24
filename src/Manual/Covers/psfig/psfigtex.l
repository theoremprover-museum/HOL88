.TH PSFIGTEX LOCAL
.SH NAME
psfigTeX \- PostScript figures in TeX
.SH SYNTAX
\\input
.B psfig
.SH DESCRIPTION
.I psfigTeX
is a package that allows easy inclusion of arbitrary PostScript code
into a TeX document.
Figures are automatically scaled and translated, and the correct amount
of space is reserved so nothing conflicts with other text on the page.
The 
.I dvips
postprocessor must be used to create the final PostScript output.
.PP
.SH USAGE
To include a postscript file, invoke the psfig macro ``\\psfig{figure=fig.ps}'',
where ``fig.ps'' is the name of a PostScript file. 
Options may be specified in the form ``\\psfig{figure=fig.ps,opt=val,opt=val...}'';
recognized options include height, width, prolog, and postlog. If a 
height but not a width is given or vice-versa, the figure will
be scaled equally in both dimensions; if niether is given, the figure's
``natural'' size will be used.
.PP
For 
.I psfig
to properly scale and move a figure, it must be able to tell what 
it's natural size and position on the page are. This is usually specified by
the bounding box comment in the PostScript file. Unfortunately, some 
applications (including MacDraw) do not provide this information. 
If your figure doesn't have a bounding box comment (a line starting with
%%BoundingBox:), it cannot be used by psfigtex. The bbfig utility can
calculate the bounding box of a file (so can a ruler). See the bbfig(l)
manual page for information on the correct format of the comment. Usually
the bounding box comment is the second line of the file.
.SH "MACINTOSH FIGURES"
Macintosh figures require a prolog file to be downloaded containing 
PostScript procedure definitions. Use the option
``prolog=/usr/lib/ps/mac.pro'' to achieve this. See the psfigtex paper for
more detailed information, especially if there are many mac figures.
.SH "DRAFT MODE"
.PP
If a figure is very expensive to print (say a 100K image) it can be set in
draft mode, printing just the name of the file. The macro \\psdraft switches
into draft mode and \\psfull returns to full mode. Use of draft mode is
highly encouraged.
.SH "BUGS"
.LP
The ``\\psfig{...}'' command must be entirely on one input line, and no
extra spaces may appear in the option list.
.LP
When a ``\\psfig'' command is used alone in a centering enviornment, it must
be preceded by a hard space ``\\\ ''. This may be a LaTeX bug.
.LP
On very large documents, the laserwriter has been known to run out of memory
and only print a portion of the document. Use the printer memorysize command
to dvips to limit the amount of memory dvips thinks it can use.
.SH AUTHOR
Trevor Darrell
.SH "SEE ALSO"
TeX(1), dvips(1), LaTeX(1)
.br
DVILASER user's manual
.br
T. Darrell,
.ul
Incorporating PostScript and Macintosh figures in TeX
.br

