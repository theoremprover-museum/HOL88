# /u/beebe/tex/makeindex/2-10/makeindex/doc/deblank.awk, Sat Jul  6 12:06:09 1991
# Edit by Nelson H. F. Beebe <beebe@rios.math.utah.edu>
# ========================================================================
# Reduce consecutive blank lines to single blank line.
# Usage:
#	awk -f deblank.awk <infile >outfile
# [06-Jul-1991]
# ========================================================================
NF == 0	{ nb++ }

NF > 0	{ if (nb > 0) print "";
	  nb = 0;
	  print $0;
	}
