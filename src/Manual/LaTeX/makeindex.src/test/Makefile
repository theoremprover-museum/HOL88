# ======================================================================
# This UNIX Makefile runs the makeindex in the src directory on several
# test files, *.idx.  The output from each file foo.* is compared with
# correct output saved in files ok-foo.*.  As new bugs are discovered
# and fixed, test files that exhibit them should be incorporated in
# this directory.  Names should be kept within the 8+3 limit of PC DOS.
# [11-Sep-1991]
# ======================================================================

FILES		=	b209a b209b b209c b209d b209e b209f \
			b211a b211d b211e b211f b211g b211h \
			book test tort

# These files have private MakeIndex styles (*.ist) with the same base name
# The German ones must be run with -g
GERMAN-FILES	=	b211b

STYLE-FILES	=	b210a b211c

MAKEINDEX	=	../src/makeindex

RM		=	/bin/rm -f

all:	
	@echo "==================================================================="
	@echo "If makeindex has compiled correctly, there should be no differences"
	@echo "output by these tests, except possibly in the version lines"
	@echo "in the *.ilg files."
	@echo "==================================================================="
	-for f in $(FILES);\
	do\
		echo "";\
		echo "==================================================";\
		echo "Test file = $$f";\
		echo "";\
		$(MAKEINDEX) $$f;\
		echo Comparing ok-$$f.ind $$f.ind;\
		diff ok-$$f.ind $$f.ind;\
		echo Comparing ok-$$f.ilg $$f.ilg;\
		diff ok-$$f.ilg $$f.ilg;\
	done
	@echo "==================================================================="
	-for f in $(GERMAN-FILES);\
	do\
		echo "";\
		echo "==================================================";\
		echo "Test file = $$f (German sort option)";\
		echo "";\
		$(MAKEINDEX) -s $$f.ist -g $$f;\
		echo Comparing ok-$$f.ind $$f.ind;\
		diff ok-$$f.ind $$f.ind;\
		echo Comparing ok-$$f.ilg $$f.ilg;\
		diff ok-$$f.ilg $$f.ilg;\
	done
	@echo "==================================================================="
	-for f in $(STYLE-FILES);\
	do\
		echo "";\
		echo "==================================================";\
		echo "Test file = $$f (Private style file)";\
		echo "";\
		$(MAKEINDEX) -s $$f.ist $$f;\
		echo Comparing ok-$$f.ind $$f.ind;\
		diff ok-$$f.ind $$f.ind;\
		echo Comparing ok-$$f.ilg $$f.ilg;\
		diff ok-$$f.ilg $$f.ilg;\
	done
	@echo "=================================================="

clean:
	$(RM) \#*
	$(RM) *~
	$(RM) core
	-for f in $(FILES) $(GERMAN-FILES) $(STYLE-FILES);\
	do\
		$(RM) $$f.ind $$f.ilg;\
	done

clobber:	clean
