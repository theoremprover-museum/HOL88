.SUFFIXES:	.ps .uu

.uu.ps:
	uudecode $<
	uncompress $*.ps.Z

manual: tooltool.ps
	$(LPR) -P$(PRINTER) -J"Tooltool Manual" tooltool.ps

tooltool.uu: tooltool.uu.1 tooltool.uu.2 tooltool.uu.3 tooltool.uu.4 tooltool.uu.5
	cat tooltool.uu.[12345] >tooltool.uu
