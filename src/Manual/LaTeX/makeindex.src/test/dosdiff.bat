:# Test of MakeIndex for PC DOS
:# [12-Sep-1991]


echo off
echo ##################################################
echo Expect only letter case differences in the output,
echo and differences in the program name in the banner.
echo ##################################################


echo ##################################################
echo test file = b209a
..\src\makeindx b209a
diff b209a.ind ok-b209a.ind
diff b209a.ilg ok-b209a.ilg


echo ##################################################
echo test file = b209b
..\src\makeindx b209b
diff b209b.ind ok-b209b.ind
diff b209b.ilg ok-b209b.ilg


echo ##################################################
echo test file = b209c
..\src\makeindx b209c
diff b209c.ind ok-b209c.ind
diff b209c.ilg ok-b209c.ilg


echo ##################################################
echo test file = b209d
..\src\makeindx b209d
diff b209d.ind ok-b209d.ind
diff b209d.ilg ok-b209d.ilg


echo ##################################################
echo test file = b209e
..\src\makeindx b209e
diff b209e.ind ok-b209e.ind
diff b209e.ilg ok-b209e.ilg


echo ##################################################
echo test file = b209f
..\src\makeindx b209f
diff b209f.ind ok-b209f.ind
diff b209f.ilg ok-b209f.ilg


echo ##################################################
echo test file = b211a
..\src\makeindx b211a
diff b211a.ind ok-b211a.ind
diff b211a.ilg ok-b211a.ilg


echo ##################################################
echo test file = b211d
..\src\makeindx b211d
diff b211d.ind ok-b211d.ind
diff b211d.ilg ok-b211d.ilg


:# b211e has a Ctl-Z, which is a problem on PC DOS
:# b211h is the same file, minus that one line
:# echo ##################################################
:# echo test file = b211e
:# ..\src\makeindx b211e
:# diff b211e.ind ok-b211e.ind
:# diff b211e.ilg ok-b211e.ilg


echo ##################################################
echo test file = b211f
..\src\makeindx b211f
diff b211f.ind ok-b211f.ind
diff b211f.ilg ok-b211f.ilg


echo ##################################################
echo test file = b211g
..\src\makeindx b211g
diff b211g.ind ok-b211g.ind
diff b211g.ilg ok-b211g.ilg


echo ##################################################
echo test file = b211h
..\src\makeindx b211h
diff b211h.ind ok-b211h.ind
diff b211h.ilg ok-b211h.ilg


echo ##################################################
echo test file = book
..\src\makeindx book
diff book.ind ok-book.ind
diff book.ilg ok-book.ilg


echo ##################################################
echo test file = test
..\src\makeindx test
diff test.ind ok-test.ind
diff test.ilg ok-test.ilg


echo ##################################################
echo test file = tort
..\src\makeindx tort
diff tort.ind ok-tort.ind
diff tort.ilg ok-tort.ilg


echo ##################################################
echo test file = b211b (German sort option)
..\src\makeindx -s b211b.ist -g b211b
diff b211b.ind ok-b211b.ind
diff b211b.ilg ok-b211b.ilg


echo ##################################################
echo test file = b210a (Private style file)
..\src\makeindx -s b210a.ist b210a
diff b210a.ind ok-b210a.ind
diff b210a.ilg ok-b210a.ilg


echo ##################################################
echo test file = b211c (Private style file)
..\src\makeindx -s b211c.ist b211c
diff b211c.ind ok-b211c.ind
diff b211c.ilg ok-b211c.ilg

