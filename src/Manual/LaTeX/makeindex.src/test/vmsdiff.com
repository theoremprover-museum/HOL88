$ ! Test of MakeIndex for VAX VMS
$ ! [12-Sep-1991]
$ !
$ ! ****** Edit this line to suit local conventions *****
$ makeindex :== $public$disk:[beebe.makeindex.src]makeindex.exe
$
$ write sys$output "=================================================="
$ write sys$output "Expect only letter case differences in the output"
$ write sys$output "=================================================="
$ !
$ !
$ write sys$output "=================================================="
$ write sys$output "test file = b209a"
$ makeindex b209a
$ diff b209a.ind ok-b209a.ind
$ diff b209a.ilg ok-b209a.ilg
$ !
$ !
$ write sys$output "=================================================="
$ write sys$output "test file = b209b"
$ makeindex b209b
$ diff b209b.ind ok-b209b.ind
$ diff b209b.ilg ok-b209b.ilg
$ !
$ !
$ write sys$output "=================================================="
$ write sys$output "test file = b209c"
$ makeindex b209c
$ diff b209c.ind ok-b209c.ind
$ diff b209c.ilg ok-b209c.ilg
$ !
$ !
$ write sys$output "=================================================="
$ write sys$output "test file = b209d"
$ makeindex b209d
$ diff b209d.ind ok-b209d.ind
$ diff b209d.ilg ok-b209d.ilg
$ !
$ !
$ write sys$output "=================================================="
$ write sys$output "test file = b209e"
$ makeindex b209e
$ diff b209e.ind ok-b209e.ind
$ diff b209e.ilg ok-b209e.ilg
$ !
$ !
$ write sys$output "=================================================="
$ write sys$output "test file = b209f"
$ makeindex b209f
$ diff b209f.ind ok-b209f.ind
$ diff b209f.ilg ok-b209f.ilg
$ !
$ !
$ write sys$output "=================================================="
$ write sys$output "test file = b211a"
$ makeindex b211a
$ diff b211a.ind ok-b211a.ind
$ diff b211a.ilg ok-b211a.ilg
$ !
$ !
$ write sys$output "=================================================="
$ write sys$output "test file = b211d"
$ makeindex b211d
$ diff b211d.ind ok-b211d.ind
$ diff b211d.ilg ok-b211d.ilg
$ !
$ !
$ write sys$output "=================================================="
$ write sys$output "test file = b211e"
$ makeindex b211e
$ diff b211e.ind ok-b211e.ind
$ diff b211e.ilg ok-b211e.ilg
$ !
$ !
$ write sys$output "=================================================="
$ write sys$output "test file = b211f"
$ makeindex b211f
$ diff b211f.ind ok-b211f.ind
$ diff b211f.ilg ok-b211f.ilg
$ !
$ !
$ write sys$output "=================================================="
$ write sys$output "test file = b211g"
$ makeindex b211g
$ diff b211g.ind ok-b211g.ind
$ diff b211g.ilg ok-b211g.ilg
$ !
$ !
$ write sys$output "=================================================="
$ write sys$output "test file = b211h"
$ makeindex b211h
$ diff b211h.ind ok-b211h.ind
$ diff b211h.ilg ok-b211h.ilg
$ !
$ !
$ write sys$output "=================================================="
$ write sys$output "test file = book"
$ makeindex book
$ diff book.ind ok-book.ind
$ diff book.ilg ok-book.ilg
$ !
$ !
$ write sys$output "=================================================="
$ write sys$output "test file = test"
$ makeindex test
$ diff test.ind ok-test.ind
$ diff test.ilg ok-test.ilg
$ !
$ !
$ write sys$output "=================================================="
$ write sys$output "test file = tort"
$ makeindex tort
$ diff tort.ind ok-tort.ind
$ diff tort.ilg ok-tort.ilg
$ !
$ !
$ write sys$output "=================================================="
$ write sys$output "test file = b211b (German sort option)"
$ makeindex -s b211b.ist -g b211b
$ diff b211b.ind ok-b211b.ind
$ diff b211b.ilg ok-b211b.ilg
$ !
$ !
$ write sys$output "=================================================="
$ write sys$output "test file = b210a (Private style file)"
$ makeindex -s b210a.ist b210a
$ diff b210a.ind ok-b210a.ind
$ diff b210a.ilg ok-b210a.ilg
$ !
$ !
$ write sys$output "=================================================="
$ write sys$output "test file = b211c (Private style file)"
$ makeindex -s b211c.ist b211c
$ diff b211c.ind ok-b211c.ind
$ diff b211c.ilg ok-b211c.ilg
$ !
$ !
