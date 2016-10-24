$! Compile and link MakeIndex under VAX/VMS for people who don't have make.
$ cc = "CC/NOLIST/DEFINE=(""OS_VAXVMS=1"")"
$ cc genind
$ cc mkind
$ cc qsort
$ cc scanid
$ cc scanst
$ cc sortid
$ link genind,mkind,qsort,scanid,scanst,sortid,-
    sys$library:vaxcrtl/lib /exe=makeindex
