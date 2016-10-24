lc -dOS_PCDOS=1 -dIBM_PC_LATTICE=1 -c -ca -cf -cs -cz -f -ml -S=32K genind.c
lc -dOS_PCDOS=1 -dIBM_PC_LATTICE=1 -c -ca -cf -cs -cz -f -ml -S=32K mkind.c
lc -dOS_PCDOS=1 -dIBM_PC_LATTICE=1 -c -ca -cf -cs -cz -f -ml -S=32K qsort.c
lc -dOS_PCDOS=1 -dIBM_PC_LATTICE=1 -c -ca -cf -cs -cz -f -ml -S=32K scanid.c
lc -dOS_PCDOS=1 -dIBM_PC_LATTICE=1 -c -ca -cf -cs -cz -f -ml -S=32K scanst.c
lc -dOS_PCDOS=1 -dIBM_PC_LATTICE=1 -c -ca -cf -cs -cz -f -ml -S=32K sortid.c
lc -L -f -ml genind.obj mkind.obj qsort.obj scanid.obj scanst.obj sortid.obj
del makeindx.exe
ren genind.exe makeindx.exe
