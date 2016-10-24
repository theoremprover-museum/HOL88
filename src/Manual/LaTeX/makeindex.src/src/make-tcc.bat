tcc -c -A -N -ml -v -y -DOS_PCDOS=1 -DIBM_PC_TURBO=1  genind.c
tcc -c -A -N -ml -v -y -DOS_PCDOS=1 -DIBM_PC_TURBO=1  mkind.c
tcc -c -A -N -ml -v -y -DOS_PCDOS=1 -DIBM_PC_TURBO=1  qsort.c
tcc -c -A -N -ml -v -y -DOS_PCDOS=1 -DIBM_PC_TURBO=1  scanid.c
tcc -c -A -N -ml -v -y -DOS_PCDOS=1 -DIBM_PC_TURBO=1  scanst.c
tcc -c -A -N -ml -v -y -DOS_PCDOS=1 -DIBM_PC_TURBO=1  sortid.c
tcc -A -N -ml -v -y -emakeindx.exe genind.obj mkind.obj qsort.obj scanid.obj scanst.obj sortid.obj
