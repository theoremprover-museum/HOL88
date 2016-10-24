cl -c -AL -Zd -Oailt -W3 -Zi -DOS_PCDOS -DIBM_PC_MICROSOFT  genind.c
cl -c -AL -Zd -Oailt -W3 -Zi -DOS_PCDOS -DIBM_PC_MICROSOFT  mkind.c
cl -c -AL -Zd -Oailt -W3 -Zi -DOS_PCDOS -DIBM_PC_MICROSOFT  qsort.c
cl -c -AL -Zd -Oailt -W3 -Zi -DOS_PCDOS -DIBM_PC_MICROSOFT  scanid.c
cl -c -AL -Zd -Oailt -W3 -Zi -DOS_PCDOS -DIBM_PC_MICROSOFT  scanst.c
cl -c -AL -Zd -Oailt -W3 -Zi -DOS_PCDOS -DIBM_PC_MICROSOFT  sortid.c
cl -o makeindx.exe genind.obj mkind.obj qsort.obj scanid.obj scanst.obj sortid.obj
