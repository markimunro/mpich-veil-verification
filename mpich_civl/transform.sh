#!/bin/bash

if test -z "$2" -o ! -e $1 ; then
    echo "usage: ./transform.sh <existing file> <new file>"
    exit 1
fi

echo "transforming $1"

sed -e 's/MPIR_Comm.*\*.*comm_ptr/MPI_Comm comm/g' \
    -e 's/comm_ptr/comm/g' \
    -e 's/MPIR_Request \*/MPI_Request /g' \
    -e 's/MPIR_Request/MPI_Request/g' \
    -e 's/, MPIR_Errflag_t errflag//g' \
    -e 's/, errflag//g' $1 > $2

exit 0
