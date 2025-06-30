#include "mpi.h"
#include <string.h>
#include <stdio.h>
#include <math.h>

int CIVL_MPI_Type_size(MPI_Datatype datatype, int *size) {
    switch (datatype) {
        case MPI_CHAR:
            *size = sizeof(char);
            break;
        case MPI_SHORT:
            *size = sizeof(short);
            break;
        case MPI_INT:
            *size = sizeof(int);
            break;
        case MPI_LONG:
            *size = sizeof(long);
            break;
        case MPI_FLOAT:
            *size = sizeof(float);
            break;
        case MPI_DOUBLE:
            *size = sizeof(double);
            break;
        default:
            // For unsupported or user-defined types
            return MPI_ERR_TYPE;
    }
    return MPI_SUCCESS;
}

int CIVL_MPI_Reduce_local(const void *inbuf, void *inoutbuf, int count,
                        MPI_Datatype datatype, MPI_Op op) {
    int i;

    switch (datatype) {
        case MPI_INT: {
            const int *in = (const int *)inbuf;
            int *inout = (int *)inoutbuf;
            switch (op) {
                case MPI_SUM:
                    for (i = 0; i < count; i++) inout[i] += in[i];
                    break;
                case MPI_PROD:
                    for (i = 0; i < count; i++) inout[i] *= in[i];
                    break;
                case MPI_MAX:
                    for (i = 0; i < count; i++) if (in[i] > inout[i]) inout[i] = in[i];
                    break;
                case MPI_MIN:
                    for (i = 0; i < count; i++) if (in[i] < inout[i]) inout[i] = in[i];
                    break;
                default:
                    fprintf(stderr, "Unsupported MPI_Op for MPI_INT\n");
                    return MPI_ERR_OP;
            }
            break;
        }

        case MPI_FLOAT: {
            const float *in = (const float *)inbuf;
            float *inout = (float *)inoutbuf;
            switch (op) {
                case MPI_SUM:
                    for (i = 0; i < count; i++) inout[i] += in[i];
                    break;
                case MPI_PROD:
                    for (i = 0; i < count; i++) inout[i] *= in[i];
                    break;
                case MPI_MAX:
                    for (i = 0; i < count; i++) if (in[i] > inout[i]) inout[i] = in[i];
                    break;
                case MPI_MIN:
                    for (i = 0; i < count; i++) if (in[i] < inout[i]) inout[i] = in[i];
                    break;
                default:
                    fprintf(stderr, "Unsupported MPI_Op for MPI_FLOAT\n");
                    return MPI_ERR_OP;
            }
            break;
        }

        case MPI_DOUBLE: {
            const double *in = (const double *)inbuf;
            double *inout = (double *)inoutbuf;
            switch (op) {
                case MPI_SUM:
                    for (i = 0; i < count; i++) inout[i] += in[i];
                    break;
                case MPI_PROD:
                    for (i = 0; i < count; i++) inout[i] *= in[i];
                    break;
                case MPI_MAX:
                    // for (i = 0; i < count; i++) if (in[i] > inout[i]) inout[i] = in[i];
                    // for (i = 0; i < count; i++) inout[i] = 0.5*(in[i] + inout[i] + fabs(in[i] - inout[i]));
                    for (i = 0; i < count; i++) inout[i] = (in[i] > inout[i]) ? in[i] : inout[i];
                    break;
                case MPI_MIN:
                    // for (i = 0; i < count; i++) if (in[i] < inout[i]) inout[i] = in[i];
                    // for (i = 0; i < count; i++) inout[i] = 0.5*(in[i] + inout[i] - fabs(in[i] - inout[i]));
                    for (i = 0; i < count; i++) inout[i] = (in[i] < inout[i]) ? in[i] : inout[i];
                    break;
                default:
                    fprintf(stderr, "Unsupported MPI_Op for MPI_DOUBLE\n");
                    return MPI_ERR_OP;
            }
            break;
        }

        default:
            fprintf(stderr, "Unsupported MPI_Datatype\n");
            return MPI_ERR_TYPE;
    }

    return MPI_SUCCESS;
}

/* exists primarily because CIVL gets unhappy about calling MPI_Sendrecv with a const buffer */

int CIVL_MPIR_Localcopy(const void *sbuf, int scount, MPI_Datatype stype, void *rbuf, int rcount, MPI_Datatype rtype){
    int typesize;

    CIVL_MPI_Type_size(stype, &typesize);
    memcpy(rbuf,sbuf,scount*typesize);

    return MPI_SUCCESS;
}
