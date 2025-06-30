#include "mpi.h"
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

// Macros and functions to make standalone

#define MPIC_Sendrecv(A,B,C,D,E,F,G,H,I,J,K,L) MPI_Sendrecv(A,B,C,D,E,F,G,H,I,J,K,L)
#define MPIC_Send(A,B,C,D,E,F) MPI_Send(A,B,C,D,E,F)
#define MPIC_Recv(A,B,C,D,E,F,G) MPI_Recv(A,B,C,D,E,F,G)
#define MPIC_Isend(A,B,C,D,E,F,G) MPI_Isend(A,B,C,D,E,F,G)
#define MPIC_Irecv(A,B,C,D,E,F,G) MPI_Irecv(A,B,C,D,E,F,G)
#define MPIC_Waitall(A,B,C) MPI_Waitall(A,B,C)
#define MPIR_Reduce_local CIVL_MPI_Reduce_local 
#define MPIR_ERR_CHECK(X)
#define MPIR_THREADCOMM_RANK_SIZE(A,B,C) MPI_Comm_rank(A, &B); MPI_Comm_size(A, &C);
#define MPL_MIN(X, Y)  ((X) < (Y) ? (X) : (Y))
#define MPL_MAX(X, Y)  ((X) > (Y) ? (X) : (Y))
#define MPIR_CHKLMEM_MAX 10
#define MPIR_CHKLMEM_DECL()                                     \
    void *(mpiu_chklmem_stk_[MPIR_CHKLMEM_MAX]) = { NULL };     \
    int mpiu_chklmem_stk_sp_=0;
#define MPIR_CHKLMEM_FREEALL()                                          \
    do {                                                                \
        while (mpiu_chklmem_stk_sp_ > 0) {                              \
            free(mpiu_chklmem_stk_[--mpiu_chklmem_stk_sp_]);            \
        }                                                               \
    } while (0)
#define MPIR_CHKLMEM_MALLOC(pointer_,nbytes_)                     \
    do {                                                          \
        pointer_ = (MPI_Aint *)malloc(nbytes_);                   \
        if (pointer_) {                                           \
            assert(mpiu_chklmem_stk_sp_<MPIR_CHKLMEM_MAX);        \
            mpiu_chklmem_stk_[mpiu_chklmem_stk_sp_++] = pointer_; \
        } else if (nbytes_ > 0) {                                 \
            assert(0);                                            \
        }                                                         \
    } while (0)
#define MPIR_CHKLMEM_MALLOC_CIVL(datatype_,pointer_,nbytes_)            \
    do {                                                                \
        switch (datatype_) {                                            \
        case MPI_INT:                                                   \
            pointer_ = (int *) malloc(nbytes_);                         \
            break;                                                      \
        case MPI_FLOAT:                                                 \
            pointer_ = (float *) malloc(nbytes_);                       \
            break;                                                      \
        case MPI_DOUBLE:                                                \
            pointer_ = (double *) malloc(nbytes_);                      \
            break;                                                      \
        }                                                               \
        if (pointer_) {                                                 \
            assert(mpiu_chklmem_stk_sp_<MPIR_CHKLMEM_MAX);              \
            mpiu_chklmem_stk_[mpiu_chklmem_stk_sp_++] = pointer_;       \
        } else if (nbytes_ > 0) {                                       \
            assert(0);                                                  \
        }                                                               \
    } while (0)

#define MPIR_ALLREDUCE_TAG            14
#define LOCALCOPY_TAG                 2153
#define MPIR_Op_is_commutative(X) 1
#define MPIR_Assert(X)
#define MPIR_Errflag_t MPI_Status*
#define MPIR_Datatype_get_extent_macro(A,B) MPIR_Datatype_get_extent(A,&B)
// define MPIR_Localcopy(sbuf, scount, sdatatype, rbuf, rcount, rdatatype) MPI_Sendrecv(sbuf, scount, sdatatype, 0, LOCALCOPY_TAG, rbuf, rcount, rdatatype, 0, LOCALCOPY_TAG, MPI_COMM_SELF, MPI_STATUS_IGNORE)
#define MPIR_Localcopy(A, B, C, D, E, F) CIVL_MPIR_Localcopy(A, B, C, D, E, F)
// Should never need max alignment, so use arbitrary value
#define MAX_ALIGNMENT 16

int CIVL_MPI_Type_size(MPI_Datatype, int *);

void MPIR_Type_get_true_extent_impl(MPI_Datatype dtype, MPI_Aint *lbptr, MPI_Aint *extentptr){
   int myextent;

   *lbptr = 0;
   CIVL_MPI_Type_size(dtype, &myextent);
   *extentptr = myextent;
}

void MPIR_Datatype_get_extent(MPI_Datatype dtype, MPI_Aint *extentptr){
   int myextent;

   CIVL_MPI_Type_size(dtype, &myextent);
   *extentptr = myextent;
}

/* Returns int(log2(number)) */
static inline int MPL_log2(int number)
{
    int p = 0;

    while (number > 0) {
        number >>= 1;
        p++;
    }
    return p - 1;
}

static inline int MPL_pof2(int number)
{
    if (number > 0) {
        return 1 << MPL_log2(number);
    } else {
        return 0;
    }
}

int CIVL_MPI_Reduce_local(const void *, void *, int, MPI_Datatype, MPI_Op);

int CIVL_MPIR_Localcopy(const void *, int, MPI_Datatype, void *, int, MPI_Datatype);
