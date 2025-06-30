#include <mpi.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define AR_OP MPI_SUM

#define N 10

int My_Allreduce(void *, void *, int, MPI_Datatype, MPI_Op, MPI_Comm);

int main(int argc, char *argv[]) {
    int rank, size;
    double x[N], allreduce_result[N], my_allreduce_result[N];

    MPI_Init(&argc, &argv);
    MPI_Comm_rank(MPI_COMM_WORLD, &rank);
    MPI_Comm_size(MPI_COMM_WORLD, &size);

    // Initialize array x on each process (example: fill with rank)
    for (int i = 0; i < N; i++) {
        x[i] = (double)rank + i*1.0;
    }

    // Perform MPI_AllReduce
    MPI_Allreduce(x, allreduce_result, N, MPI_DOUBLE, AR_OP, MPI_COMM_WORLD);

    My_Allreduce(x, my_allreduce_result, N, MPI_DOUBLE, AR_OP, MPI_COMM_WORLD);

    // Compare results
    int correct = 1;
    for (int i = 0; i < N; i++) {
        if (allreduce_result[i] != my_allreduce_result[i]) {
            correct = 0;
            break;
        }
    }

    if (correct) {
        printf("Rank %d: Results match!\n", rank);
    } else {
        printf("Rank %d: Results do NOT match!\n", rank);
    }

    MPI_Finalize();
    return 0;
}
    // Perform MPI_Reduce followed by MPI_Bcast
int My_Allreduce(void *x, void *result, int bufsize, MPI_Datatype datatype, MPI_Op op, MPI_Comm comm){
   int rank;

   MPI_Comm_rank(comm, &rank);
   if (rank == 0) {
       MPI_Reduce(x, result, bufsize, datatype, op, 0, comm);
   } else {
       MPI_Reduce(x, NULL, bufsize, datatype, op, 0, comm);
   }
   MPI_Bcast(result, bufsize, datatype, 0, comm);

   return 0;
}

