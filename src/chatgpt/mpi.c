#include <mpi.h>
#include <stdio.h>

int main(int argc, char **argv)
{
    int rank, size;
    int local_value, sum;

    MPI_Init(&argc, &argv);
    MPI_Comm_rank(MPI_COMM_WORLD, &rank);
    MPI_Comm_size(MPI_COMM_WORLD, &size);

    if (size != 2)
    {
        if (rank == 0)
            fprintf(stderr, "This program requires exactly 2 processes.\n");
        MPI_Abort(MPI_COMM_WORLD, 1);
    }

    // Initialize local data
    if (rank == 0)
    {
        local_value = 3; // Rank 0's value
    }
    else
    {
        local_value = 5; // Rank 1's value
    }

    if (rank == 1)
    {
        // Send to rank 0
        MPI_Send(&local_value, 1, MPI_INT, 0, 0, MPI_COMM_WORLD);
        // Receive sum from rank 0
        MPI_Recv(&sum, 1, MPI_INT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    }
    else if (rank == 0)
    {
        int received_value;
        // Receive from rank 1
        MPI_Recv(&received_value, 1, MPI_INT, 1, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
        sum = local_value + received_value;
        // Send sum to rank 1
        MPI_Send(&sum, 1, MPI_INT, 1, 0, MPI_COMM_WORLD);
    }

    // All ranks print the result
    printf("Rank %d: Final sum is %d\n", rank, sum);

    MPI_Finalize();
    return 0;
}