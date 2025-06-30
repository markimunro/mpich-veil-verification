civl: naive_verify rd_verify rsag_verify

all: my_allreduce rd_allreduce rm_allreduce

transform_sources:
	bash transform.sh allreduce_intra_recursive_doubling.c allred_recursive_doubling.c
	bash transform.sh allreduce_intra_recursive_multiplying.c allred_recursive_multiplying.c
	bash transform.sh allreduce_intra_reduce_scatter_allgather.c allred_reduce_scatter_allgather.c

my_allreduce: my_allreduce_driver.c
	mpicc -o my_allreduce my_allreduce_driver.c

naive_allreduce: naive_allreduce_driver.c
	mpicc -o naive_allreduce naive_allreduce_driver.c

rd_allreduce: rd_allreduce_driver.c allred_recursive_doubling.c mpiimpl.h
	bash transform.sh allreduce_intra_recursive_doubling.c allred_recursive_doubling.c
	mpicc -o rd_allreduce rd_allreduce_driver.c allred_recursive_doubling.c

rm_allreduce: rm_allreduce_driver.c allreduce_intra_recursive_multiplying.c mpiimpl.h
	bash transform.sh allreduce_intra_recursive_multiplying.c allred_recursive_multiplying.c
	mpicc -o rm_allreduce rm_allreduce_driver.c allred_recursive_multiplying.c

rsag_allreduce: rsag_allreduce_driver.c allreduce_intra_reduce_scatter_allgather.c mpiimpl.h
	bash transform.sh allreduce_intra_reduce_scatter_allgather.c allred_reduce_scatter_allgather.c
	mpicc -o rsag_allreduce rsag_allreduce_driver.c allred_reduce_scatter_allgather.c

naive_verify: naive_allreduce_driver.cvl
	civl verify -input_mpi_nprocs_lo=1 -input_mpi_nprocs_hi=10 naive_allreduce_driver.cvl

rd_verify: rd_allreduce_driver.cvl civl_allreduce_intra_recursive_doubling.c civl_mpi_funcs.c mpiimpl_cvl.h
	bash transform.sh civl_allreduce_intra_recursive_doubling.c civl_allred_recursive_doubling.c
	civl verify -input_mpi_nprocs_lo=1 -input_mpi_nprocs_hi=10 -DAR_OP=MPI_PROD rd_allreduce_driver.cvl civl_allred_recursive_doubling.c civl_mpi_funcs.c
	civl verify -input_mpi_nprocs_lo=1 -input_mpi_nprocs_hi=10 -DAR_OP=MPI_SUM rd_allreduce_driver.cvl civl_allred_recursive_doubling.c civl_mpi_funcs.c
	civl verify -input_mpi_nprocs_lo=1 -input_mpi_nprocs_hi=5 -DNMAX=5 -DAR_OP=MPI_MAX rd_allreduce_driver.cvl civl_allred_recursive_doubling.c civl_mpi_funcs.c
	civl verify -input_mpi_nprocs_lo=1 -input_mpi_nprocs_hi=5 -DNMAX=5 -DAR_OP=MPI_MIN rd_allreduce_driver.cvl civl_allred_recursive_doubling.c civl_mpi_funcs.c

rsag_verify: rsag_allreduce_driver.cvl civl_allreduce_intra_reduce_scatter_allgather.c civl_mpi_funcs.c mpiimpl_cvl.h
	bash transform.sh civl_allreduce_intra_reduce_scatter_allgather.c civl_allred_reduce_scatter_allgather.c
	civl verify -input_mpi_nprocs_lo=1 -input_mpi_nprocs_hi=10 -DAR_OP=MPI_PROD rsag_allreduce_driver.cvl civl_allred_reduce_scatter_allgather.c civl_mpi_funcs.c
	civl verify -input_mpi_nprocs_lo=1 -input_mpi_nprocs_hi=10 -DAR_OP=MPI_SUM rsag_allreduce_driver.cvl civl_allred_reduce_scatter_allgather.c civl_mpi_funcs.c
	civl verify -input_mpi_nprocs_lo=1 -input_mpi_nprocs_hi=5 -DNMAX=5 -DAR_OP=MPI_MAX rsag_allreduce_driver.cvl civl_allred_reduce_scatter_allgather.c civl_mpi_funcs.c
	civl verify -input_mpi_nprocs_lo=1 -input_mpi_nprocs_hi=5 -DNMAX=5 -DAR_OP=MPI_MIN rsag_allreduce_driver.cvl civl_allred_reduce_scatter_allgather.c civl_mpi_funcs.c

clean:
	rm -rf my_allreduce rd_allreduce rm_allreduce rsag_allreduce naive_allreduce my_allreduce.dSYM rd_allreduce.dSYM rm_allreduce.dSYM rsag_allreduce.dSYM naive_allreduce.dSYM
