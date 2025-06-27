# Veil Verification of MPICH Allreduce Algorithms

This repository contains a formal verification project using the [Veil](https://github.com/verse-lab/veil) specification language to verify the correctness of MPI allreduce algorithms from the MPICH implementation.

## Project Overview

**Goal**: Formally verify the correctness of `allreduce_intra_recursive_doubling.c` from MPICH using Veil, a domain-specific language for specifying and verifying distributed protocols.

**Approach**: Build on existing CIVL-based verification work to create higher-level correctness proofs using Veil's protocol specification capabilities, going beyond differential testing to prove fundamental algorithmic properties.

## Repository Structure

### 📁 Core Directories

- **`src/`** - Development workspace
  - `allreduce_intra_recursive_doubling.lean` - Main Veil specification (target file)
  - `chatgpt/` - Previous MPI verification attempts (reference only)

- **`info/`** - Reference Materials & Documentation
  - `context.txt` - Complete project instructions and verification rules
  - `Ring.lean` - Heavily commented Veil tutorial (primary syntax reference)
  - `veil/` - Extracted Veil creation paper
  - `collective contracts for message-passing parallel programs/` - Collective contracts theory
    - `collective contracts for message-passing parallel programs.txt` - Full paper text
    - `MPI_Allreduce_CIVL_contract.png` - Figure 5: CIVL-C contract for MPI_Allreduce

### 📁 Reference Implementations

- **`mpich_civl/`** - CIVL verification work by Hovland et al.
  - `allreduce_intra_recursive_doubling.c` - Original MPICH implementation
  - `civl_allreduce_intra_recursive_doubling.c` - CIVL-annotated version
  - `hovland-mpich-vss2025.txt` - VSS 2025 challenge problem paper
  - Various driver files and verification infrastructure

- **`mpich_repo/`** - Complete MPICH repository for reference

- **`veil_repo/`** - Complete Veil repository with examples
  - `Examples/` - Additional Veil specification patterns and tutorials

## Verification Strategy

### Phase 1: Abstract Model
- Model processes, data values, and communication abstractly
- Focus on the 3-phase algorithm structure:
  1. **Pre-processing**: Handle non-power-of-2 process counts
  2. **Recursive Doubling**: Main algorithm loop
  3. **Post-processing**: Distribute results back

### Phase 2: Correctness Properties
- **Safety**: All processes end up with the same reduced result
- **Correctness**: Result equals the reduction of all input values
- **Termination**: Algorithm completes for all valid inputs

### Phase 3: Detailed Implementation
- Handle non-power-of-2 edge cases with precise modeling
- Model commutative vs non-commutative operation semantics
- Verify complex addressing patterns in recursive doubling

## Key Resources

### Theoretical Foundation
- **Veil Language**: Domain-specific language for distributed protocol specification
- **Collective Contracts**: Formal theory for message-passing procedure contracts
- **CIVL Verification**: Existing verification of recursive doubling and reduce-scatter-allgather

### Reference Patterns
1. **Veil Syntax**: `info/Ring.lean` - comprehensive tutorial with leader election in ring
2. **MPI Verification**: CIVL approach in `mpich_civl/` - differential testing against MPI_Allreduce
3. **Contract Theory**: Collective contracts paper - formal semantics for MPI procedures

## Development Rules

### Veil Specification Guidelines
1. **Always reference `info/Ring.lean` first** for syntax patterns
2. **Reference `veil_repo/Examples`** for additional patterns  
3. **Break complex algorithms into phases** rather than modeling everything at once
4. **Prioritize correctness properties early** - define safety/invariants before complex actions

### Key Veil Patterns
- `type` for uninterpreted types (like `proc`)
- `relation` for mutable state
- `after_init` for initial conditions  
- `action` for state transitions
- `invariant` for properties that must hold
- `safety` for correctness properties

## Getting Started

1. **Study the references**: Start with `info/Ring.lean` for Veil syntax
2. **Understand the algorithm**: Read `mpich_civl/allreduce_intra_recursive_doubling.c`
3. **Review CIVL approach**: Check `mpich_civl/hovland-mpich-vss2025.txt` for verification insights
4. **Begin specification**: Implement in `src/allreduce_intra_recursive_doubling.lean`

## Background

This project builds on:
- **MPICH**: High-performance MPI implementation with multiple allreduce algorithms
- **CIVL**: Concurrency Intermediate Verification Language with MPI semantics
- **Veil**: Protocol specification language from VERSE lab
- **Collective Contracts**: Theory for modular verification of message-passing procedures

## Status

🚧 **In Development** - Setting up Veil specification for recursive doubling allreduce algorithm

---

**Related Work**: This verification complements the CIVL-based verification by Hovland et al., extending from differential testing to direct correctness proofs of algorithmic properties.
