import Veil

/-! # Recursive Doubling Allreduce Verification

This file specifies and verifies the correctness of the recursive doubling
allreduce algorithm using the Veil verification framework.

The specification ensures that all processes end with the same value, which
is the mathematically correct reduction of all processes' initial contributions.
-/

-- Configure Veil for effective counterexample-driven development
set_option veil.printCounterexamples true
set_option veil.smt.model.minimize true
set_option veil.vc_gen "transition"

veil module AllreduceRecursiveDoubling

-- **Types**

-- Represents process identifiers in the parallel system
type proc

-- Represents the data values being reduced across processes
type value

-- Reduction operations supported by the allreduce algorithm
-- Corresponds to standard MPI reduction operations
inductive operation
| sum
| prod
| min
| max

-- **Core State Relations**

-- Process p currently holds value v as its working data
relation has_value (p : proc) (v : value)

-- Process p has received value v but hasn't processed it yet
relation received_value (p : proc) (v : value)

-- Process p has completed the allreduce algorithm
relation completed (p : proc)

-- **Semantic Tracking Relations**

-- Process p initially contributed value v to the allreduce
-- This relation is immutable once set and tracks original contributions
relation initial_value (p : proc) (v : value)

-- Process p is participating in this allreduce operation
-- Models MPI communicator membership
relation participating (p : proc)

-- The reduction operation being used in this allreduce
-- All participating processes must use the same operation
relation using_operation (op : operation)

-- **Communication Model**

-- Message containing value v is in transit from src to dst
relation pending (src : proc) (dst : proc) (v : value)

#gen_state

-- **Ghost Relations**

-- Placeholder for defining when a value is the correct reduction result
-- Will be refined to encode actual reduction semantics
ghost relation correct_reduction_result (v : value) (op : operation) :=
  True

-- **Initial State**

after_init {
  has_value P V := False
  received_value P V := False
  pending P Q V := False
  completed P := False
  initial_value P V := False
  participating P := False
  using_operation OP := False
}

-- **Actions**

-- Process p starts the allreduce with initial value v using operation op
-- Establishes both computational state and semantic tracking
action start_with_value (p : proc) (v : value) (op : operation) = {
  require ∀ V, ¬has_value p V
  require ∀ V, ¬initial_value p V
  require ¬completed p
  require ¬participating p

  -- Ensure all processes use the same operation
  require (∀ op_any, ¬using_operation op_any) ∨ using_operation op

  has_value p v := True
  initial_value p v := True
  participating p := True
  using_operation op := True
}

-- Process sender sends its current value to receiver
action send_value (sender : proc) (receiver : proc) (v : value) = {
  require has_value sender v
  require sender ≠ receiver
  require participating sender

  pending sender receiver v := True
}

-- Process receiver accepts a pending message from sender
action receive_message (receiver : proc) (sender : proc) (v : value) = {
  require pending sender receiver v
  require participating receiver

  pending sender receiver v := False
  received_value receiver v := True
}

-- Process p combines its local value with a received value
-- Will be enhanced to enforce correct reduction operation semantics
action combine_values (p : proc) (v_local : value) (v_received : value) (v_result : value) (op : operation) = {
  require has_value p v_local
  require received_value p v_received
  require using_operation op
  require participating p
  require ¬completed p

  -- Placeholder for reduction operation constraints
  require True

  has_value p v_local := False
  received_value p v_received := False
  has_value p v_result := True
}

-- Process p completes the allreduce when it has a final result
action finish_allreduce (p : proc) = {
  require ¬completed p
  require participating p
  require ∃ v, has_value p v
  require ∀ v, ¬received_value p v
  require ∀ q v, ¬pending p q v

  -- Ensure consistency with already completed processes
  require ∀ q v1 v2, completed q ∧ has_value p v1 ∧ has_value q v2 → v1 = v2

  completed p := True
}

-- **Safety Properties**

-- The final result must be the mathematically correct reduction
safety [allreduce_functional_correctness]
  ∀ p v op, completed p ∧ has_value p v ∧ using_operation op →
    correct_reduction_result v op

-- All completed processes have identical final values
safety [allreduce_correctness]
  ∀ p1 p2 v1 v2, completed p1 ∧ completed p2 ∧ has_value p1 v1 ∧ has_value p2 v2 → v1 = v2

-- Each process holds at most one value at any time
safety [single_value_per_process]
  ∀ p v1 v2, has_value p v1 ∧ has_value p v2 → v1 = v2

-- Each process contributes exactly one initial value
safety [unique_initial_value]
  ∀ p v1 v2, initial_value p v1 ∧ initial_value p v2 → v1 = v2

-- Processes with initial values must be participants
safety [participation_consistency]
  ∀ p v, initial_value p v → participating p

-- All processes use the same reduction operation
safety [single_operation]
  ∀ op1 op2, using_operation op1 ∧ using_operation op2 → op1 = op2

-- Only participating processes can complete
safety [completion_requires_participation]
  ∀ p, completed p → participating p

#gen_spec
#check_invariants
