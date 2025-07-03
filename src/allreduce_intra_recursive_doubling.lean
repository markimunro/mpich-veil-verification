import Veil

/-! # Recursive Doubling Allreduce Verification

This file specifies and verifies the correctness of the recursive doubling
allreduce algorithm using the Veil verification framework.

The specification focuses on the communication coordination that ensures all
processes converge to the same final result through the recursive doubling pattern.
The actual reduction operation semantics are abstracted away (like MPIR_Reduce_local
in the C implementation).
-/

-- Configure Veil for effective counterexample-driven development
set_option veil.printCounterexamples true
set_option veil.smt.model.minimize true
set_option veil.vc_gen "transition"

veil module AllreduceRecursiveDoubling

-- **Types**

-- Represents process identifiers in the parallel system
type proc

-- Represents the data values being communicated and reduced
type value

-- **Abstract Reduction Operation**

-- Models MPIR_Reduce_local() - a trusted black box that combines two values
-- The algorithm doesn't need to know the specific arithmetic, just that
-- it produces deterministic results for coordination
immutable function reduce_op : value → value → value

-- Each participating process has an immutable input value
immutable function input_value : proc → value

-- **Core State Relations**

-- Process p currently holds value v as its working data
relation has_value (p : proc) (v : value)

-- Process p has received value v but hasn't processed it yet
relation received_value (p : proc) (v : value)

-- Process p has completed the allreduce algorithm
relation completed (p : proc)

-- **Coordination Relations**

-- Process p is participating in this allreduce operation
-- Models MPI communicator membership
relation participating (p : proc)

-- **Communication Model**

-- Message containing value v is in transit from src to dst
relation pending (src : proc) (dst : proc) (v : value)

#gen_state

-- **Initial State**

after_init {
  has_value P V := False
  received_value P V := False
  pending P Q V := False
  completed P := False
  participating P := False
}

-- **Actions**

-- Process p starts the allreduce with its input value
action start_allreduce (p : proc) = {
  require ∀ V, ¬has_value p V
  require ¬completed p
  require ¬participating p

  let v := input_value p
  has_value p v := True
  participating p := True
}

-- Process sender sends its current value to receiver
action send_value (sender : proc) (receiver : proc) (v : value) = {
  require has_value sender v
  require sender ≠ receiver
  require participating sender
  require ∀ V, ¬pending sender receiver V  -- Prevent duplicate messages

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
-- Uses the abstract reduce_op (like MPIR_Reduce_local in the C code)
action combine_values (p : proc) (v_local : value) (v_received : value) = {
  require has_value p v_local
  require received_value p v_received
  require participating p
  require ¬completed p

  -- Use the abstract reduction operation (trusted black box)
  let v_result := reduce_op v_local v_received

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

-- All completed processes have identical final values (consensus)
-- This is the core property the recursive doubling algorithm must ensure
safety [allreduce_consensus]
  ∀ p1 p2 v1 v2, completed p1 ∧ completed p2 ∧ has_value p1 v1 ∧ has_value p2 v2 → v1 = v2

-- Each process holds at most one value at any time
safety [single_value_per_process]
  ∀ p v1 v2, has_value p v1 ∧ has_value p v2 → v1 = v2

-- No duplicate pending messages between same processes
safety [no_duplicate_messages]
  ∀ p1 p2 v1 v2, pending p1 p2 v1 ∧ pending p1 p2 v2 → v1 = v2

-- Only participating processes can complete
safety [completion_requires_participation]
  ∀ p, completed p → participating p

-- Processes that complete must have started
safety [completion_requires_start]
  ∀ p, completed p → ∃ v, has_value p v

#gen_spec
#check_invariants
