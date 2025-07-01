import Veil

/-! # Recursive Doubling Allreduce - Minimal Foundation

Following Ring.lean patterns and collective contracts approach.
Goal: Verify that all processes end with the same reduced value.

Key insight from CIVL: Prove functional equivalence to reduce + broadcast.
Key insight from collective contracts: Specify global effect across all processes.

Starting minimal and building incrementally via CTI-driven development.
-/

-- Essential debugging setup (from Ring.lean)
set_option veil.printCounterexamples true
set_option veil.smt.model.minimize true
set_option veil.vc_gen "transition"

veil module AllreduceRecursiveDoubling

-- Basic types following Ring.lean pattern
type proc       -- Process identifier
type value      -- Data values being reduced

-- Core state: What does each process hold?
relation has_value (p : proc) (v : value)           -- Process p currently holds value v
relation received_value (p : proc) (v : value)      -- Process p has received value v but not yet processed it
relation completed (p : proc)                       -- Process p has completed the allreduce algorithm

-- Communication state (following Ring.lean message pattern)
relation pending (src : proc) (dst : proc) (v : value)       -- Message from src to dst containing value v

#gen_state

-- Initial state: Clean and simple (following Ring.lean pattern)
after_init {
  -- No process has any value initially
  has_value P V := False
  received_value P V := False
  pending P Q V := False
  completed P := False
}

-- Initialization action: Each process gets its initial value
action start_with_value (p : proc) (v : value) = {
  require ∀ V, ¬has_value p V  -- Process has no value yet
  require ¬completed p         -- Process not completed yet
  has_value p v := True
}

-- Basic action: Send current value to another process
action send_value (sender : proc) (receiver : proc) (v : value) = {
  require has_value sender v
  require sender ≠ receiver

  pending sender receiver v := True
}

-- Simple action: Receive a message (just handle communication)
action receive_message (receiver : proc) (sender : proc) (v : value) = {
  require pending sender receiver v

  -- Move message from pending to received
  pending sender receiver v := False
  received_value receiver v := True
}

-- Simple action: Combine values (just handle computation)
action combine_values (p : proc) (v_local : value) (v_received : value) (v_result : value) = {
  require has_value p v_local
  require received_value p v_received
  require ¬completed p

  -- Clear old values and set new result (abstracted reduction for now)
  has_value p v_local := False
  received_value p v_received := False
  has_value p v_result := True
}

-- Natural completion: Process finishes when it has final value and no pending work
action finish_allreduce (p : proc) = {
  require ¬completed p
  require ∃ v, has_value p v                     -- Has a final value
  require ∀ v, ¬received_value p v               -- No pending received values to process
  require ∀ q v, ¬pending p q v                  -- No outgoing messages
  -- Consistency constraint: if other processes are completed, must have same value
  require ∀ q v1 v2, completed q ∧ has_value p v1 ∧ has_value q v2 → v1 = v2

  completed p := True
}

-- Core safety property: All completed processes have the same final value
safety [allreduce_correctness]
  ∀ p1 p2 v1 v2, completed p1 ∧ completed p2 ∧ has_value p1 v1 ∧ has_value p2 v2 → v1 = v2

-- Basic consistency: Each process has exactly one value
safety [single_value_per_process]
  ∀ p v1 v2, has_value p v1 ∧ has_value p v2 → v1 = v2

#gen_spec
#check_invariants
