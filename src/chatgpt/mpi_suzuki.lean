import Veil
veil module TwoRankSum

--------------------------------------------------------------------
-- 1.  Base sort
--------------------------------------------------------------------
type proc

--------------------------------------------------------------------
-- 2.  Rank labels (mutable)
--------------------------------------------------------------------
relation is_r0 (p : proc)
relation is_r1 (p : proc)

--------------------------------------------------------------------
-- 3.  Immutable constants
--------------------------------------------------------------------
immutable individual v0 : Int      -- rank-0’s input
immutable individual v1 : Int      -- rank-1’s input

--------------------------------------------------------------------
-- 4.  Mutable state
--------------------------------------------------------------------
relation pending (src : proc) (dst : proc) (v : Int)
relation sum     (p   : proc) (v   : Int)
relation printed (p   : proc)

#gen_state

--------------------------------------------------------------------
-- 5.  Initial state
--------------------------------------------------------------------
after_init {
  let r0 ← fresh;                   -- pick two *distinct* procs
  let r1 ← fresh;
  is_r0 P := (P = r0)
  is_r1 P := (P ≠ r0 ∧ P = r1)

  pending S D V := False
  printed P     := False

  sum P V := False
  sum P 0 := True                   -- neutral placeholder
}

--------------------------------------------------------------------
-- 6.  Actions
--------------------------------------------------------------------
action send_1_to_0 (S D : proc) = {
  require is_r1 S ∧ is_r0 D ∧ S ≠ D
  require (∀ V, ¬ pending S D V)          -- no duplicate
  pending S D v1 := True
}

action recv_on_0 (S D : proc) = {
  require is_r1 S ∧ is_r0 D
  require pending S D v1
  pending S D v1 := False
  sum D 0 := False                        -- drop old entry
  sum D (v0 + v1) := True
}

action send_0_to_1 (S D : proc) = {
  require is_r0 S ∧ is_r1 D ∧ S ≠ D
  require sum S (v0 + v1)
  require (∀ V, ¬ pending S D V)
  pending S D (v0 + v1) := True
}

action recv_on_1 (S D : proc) = {
  require is_r0 S ∧ is_r1 D
  require pending S D (v0 + v1)
  pending S D (v0 + v1) := False
  sum D 0 := False
  sum D (v0 + v1) := True
}

action print (P : proc) = {
  require ¬ printed P
  require sum P (v0 + v1)
  printed P := True
}

--------------------------------------------------------------------
-- 7.  Invariants
--------------------------------------------------------------------
invariant [unique_r0] is_r0 P ∧ is_r0 Q → P = Q
invariant [unique_r1] is_r1 P ∧ is_r1 Q → P = Q
invariant [roles_disjoint]  is_r0 P ∧ is_r1 P → False
invariant [roles_partition] is_r0 P ∨ is_r1 P

invariant [payload_1_0]
  pending S D V ∧ is_r1 S ∧ is_r0 D → V = v1
invariant [payload_0_1]
  pending S D V ∧ is_r0 S ∧ is_r1 D → V = v0 + v1

invariant [sum_functional]  sum P V ∧ sum P W → V = W
invariant [sum_correct]     sum P V ∧ V ≠ 0  → V = v0 + v1
invariant [single_message]  pending S D V ∧ pending S D W → V = W

--------------------------------------------------------------------
-- 8.  Safety
--------------------------------------------------------------------
safety [both_print_same]
  printed P ∧ printed Q → sum P (v0 + v1) ∧ sum Q (v0 + v1)

#gen_spec
set_option veil.printCounterexamples true
#check_invariants
end TwoRankSum
