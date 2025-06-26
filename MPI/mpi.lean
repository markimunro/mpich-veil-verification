import Veil

-- ================================================================
--  Two-rank “sum” example – pure Veil syntax (Variant A)
-- ================================================================

veil module TwoRankSum

-- ------------------------------------------------
-- 1.  Base type: the set of MPI processes
-- ------------------------------------------------
type proc -- declares an uninterpreted type `proc` to represent MPI processes

-- -----------------------------------------------------------
-- 2.  Mutable relations that label the two ranks (predicates)
-- -----------------------------------------------------------
relation is_r0 (p : proc)
relation is_r1 (p : proc)

-- ------------------------------------------------
-- 3.  Mutable protocol state
-- ------------------------------------------------
relation pending (src : proc) (dst : proc) (v : Int) --  currently in-flight messages
relation sum     (p : proc) (v : Int) --  local variable `sum`
relation printed (p : proc) --  has `printf` run?

#gen_state -- assembles the state type for this Veil module, based on the previously declared state components.


-- ------------------------------------------------
-- 4.  Immutable helper: each rank’s constant value
-- ------------------------------------------------
ghost relation local_val (p : proc) (v : Int) :=
  (is_r0 p ∧ v = 3) ∨ (is_r1 p ∧ v = 5)

-- ------------------------------------------------
-- 5.  Initialisation
-- ------------------------------------------------
after_init {
  --  pick an arbitrary subset of procs to be rank 0
  is_r0 P := *                --  fresh SMT symbol
  --  every proc that is *not* rank 0 is rank 1
  is_r1 P := ¬ is_r0 P

  --  network empty, nothing printed
  pending S D V := False
  printed P     := False

  --  clear `sum` completely, then set it to 0 everywhere
  sum P V := False
  sum P 0 := True
}

-- ------------------------------------------------
-- 6.  Actions  (MPI calls)
-- ------------------------------------------------

action send_1_to_0 (s d : proc) = {
  require is_r1 s ∧ is_r0 d
  pending s d 5 := True
}

action recv_on_0 (s d : proc) = {
  require is_r1 s ∧ is_r0 d
  require pending s d 5
  pending s d 5 := False
  sum     d 8   := True                 --  3 + 5
}

action send_0_to_1 (s d : proc) = {
  require is_r0 s ∧ is_r1 d
  require sum s 8
  pending s d 8 := True
}

action recv_on_1 (s d : proc) = {
  require is_r0 s ∧ is_r1 d
  require pending s d 8
  pending s d 8 := False
  sum     d 8   := True
}

action print (p : proc) = {
  require ¬ printed p
  require sum p 8
  printed p := True
}

-- ------------------------------------------------
-- 7.  Invariants  (collective contract + role facts)
-- ------------------------------------------------

--  roles are disjoint and collectively exhaustive
invariant [roles_disjoint]   is_r0 P ∧ is_r1 P → False
invariant [roles_partition]  is_r0 P ∨ is_r1 P

--  message payloads are fixed by direction
invariant [payload_1_0]  pending S D V ∧ is_r1 S ∧ is_r0 D → V = 5
invariant [payload_0_1]  pending S D V ∧ is_r0 S ∧ is_r1 D → V = 8

--  once a rank’s `sum` is set, it is the correct 8
invariant [sum_correct]  sum P V ∧ V ≠ 0 → V = 8

--  at most one message per channel direction
invariant [single_message]  pending S D V ∧ pending S D W → V = W

-- ------------------------------------------------
-- 8.  Safety: both ranks print the same 8
-- ------------------------------------------------
safety [both_print_same]  printed P ∧ printed Q → sum P 8 ∧ sum Q 8

#gen_spec
set_option veil.printCounterexamples true
#check_invariants            --  all ✓

sat trace {
  send_1_to_0
  recv_on_0
  send_0_to_1
  recv_on_1
  print           -- first rank that satisfies the guard
  print           -- second (other) rank
  assert (∃ x y, printed x ∧ printed y)
} by { bmc_sat }

end TwoRankSum
