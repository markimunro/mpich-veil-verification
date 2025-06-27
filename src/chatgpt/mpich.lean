import Veil
veil module MPI_Allreduce_Int

-- base sort -------------------------------------------------------
type proc

-- role labelling --------------------------------------------------
relation is_root (p : proc)
relation is_leaf (p : proc)

-- mutable state ---------------------------------------------------
relation pending   (src : proc) (dst : proc) (v : Int)
relation received  (p : proc)
relation sum       (p : proc) (v : Int)
relation printed   (p : proc)

#gen_state

-- immutable local inputs -----------------------------------------
ghost relation local_val (p : proc) (v : Int) :=
  (is_root p ∧ v = 3) ∨ (is_leaf p ∧ v = 5)

-- initial state ---------------------------------------------------
after_init {
  let root ← fresh
  is_root P := (P = root)
  is_leaf P := ¬ is_root P

  pending  S D V := False
  received P     := False

  sum P V := False
  sum root 3 := True
  sum P 0   := is_leaf P -- only leaves start with 0

  printed P := False
}

-- actions ---------------------------------------------------------

action send_to_root (S : proc) (R : proc) (V : Int) = {
  require is_leaf S ∧ is_root R
  require local_val S V
  require ¬ received S -- only once per leaf
  require (∀ W, ¬ pending S R W) -- no duplicate on same channel
  pending S R V := True
}

action root_recv (S : proc) (R : proc) (V : Int) (OLD : Int) = {
  require is_leaf S ∧ is_root R
  require pending S R V
  pending S R V := False
  received S := True
  require sum R OLD
  sum R OLD := False
  sum R (OLD + V) := True
}

action root_bcast (R : proc) (D : proc) (GS : Int) = {
  require is_root R ∧ is_leaf D
  require (∀ L, is_leaf L → received L) -- gathered everyone
  require sum R GS -- GS is global sum
  require (∀ X Y Z, ¬ pending X Y Z) -- buffer empty
  pending R D GS := True
}

action leaf_recv (R : proc) (D : proc) (V : Int) = {
  require is_root R ∧ is_leaf D
  require pending R D V
  pending R D V := False
  sum D 0 := False
  sum D V := True
}

action print (P : proc) (V : Int) = {
  require ¬ printed P
  require sum P V ∧ V ≠ 0
  require (∀ Q, sum Q V)
  printed P := True
}

-- invariants ------------------------------------------------------

invariant [unique_root] is_root P ∧ is_root Q → P = Q
invariant [roles_disjoint] is_root P ∧ is_leaf P → False
invariant [roles_cover] is_root P ∨ is_leaf P

invariant [payload_leaf_root]
  pending S D V ∧ is_leaf S ∧ is_root D → local_val S V

invariant [payload_root_leaf]
  pending S D V ∧ is_root S ∧ is_leaf D ∧ sum S GS → V = GS

invariant [sum_functional]
  sum P V ∧ sum P W → V = W

invariant [leaf_matches_root]
  is_leaf P ∧ sum P V ∧ V ≠ 0 →
    (∃ R GS, is_root R ∧ sum R GS ∧ V = GS)

invariant [single_message]
  pending S D V ∧ pending S D W → V = W

-- safety ----------------------------------------------------------
safety [all_print_same]
  printed P ∧ printed Q → sum P V ∧ sum Q V

#gen_spec

set_option veil.printCounterexamples true
set_option veil.vc_gen "transition"

#check_invariants

end MPI_Allreduce_Int
