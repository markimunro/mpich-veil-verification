-- ## ABSTRACTIONS (Never modeling these)


import Veil

set_option veil.printCounterexamples true
set_option veil.smt.model.minimize true
set_option veil.vc_gen "transition"

veil module AllreduceRecursiveDoubling

-- like typedef in C
notation "rank" => Nat
-- for now just an uninterpreted type for data
type data
immutable individual sample_data : data

immutable individual comm_size : Nat -- used to be immutable, now demonically defined
-- these 2 are based on comm_size and stay the same for the entire program
immutable individual pof2 : Nat -- largest power of 2 ≤ comm_size
immutable individual rem : Nat -- comm_size - pof2
individual mask : Nat

-- ranks that are < comm_size and ≥ 0
relation valid_rank (r : rank) : Prop

-- will probably flip op and operation naming because of C code
type op
individual operation : op
-- non-deterministicly defined in after_init but for now just set to true
relation is_commutative (operation : op) : Prop
-- trusted black box that combines two values
immutable function reduce_op (operation : op) (d1 : data) (d2 : data) : data


-- rank r currently holds data d
relation has_value (r : rank) (d : data) : Prop

-- rank src has sent data d to rank dst but hasn't reduced yet
relation sent_value (src : rank) (dst : rank) (d : data) : Prop

--represents newrank = -1 in C code
relation non_loop_newrank (r : rank) : Prop
-- represents any other newrank value that will be used in the loop
relation loop_newrank (r : rank) (nr : rank) : Prop

relation main_sent (r : rank) : Prop
relation main_recvd (r : rank) : Prop

-- PROBABLY NOT NEEDED, 2 RELATIONS ABOVE DO ITS JOB
-- -- non-power of 2 preprocessing completed
-- relation preprocessing_done (r : rank): Prop

#gen_state
-- assumption [comm_size_positive] comm_size > 0
-- assumption [rank_positive] ∀ (r : rank), r ≥ 0
-- assumption [commutative_op] ∀ (operation : op), is_commutative operation = True ∨ is_commutative operation = False
assumption [comm_size_positive] comm_size > 0
assumption [pof2_is_power_of_two] ∃ k, pof2 = 2^k
assumption [pof2_bounds] pof2 ≤ comm_size ∧ 2 * pof2 > comm_size
assumption [rem_correct] rem = comm_size - pof2

after_init {
  -- comm_size := *
  valid_rank R := R < comm_size ∧ R ≥ 0
  -- pof2 := *
  -- rem := comm_size - pof2
  mask := 1

  operation := *
  is_commutative operation := True -- change to *

  has_value R D := False
  has_value R sample_data := True -- temporary, this sets every processor to the same value
  sent_value SRC DST D := False

  non_loop_newrank R := False
  loop_newrank R NR := False
  --preprocessing_done R := False

  main_sent R := False
  main_recvd R := False
}

-- newrank is only assigned to valid ranks, so preprocessing relation is not needed anymore
-- newrank relations will serve as a check in main loop and will immediately separate correct
/-! *** Pre-processing *** -/
action non_pof2_even (r : rank) (d : data) = {
  -- validation
  require valid_rank r
  require ¬ non_loop_newrank r
  require ∀ NR, ¬ loop_newrank r NR
  --require ∀ R, ¬ preprocessing_done R

  -- loop specifics
  require r < 2 * rem
  require r % 2 = 0

  -- initialization
  require has_value r d

  sent_value r (r + 1) d := True

  non_loop_newrank r := True
  --preprocessing_done r := True
}

action non_pof2_odd (r : rank) (d : data) (recv_d : data) = {
  -- validation
  require valid_rank r
  require ¬ non_loop_newrank r
  require ∀ NR, ¬ loop_newrank r NR
  --require ∀ R, ¬ preprocessing_done R

  -- loop specifics
  require r < 2 * rem
  require r % 2 = 1

  -- initialization
  require has_value r d
  require sent_value (r - 1) r recv_d

  has_value r d := False
  has_value r (reduce_op operation d recv_d) := True

  sent_value (r - 1) r recv_d := False

  loop_newrank r (r / 2) := True
  --preprocessing_done r := True
}

action pof2 (r : rank) = {
  -- validation
  require valid_rank r
  require ¬ non_loop_newrank r
  require ∀ NR, ¬ loop_newrank r NR
  --require ∀ R, ¬ preprocessing_done R

  -- loop specifics
  require r ≥ 2 * rem

  loop_newrank r (r - rem) := True
  --preprocessing_done r := True
}

/-! *** Main loop *** -/
action main_send (r : rank) (d : data) (nr : rank) = {
  -- validation
  require loop_newrank r nr
  -- require ∀ R D, ¬ sent_value R r D -- nothing sent to current r, so it will be the one sending. not needed, since we actually want to be able to send a message if one has been sent to me, what we want is below
  require ¬ main_recvd r
  require ¬ main_sent r

  -- loop specifics
  -- require ¬ non_loop_newrank r -- not sure if needed since loop_newrank r nr makes this never possible to happen and doesn't add much since we already know r is valid as well. not needed since loop_newrank r nr
  require mask < pof2

  -- initialization
  require has_value r d

  let newdst := nr ^ mask
  let dst := if newdst < rem then newdst * 2 + 1 else newdst + rem

  sent_value r dst d := True
  main_sent r := True
}

-- make a main_sent relation: require it to be false before the send, and set it to true after. the relation includes the rank
-- do the same with main_received.
-- if i have all of that, then i create an advance_mask action that requires all ranks to have both sent and received, and then multiply the global mask by 2 and set the sent and received to false in all ranks, which will allow the ranks to go back to main_send action.


-- doesn't deal with commutitivity
action main_recv (r : rank) (d : data) (sndr_r : rank) (sndr_d : data)  = {
  -- validation
  require ∃ NR, loop_newrank r NR
  -- require ¬ non_loop_newrank r -- since we don't need newrank, then this can be used as validation instead. since i'm just denying it should be -1, i'm a bit scared this allows non-valid ranks but i think it should be fine cause of the sent_value under
  require sent_value sndr_r r sndr_d
  -- could put require ∀ R, main_sent R. however, i think the above require is fine.
  require ¬ main_recvd r

  -- loop specifics
  require mask < pof2

  -- initialization
  require has_value r d
  require has_value sndr_r sndr_d

  has_value r d := False
  has_value r (reduce_op operation d sndr_d) := True

  sent_value sndr_r r sndr_d := False
  main_recvd r := True
}

action advance_mask = {
  require ∀ R NR, loop_newrank R NR → main_sent R ∧ main_recvd R

  mask := mask * 2
  main_sent R := False
  main_recvd R := False
}

-- mask being over pof2 serves to force this to only happen after the main loop
 /-! *** Post Main Loop *** -/
action main_non_loop_odd (r : rank) (d : data) = {
  -- validation
  require mask ≥ pof2 -- is this valid? there's no test for this in the C code but it does what I want. also, if mask is only changed in that loop then i would also not need any validation in terms of newrank stuff. i'm wondering if this is a valid way to represent it since i'm basically assuming that there would be no bugs in the code for this to work.
  require valid_rank r

  -- loop specifics
  require r < 2 * rem
  require r % 2 = 1

  -- initialization
  require has_value r d

  sent_value r (r - 1) d := True
}

action main_non_loop_even (r : rank) (d : data) (recv_d : data) = {
  -- validation
  require mask ≥ pof2

  -- loop specifics
  require r < 2 * rem
  require r % 2 = 0

  -- initialization
  require has_value r d
  require sent_value (r + 1) r recv_d

  has_value r d := False
  has_value r (reduce_op operation d recv_d) := True

  sent_value (r + 1) r recv_d := False
}

-- Start with these basic ones
invariant [unique_value] ∀ r d1 d2, has_value r d1 ∧ has_value r d2 → d1 = d2
invariant [valid_participants] ∀ r nr, loop_newrank r nr → valid_rank r
invariant [unique_newrank] ∀ r nr1 nr2, loop_newrank r nr1 ∧ loop_newrank r nr2 → nr1 = nr2
invariant [excluded_dont_participate] ∀ r, non_loop_newrank r → (∀ nr, ¬ loop_newrank r nr)
invariant [no_self_send] ∀ r d, ¬ sent_value r r d
invariant [sent_to_valid] ∀ src dst d, sent_value src dst d → valid_rank src ∧ valid_rank dst
invariant [even_excluded_correctly] ∀ r, valid_rank r → (r < 2 * rem ∧ r % 2 = 0) → non_loop_newrank r
invariant [mask_is_power_of_2] ∃ k, mask = 2^k



safety [no_invalid_ranks] ∀ r, ¬ valid_rank r → r ≥ comm_size

#gen_spec
#check_invariants

-- sat trace {

-- } by { bmc_sat }

-- Basic state consistency
-- invariant [unique_value] ∀ r d1 d2, has_value r d1 ∧ has_value r d2 → d1 = d2

-- invariant [unique_newrank] ∀ r nr1 nr2, loop_newrank r nr1 ∧ loop_newrank r nr2 → nr1 = nr2

-- invariant [valid_participants] ∀ r nr, loop_newrank r nr → valid_rank r

-- invariant [excluded_dont_participate] ∀ r, non_loop_newrank r → (∀ nr, ¬ loop_newrank r nr)

-- -- Communication well-formedness
-- invariant [sent_to_valid] ∀ src dst d, sent_value src dst d → valid_rank src ∧ valid_rank dst

-- invariant [no_self_send] ∀ r d, ¬ sent_value r r d

-- -- Preprocessing correctness
-- invariant [even_excluded_correctly] ∀ r, (r < 2 * rem ∧ r % 2 = 0) → non_loop_newrank r

-- -- Mask progression
-- invariant [mask_is_power_of_2] ∃ k, mask = 2^k

-- invariant [mask_bounded] mask ≤ 2 * pof2



-- -- Round synchronization
-- invariant [participants_same_round] ∀ r1 r2 nr1 nr2,
--   (loop_newrank r1 nr1 ∧ loop_newrank r2 nr2 ∧ main_sent r1 ∧ main_sent r2) →
--   (∃ dst1 dst2, sent_value r1 dst1 * ∧ sent_value r2 dst2 *)

-- -- Newrank bounds
-- invariant [newrank_bounded] ∀ r nr, loop_newrank r nr → nr < pof2

-- -- Every valid rank has some value
-- invariant [all_valid_have_data] ∀ r, valid_rank r → ∃ d, has_value r d

-- -- Communication preserves data
-- invariant [sender_has_data] ∀ src dst d, sent_value src dst d → has_value src d

end AllreduceRecursiveDoubling


-- -- Atomic sendrecv + reduce for both partners
-- action main_exchange (r1 : rank) (r2 : rank) (d1 : data) (d2 : data) (nr1 : rank) (nr2 : rank) = {
--   require preprocessing_done
--   require mask < pof2

--   -- prevents duplicate exchanges
--   require r1 < r2

--   -- Both ranks must be participating in the loop
--   require loop_newrank r1 nr1
--   require loop_newrank r2 nr2

--   -- They must be partners for this round
--   require nr2 = nr1 ^ mask
--   require nr1 = nr2 ^ mask  -- symmetric check

--   -- Calculate actual destinations
--   let dst1 := if nr2 < rem then nr2 * 2 + 1 else nr2 + rem
--   let dst2 := if nr1 < rem then nr1 * 2 + 1 else nr1 + rem
--   require r2 = dst1
--   require r1 = dst2

--   -- Both must have current values
--   require has_value r1 d1
--   require has_value r2 d2

--   -- Both exchange and reduce simultaneously
--   let new_d1 := reduce_op operation d1 d2
--   let new_d2 := reduce_op operation d2 d1

--   has_value r1 d1 := False
--   has_value r2 d2 := False
--   has_value r1 new_d1 := True
--   has_value r2 new_d2 := True

--   mask := mask * 2
-- }


-- -- Safety properties
-- safety [agreement] completed N1 ∧ completed N2 ∧ current_value N1 V1 ∧ current_value N2 V2 → V1 = V2

-- -- Invariants
-- invariant [unique_current_value] current_value N V1 ∧ current_value N V2 → V1 = V2

-- invariant [unique_initial_value] initial_value N V1 ∧ initial_value N V2 → V1 = V2

-- invariant [completed_has_value] completed N → ∃ V, current_value N V

-- invariant [excluded_not_participating] excluded_even N → ¬ participating N

-- invariant [participating_active] participating N ∧ max_rounds_reached →
--   ∃ V, current_value N V

-- invariant [unique_round] current_round R1 ∧ current_round R2 → R1 = R2
