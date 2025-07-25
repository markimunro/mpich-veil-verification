import Veil

-- https://github.com/markyuen/tlaplus-to-ivy/blob/main/ivy/suzuki_kasami_int.ivy

veil module SuzukiKasamiNats


type node
notation "seq_t" => Nat
immutable individual init_node : node

@[actSimp, invSimp] abbrev next : seq_t → seq_t → Prop := λ x y => (x + 1) = y


-- State

--- Nodes
relation n_have_privilege : node → Prop
relation n_requesting : node → Prop
function n_RN : node → node → seq_t
-- the sequence number of the most recently granted request by `node`
function n_token_seq : node → seq_t

--- Requests
relation reqs : node → node → seq_t → Prop

--- Tokens
relation t_for : seq_t → node → Prop
function t_LN : seq_t → node → seq_t
relation t_q : seq_t → node → Prop

--- Critical section
relation crit : node → Prop

#gen_state

after_init {
  n_have_privilege N := N = init_node;
  n_requesting N := False;
  n_RN N M := 0;
  n_token_seq N := if N = init_node then 1 else 0;

  reqs N M I := False;

  t_for I N := I = 1 ∧ N = init_node;
  t_LN I N := 0;
  t_q I N := False;

  crit N := False
}

action request (n : node) = {
  require ¬ n_requesting n;
  n_requesting n := True;
  if (¬ n_have_privilege n) then
    let k := (n_RN n n) + 1
    n_RN n n := k;
    reqs N n (n_RN n n) := N ≠ n
}

-- node `n` receiving a request from `m` with sequence number `r`
action rcv_request (n : node) (m : node) (r : seq_t) = {
  require reqs n m r;
  n_RN n m := if Nat.le r (n_RN n m) then n_RN n m else r;
  if (n_have_privilege n ∧ ¬ n_requesting n ∧ next (t_LN (n_token_seq n) m) (n_RN n m)) then
    n_have_privilege n := False;
    let k : seq_t := (n_token_seq n) + 1
    t_for k m := True;
    t_LN k N := t_LN (n_token_seq n) N;
    t_q k N := t_q (n_token_seq n) N
}

action rcv_privilege (n: node) (t: seq_t) = {
  require t_for t n;
  require Nat.lt (n_token_seq n) t;
  n_have_privilege n := True;
  n_token_seq n := t
}

action enter (n : node) = {
    require n_have_privilege n
    require n_requesting n
    -- Add n to crit
    crit n := True
}

action exit (n : node) = {
  require crit n;
  crit n := False;
  n_requesting n := False;
  t_LN (n_token_seq n) n := n_RN n n;
  t_q (n_token_seq n) N := next (t_LN (n_token_seq n) N) (n_RN n N);
  if m : (t_q (n_token_seq n) m) then
    t_q (n_token_seq n) m := False;
    n_have_privilege n := False;
    let k : seq_t := (n_token_seq n) + 1
    t_for k m := True;
    t_LN k N := t_LN (n_token_seq n) N;
    t_q k N := t_q (n_token_seq n) N
}

-- Invariants
safety [mutex] (crit N ∧ crit M) → N = M
invariant [unique_tokens] ((t_for I N) ∧ (t_for I M)) → N = M
invariant ((n_token_seq N) ≠ 0) → t_for (n_token_seq N) N
invariant [curr_priv1] ((n_have_privilege N) ∧ N ≠ M) → (n_token_seq M) < (n_token_seq N)
invariant [curr_priv2] ((n_have_privilege N) ∧ (t_for I M)) → I ≤ (n_token_seq N)
invariant [no_request_to_self] (reqs N M I) → N ≠ M
invariant ((t_for I N) ∧ ((J + 1) = I) ∧ (t_for J M)) → N ≠ M
invariant [token_relation] ((t_for I N) ∧ (t_for J M) ∧ I < J) → I ≤ (n_token_seq N)
invariant [one_priv] (n_have_privilege N ∧ n_have_privilege M) → N = M
invariant [allowed_crit] (crit N) → (n_have_privilege N ∧ n_requesting N)

#gen_spec

sat trace {
  request
  enter
  exit
  request
  enter
  exit
} by bmc_sat

unsat trace {
  enter
  enter
  any 2 actions
} by bmc


set_option veil.smt.finiteModelFind false in
#time #check_invariants

@[invProof]
  theorem enter_mutex_manual :
      ∀ (st : @State node) (st' : @State node),
        (@System node node_dec node_ne).assumptions st →
          (@System node node_dec node_ne).inv st →
            (@SuzukiKasamiNats.enter.tr node node_dec node_ne) st st' ->
              @SuzukiKasamiNats.mutex node node_dec node_ne st' := by
  intros st st' _ inv
  simp[enter.tr, invSimp] at *
  rcases inv with ⟨allowed_crit, one_priv, _⟩
  rintro n priv req ⟨⟩  N M critN critM; simp at *
  apply one_priv
  . by_cases h : (N = n) <;> simp [allowed_crit, h, priv, critN]
  . by_cases h : (M = n) <;> simp [allowed_crit, h, priv, critM]

end SuzukiKasamiNats
