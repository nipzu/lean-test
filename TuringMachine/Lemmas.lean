import Mathlib.Data.Stream.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Stream.Init
import TuringMachine.Defs
import Mathlib.Tactic.Linarith.Frontend

variable {Q Γ : Type _}
variable {δ : Q -> Γ -> Option Q × Γ × Direction}


inductive State5 where
  | A : State5
  | B : State5
  | C : State5
  | D : State5
  | E : State5

inductive Symbol2 where
  | V0 : Symbol2
  | V1 : Symbol2

def Symbol2.decEq (a b : Symbol2) : Decidable (Eq a b) :=
   match a, b with
   | V0, V0 => isTrue rfl
   | V0, V1  => isFalse (fun h => Symbol2.noConfusion h)
   | V1, V0  => isFalse (fun h => Symbol2.noConfusion h)
   | V1, V1   => isTrue rfl

instance : DecidableEq Symbol2 :=
   Symbol2.decEq


def TuringMachine.decNotHalted (tm : TuringMachine δ) : Decidable (tm.is_not_halted) := by
  unfold TuringMachine.is_not_halted
  exact Bool.decEq _ true

instance : DecidablePred (α := TuringMachine δ) TuringMachine.is_not_halted := by
  unfold TuringMachine.is_not_halted
  unfold DecidablePred
  intro tm
  simp
  exact Bool.decEq _ true

def list_repeat (n : Nat) (x : List Γ) : List Γ :=
  match n with
  | 0 => []
  | (n'+1) => x ++ list_repeat n' x

infix:80 " ** " => list_repeat

def append_to_repeated (n : Nat) (l : List Γ) : Stream' Γ -> Stream' Γ :=
  Stream'.appendStream' (list_repeat n l)

theorem append_one_eq_cons (s : Γ) : append_to_repeated 1 [s] = Stream'.cons s := rfl

theorem append_two_eq_cons (s1 s2 : Γ) : append_to_repeated 1 [s1, s2] = Stream'.cons s1 ∘ Stream'.cons s2 := rfl

theorem append_sum : (n + k) ** l ++ₛ s = (n ** l ++ₛ (k ** l ++ₛ s)) := by
  induction n with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ n' ih =>
    rw [←Nat.add_one, Nat.add_assoc]
    simp [Nat.add_comm]
    rw [←Nat.add_assoc]
    conv =>
      pattern list_repeat (n' + 1) l 
      unfold list_repeat
    conv => lhs; unfold list_repeat
    simp
    unfold append_to_repeated at ih
    rw [Stream'.append_append_stream]
    conv => rhs; rw [Stream'.append_append_stream]
    rw [ih]

theorem append_get' (h : k < n) : (n ** [a] ++ₛ s) k = a := by
  induction n with
  | zero =>
    exact False.elim $ Nat.not_lt_zero k h
  | succ n' =>
    unfold list_repeat
    cases k with
    | zero => rfl
    | succ k' => 
      rw [Stream'.append_append_stream]
      unfold Stream'.appendStream'
      unfold Stream'.cons
      simp
      rw [Stream'.nil_append_stream]
      have h' : k' < n' := by rw [←Nat.add_one, ←Nat.add_one] at h; exact Nat.lt_of_add_lt_add_right h
      exact append_get' h'

theorem get_drop (n m : Nat) (s : Stream' α) : (Stream'.drop m s) n = s (n + m) :=
  rfl

theorem append_get (k n : Nat) (l : List T) (s : Stream' T) : (k ** l ++ₛ s) (l.length * k + n) = s n := by
  cases k with
  | zero =>
    simp
    rfl
  | succ k' => 
    rw [←Nat.add_one, append_sum, Nat.left_distrib, Nat.add_assoc]
    rw [append_get k' (l.length * 1 + n) l (1 ** l ++ₛ s)]
    unfold list_repeat
    unfold list_repeat
    simp
    rw [Nat.add_comm]
    rw [←get_drop n l.length (l ++ₛ s)]
    rw [Stream'.drop_append_stream]

theorem append_stream_one (x : Γ) (xs : List Γ) :
  Stream'.appendStream' (x :: xs) = Stream'.cons x ∘ Stream'.appendStream' xs
    := rfl

theorem list_repeat_one_cons (n : Nat) (s : Γ) :
  list_repeat (n + 1) [s] = s :: list_repeat n [s]
    := rfl

theorem append_repeated_zero (l : List Γ) :
  0 ** l ++ₛ s = s := rfl

theorem append_repeated_one (n : Nat) (s : Γ) :
  append_to_repeated (n + 1) [s] = append_to_repeated 1 [s] ∘ append_to_repeated n [s]
  := by
    rw [append_one_eq_cons]
    have : append_to_repeated (n + 1) [s] = Stream'.appendStream' (list_repeat (n + 1) [s]) := rfl
    rw [this, list_repeat_one_cons, append_stream_one]
    rfl

theorem cons_to_const (a : Γ) : [a] ++ₛ (Stream'.const a) = (Stream'.const a) := by
  funext n
  cases n <;> rfl

def tm_succeeds (tm1 tm2 : TuringMachine δ) :=
  ∃n : Nat, (TuringMachine.advance^[n] tm1) = tm2

infix:60 " =>> " => tm_succeeds

theorem trans_succeeds {tm1 tm2 tm3 : TuringMachine δ} (h1 : tm1 =>> tm2) (h2 : tm2 =>> tm3) : tm1 =>> tm3 := by
  let ⟨n1, t1⟩ := h1
  let ⟨n2, t2⟩ := h2
  exists (n2 + n1)
  rw [Function.iterate_add_apply, t1, t2]

instance : Trans (tm_succeeds (Q := Q) (Γ := Γ) (δ := δ)) tm_succeeds tm_succeeds where
  trans := trans_succeeds

theorem halted_to_halted (tm : TuringMachine δ) (k : Nat) (h : ¬(TuringMachine.is_not_halted tm)) : ¬(TuringMachine.is_not_halted (TuringMachine.advance^[k] tm)) :=
  match k with
  | 0 => h
  | k' + 1 => by
    simp [Function.iterate_add_apply]
    apply halted_to_halted (TuringMachine.advance tm) k'
    let (TuringMachine.mk tape state) := tm
    cases state
    . let tm' : TuringMachine δ := TuringMachine.advance { tape := tape, state := none }
      have : tm'.state = none := rfl
      let (TuringMachine.mk tape' state') := tm'
      cases state'
      . intro hnh
        exact (Bool.self_ne_not false) hnh  
      . contradiction
    . contradiction

theorem not_halted_if_next_not_halted (tm : TuringMachine δ) (h : (TuringMachine.advance tm).is_not_halted) : tm.is_not_halted := by
  unfold TuringMachine.is_not_halted
  rw [←Option.ne_none_iff_isSome]
  intro hn
  have : tm.advance.state = none := by
    unfold TuringMachine.advance
    simp [hn]
  unfold TuringMachine.advance at h
  simp [hn] at h
  unfold TuringMachine.is_not_halted at h
  rw [hn] at h
  simp at h

theorem not_halted_if_later_not_halted (tm : TuringMachine δ) (k : Nat) (h : TuringMachine.is_not_halted (TuringMachine.advance^[k] tm)) : TuringMachine.is_not_halted tm := by
  induction k with
  | zero => exact h
  | succ k' ih =>
    have := not_halted_if_next_not_halted (TuringMachine.advance^[k'] tm)
    conv at this => arg 1; arg 1; rw [←Function.iterate_one TuringMachine.advance]; arg 3; simp
    rw [←Function.iterate_add_apply] at this
    rw [Nat.add_comm] at this
    exact ih (this h)

lemma reaches_f_n_with_ge_n_steps
  (f : Nat -> TuringMachine δ)
  (hs : ∀n, f n =>> f (n + 1))
  (hnn : ∀n, f n ≠ f (n + 1))
  (n : Nat)
  : ∃k, TuringMachine.advance^[k] (f 0) = f n ∧ n <= k :=
  by
    induction n with
    | zero => exists 0
    | succ n' ih => 
      let ⟨k', ⟨hk', hk''⟩⟩ := ih
      let ⟨m, hm⟩ := hs n'
      exists m + k'
      apply And.intro
      . rw [Function.iterate_add_apply, hk', hm]
      . cases m with
        | zero =>
          simp at hm
          have t2 := hnn n'
          have := t2 hm
          exfalso
          exact this
        | succ m' =>
          have t1 : 1 <= m' + 1 := by
            apply Nat.le_add_left
          rw [←Nat.one_add]
          exact Nat.add_le_add t1 hk''

lemma reaches_some
  (f : Nat -> TuringMachine δ)
  (hs : ∀n, f n =>> f (n + 1))
  (hnn : ∀n, f n ≠ f (n + 1))
  (starting_machine : TuringMachine δ)
  (hl : ∃l, TuringMachine.advance^[l] starting_machine = f 0)
  (n : Nat)
  : ∃ m k : Nat, TuringMachine.advance^[n + k] starting_machine = f m :=
  let ⟨l, hl'⟩ := hl
  Decidable.casesOn (Nat.decLe n l)
    (fun t => by
      rw [Nat.not_le] at t
      have := Nat.succ_le_of_lt t 
      let ⟨n', hn'⟩ := Nat.exists_eq_add_of_le this
      rw [hn']
      exists (n' + 1)
      have ⟨m', ⟨hm', hm''⟩⟩ := reaches_f_n_with_ge_n_steps f hs hnn (n' + 1)
      rw [←hl'] at hm'
      rw [←Function.iterate_add_apply] at hm'
      exists (m' - n' - 1)
      have : Nat.succ l + n' + (m' - n' - 1) = m' + l := by
        rw [←Nat.sub_add_eq, ←Nat.add_sub_assoc hm'']
        rw [Nat.sub_eq_of_eq_add]
        linarith
      rw [this]
      exact hm'
    )
    (fun t => by
      exists 0
      exists (l - n)
      rw [Nat.add_sub_of_le t]
      exact hl'
    )

lemma halted_state_none
  (tm : TuringMachine δ)
  (h : ¬tm.is_not_halted)
  : tm.state = none :=
    (Bool.decEq (Option.isSome tm.state) true).casesOn
    (fun h' => by
      rw [Option.not_isSome_iff_eq_none] at h'
      exact h'
    )
    (fun h' => by
      unfold TuringMachine.is_not_halted at h
      exact False.elim (h h') 
    )

lemma next_of_halted_halted
  (tm : TuringMachine δ)
  (h : ¬tm.is_not_halted)
  (n : Nat)
  : ¬(TuringMachine.advance^[n] tm).is_not_halted := by
    cases n with
    | zero => exact h
    | succ n' =>
      rw [←Nat.add_one, Function.iterate_add_apply]
      apply next_of_halted_halted
      have t1 : tm.state = none := halted_state_none tm h
      unfold TuringMachine.advance
      simp
      rw [t1]
      simp
      exact h

lemma next_of_halted_eq
  (tm : TuringMachine δ)
  (h : ¬tm.is_not_halted)
  (n : Nat)
  : (TuringMachine.advance^[n] tm) = tm := by
    cases n
    . rfl
    case succ n' => 
      rw [←Nat.one_add, Function.iterate_add_apply]
      simp [next_of_halted_eq tm h n']
      have t1 := halted_state_none tm h
      unfold TuringMachine.advance
      rw [t1]

lemma tm_not_halted
  (f : Nat -> TuringMachine δ)
  (hs : ∀n, f n =>> f (n + 1))
  (hnn : ∀n, f n ≠ f (n + 1))
  (n : Nat)
  : (f n).is_not_halted :=
    (f n).decNotHalted.casesOn
    (fun h => by
      let ⟨m, hm⟩ := hs n
      rw [next_of_halted_eq (f n) h m] at hm
      exact False.elim $ (hnn n) hm
    )
    id

theorem tm_not_halt'
  (f : Nat -> TuringMachine δ)
  (starting_machine : TuringMachine δ)
  (hs : ∀n, f n =>> f (n + 1))
  (hnn : ∀n, f n ≠ f (n + 1))
  (hl : starting_machine =>> f 0) 
  : TuringMachine.does_not_halt starting_machine := by
  intro n
  have ⟨m,⟨k, h⟩⟩ := reaches_some f hs hnn starting_machine hl n
  have t1 := not_halted_if_later_not_halted (TuringMachine.advance^[n] starting_machine) k
  rw [←Function.iterate_add_apply, Nat.add_comm, h] at t1
  have t2 : (f m).is_not_halted := tm_not_halted f hs hnn m
  exact t1 t2
