import Mathlib.Data.Stream.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Stream.Init
import TuringMachine.Defs

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

def list_repeat (n : Nat) (x : List Γ) : List Γ :=
  match n with
  | 0 => []
  | (n'+1) => x ++ list_repeat n' x

def append_to_repeated (n : Nat) (l : List Γ) : Stream' Γ -> Stream' Γ :=
  Stream'.appendStream' (list_repeat n l)

theorem append_one_eq_cons (s : Γ) : append_to_repeated 1 [s] = Stream'.cons s := rfl

theorem append_two_eq_cons (s1 s2 : Γ) : append_to_repeated 1 [s1, s2] = Stream'.cons s1 ∘ Stream'.cons s2 := rfl

theorem append_sum : append_to_repeated (n + k) l s = (append_to_repeated n l $ append_to_repeated k l s) := by
  induction n with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ n' ih =>
    rw [←Nat.add_one, Nat.add_assoc]
    simp [Nat.add_comm]
    rw [←Nat.add_assoc]
    unfold append_to_repeated
    conv =>
      pattern list_repeat (n' + 1) l 
      unfold list_repeat
    conv => lhs; unfold list_repeat
    simp
    unfold append_to_repeated at ih
    rw [Stream'.append_append_stream]
    conv => rhs; rw [Stream'.append_append_stream]
    rw [ih]

theorem append_get' (h : k < n) : (append_to_repeated n [a] s) k = a := by
  induction n with
  | zero =>
    exact False.elim $ Nat.not_lt_zero k h
  | succ n' =>
    unfold append_to_repeated
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

theorem append_get (k n : Nat) (l : List T) (s : Stream' T) : (append_to_repeated k l s) (l.length * k + n) = s n := by
  cases k with
  | zero =>
    simp
    rfl
  | succ k' => 
    rw [←Nat.add_one, append_sum, Nat.left_distrib, Nat.add_assoc]
    rw [append_get k' (l.length * 1 + n) l (append_to_repeated 1 l s)]
    unfold append_to_repeated
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
  append_to_repeated 0 l = id := rfl

theorem append_repeated_one (n : Nat) (s : Γ) :
  append_to_repeated (n + 1) [s] = append_to_repeated 1 [s] ∘ append_to_repeated n [s]
  := by
    rw [append_one_eq_cons]
    have : append_to_repeated (n + 1) [s] = Stream'.appendStream' (list_repeat (n + 1) [s]) := rfl
    rw [this, list_repeat_one_cons, append_stream_one]
    rfl

theorem cons_to_const (s : Γ) : Stream'.cons s (Stream'.const s) = (Stream'.const s) := by
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

