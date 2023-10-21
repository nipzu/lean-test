import TuringMachine2
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Stream.Init

inductive State where
  | ST_A : State
  | ST_B : State
  | ST_C : State
  | ST_D : State
  | ST_E : State

inductive Symbol where
  | SYM_0 : Symbol
  | SYM_1 : Symbol

def Symbol.decEq (a b : Symbol) : Decidable (Eq a b) :=
   match a, b with
   | SYM_0, SYM_0 => isTrue rfl
   | SYM_0, SYM_1  => isFalse (fun h => Symbol.noConfusion h)
   | SYM_1, SYM_0  => isFalse (fun h => Symbol.noConfusion h)
   | SYM_1, SYM_1   => isTrue rfl

instance : DecidableEq Symbol :=
   Symbol.decEq

def transition : State -> Symbol -> Option State × Symbol × Direction :=
  fun state symbol =>
    match state, symbol with
    | State.ST_A, Symbol.SYM_0 => (some State.ST_B, Symbol.SYM_1, Direction.right)
    | State.ST_A, Symbol.SYM_1 => (some State.ST_E, Symbol.SYM_1, Direction.right)
    | State.ST_B, Symbol.SYM_0 => (some State.ST_C, Symbol.SYM_1, Direction.left)
    | State.ST_B, Symbol.SYM_1 => (some State.ST_B, Symbol.SYM_1, Direction.right)
    | State.ST_C, Symbol.SYM_0 => (some State.ST_A, Symbol.SYM_0, Direction.right)
    | State.ST_C, Symbol.SYM_1 => (some State.ST_D, Symbol.SYM_0, Direction.left)
    | State.ST_D, Symbol.SYM_0 => (some State.ST_B, Symbol.SYM_1, Direction.left)
    | State.ST_D, Symbol.SYM_1 => (some State.ST_D, Symbol.SYM_1, Direction.left)
    | State.ST_E, Symbol.SYM_0 => (none,            Symbol.SYM_1, Direction.left)
    | State.ST_E, Symbol.SYM_1 => (some State.ST_A, Symbol.SYM_0, Direction.right)

def starting_machine : TuringMachine transition := 
  TuringMachine.mk (Tape.blank Symbol.SYM_0) (State.ST_A)

namespace proof

def list_repeat {A : Type} (n : Nat) (x : List A) : List A :=
  match n with
  | 0 => []
  | (n'+1) => x ++ list_repeat n' x

def append_to_repeated {A : Type} (n : Nat) (l : List A) : Stream' A -> Stream' A :=
  Stream'.appendStream' (list_repeat n l)

-- state: C
-- tape: C0 + n * [11] + [0] + n * [1]
def A (n : Nat) : TuringMachine transition :=
  let right_tape : Stream' Symbol := 
    append_to_repeated (2*n) [Symbol.SYM_1] $
    Stream'.cons Symbol.SYM_0 $
    append_to_repeated n [Symbol.SYM_1] $
    Stream'.const Symbol.SYM_0
  let tape : Tape Symbol := Tape.mk (Stream'.const Symbol.SYM_0) Symbol.SYM_0 right_tape
  TuringMachine.mk tape State.ST_C

-- state: E
-- tape: nl * [01] + E1 + nr * [11] + (nr + nl) * [1]
def A' (nl : Nat) (nr : Nat) : TuringMachine transition :=
  let left_tape : Stream' Symbol := 
    append_to_repeated nl [Symbol.SYM_1, Symbol.SYM_0] $
    Stream'.const Symbol.SYM_0
  let right_tape : Stream' Symbol := 
    append_to_repeated (2*nr) [Symbol.SYM_1] $
    Stream'.cons Symbol.SYM_0 $
    append_to_repeated (nr + nl) [Symbol.SYM_1] $
    Stream'.const Symbol.SYM_0
  TuringMachine.mk (Tape.mk left_tape Symbol.SYM_1 right_tape) State.ST_E

-- state: B
-- tape: nl * [01] + nlm * [1] + D1 + nrm * [1] + [0] + nr * [1]
def M (nl nlm nrm nr : Nat) : TuringMachine transition :=
  let left_tape : Stream' Symbol := 
    append_to_repeated nlm [Symbol.SYM_1] $
    append_to_repeated nl [Symbol.SYM_1, Symbol.SYM_0] $
    Stream'.const Symbol.SYM_0
  let right_tape : Stream' Symbol := 
    append_to_repeated nrm [Symbol.SYM_1] $
    Stream'.cons Symbol.SYM_0 $
    append_to_repeated nr [Symbol.SYM_1] $
    Stream'.const Symbol.SYM_0
  TuringMachine.mk (Tape.mk left_tape Symbol.SYM_1 right_tape) State.ST_B

-- state: D
-- tape: nl * [01] + nlm * [1] + D1 + nrm * [1] + [0] + nr * [1]
def M' (nl nlm nrm nr : Nat) : TuringMachine transition :=
  let left_tape : Stream' Symbol := 
    append_to_repeated nlm [Symbol.SYM_1] $
    append_to_repeated nl [Symbol.SYM_1, Symbol.SYM_0] $
    Stream'.const Symbol.SYM_0
  let right_tape : Stream' Symbol := 
    append_to_repeated nrm [Symbol.SYM_1] $
    Stream'.cons Symbol.SYM_0 $
    append_to_repeated nr [Symbol.SYM_1] $
    Stream'.const Symbol.SYM_0
  TuringMachine.mk (Tape.mk left_tape Symbol.SYM_1 right_tape) State.ST_D

theorem reaches_A1 : TuringMachine.advance^[5] starting_machine = A 1 := rfl

theorem append_one_eq_cons (s : Symbol) : append_to_repeated 1 [s] = Stream'.cons s := rfl

theorem append_two_eq_cons (s1 s2 : Symbol) : append_to_repeated 1 [s1, s2] = Stream'.cons s1 ∘ Stream'.cons s2 := rfl

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

theorem append_stream_one {A : Type} (x : A) (xs : List A) :
  Stream'.appendStream' (x :: xs) = Stream'.cons x ∘ Stream'.appendStream' xs
  := rfl

theorem list_repeat_one_cons {A : Type} (n : Nat) (s : A) :
  list_repeat (n + 1) [s] = s :: list_repeat n [s]
  := rfl

theorem append_repeated_zero (l : List Symbol) :
  append_to_repeated 0 l = id := rfl

theorem append_repeated_one (n : Nat) (s : Symbol) :
  append_to_repeated (n + 1) [s] = append_to_repeated 1 [s] ∘ append_to_repeated n [s]
  := by
    rw [append_one_eq_cons]
    have : append_to_repeated (n + 1) [s] = Stream'.appendStream' (list_repeat (n + 1) [s]) := rfl
    rw [this, list_repeat_one_cons, append_stream_one]
    rfl

theorem cons_to_const (s : Symbol) : Stream'.cons s (Stream'.const s) = (Stream'.const s) := by
  funext n
  cases n <;> rfl

def tm_succeeds {Q Γ : Type _} {δ : Q -> Γ -> (Option Q × Γ × Direction)} (tm1 tm2 : TuringMachine δ) :=
  ∃n : Nat, (TuringMachine.advance^[n] tm1) = tm2

infix:60 " =>> " => tm_succeeds

theorem trans_succeeds {tm1 tm2 tm3 : TuringMachine δ} (h1 : tm1 =>> tm2) (h2 : tm2 =>> tm3) : tm1 =>> tm3 := by
  let ⟨n1, t1⟩ := h1
  let ⟨n2, t2⟩ := h2
  exists (n2 + n1)
  rw [Function.iterate_add_apply, t1, t2]

instance : Trans (tm_succeeds (Q := Q) (Γ := Γ) (δ := δ)) tm_succeeds tm_succeeds where
  trans := trans_succeeds

theorem A'_to_M_ : A' (n + 1) 0 =>> M (n + 2) 0 n 0 := by
  unfold tm_succeeds
  exists 2
  ext : 1
  . ext : 1
    repeat rfl
    . have t1 : (TuringMachine.advance^[2] (A' (n + 1) 0)).tape.right_half = 
        (append_to_repeated n [Symbol.SYM_1] $ Stream'.const Symbol.SYM_0) := by
          conv => arg 2; rw [←Nat.zero_add n]
      unfold M; conv => rhs; simp
      rw [append_repeated_zero, t1]
      simp
      rw [cons_to_const]
  . rfl

theorem M_to_M_iter_ : M nl nlm nrm nr =>> M nl (nlm + nrm) 0 nr := by
  cases nrm
  . exists 0
  case succ nrm' =>
    calc M nl nlm (nrm' + 1) nr
      _ =>> M nl (nlm + 1) nrm' nr       := by exists 1
      _ =>> M nl (nlm + 1 + nrm') 0 nr   := M_to_M_iter_
      _ =   M nl (nlm + (nrm' + 1)) 0 nr := by rw [Nat.add_assoc]; conv => lhs; arg 2; arg 2; rw [Nat.add_comm]

theorem M'_to_M'_iter_ : M' nl nlm nrm nr =>> M' nl 0 (nrm + nlm) nr := by
  cases nlm
  . exists 0
  case succ nlm' =>
    calc M' nl (nlm' + 1) nrm nr
      _ =>> M' nl nlm' (nrm + 1) nr       := by exists 1
      _ =>> M' nl 0 (nrm + 1 + nlm') nr   := M'_to_M'_iter_
      _ =   M' nl 0 (nrm + (nlm' + 1)) nr := by
        rw [Nat.add_assoc]
        conv => lhs; arg 3; arg 2; rw [Nat.add_comm]

theorem Ml_to_M'l_ : M nl 0 (nm + 1) nr =>> M' nl 0 nm (nr + 1) := by
  calc M nl 0 (nm + 1) nr
    _ =>> M nl (0 + (nm + 1)) 0 nr  := M_to_M_iter_
    _ =   M nl (nm + 1) 0 nr        := by simp
    _ =>> M' nl nm 0 (nr + 1)       := by exists 3
    _ =>> M' nl 0 (0 + nm) (nr + 1) := M'_to_M'_iter_
    _ =   M' nl 0 nm (nr + 1)       := by rw [Nat.zero_add]

theorem Ml_to_Ml_ : M (nl + 2) 0 (nm + 1) nr =>> M (nl + 1) 0 (nm + 2) (nr + 1) := by
  calc M (nl + 2) 0 (nm + 1) nr
    _ =>> M' (nl + 2) 0 nm (nr + 1)      := Ml_to_M'l_
    _ =>> M (nl + 1) 0 (nm + 2) (nr + 1) := by exists 4

theorem Ml_to_A_iter : M (nl + 1) 0 (2 * nr + nl + 1) (nr + 1) =>> A (nl + nr + 2) := by
  cases nl
  . simp
    calc M 1 0 (2 * nr + 1) (nr + 1)
      _ =>> M' 1 0 (2 * nr) (nr + 2) := Ml_to_M'l_
      _ =>> A (nr + 2)               := by exists 4
  case succ nl' =>
    have t1 : 2 * nr + (nl' + 1) + 1 = 2 * nr + 1 + nl' + 1 := by linarith
    have t2 : 2 * (nr + 1) + nl' + 1 = (2*nr + 1 + nl') + 2 := by linarith
    have t3 : (nl' + 1) + nr + 2 = nl' + (nr + 1) + 2       := by linarith
    calc M (nl' + 2) 0 (2 * nr + (nl' + 1) + 1) (nr + 1)
      _ =   M (nl' + 2) 0 ((2*nr + 1 + nl') + 1) (nr + 1)   := by rw [t1]
      _ =>> M (nl' + 1) 0 ((2*nr + 1 + nl') + 2) (nr + 2)   := Ml_to_Ml_
      _ =   M (nl' + 1) 0 (2 * (nr + 1) + nl' + 1) (nr + 2) := by rw [t2]
      _ =>> A (nl' + (nr + 1) + 2) := Ml_to_A_iter
      _ =   A ((nl' + 1) + nr + 2) := by rw [t3]

theorem A'_to_A'_ : A' nl (nr + 1) =>> A' (nl + 1) nr := by
  exists 2
  ext : 1
  . ext : 1
    repeat rfl
    . conv => rhs; unfold A'
      simp
      have t1 : nr + (nl + 1) = (nr + 1) + nl := by linarith
      rw [t1]
      rfl
  . rfl

theorem A'_to_A'_iter_ : A' nl nr =>> A' (nl + nr) 0 := by
  cases nr
  . exists 0
  case succ nr' =>
    have t1 : nl + 1 + nr' = nl + (nr' + 1) := by linarith
    calc A' nl (nr' + 1)
      _ =>> A' (nl + 1) nr'       := A'_to_A'_
      _ =>> A' (nl + 1 + nr') 0   := A'_to_A'_iter_
      _ =   A' (nl + (nr' + 1)) 0 := by rw [t1]

theorem A_to_A_ : A (n + 2) =>> A (n + 3) := by
  calc A (n + 2)
    _ =>> A' 1 (n + 1)          := by exists 2
    _ =>> A' (1 + (n + 1)) 0    := A'_to_A'_iter_
    _ =   A' (n + 2) 0          := by rw [Nat.add_comm]
    _ =>> M (n + 3) 0 (n + 1) 0 := A'_to_M_
    _ =>> M (n + 2) 0 (n + 2) 1 := Ml_to_Ml_
    _ =   M (n + 2) 0 (2 * 0 + (n + 1) + 1) 1 := by simp
    _ =>> A (n + 3) := Ml_to_A_iter

theorem halted_to_halted (tm : TuringMachine transition) (k : Nat) (h : ¬(TuringMachine.is_not_halted tm)) : ¬(TuringMachine.is_not_halted (TuringMachine.advance^[k] tm)) :=
  match k with
  | 0 => h
  | k' + 1 => by
    simp [Function.iterate_add_apply]
    apply halted_to_halted (TuringMachine.advance tm) k'
    let (TuringMachine.mk tape state) := tm
    cases state
    . let tm' : TuringMachine transition := TuringMachine.advance { tape := tape, state := none }
      have : tm'.state = none := rfl
      let (TuringMachine.mk tape' state') := tm'
      cases state'
      . intro hnh
        exact (Bool.self_ne_not false) hnh  
      . contradiction
    . contradiction

theorem not_halted_if_next_not_halted (tm : TuringMachine transition) (h : (TuringMachine.advance tm).is_not_halted) : tm.is_not_halted := by
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

theorem not_halted_if_later_not_halted (tm : TuringMachine transition) (k : Nat) (h : TuringMachine.is_not_halted (TuringMachine.advance^[k] tm)) : TuringMachine.is_not_halted tm := by
  induction k with
  | zero => exact h
  | succ k' ih =>
    have := not_halted_if_next_not_halted (TuringMachine.advance^[k'] tm)
    conv at this => arg 1; arg 1; rw [←Function.iterate_one TuringMachine.advance]; arg 3; simp
    rw [←Function.iterate_add_apply] at this
    rw [Nat.add_comm] at this
    exact ih (this h)

theorem A_to_any_A_ (k : Nat) : ∃m : Nat, (TuringMachine.advance^[m] (A 2)) = A (k + 2) ∧ k <= m := by
  induction k with
  | zero => exists 0
  | succ k' ih =>
    let ⟨m', ⟨h1, h2⟩⟩ := ih
    let ⟨m'', hm⟩ : A (k' + 2) =>> A (k' + 3) := A_to_A_
    have t1 : 1 <= m'' := by
      have t2 : A (k' + 2) ≠ A (k' + 3) := by
        have t4 : (A (k' + 2)).tape.right_half (2 * (k' + 2)) = Symbol.SYM_0 := by
          unfold A; simp
          have t3 := append_get (2 * (k' + 2)) 0 [Symbol.SYM_1]
          simp at t3
          rw [t3]
          rfl
        have t5 : (A (k' + 3)).tape.right_half (2 * (k' + 2)) = Symbol.SYM_1 := by
          unfold A; simp
          have : 2 * (k' + 2) < 2 * (k' + 3) := by simp
          rw [append_get' (a := Symbol.SYM_1) this]
        intro h
        have := congr_arg (fun x => x.tape.right_half (1 * (2 * (k' + 2)))) h
        simp at this
        rw [t4, t5] at this
        have t7 : Symbol.SYM_0 ≠ Symbol.SYM_1 := by decide
        exact t7 this
      rw [Nat.one_le_iff_ne_zero]
      intro hm''z
      rw [hm''z] at hm
      exact t2 hm
    exists m'' + m'
    apply And.intro
    . rw [Function.iterate_add_apply, h1, hm]
    . rw [Nat.add_comm]
      exact Nat.add_le_add h2 t1 

theorem reaches_A2 : TuringMachine.advance^[23] starting_machine = A 2 := rfl

theorem any_to_A (n : Nat) : ∃ m k : Nat, TuringMachine.advance^[n + k] starting_machine = A (m + 2) :=
  Decidable.casesOn (Nat.decLe n 23)
    (fun t => by
      rw [Nat.not_le] at t
      have := Nat.succ_le_of_lt t 
      let ⟨n', hn'⟩ := Nat.exists_eq_add_of_le this
      rw [hn']
      exists (n' + 1)
      have ⟨m', ⟨hm', hm''⟩⟩ := A_to_any_A_ (n' + 1)
      rw [←reaches_A2] at hm'
      rw [←Function.iterate_add_apply] at hm'
      exists (m' - n' - 1)
      have : Nat.succ 23 + n' + (m' - n' - 1) = m' + 23 := by
        rw [←Nat.sub_add_eq, ←Nat.add_sub_assoc hm'']
        rw [Nat.sub_eq_of_eq_add]
        linarith
      rw [this]
      exact hm'
    )
    (fun t => by
      exists 0
      exists (23 - n)
      rw [Nat.add_sub_of_le t]
      exact reaches_A2
    )

theorem tm_not_halt : TuringMachine.does_not_halt starting_machine := by
  intro n
  have ⟨m,⟨k, h⟩⟩ := any_to_A n
  have t1 := not_halted_if_later_not_halted (TuringMachine.advance^[n] starting_machine) k
  rw [←Function.iterate_add_apply, Nat.add_comm, h] at t1
  have t2 : (A (n + 2)).is_not_halted := rfl
  exact t1 t2

end proof
