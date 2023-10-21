import TuringMachine.Defs
import TuringMachine.Lemmas
import Mathlib.Tactic.Linarith.Frontend

def transition : State5 -> Symbol2 -> Option State5 × Symbol2 × Direction
  | State5.A, Symbol2.V0 => (some State5.B, Symbol2.V1, Direction.right)
  | State5.A, Symbol2.V1 => (some State5.E, Symbol2.V1, Direction.right)
  | State5.B, Symbol2.V0 => (some State5.C, Symbol2.V1, Direction.left )
  | State5.B, Symbol2.V1 => (some State5.B, Symbol2.V1, Direction.right)
  | State5.C, Symbol2.V0 => (some State5.A, Symbol2.V0, Direction.right)
  | State5.C, Symbol2.V1 => (some State5.D, Symbol2.V0, Direction.left )
  | State5.D, Symbol2.V0 => (some State5.B, Symbol2.V1, Direction.left )
  | State5.D, Symbol2.V1 => (some State5.D, Symbol2.V1, Direction.left )
  | State5.E, Symbol2.V0 => (none,          Symbol2.V1, Direction.left )
  | State5.E, Symbol2.V1 => (some State5.A, Symbol2.V0, Direction.right)

abbrev TM_10756090 := TuringMachine transition

-- In state A and tape filled with zeroes 
def starting_machine : TM_10756090 := 
  TuringMachine.mk (Tape.blank Symbol2.V0) (State5.A)

namespace proof

-- state: C
-- tape: C0 + n * [11] + [0] + n * [1]
def A (n : Nat) : TuringMachine transition :=
  let right_tape : Stream' Symbol2 := 
    append_to_repeated (2*n) [Symbol2.V1] $
    Stream'.cons Symbol2.V0 $
    append_to_repeated n [Symbol2.V1] $
    Stream'.const Symbol2.V0
  let tape : Tape Symbol2 := Tape.mk (Stream'.const Symbol2.V0) Symbol2.V0 right_tape
  TuringMachine.mk tape State5.C

-- state: E
-- tape: nl * [01] + E1 + nr * [11] + (nr + nl) * [1]
def A' (nl : Nat) (nr : Nat) : TM_10756090 :=
  let left_tape : Stream' Symbol2 := 
    append_to_repeated nl [Symbol2.V1, Symbol2.V0] $
    Stream'.const Symbol2.V0
  let right_tape : Stream' Symbol2 := 
    append_to_repeated (2*nr) [Symbol2.V1] $
    Stream'.cons Symbol2.V0 $
    append_to_repeated (nr + nl) [Symbol2.V1] $
    Stream'.const Symbol2.V0
  TuringMachine.mk (Tape.mk left_tape Symbol2.V1 right_tape) State5.E

-- state: B
-- tape: nl * [01] + nlm * [1] + D1 + nrm * [1] + [0] + nr * [1]
def M (nl nlm nrm nr : Nat) : TM_10756090 :=
  let left_tape : Stream' Symbol2 := 
    append_to_repeated nlm [Symbol2.V1] $
    append_to_repeated nl [Symbol2.V1, Symbol2.V0] $
    Stream'.const Symbol2.V0
  let right_tape : Stream' Symbol2 := 
    append_to_repeated nrm [Symbol2.V1] $
    Stream'.cons Symbol2.V0 $
    append_to_repeated nr [Symbol2.V1] $
    Stream'.const Symbol2.V0
  TuringMachine.mk (Tape.mk left_tape Symbol2.V1 right_tape) State5.B

-- state: D
-- tape: nl * [01] + nlm * [1] + D1 + nrm * [1] + [0] + nr * [1]
def M' (nl nlm nrm nr : Nat) : TM_10756090 :=
  let left_tape : Stream' Symbol2 := 
    append_to_repeated nlm [Symbol2.V1] $
    append_to_repeated nl [Symbol2.V1, Symbol2.V0] $
    Stream'.const Symbol2.V0
  let right_tape : Stream' Symbol2 := 
    append_to_repeated nrm [Symbol2.V1] $
    Stream'.cons Symbol2.V0 $
    append_to_repeated nr [Symbol2.V1] $
    Stream'.const Symbol2.V0
  TuringMachine.mk (Tape.mk left_tape Symbol2.V1 right_tape) State5.D

lemma A'_to_M : A' (n + 1) 0 =>> M (n + 2) 0 n 0 := by
  unfold tm_succeeds
  exists 2
  ext : 1
  . ext : 1
    repeat rfl
    . have t1 : (TuringMachine.advance^[2] (A' (n + 1) 0)).tape.right_half = 
        (append_to_repeated n [Symbol2.V1] $ Stream'.const Symbol2.V0) := by
          conv => arg 2; rw [←Nat.zero_add n]
      unfold M; conv => rhs; simp
      rw [append_repeated_zero, t1]
      simp
      rw [cons_to_const]
  . rfl

lemma M_to_M_iter : M nl nlm nrm nr =>> M nl (nlm + nrm) 0 nr := by
  cases nrm
  . exists 0
  case succ nrm' =>
    calc M nl nlm (nrm' + 1) nr
      _ =>> M nl (nlm + 1) nrm' nr       := by exists 1
      _ =>> M nl (nlm + 1 + nrm') 0 nr   := M_to_M_iter
      _ =   M nl (nlm + (nrm' + 1)) 0 nr := by rw [Nat.add_assoc]; conv => lhs; arg 2; arg 2; rw [Nat.add_comm]

lemma M'_to_M'_iter : M' nl nlm nrm nr =>> M' nl 0 (nrm + nlm) nr := by
  cases nlm
  . exists 0
  case succ nlm' =>
    calc M' nl (nlm' + 1) nrm nr
      _ =>> M' nl nlm' (nrm + 1) nr       := by exists 1
      _ =>> M' nl 0 (nrm + 1 + nlm') nr   := M'_to_M'_iter
      _ =   M' nl 0 (nrm + (nlm' + 1)) nr := by
        rw [Nat.add_assoc]
        conv => lhs; arg 3; arg 2; rw [Nat.add_comm]

lemma Ml_to_M' : M nl 0 (nm + 1) nr =>> M' nl 0 nm (nr + 1) := by
  calc M nl 0 (nm + 1) nr
    _ =>> M nl (0 + (nm + 1)) 0 nr  := M_to_M_iter
    _ =   M nl (nm + 1) 0 nr        := by simp
    _ =>> M' nl nm 0 (nr + 1)       := by exists 3
    _ =>> M' nl 0 (0 + nm) (nr + 1) := M'_to_M'_iter
    _ =   M' nl 0 nm (nr + 1)       := by rw [Nat.zero_add]

lemma Ml_to_Ml : M (nl + 2) 0 (nm + 1) nr =>> M (nl + 1) 0 (nm + 2) (nr + 1) := by
  calc M (nl + 2) 0 (nm + 1) nr
    _ =>> M' (nl + 2) 0 nm (nr + 1)      := Ml_to_M'
    _ =>> M (nl + 1) 0 (nm + 2) (nr + 1) := by exists 4

lemma Ml_to_A_iter : M (nl + 1) 0 (2 * nr + nl + 1) (nr + 1) =>> A (nl + nr + 2) := by
  cases nl
  . simp
    calc M 1 0 (2 * nr + 1) (nr + 1)
      _ =>> M' 1 0 (2 * nr) (nr + 2) := Ml_to_M'
      _ =>> A (nr + 2)               := by exists 4
  case succ nl' =>
    have t1 : 2 * nr + (nl' + 1) + 1 = 2 * nr + 1 + nl' + 1 := by linarith
    have t2 : 2 * (nr + 1) + nl' + 1 = (2*nr + 1 + nl') + 2 := by linarith
    have t3 : (nl' + 1) + nr + 2 = nl' + (nr + 1) + 2       := by linarith
    calc M (nl' + 2) 0 (2 * nr + (nl' + 1) + 1) (nr + 1)
      _ =   M (nl' + 2) 0 ((2*nr + 1 + nl') + 1) (nr + 1)   := by rw [t1]
      _ =>> M (nl' + 1) 0 ((2*nr + 1 + nl') + 2) (nr + 2)   := Ml_to_Ml
      _ =   M (nl' + 1) 0 (2 * (nr + 1) + nl' + 1) (nr + 2) := by rw [t2]
      _ =>> A (nl' + (nr + 1) + 2) := Ml_to_A_iter
      _ =   A ((nl' + 1) + nr + 2) := by rw [t3]

lemma A'_to_A' : A' nl (nr + 1) =>> A' (nl + 1) nr := by
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

lemma A'_to_A'_iter : A' nl nr =>> A' (nl + nr) 0 := by
  cases nr
  . exists 0
  case succ nr' =>
    have t1 : nl + 1 + nr' = nl + (nr' + 1) := by linarith
    calc A' nl (nr' + 1)
      _ =>> A' (nl + 1) nr'       := A'_to_A'
      _ =>> A' (nl + 1 + nr') 0   := A'_to_A'_iter
      _ =   A' (nl + (nr' + 1)) 0 := by rw [t1]

theorem A_to_A : A (n + 2) =>> A (n + 3) := by
  calc A (n + 2)
    _ =>> A' 1 (n + 1)          := by exists 2
    _ =>> A' (1 + (n + 1)) 0    := A'_to_A'_iter
    _ =   A' (n + 2) 0          := by rw [Nat.add_comm]
    _ =>> M (n + 3) 0 (n + 1) 0 := A'_to_M
    _ =>> M (n + 2) 0 (n + 2) 1 := Ml_to_Ml
    _ =   M (n + 2) 0 (2 * 0 + (n + 1) + 1) 1 := by simp
    _ =>> A (n + 3) := Ml_to_A_iter

lemma A_to_any_A (k : Nat) : ∃m : Nat, (TuringMachine.advance^[m] (A 2)) = A (k + 2) ∧ k <= m := by
  induction k with
  | zero => exists 0
  | succ k' ih =>
    let ⟨m', ⟨h1, h2⟩⟩ := ih
    let ⟨m'', hm⟩ : A (k' + 2) =>> A (k' + 3) := A_to_A
    have t1 : 1 <= m'' := by
      have t2 : A (k' + 2) ≠ A (k' + 3) := by
        have t4 : (A (k' + 2)).tape.right_half (2 * (k' + 2)) = Symbol2.V0 := by
          unfold A; simp
          have t3 := append_get (2 * (k' + 2)) 0 [Symbol2.V1]
          simp at t3
          rw [t3]
          rfl
        have t5 : (A (k' + 3)).tape.right_half (2 * (k' + 2)) = Symbol2.V1 := by
          unfold A; simp
          have : 2 * (k' + 2) < 2 * (k' + 3) := by simp
          rw [append_get' (a := Symbol2.V1) this]
        intro h
        have := congr_arg (fun x => x.tape.right_half (1 * (2 * (k' + 2)))) h
        simp at this
        rw [t4, t5] at this
        have t7 : Symbol2.V0 ≠ Symbol2.V1 := by decide
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

lemma reaches_A2 : TuringMachine.advance^[23] starting_machine = A 2 := rfl

lemma any_to_A (n : Nat) : ∃ m k : Nat, TuringMachine.advance^[n + k] starting_machine = A (m + 2) :=
  Decidable.casesOn (Nat.decLe n 23)
    (fun t => by
      rw [Nat.not_le] at t
      have := Nat.succ_le_of_lt t 
      let ⟨n', hn'⟩ := Nat.exists_eq_add_of_le this
      rw [hn']
      exists (n' + 1)
      have ⟨m', ⟨hm', hm''⟩⟩ := A_to_any_A (n' + 1)
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
