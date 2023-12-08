import TuringMachine.Defs
import TuringMachine.Lemmas
import Mathlib.Tactic.Linarith.Frontend

def transition : State5 -> Symbol2 -> Option State5 × Symbol2 × Direction
  | State5.A, Symbol2.V0 => (some State5.B, Symbol2.V1, Direction.right)
  | State5.A, Symbol2.V1 => (some State5.A, Symbol2.V1, Direction.right)
  | State5.B, Symbol2.V0 => (some State5.C, Symbol2.V1, Direction.right)
  | State5.B, Symbol2.V1 => (some State5.B, Symbol2.V1, Direction.left )
  | State5.C, Symbol2.V0 => (some State5.D, Symbol2.V0, Direction.left )
  | State5.C, Symbol2.V1 => (some State5.A, Symbol2.V0, Direction.right)
  | State5.D, Symbol2.V0 => (some State5.A, Symbol2.V1, Direction.right)
  | State5.D, Symbol2.V1 => (some State5.E, Symbol2.V1, Direction.left )
  | State5.E, Symbol2.V0 => (none         , Symbol2.V1, Direction.right)
  | State5.E, Symbol2.V1 => (some State5.D, Symbol2.V0, Direction.left)

abbrev TM_8120967 := TuringMachine transition

-- In state A and tape filled with zeroes
def starting_machine : TM_8120967 :=
  TuringMachine.mk (Tape.blank Symbol2.V0) (State5.A)

namespace proof

-- state: C
-- tape: n*[1] + [0] + (2n+2)*[1] + B0
def C (n : Nat) : TM_8120967 :=
  let left_tape : Stream' Symbol2 :=
    (2*n+2) ** [Symbol2.V1] ++
                Symbol2.V0  ::
       n    ** [Symbol2.V1] ++ₛ
    Stream'.const Symbol2.V0
  let tape : Tape Symbol2 := Tape.mk left_tape Symbol2.V0 (Stream'.const Symbol2.V0)
  TuringMachine.mk tape State5.C

-- state: E
-- tape: (nm+nr) * [1] + [0] + nm * [11] + E1 + (nr+1)*[10]
def C' (nm nr : Nat) : TM_8120967 :=
  let left_tape : Stream' Symbol2 :=
    (2*nm) ** [Symbol2.V1] ++
    Symbol2.V0 ::
    (nm + nr) ** [Symbol2.V1] ++ₛ
    Stream'.const Symbol2.V0
  let right_tape : Stream' Symbol2 :=
    (nr + 1) ** [Symbol2.V1, Symbol2.V0] ++ₛ
    Stream'.const Symbol2.V0
  TuringMachine.mk (Tape.mk left_tape Symbol2.V1 right_tape) State5.E

-- state: B
-- tape: nl * [1] + [0] + nml * [1] + B1 + nmr * [1] + [0] + nr*[10]
def B (nl nml nmr nr : Nat) : TM_8120967 :=
  let left_tape : Stream' Symbol2 :=
    nml ** [Symbol2.V1] ++
    Symbol2.V0 ::
    nl ** [Symbol2.V1] ++ₛ
    Stream'.const Symbol2.V0
  let right_tape : Stream' Symbol2 :=
    nmr ** [Symbol2.V1] ++
    Symbol2.V0 ::
    nr ** [Symbol2.V1, Symbol2.V0] ++ₛ
    Stream'.const Symbol2.V0
  TuringMachine.mk (Tape.mk left_tape Symbol2.V1 right_tape) State5.B

-- state: A
-- tape: nl * [1] + [0] + nml * [1] + B1 + nmr * [1] + [0] + nr*[10]
def B' (nl nml nmr nr : Nat) : TM_8120967 :=
  let left_tape : Stream' Symbol2 :=
    nml ** [Symbol2.V1] ++
    Symbol2.V0 ::
    nl ** [Symbol2.V1] ++ₛ
    Stream'.const Symbol2.V0
  let right_tape : Stream' Symbol2 :=
    nmr ** [Symbol2.V1] ++
    Symbol2.V0 ::
    nr ** [Symbol2.V1, Symbol2.V0] ++ₛ
    Stream'.const Symbol2.V0
  TuringMachine.mk (Tape.mk left_tape Symbol2.V1 right_tape) State5.A

lemma reaches_C0 : starting_machine =>> C 0 := by
  exists 2
  unfold C
  simp
  rw [append_assoc, cons_to_const]
  rfl

lemma C_to_C' : C (nm + nr) =>> C' nm nr := by
  cases nr with
  | zero => exists 2
  | succ nr' =>
    have t1 : nm + (nr' + 1) = (nm + 1) + nr' := by linarith
    calc C (nm + (nr' + 1))
      _ =   C ((nm + 1) + nr') := by rw [t1]
      _ =>> C' (nm + 1) nr' := C_to_C'
      _ =>> C' nm (nr' + 1) := by
        exists 2; unfold C'; rw [t1]; rfl

lemma C'_to_B : C' 0 (nml + nmr) =>> B 0 nml (nmr + 2) (nml + nmr) := by
  cases nmr with
  | zero =>
    simp
    exists 5
    ext : 1
    . ext : 1
      . have t1 : (TuringMachine.advance^[5] (C' 0 nml)).tape.left_half
          = ((0 + nml) ** [Symbol2.V1] ++ₛ Stream'.const Symbol2.V0) := rfl
        rw [t1]
        unfold B
        rw [append_assoc]
        simp
        rw [cons_to_const]
      repeat rfl
    . rfl
  | succ nmr' =>
    have t1 : nml + (nmr' + 1) = (nml + 1) + nmr' := by linarith
    calc C' 0 (nml + (nmr' + 1))
      _ = C' 0 ((nml + 1) + nmr') := by rw [t1]
      _ =>> B 0 (nml + 1) (nmr' + 2) ((nml + 1) + nmr') := C'_to_B
      _ =>> B 0 nml (nmr' + 3) ((nml + 1) + nmr') := by exists 1
      _ =   B 0 nml (nmr' + 3) (nml + (nmr' + 1)) := by rw [←t1]

lemma B_to_B' : B nl 0 (nml + nmr + 1) nr =>> B' (nl + 1) nml nmr nr := by
  cases nml with
  | zero => exists 3; simp; rfl
  | succ nml' =>
    have t1 : (nml' + 1) + nmr = nml' + (nmr + 1) := by linarith
    calc B nl 0 ((nml' + 1) + nmr + 1) nr
      _ =   B nl 0 (nml' + (nmr + 1) + 1) nr := by rw [t1]
      _ =>> B' (nl + 1) nml' (nmr + 1) nr := B_to_B'
      _ =>> B' (nl + 1) (nml' + 1) nmr nr := by exists 1

lemma B'_to_B : B' nl (nml + nmr) 0 (nr + 1) =>> B nl nml (nmr + 2) nr := by
  cases nmr with
  | zero => exists 4
  | succ nmr' =>
    have t1 : nml + (nmr' + 1) = (nml + 1) + nmr' := by linarith
    calc B' nl (nml + (nmr' + 1)) 0 (nr + 1)
      _ =   B' nl ((nml + 1) + nmr') 0 (nr + 1) := by rw [t1]
      _ =>> B nl (nml + 1) (nmr' + 2) nr := B'_to_B
      _ =>> B nl nml (nmr' + 3) nr := by exists 1

lemma C_to_B' : C (nl + nr) =>> B' (nl + 1) (2*nl + nr + 1) 0 nr := by
  cases nl with
  | zero =>
    conv => rhs; simp
    calc C (0 + nr)
      _ =>> C' 0 nr := C_to_C'
      _ =   C' 0 (0 + nr) := by simp
      _ =>> B 0 0 (nr + 2) (0 + nr) := C'_to_B
      _ =>> B' 1 (nr + 1) 0 (0 + nr) := B_to_B' (nmr := 0)
      _ = B' 1 (nr + 1) 0 nr := by simp
  | succ nl' =>
    have t1 : (nl' + 1) + nr = nl' + (nr + 1) := by linarith
    have t2 : 2*nl' + (nr + 1) + 1 = (2*(nl' + 1)) + nr := by linarith
    calc C ((nl' + 1) + nr)
      _ =   C (nl' + (nr + 1)) := by rw [t1]
      _ =>> B' (nl' + 1) (2*nl' + (nr + 1) + 1) 0 (nr + 1) := C_to_B'
      _ =   B' (nl' + 1) (0 + (2*nl' + (nr + 1) + 1)) 0 (nr + 1) := by simp
      _ =>> B (nl' + 1) 0 (2*nl' + (nr + 1) + 1 + 2) nr := B'_to_B
      _ =>> B' (nl' + 2) (2*nl' + (nr + 1) + 1 + 1) 0 nr := B_to_B' (nr := nr) (nl := nl' + 1) (nmr := 0) (nml := (2*nl' + (nr + 1) + 1 + 1))
      _ =   B' (nl' + 2) ((2*(nl' + 1)) + nr + 1) 0 nr := by rw [t2]

theorem C_to_C : C n =>> C (n + 1) := by
  calc C n
    _ =>> B' (n + 1) (2*n + 0 + 1) 0 0 := C_to_B' (nr := 0)
    _ =>> C (n + 1) := by exists 3

theorem C_ne_C : C n ≠ C (n + 1) := by
  intro h
  have t1 := congr_arg (fun tm => tm.tape.left_half (2 * n + 2)) h
  unfold C at t1
  simp at t1
  have t3 := append_get (2 * n + 2) 0 [Symbol2.V1]
  simp at t3
  rw [append_assoc, t3] at t1
  have t2 : 2 * n + 2 < 2 * (n + 1) + 2 := by simp
  rw [append_assoc, append_get' t2] at t1
  have t7 : Symbol2.V0 ≠ Symbol2.V1 := by decide
  exact t7 t1

theorem tm_not_halt : TuringMachine.does_not_halt starting_machine :=
    tm_not_halt'
      C
      starting_machine
      @C_to_C
      @C_ne_C
      reaches_C0

end proof
