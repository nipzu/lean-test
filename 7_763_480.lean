import TuringMachine.Defs
import TuringMachine.Lemmas
import Mathlib.Tactic.Linarith.Frontend

def transition : State5 -> Symbol2 -> Option State5 × Symbol2 × Direction
  | State5.A, Symbol2.V0 => (some State5.B, Symbol2.V1, Direction.right)
  | State5.A, Symbol2.V1 => (some State5.E, Symbol2.V0, Direction.left )
  | State5.B, Symbol2.V0 => (some State5.C, Symbol2.V1, Direction.right)
  | State5.B, Symbol2.V1 => (some State5.B, Symbol2.V1, Direction.right)
  | State5.C, Symbol2.V0 => (some State5.D, Symbol2.V1, Direction.right)
  | State5.C, Symbol2.V1 => (some State5.C, Symbol2.V1, Direction.left )
  | State5.D, Symbol2.V0 => (some State5.E, Symbol2.V0, Direction.left )
  | State5.D, Symbol2.V1 => (some State5.B, Symbol2.V0, Direction.right)
  | State5.E, Symbol2.V0 => (none         , Symbol2.V1, Direction.right)
  | State5.E, Symbol2.V1 => (some State5.A, Symbol2.V1, Direction.left )

abbrev TM_7763480 := TuringMachine transition

-- In state A and tape filled with zeroes
def starting_machine : TM_7763480 :=
  TuringMachine.mk (Tape.blank Symbol2.V0) (State5.A)

namespace proof

-- state: D
-- tape: n*[1] + [0] + (2n+3)*[1] + D0
def D (n : Nat) : TM_7763480 :=
  let left_tape : Stream' Symbol2 :=
    (2*n+3) ** [Symbol2.V1] ++
                Symbol2.V0  ::
       n    ** [Symbol2.V1] ++ₛ
    Stream'.const Symbol2.V0
  let tape : Tape Symbol2 := Tape.mk left_tape Symbol2.V0 (Stream'.const Symbol2.V0)
  TuringMachine.mk tape State5.D

-- state: E
-- tape: (nm+nr) * [1] + [0] + nm * [11] + E1 + (nr+1)*[01]
def D' (nm nr : Nat) : TM_7763480 :=
  let left_tape : Stream' Symbol2 :=
    (2*nm) ** [Symbol2.V1] ++
    Symbol2.V0 ::
    (nm + nr) ** [Symbol2.V1] ++ₛ
    Stream'.const Symbol2.V0
  let right_tape : Stream' Symbol2 :=
    (nr + 1) ** [Symbol2.V0, Symbol2.V1] ++ₛ
    Stream'.const Symbol2.V0
  TuringMachine.mk (Tape.mk left_tape Symbol2.V1 right_tape) State5.E

-- state: C
-- tape: nl * [1] + [0] + nml * [1] + C1 + nmr * [1] + nr*[01]
def C (nl nml nmr nr : Nat) : TM_7763480 :=
  let left_tape : Stream' Symbol2 :=
    nml ** [Symbol2.V1] ++
    Symbol2.V0 ::
    nl ** [Symbol2.V1] ++ₛ
    Stream'.const Symbol2.V0
  let right_tape : Stream' Symbol2 :=
    nmr ** [Symbol2.V1] ++
    nr ** [Symbol2.V0, Symbol2.V1] ++ₛ
    Stream'.const Symbol2.V0
  TuringMachine.mk (Tape.mk left_tape Symbol2.V1 right_tape) State5.E

-- state: B
-- tape: nl * [1] + [0] + nml * [1] + C1 + nmr * [1] + nr*[01]
def C' (nl nml nmr nr : Nat) : TM_7763480 :=
  let left_tape : Stream' Symbol2 :=
    nml ** [Symbol2.V1] ++
    Symbol2.V0 ::
    nl ** [Symbol2.V1] ++ₛ
    Stream'.const Symbol2.V0
  let right_tape : Stream' Symbol2 :=
    nmr ** [Symbol2.V1] ++
    nr ** [Symbol2.V0, Symbol2.V1] ++ₛ
    Stream'.const Symbol2.V0
  TuringMachine.mk (Tape.mk left_tape Symbol2.V1 right_tape) State5.B

lemma reaches_D0 : starting_machine =>> D 0 := by
  exists 3
  unfold D
  simp [append_assoc, cons_to_const]
  rfl

lemma D_to_D' : D (nm + nr) =>> D' nm nr := by
  cases nr with
  | zero =>
    exists 3
    ext : 1
    . ext : 1
      repeat rfl
      . have t1 : (TuringMachine.advance^[3] (D nm)).tape.right_half
          = [Symbol2.V0, Symbol2.V1] ++ [Symbol2.V0] ++ₛ Stream'.const Symbol2.V0 := rfl
        rw [Nat.add_zero, t1, append_assoc, cons_to_const]
        rfl
    . rfl
  | succ nr' =>
    have t1 : nm + (nr' + 1) = (nm + 1) + nr' := by linarith
    calc D (nm + (nr' + 1))
      _ =   D ((nm + 1) + nr') := by rw [t1]
      _ =>> D' (nm + 1) nr' := D_to_D'
      _ =>> D' nm (nr' + 1) := by
        exists 2
        ext : 1
        . ext : 1
          . unfold D'
            rw [t1]
            rfl
          repeat rfl
        . rfl

lemma D'_to_C : D' 0 (nr + 1) =>> C 0 (nr + 3) 0 nr := by
  admit

theorem tm_not_halt : starting_machine.does_not_halt :=
  sorry

end proof
