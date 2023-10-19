import Mathlib.Data.Stream.Defs
import Mathlib.Init.Data.Nat.Lemmas

inductive Direction where
  | left : Direction
  | right : Direction



structure Tape (m : Nat) where
  left_half : Stream' (Fin m)
  cur_symbol : Fin m
  right_half : Stream' (Fin m)

namespace Tape

variable {m : Nat}

def write (new_symbol : Fin m) (tape : Tape m) : Tape m := 
  Tape.mk tape.left_half new_symbol tape.right_half

def move : Direction → Tape m → Tape m
  | Direction.left, (Tape.mk left_half cur_symbol right_half) 
    => Tape.mk (left_half.tail) (left_half.head) (right_half.cons cur_symbol)
  | Direction.right, (Tape.mk left_half cur_symbol right_half)
    => Tape.mk (left_half.cons cur_symbol) (right_half.head) (right_half.tail)

def blank (nzm : 0 < m) : Tape m :=
  let zero := ⟨0, nzm⟩;
  Tape.mk (Stream'.const zero) zero (Stream'.const zero)

end Tape


structure TuringMachine (n m : Nat) (δ : Fin n → Fin m → Option (Fin n) × Fin m × Direction) where
  tape : Tape m
  state : Option (Fin n)

namespace TuringMachine

variable {n m : Nat} {δ : Fin n → Fin m → Option (Fin n) × Fin m × Direction} 

def advance (tm : TuringMachine n m δ) : (TuringMachine n m δ) :=
  let cur_tape   := tm.tape;
  let cur_symbol := cur_tape.cur_symbol;
  match tm.state with
  | some cur_state => 
    let (new_state, new_symbol, direction) := δ cur_state cur_symbol
    let new_tape := Tape.move direction $ Tape.write new_symbol cur_tape;
    TuringMachine.mk new_tape new_state
  | none => tm

def is_not_halted (tm : TuringMachine n m δ) : Prop :=
  Option.isSome tm.state

def does_not_halt (tm : TuringMachine n m δ) : Prop :=
  ∀k : Nat, (is_not_halted (advance^[k] tm))
  
end TuringMachine
