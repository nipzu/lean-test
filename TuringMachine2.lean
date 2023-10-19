import Mathlib.Data.Stream.Defs
import Mathlib.Init.Data.Nat.Lemmas

inductive Direction where
  | left : Direction
  | right : Direction




@[ext]
structure Tape (Γ : Type _) where
  left_half : Stream' Γ
  cur_symbol : Γ
  right_half : Stream' Γ

namespace Tape

variable {Γ : Type _}

def write (new_symbol : Γ) (tape : Tape Γ) : Tape Γ :=
  Tape.mk tape.left_half new_symbol tape.right_half

def move : Direction → Tape Γ → Tape Γ
  | Direction.left, (Tape.mk left_half cur_symbol right_half)
    => Tape.mk (left_half.tail) (left_half.head) (right_half.cons cur_symbol)
  | Direction.right, (Tape.mk left_half cur_symbol right_half)
    => Tape.mk (left_half.cons cur_symbol) (right_half.head) (right_half.tail)

def blank (b : Γ) : Tape Γ :=
  Tape.mk (Stream'.const b) b (Stream'.const b)

end Tape




@[ext]
structure TuringMachine (Q Γ : Type _) (δ : Q → Γ → Option Q × Γ × Direction) where
  tape : Tape Γ
  state : Option Q

namespace TuringMachine

variable {Q Γ : Type _} {δ : Q → Γ → Option Q × Γ × Direction}

def advance (tm : TuringMachine Q Γ δ) : TuringMachine Q Γ δ :=
  let cur_tape   := tm.tape;
  let cur_symbol := cur_tape.cur_symbol;
  match tm.state with
  | some cur_state =>
    let (new_state, new_symbol, direction) := δ cur_state cur_symbol
    let new_tape := Tape.move direction $ Tape.write new_symbol cur_tape;
    TuringMachine.mk new_tape new_state
  | none => tm

def is_not_halted (tm : TuringMachine Q Γ δ) : Prop :=
  Option.isSome tm.state

def does_not_halt (tm : TuringMachine Q Γ δ) : Prop :=
  ∀k : Nat, (is_not_halted (advance^[k] tm))

end TuringMachine
