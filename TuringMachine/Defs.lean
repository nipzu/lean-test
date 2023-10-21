import Mathlib.Data.Stream.Defs
import Mathlib.Logic.Function.Iterate

-- A simple enum used for Turing machine transitions
inductive Direction where
  | left : Direction
  | right : Direction

-- Define:
-- ∘ Q, the type of states
-- ∘ Γ, the type of symbols
-- In contrast to the usual definiton, these
-- are neither required to be finite nor sets.
variable {Q Γ : Type _}

-- A tape of cells of Γ,
-- extending infinitely to the left and right
-- A `Tape` is explicitly divided into two halves
-- to faciliate (NORMALIZATION OF THEOREMS???).
-- A tape could also be defined as a function
-- ℤ → Γ which would have been(?) more cumbersome to work with. 
--
-- In contrast to usual tapes of Turing machines,
-- this definiton technically allows an infite number
-- of non-blank symbols to exist on the tape.
@[ext] -- automatically generate extensionability theorems
structure Tape (Γ : Type _) where
  left_half : Stream' Γ
  cur_symbol : Γ
  right_half : Stream' Γ

namespace Tape
  -- Replace the symbol under the head with the new one
  def write (new_symbol : Γ) (tape : Tape Γ) : Tape Γ :=
    Tape.mk tape.left_half new_symbol tape.right_half

  -- Move the head left or right by one 
  def move : Direction -> Tape Γ -> Tape Γ
    | Direction.left,  (Tape.mk L H R)
      => Tape.mk (L.tail  ) (L.head) (R.cons H)
    | Direction.right, (Tape.mk L H R)
      => Tape.mk (L.cons H) (R.head) (R.tail  )

  -- A tape with all cells filled with b
  def blank (b : Γ) : Tape Γ :=
    Tape.mk (Stream'.const b) b (Stream'.const b)
end Tape

-- The structure `TuringMachine` represents the running state
-- of a Turing machine with states Q, symbols Γ and transition
-- function δ : Q × Γ -> (Q ⊕ HALT) × Γ × Direction. The halting
-- state is represented by the `none` variant of the `Option Q` type.
@[ext] -- automatically generate extensionability theorems
structure TuringMachine (δ : Q -> Γ -> Option Q × Γ × Direction) where
  tape : Tape Γ
  state : Option Q

namespace TuringMachine
  variable {δ : Q -> Γ -> Option Q × Γ × Direction}

  -- Evaluate the transition function once and change
  -- state and tape accordingly. If the machine was
  -- already halted, do nothing to it.
  def advance (tm : TuringMachine δ) : TuringMachine δ :=
    match tm.state with
    | none => tm
    | some cur_state =>
      let cur_tape   := tm.tape
      let cur_symbol := cur_tape.cur_symbol
      let (new_state, new_symbol, direction) := δ cur_state cur_symbol
      let new_tape := Tape.move direction $ Tape.write new_symbol cur_tape
      TuringMachine.mk new_tape new_state

  -- Is the machine not in the halting state?
  def is_not_halted (tm : TuringMachine δ) : Prop :=
    Option.isSome tm.state

  -- Will the machine not enter the halting state in the future?
  def does_not_halt (tm : TuringMachine δ) : Prop :=
    ∀n : Nat, (is_not_halted (advance^[n] tm))
end TuringMachine
