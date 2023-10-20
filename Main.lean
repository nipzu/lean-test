import Mathlib.Data.Vector
import Mathlib.Data.Nat.Order.Basic

-- import TuringMachine
import TuringMachine2
-- import 10_756_090

def main (args : List String) : IO Unit := IO.println args.head!

lemma vec_mul_take {α : Type _} (x : Nat) (y : Nat) : Vector α (min x (x * (y + 1))) = Vector α x := by
  rw [Nat.min_eq_left $ Nat.le_mul_of_pos_right $ Nat.succ_pos y]

lemma vec_mul_drop {α : Type _} (x : Nat) (y : Nat) : Vector α (x * (y + 1) - x) = Vector α (x * y) := by
  have t1 : x * (y + 1) = x * y + x := rfl;
  simp [t1]

lemma vec_tail_len {α : Type _} {n : Nat} {a : α} {as : List α} (h : List.length (a :: as) = n+1) : List.length as = n := by
  have tc : List.tail (a :: as) = as := List.tail_cons;
  rw [←tc, List.length_tail]
  exact congr_arg Nat.pred h

def vec_chunks {α : Type _} : (x : Nat) → (y : Nat) → (v : Vector α (x * y)) → Vector (Vector α x) y
  | _, 0, _ => Vector.nil
  | x, y'+1, v =>
    let v'   : Vector α (x * y') := cast (vec_mul_drop x y') (v.drop x);
    let head : Vector α x        := cast (vec_mul_take x y') (v.take x);
    Vector.cons head $ vec_chunks x y' v'

def vec_mapM {α : Type _} {β : Type _} {n : Nat} (f : α → Option β) (as : Vector α n) : Option (Vector β n) :=
  match n with
  | 0 => some Vector.nil
  | n'+1 =>
    let ⟨a' :: as', h⟩ := as;
    let b : Option β := f a';
    let bs : Option (Vector β n') := vec_mapM f ⟨as', vec_tail_len h⟩;
    match b, bs with
    | some b', some bs' => some (Vector.cons b' bs')
    | _, _ => none

def nat_to_fin {m : Nat} (n : Nat) : Option (Fin m) :=
  (Nat.decLt n m).casesOn (fun _ => none) (fun h => some ⟨n, h⟩)

def parse_symbol (m : Nat) (c : Char) : Option (Fin m) :=
  if '0' <= c ∧ c <= '9' then
    nat_to_fin (c.val - '0'.val).toNat
  else
    none

def parse_state (n : Nat) (c : Char) : Option $ Option (Fin n) :=
  if 'A' <= c ∧ c < 'Z' then
    Option.map some $ nat_to_fin (c.val - 'A'.val).toNat
  else if c = 'Z' then
    some none
  else
    none

def parse_direction : (c : Char) → Option Direction
  | 'L' => some Direction.left
  | 'R' => some Direction.right
  | _ => none

def parse_transition (n : Nat) (m : Nat) (chars : Vector Char 3) : Option $ Option (Fin n × Fin m × Direction) :=
  let ⟨sym :: dir :: state :: [], _⟩ := chars;
  if let ('-', '-', '-') := (sym, dir, state) then
    some none
  else if let (some sym', some state', some dir') := (parse_symbol n sym, parse_state m sym, parse_direction dir) then
    some $ 
      if let some state'' := state' then 
        some (sym', state'', dir') 
      else
        none
  else
    none

def parse_state_transitions (n : Nat) (m : Nat) (chars : Vector Char (3 * m + 1)) : Option (Vector (Option (Fin n × Fin m × Direction)) m) :=
  let ⟨_ :: cs, h⟩ := chars;
  let transitions := vec_chunks 3 m ⟨cs, vec_tail_len h⟩;
  vec_mapM (parse_transition n m) transitions

-- Fails if n or m is too large
def parse_transition_table : (n : Nat) → (m : Nat) → String → Option (Vector (Vector (Option (Fin n × Fin m × Direction)) m) n)
  | n, m, s =>
    let input : List Char := '_' :: s.data;
    Decidable.casesOn (decEq input.length ((3 * m + 1) * n))
      (fun _ => none)
      (
        fun h =>
          let states := vec_chunks (3 * m + 1) n ⟨input, h⟩;
          vec_mapM (parse_state_transitions n m) states
      )




variable {n m : Nat} {δ : Fin n → Fin m → Option (Fin n) × Fin m × Direction}
  {P : TuringMachine δ → Prop}
  {ind_step : ∀ tm : TuringMachine δ, P tm → P (TuringMachine.advance tm)}
  {hP : ∀ tm : TuringMachine δ, P tm → (TuringMachine.is_not_halted tm)}

lemma iter_ind (k : Nat) (tm : TuringMachine δ) (h : P tm) : P (TuringMachine.advance^[k] tm) := by
  cases k with
  | zero => assumption
  | succ k' =>
    apply iter_ind k'
    apply ind_step
    assumption

theorem non_halting_by_induction (tm : TuringMachine δ) (h : P tm) : TuringMachine.does_not_halt tm := by
  intro k
  apply hP
  apply iter_ind k tm h
  assumption


structure Point where

