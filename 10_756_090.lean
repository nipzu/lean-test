import TuringMachine2

inductive State where
  | ST_A : State
  | ST_B : State
  | ST_C : State
  | ST_D : State
  | ST_E : State

inductive Symbol where
  | SYM_0 : Symbol
  | SYM_1 : Symbol

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
    | State.ST_E, Symbol.SYM_0 => (none,            Symbol.SYM_0, Direction.left)
    | State.ST_E, Symbol.SYM_1 => (some State.ST_A, Symbol.SYM_0, Direction.right)

def starting_machine : TuringMachine State Symbol transition := 
  TuringMachine.mk (Tape.blank Symbol.SYM_0) (State.ST_A)

theorem tm_not_halt : TuringMachine.does_not_halt starting_machine := by
  admit

namespace proof 

def list_repeat {A : Type} (n : Nat) (x : List A) : List A :=
  match n with
  | 0 => []
  | (n'+1) => x ++ list_repeat n' x

def append_to_repeated {A : Type} (n : Nat) (l : List A) : Stream' A -> Stream' A :=
  Stream'.appendStream' (list_repeat n l)

-- state: C
-- tape: C0 + 2n * [1] + [0] + n * [1]
def A (n : Nat) : TuringMachine State Symbol transition :=
  let right_tape : Stream' Symbol := 
    append_to_repeated (2*n) [Symbol.SYM_1] $
    Stream'.cons Symbol.SYM_0 $
    append_to_repeated n [Symbol.SYM_1] $
    (Stream'.const Symbol.SYM_0) 
  let tape : Tape Symbol := Tape.mk (Stream'.const Symbol.SYM_0) Symbol.SYM_0 right_tape
  TuringMachine.mk tape State.ST_C

-- state: E
-- tape: nl * [01] + E1 + nr * [11] + (nr + nl) * [1]
def A' (nl : Nat) (nr : Nat) : TuringMachine State Symbol transition :=
  let left_tape : Stream' Symbol := 
    append_to_repeated nl [Symbol.SYM_1, Symbol.SYM_0] $
    Stream'.const Symbol.SYM_0
  let right_tape : Stream' Symbol := 
    append_to_repeated (2*nr) [Symbol.SYM_1] $
    Stream'.cons Symbol.SYM_0 $
    append_to_repeated (nr + nl) [Symbol.SYM_1] $
    Stream'.const Symbol.SYM_0
  TuringMachine.mk (Tape.mk left_tape Symbol.SYM_1 right_tape) State.ST_E

-- state: D
-- tape: nl * [10] + nlm * [1] + D1 + nrm * [1] + [0] + nr * [1]
def M (nl : Nat) (nlm : Nat) (nrm : Nat) (nr : Nat) : TuringMachine State Symbol transition :=
  let left_tape : Stream' Symbol := 
    append_to_repeated nlm [Symbol.SYM_1] $
    append_to_repeated nl [Symbol.SYM_0, Symbol.SYM_1] $
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

theorem append_stream_one {A : Type} (x : A) (xs : List A) :
  Stream'.appendStream' (x :: xs) = Stream'.cons x ∘ Stream'.appendStream' xs
  := rfl

theorem list_repeat_one_cons {A : Type} (n : Nat) (s : A) :
  list_repeat (n + 1) [s] = s :: list_repeat n [s]
  := rfl

theorem append_repeated_one (n : Nat) (s : Symbol) :
  append_to_repeated (n + 1) [s] = append_to_repeated 1 [s] ∘ append_to_repeated n [s]
  := by
    rw [append_one_eq_cons]
    have : append_to_repeated (n + 1) [s] = Stream'.appendStream' (list_repeat (n + 1) [s]) := rfl
    rw [this, list_repeat_one_cons, append_stream_one]
    rfl

-- A' nl nr =>^2 A' (nl + 1) (nr - 1)
-- A' n 0  =>^2  M n 1 (n - 1) 0
-- M nl nlm nrm nr => M nl (nlm + 1) (nrm - 1) nr 

-- theorem A'_to_M ()

theorem A_to_A' (n : Nat) : TuringMachine.advance^[2] (A (n + 1)) = A' 1 n := by
  -- let next := TuringMachine.advance (A (n + 1))
  -- have : next.state = State.ST_A := rfl
  -- let cur := A (n + 1)
  -- have h1 : cur.state = some State.ST_C := rfl
  -- have h2 : cur.tape.cur_symbol = Symbol.SYM_0 := rfl
  -- let cur_state := Option.get cur.state (congr_arg Option.isSome h1)
  -- have : cur_state = State.ST_C := rfl
  -- let (next_state, written, dir) := transition cur_state cur.tape.cur_symbol
 
  -- have : cur.state = State.ST_C := rfl
  -- have : cur.tape.cur_symbol = Symbol.SYM_0 := rfl
  -- have : cur.tape.left_half 0 = Symbol.SYM_0 := rfl
  -- have : cur.tape.right_half 0 = Symbol.SYM_1 := rfl
  -- have : cur.tape.right_half 1 = Symbol.SYM_1 := rfl

  -- have : next.tape.cur_symbol = Symbol.SYM_1 := rfl
  -- have : next.tape.right_half 0 = Symbol.SYM_1 := rfl
  -- have : next.state = State.ST_A := rfl

  -- let next2 := TuringMachine.advance next
  -- have : next2.state = State.ST_E := rfl
  -- have : next2.tape.cur_symbol = Symbol.SYM_1 := rfl
  -- have : next2.tape.left_half = (A' 1 n).tape.left_half := rfl
  -- have : next2.tape.right_half 0 = (A' 1 n).tape.right_half 0 := rfl
  -- have t1 : next2.tape.right_half = 
  --   (append_to_repeated (2*n) [Symbol.SYM_1] $
  --   Stream'.cons Symbol.SYM_0 $
  --   append_to_repeated (1 + n) [Symbol.SYM_1] $
  --   Stream'.const Symbol.SYM_0) := rfl

  -- have : next2.tape.right_half = (A' 1 n).tape.right_half := by
  --   cases n
  --   . rfl
  --   . rfl

  -- have : next2 = TuringMachine.advance^[2] (A (n + 1)) := rfl
  rfl

theorem A'_to_A' (nl nr : Nat) : TuringMachine.advance^[2] (A' nl (nr + 1)) = A' (nl + 1) nr := by
  -- let cur := A' nl (nr + 1)
  -- have : cur.state = State.ST_E := rfl
  let next2 := TuringMachine.advance^[2] (A' nl (nr + 1))
  -- let next2 := TuringMachine.advance next
  -- have : next.state = State.ST_A := rfl
  -- have : next.tape.cur_symbol = Symbol.SYM_1 := rfl
  -- have : next.tape.right_half 0 = Symbol.SYM_1 := rfl
  -- have : next2.state = State.ST_E := rfl
  -- have : next2.tape.cur_symbol = Symbol.SYM_1 := rfl
  -- have : next2.tape.left_half = (A' (nl + 1) nr).tape.left_half := rfl
  -- have : next2.tape.right_half 0 = (A' (nl + 1) nr).tape.right_half 0 := by
  --   cases nr
  --   . rfl
  --   . rfl
  -- have : next2.tape.right_half 0 = (A' (nl + 1) nr).tape.right_half 0 := by
  --   cases nr
  --   . rfl
  --   . rfl
  have tr : next2.tape.right_half = (A' (nl + 1) nr).tape.right_half := by
    have t1 : (A' (nl + 1) nr).tape.right_half = 
      (append_to_repeated (2*nr) [Symbol.SYM_1] $
      Stream'.cons Symbol.SYM_0 $
      append_to_repeated (nr + (nl + 1)) [Symbol.SYM_1] $
      Stream'.const Symbol.SYM_0) := rfl
    have t2 : next2.tape.right_half = 
      (append_to_repeated (2*nr) [Symbol.SYM_1] $
      Stream'.cons Symbol.SYM_0 $
      append_to_repeated ((nr + 1) + nl) [Symbol.SYM_1] $
      Stream'.const Symbol.SYM_0) := rfl
    rw [t1, t2]
    have t3 : (nr + 1) + nl = nr + (nl + 1) := by
      rw [Nat.add_assoc]
      conv => arg 2; arg 2; rw [Nat.add_comm]
    rw [t3]
  -- have tl : next2.tape.left_half = (A' (nl + 1) nr).tape.left_half := rfl
  -- have tc : next2.tape.cur_symbol = (A' (nl + 1) nr).tape.cur_symbol := rfl
  -- have eqs : next2.state = (A' (nl + 1) nr).state := rfl
  ext : 1
  . ext : 1
    repeat rfl
    . exact tr
  . rfl

theorem A'_to_A'_iter (nl nr : Nat) : TuringMachine.advance^[2*nr] (A' nl nr) = A' (nl + nr) 0 := by
  cases nr
  . rfl
  case succ nr' =>
    have t := A'_to_A' nl nr'
    have t2 := congr_arg TuringMachine.advance^[2*nr'] t
    have t3 : TuringMachine.advance^[2 * (nr' + 1)] (A' nl (nr' + 1)) =
      TuringMachine.advance^[2 * nr'] (A' (nl + 1) nr') := t2
    have t4 := A'_to_A'_iter (nl + 1) nr'
    rw [t4] at t3
    have t5 : (nl + 1) + nr' = nl + (nr' + 1) := by
      rw [Nat.add_assoc]
      conv => arg 2; arg 2; rw [Nat.add_comm]
    rw [←t5]
    exact t3

theorem A_to_A'_iter (n : Nat) : TuringMachine.advance^[2*(n + 1)] (A (n + 1)) = A' (n + 1) 0 := by
  have t1 := A_to_A' n
  have t2 := congr_arg TuringMachine.advance^[2*n] t1
  have t3 := A'_to_A'_iter 1 n
  rw [t3] at t2
  conv => arg 2; arg 1; rw [Nat.add_comm]
  exact t2

end proof
