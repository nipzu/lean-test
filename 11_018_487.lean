import TuringMachine.Defs
import TuringMachine.Lemmas
import Mathlib.Tactic.Linarith.Frontend

def transition : State5 -> Symbol2 -> Option State5 × Symbol2 × Direction
  | State5.A, Symbol2.V0 => (some State5.B, Symbol2.V1, Direction.right)
  | State5.A, Symbol2.V1 => (some State5.A, Symbol2.V1, Direction.left )
  | State5.B, Symbol2.V0 => (some State5.C, Symbol2.V0, Direction.left )
  | State5.B, Symbol2.V1 => (some State5.E, Symbol2.V0, Direction.right)
  | State5.C, Symbol2.V0 => (none,          Symbol2.V1, Direction.right)
  | State5.C, Symbol2.V1 => (some State5.D, Symbol2.V1, Direction.left )
  | State5.D, Symbol2.V0 => (some State5.A, Symbol2.V1, Direction.left )
  | State5.D, Symbol2.V1 => (some State5.C, Symbol2.V0, Direction.left )
  | State5.E, Symbol2.V0 => (some State5.A, Symbol2.V1, Direction.right)
  | State5.E, Symbol2.V1 => (some State5.E, Symbol2.V1, Direction.right)

abbrev TM_11018487 := TuringMachine transition

-- In state A and tape filled with zeroes
def starting_machine : TM_11018487 :=
  TuringMachine.mk (Tape.blank Symbol2.V0) (State5.A)

namespace proof

-- state: B
-- tape: n*[1] + [0] + (2n+1)*[1] + B0
def B (n : Nat) : TuringMachine transition :=
  let left_tape : Stream' Symbol2 :=
    (2*n+1) ** [Symbol2.V1] ++
                Symbol2.V0  ::
       n    ** [Symbol2.V1] ++ₛ
    Stream'.const Symbol2.V0
  let tape : Tape Symbol2 := Tape.mk left_tape Symbol2.V0 (Stream'.const Symbol2.V0)
  TuringMachine.mk tape State5.B

-- state: C
-- tape: (nm + nr) * [1] + [0] + nm * [11] + C1 + nr * [01]
def B' (nm nr : Nat) : TM_11018487 :=
  let left_tape : Stream' Symbol2 :=
    (2*nm)  ** [Symbol2.V1] ++
                Symbol2.V0  ::
    (nm+nr) ** [Symbol2.V1] ++ₛ
    Stream'.const Symbol2.V0
  let right_tape : Stream' Symbol2 :=
    nr  ** [Symbol2.V0, Symbol2.V1] ++ₛ
    Stream'.const Symbol2.V0
  TuringMachine.mk (Tape.mk left_tape Symbol2.V1 right_tape) State5.C

-- state: A
-- tape: nl * [1] + [0] + nml * [1] + A1 + nmr * [1] + nr * [01]
def M (nl nml nmr nr : Nat) : TM_11018487 :=
  let left_tape : Stream' Symbol2 :=
    nml ** [Symbol2.V1] ++
            Symbol2.V0  ::
    nl  ** [Symbol2.V1] ++ₛ
    Stream'.const Symbol2.V0
  let right_tape : Stream' Symbol2 :=
    nmr ** [Symbol2.V1]             ++
    nr  ** [Symbol2.V0, Symbol2.V1] ++ₛ
    Stream'.const Symbol2.V0
  TuringMachine.mk (Tape.mk left_tape Symbol2.V1 right_tape) State5.A

-- state: E
-- tape: nl * [1] + [0] + nml * [1] + E1 + nmr * [1] + nr * [01]
def M' (nl nml nmr nr : Nat) : TM_11018487 :=
  let left_tape : Stream' Symbol2 :=
    nml ** [Symbol2.V1] ++
            Symbol2.V0  ::
    nl  ** [Symbol2.V1] ++ₛ
    Stream'.const Symbol2.V0
  let right_tape : Stream' Symbol2 :=
    nmr ** [Symbol2.V1]             ++
    nr  ** [Symbol2.V0, Symbol2.V1] ++ₛ
    Stream'.const Symbol2.V0
  TuringMachine.mk (Tape.mk left_tape Symbol2.V1 right_tape) State5.E

lemma reaches_B1 : starting_machine =>> B 1 := by exists 9

lemma B_to_B'_ : B (nm + nr) =>> B' nm nr := by
  cases nr with
  | zero =>
    exists 1
    ext : 1
    . ext : 1
      repeat rfl
      . have t1 : (TuringMachine.advance (B nm)).tape.right_half
          = [Symbol2.V0] ++ₛ (Stream'.const Symbol2.V0) := rfl
        simp [t1, cons_to_const]
        rfl
    . rfl
  | succ nr' =>
    have t1 : nm + (nr' + 1) = (nm + 1) + nr' := by linarith
    calc B (nm + (nr' + 1))
      _ =   B ((nm + 1) + nr') := by rw [t1]
      _ =>> B' (nm + 1) nr' := B_to_B'_ (nm := nm + 1) (nr := nr')
      _ =>> B' nm (nr' + 1) := by
        exists 2
        unfold B'
        ext : 2
        simp [t1]
        repeat rfl

lemma B'_to_M_ : B' 0 (nml + nmr + 1) =>> M 0 nml (nmr + 2) (nml + nmr + 1) := by
  cases nmr with
  | zero =>
    exists 2
    simp
    ext : 1
    . ext : 1
      . unfold M; simp
        have t1 : (TuringMachine.advance^[2] (B' 0 (nml + 1))).tape.left_half =
           (0 + nml) ** [Symbol2.V1] ++ₛ Stream'.const Symbol2.V0 := rfl
        simp [Nat.zero_add] at t1
        have t2 : [Symbol2.V0] ++ₛ Stream'.const Symbol2.V0 = Stream'.const Symbol2.V0 := by
          apply cons_to_const
        rw [t1, append_assoc, t2]
      . rfl
      . unfold M
        simp
        have t1 : (TuringMachine.advance $ TuringMachine.advance (B' 0 (nml + 1))).tape.right_half =
          Symbol2.V1::Symbol2.V1:: (nml + 1) ** [Symbol2.V0, Symbol2.V1] ++ₛ Stream'.const Symbol2.V0 := rfl
        rw [t1]
        rfl
    . rfl
  | succ nmr' =>
    have t1 : nml + (nmr' + 1) = (nml + 1) + nmr' := by linarith
    have t2 : (nml + 1) + nmr' + 1 = nml + nmr' + 2 := by linarith
    calc B' 0 (nml + (nmr' + 1) + 1)
      _ =   B' 0 ((nml + 1) + nmr' + 1) := by rw [t1]
      _ =>> M 0 (nml + 1) (nmr' + 2) ((nml + 1) + nmr' + 1) := B'_to_M_
      _ =   M 0 (nml + 1) (nmr' + 2) (nml + nmr' + 2) := by rw [t2]
      _ =>> M 0 nml (nmr' + 3) (nml + nmr' + 2) := by exists 1

lemma M_to_M'_ : M nl 0 (nml + nmr + 1) nr =>> M' (nl + 1) nml nmr nr := by
  cases nml with
  | zero => exists 3; simp; rfl
  | succ nml' =>
    have t1 : (nml' + 1) + nmr = nml' + (nmr + 1) := by linarith
    calc M nl 0 ((nml' + 1) + nmr + 1) nr
      _ =   M nl 0 (nml' + (nmr + 1) + 1) nr := by rw [t1]
      _ =>> M' (nl + 1) nml' (nmr + 1) nr := M_to_M'_
      _ =>> M' (nl + 1) (nml' + 1) nmr nr := by exists 1

lemma M'_to_M_ : M' nl (nml + nmr) 0 (nr + 1) =>> M nl nml (nmr + 2) nr := by
  cases nmr with
  | zero => exists 4
  | succ nmr' =>
    have t1 : nml + (nmr' + 1) = (nml + 1) + nmr' := by linarith
    calc M' nl (nml + (nmr' + 1)) 0 (nr + 1)
      _ = M' nl ((nml + 1) + nmr') 0 (nr + 1) := by rw [t1]
      _ =>> M nl (nml + 1) (nmr' + 2) nr := M'_to_M_
      _ =>> M nl nml (nmr' + 3) nr := by exists 1

lemma B_to_M' (h : nl + nr ≠ 0) : B (nl + nr) =>> M' (nl + 1) (nr + 2 * nl) 0 nr := by
  cases nl with
  | zero =>
    simp at h
    have ⟨nr', hnr'⟩ := Nat.exists_eq_succ_of_ne_zero h
    rw [hnr']
    simp
    calc B (nr' + 1)
      _ = B (0 + (nr' + 1)) := by simp
      _ =>> B' 0 (nr' + 1) := B_to_B'_
      _ =   B' 0 (0 + nr' + 1) := by simp
      _ =>> M 0 0 (nr' + 2) (0 + nr' + 1) := B'_to_M_ (nml := 0) (nmr := nr')
      _ =   M 0 0 (nr' + 2) (nr' + 1) := by simp
      _ =>> M' 1 (nr' + 1) 0 (nr' + 1) := M_to_M'_ (nl := 0) (nml := nr' + 1) (nmr := 0) (nr := nr' + 1)
  | succ nl' =>
    have t1 : (nl' + 1) + nr = nl' + (nr + 1) := by linarith
    have t2 : nr + 1 + 2 * nl' + 2 = nr + 2 * (nl' + 1) + 0 + 1 := by linarith
    have t3 : nl' + (nr + 1) ≠ 0 := by simp
    calc B ((nl' + 1) + nr)
      _ = B (nl' + (nr + 1)) := by rw [t1]
      _ =>> M' (nl' + 1) (nr + 1 + 2 * nl') 0 (nr + 1) := B_to_M' (nl := nl') (nr := nr + 1) t3
      _ =   M' (nl' + 1) (0 + (nr + 1 + 2 * nl')) 0 (nr + 1) := by simp
      _ =>> M  (nl' + 1) 0 (_ + 2) nr := M'_to_M_ (nl := nl' + 1) (nr := nr) (nml := 0) (nmr := nr + 1 + 2 * nl')
      _ =   M  (nl' + 1) 0 (nr + 2 * (nl' + 1) + 0 + 1) nr := by rw [t2]
      _ =>> M' (nl' + 2) (nr + 2 * (nl' + 1)) 0 nr := M_to_M'_ (nml := nr + 2 * (nl' + 1)) (nmr := 0) (nr := nr)

theorem B_to_B : B (n + 1) =>> B (n + 2) := by
  have t1 : n + 1 + 0 ≠ 0 := by simp
  calc B (n + 1)
    _ =  B ((n + 1) + 0) := by simp
    _ =>> M' (n + 2) (0 + 2 * (n + 1)) 0 0 := B_to_M' t1
    _ =>> B (n + 2) := by simp; exists 3

lemma B_ne_B : B n ≠ B (n + 1) := by
  intro h
  unfold B at h
  simp at h
  have h' := congr_arg (fun s => s (2 * n + 1)) h
  simp at h'
  rw [append_assoc, append_assoc] at h'
  have t1 : 2 * n + 1 < 2 * (n + 1) + 1 := by linarith
  conv at h' => rhs; rw [append_get' t1]
  conv at h' => arg 1; arg 3; rw [←Nat.one_mul (2 * n + 1)]
  have t2 : List.length [Symbol2.V1] * (2 * n + 1) + 0 = 1 * (2 * n + 1) := by rfl
  rw [←t2] at h'
  rw [append_get (k := (2 * n + 1)) (l := [Symbol2.V1]) (n := 0) (s := (Symbol2.V0 :: n ** [Symbol2.V1] ++ₛ Stream'.const Symbol2.V0))] at h'
  have t3 : Symbol2.V0 = Symbol2.V1 := h'
  have t4 : Symbol2.V0 ≠ Symbol2.V1 := by decide
  exact t4 t3

theorem tm_not_halt : TuringMachine.does_not_halt starting_machine :=
  tm_not_halt'
    (fun n => B (n + 1))
    starting_machine
    @B_to_B
    (fun n => @B_ne_B (n + 1))
    reaches_B1

end proof
