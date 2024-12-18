import Aoc.Common

namespace Day17

open Batteries
open Parser Char ASCII

structure State where
  ptr : ℕ
  out : List ℕ
  code : Array ℕ
  regA : ℕ
  regB : ℕ
  regC : ℕ
deriving Repr

def parse (input : String) : Option State :=
  match Parser.run (p <* endOfInput) input.trim with
  | .ok _ r => some r
  | .error _ _ => none
  where
    p : P State := do
      let regA ← pReg
      let regB ← pReg
      let regC ← pReg
      let _ ← lf *> string "Program: "
      let code ← sepBy (char ',') parseNat
      pure { ptr := 0, out := [], code, regA, regB, regC }

    pReg : P ℕ :=
      string "Register " *> anyToken *> string ": " *> parseNat <* lf

def step (s : State) : Option State :=
  match s.code.get? s.ptr, s.code.get? (s.ptr + 1) with
  | some op, some arg => some <| match Fin.ofNat' 8 op with
    | 0 => adv { s with regA := s.regA.shiftRight (combo arg) }
    | 1 => adv { s with regB := s.regB.xor arg }
    | 2 => adv { s with regB := combo arg % 8 }
    | 3 => if s.regA = 0 then adv s else { s with ptr := arg }
    | 4 => adv { s with regB := s.regB.xor s.regC }
    | 5 => adv { s with out := (combo arg % 8) :: s.out }
    | 6 => adv { s with regB := s.regA / 2 ^ combo arg }
    | 7 => adv { s with regC := s.regA / 2 ^ combo arg }
  | _, _ => none
  where
    adv (s : State) : State := { s with ptr := s.ptr + 2 }

    combo (n : ℕ) : ℕ :=
      if n = 4 then s.regA else
      if n = 5 then s.regB else
      if n = 6 then s.regC else
      n

def runOut (s : State) : List ℕ := Id.run do
  let mut s := s
  while true do
    match step s with
    | none => return s.out.reverse
    | some s' => s := s'
  pure default

def run (input : String) : Option (String × ℕ) := do
  let s: State ← parse input

  let out := runOut s
  let part1 := out |>.map toString |> String.intercalate ","

  -- This assumes that the program has a certain structure (i.e. it ends with
  -- 3,0, has no other jumps, only modifies A via 0,3, and B/C don't carry state
  -- across loop iterations), and returns nonsense otherwise.
  let sBodyLoop : State :=
    { s with code := s.code.toList.reverse.drop 2 |>.reverse.toArray }
  let asWithOutput (o : ℕ) (msba : ℕ) : List ℕ :=
    List.range 8 |>.filterMap fun lsba ↦ do
      let a := msba.shiftLeft 3 + lsba
      let s := { sBodyLoop with regA := a, out := [], ptr := 0 }
      guard <| runOut s = [o]
      pure a
  let part2 ← s.code.toList
    |>.foldr (fun c ↦ (·.flatMap (asWithOutput c))) [0] |>.min?

  (part1, part2)

def ex0 := "
Register A: 729
Register B: 0
Register C: 0

Program: 0,1,5,4,3,0
"

/-- info: some ("4,6,3,5,6,3,5,2,1,0", 29328) -/
#guard_msgs in #eval run ex0

def ex1 := "
Register A: 2024
Register B: 0
Register C: 0

Program: 0,3,5,4,3,0
"

/-- info: some ("5,7,3,0", 117440) -/
#guard_msgs in #eval run ex1
