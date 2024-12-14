import Aoc.Common
import Parser

namespace Day13

open Batteries
open Parser Char ASCII

structure Claw where
  a : ℕ × ℕ
  b : ℕ × ℕ
  tgt : ℕ × ℕ
deriving Repr

abbrev P := Parser Unit Substring Char

def parse (input : String) : List Claw :=
  match Parser.run (p <* endOfInput) input with
  | .ok _ r => r
  | .error _ _ => []
  where
    p : P (List Claw) := do
      let claws ← takeMany (dropUntil pClaw anyToken)
      dropMany anyToken
      pure claws.toList

    pClaw : P Claw := do
      let a ← string "Button A: " *> pCoord <* lf
      let b ← string "Button B: " *> pCoord <* lf
      let tgt ← string "Prize: " *> pCoord <* lf
      pure { a, b, tgt }

    pCoord : P (ℕ × ℕ) := do
      let x ← string "X" *> anyToken *> parseNat
      let y ← string ", Y" *> anyToken *> parseNat
      pure (x, y)

def solveDio (a b c : ℕ) : Option ((ℤ × ℤ) × (ℤ × ℤ)) := do
  let (x, y) := Nat.xgcd a b
  let g := x * a + y * b
  guard <| g ∣ c
  let m := c / g
  let s := (x * m, y * m)
  let d : ℤ × ℤ := (b / g, - a / g)
  pure (s, d)

def play (claw : Claw) : Option ℕ := do
  let (s1, d1) ← solveDio claw.a.1 claw.b.1 claw.tgt.1
  let (s2, d2) ← solveDio claw.a.2 claw.b.2 claw.tgt.2
  let det := d2.2 * d1.1 - d2.1 * d1.2
  guard <| det ≠ 0 -- just doesn't occur in the test cases
  let num := d1.2 * (s2.1 - s1.1) - d1.1 * (s2.2 - s1.2)
  guard <| det ∣ num
  let l := num / det
  let (a, b) := (s2.1 + l * d2.1, s2.2 + l * d2.2)
  guard <| a ≥ 0 ∧ b ≥ 0
  pure <| 3 * a + b |>.toNat

def run (input : String) : ℕ × ℕ :=
  let input := parse input
  let part1 := input.filterMap play |> List.sum
  let off := 10000000000000
  let part2 := input
    |>.map (fun c ↦ { c with tgt := c.tgt + (off, off) })
    |>.filterMap play |> List.sum
  (part1, part2)

def ex := "
Button A: X+94, Y+34
Button B: X+22, Y+67
Prize: X=8400, Y=5400

Button A: X+26, Y+66
Button B: X+67, Y+21
Prize: X=12748, Y=12176

Button A: X+17, Y+86
Button B: X+84, Y+37
Prize: X=7870, Y=6450

Button A: X+69, Y+23
Button B: X+27, Y+71
Prize: X=18641, Y=10279
"

/-- info: (480, 875318608908) -/
#guard_msgs in #eval run ex
