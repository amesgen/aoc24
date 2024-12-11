import Aoc.Common
import Parser

namespace Day3

open Batteries
open Parser Char ASCII

inductive Instr where
  | Mul (a b : ℕ)
  | Do (enabled : Bool)
deriving Repr

abbrev P := Parser Unit Substring Char

def parse (input : String) : List Instr :=
  match Parser.run (p <* endOfInput) input with
  | .ok _ r => r
  | .error _ _ => []
  where
    p : P (List Instr) := do
      let instrs ← takeMany (dropUntil pInstr anyToken)
      dropMany anyToken
      pure instrs.toList

    pInstr : P Instr := first [pMul, pDo, pDont]

    pMul : P Instr := do
      let _ ← string "mul("
      let a ← parseNat
      let _ ← char ','
      let b ← parseNat
      let _ ← char ')'
      pure <| .Mul a b

    pDo : P Instr := pure (.Do true) <* string "do()"
    pDont : P Instr := pure (.Do false) <* string "don't()"

def run (input : String) : ℕ × ℕ :=
  let input := parse input
  let part1 := input.map (fun | .Mul a b => a * b | _ => 0) |> List.sum
  let part2 :=
    let rec go (enabled : Bool) : List Instr → ℕ
    | [] => 0
    | .Mul a b :: xs => (if enabled then a * b else 0) + go enabled xs
    | .Do enabled :: xs => go enabled xs
    go true input
  (part1, part2)

def ex0 := "xmul(2,4)%&mul[3,7]!@^do_not_mul(5,5)+mul(32,64]then(mul(11,8)mul(8,5))"

/-- info: (161, 161) -/
#guard_msgs in #eval run ex0

def ex1 := "xmul(2,4)&mul[3,7]!^don't()_mul(5,5)+mul(32,64](mul(11,8)undo()?mul(8,5))"

/-- info: (161, 48) -/
#guard_msgs in #eval run ex1
