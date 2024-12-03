import Aoc.Common

namespace Day3

open Batteries

inductive Instr where
  | Mul (a b : ℕ)
  | Do | Dont
deriving Repr

def parse (input : String) : List Instr :=
  input.trim.toList.tails.filterMap fun l ↦ do
    let l := l.asString
    match l.dropPrefix? "mul(" with
    | none =>
      if l.startsWith "do()" then some .Do else
      if l.startsWith "don't()" then some .Dont
      else none
    | some l => do
      let l :: _ :: _ := l.splitOn ")" | none
      let [a, b] := l.splitOn "," | none
      pure <| .Mul (← a.toNat?) (← b.toNat?)

def run (input : String) : ℕ × ℕ :=
  let input := parse input
  let part1 := input.map (fun | .Mul a b => a * b | _ => 0) |> Nat.sum
  let part2 :=
    let rec go (enabled : Bool) : List Instr → ℕ
    | [] => 0
    | .Mul a b :: xs => (if enabled then a * b else 0) + go enabled xs
    | .Do :: xs => go true xs
    | .Dont :: xs => go false xs
    go true input
  (part1, part2)

def ex0 := "xmul(2,4)%&mul[3,7]!@^do_not_mul(5,5)+mul(32,64]then(mul(11,8)mul(8,5))"

/-- info: (161, 161) -/
#guard_msgs in #eval run ex0

def ex1 := "xmul(2,4)&mul[3,7]!^don't()_mul(5,5)+mul(32,64](mul(11,8)undo()?mul(8,5))"

/-- info: (161, 48) -/
#guard_msgs in #eval run ex1
