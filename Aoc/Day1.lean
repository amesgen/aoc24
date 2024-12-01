import Aoc.Common

namespace Day1

open Batteries

def parse (input : String) : List (ℕ × ℕ) :=
  input.splitOn "\n" |>.filterMap fun l ↦ do
    let [a, b] := l.splitOn "   " | none
    pure (← a.toNat?, ← b.toNat?)

def run (input : String) : ℕ × ℕ := 
  let (as, bs) := parse input |>.unzip
  let part1 := as.sort.zip bs.sort
    |>.map (fun (a, b) ↦ if a >= b then a - b else b - a)
    |> Nat.sum
  let mults : RBMap ℕ ℕ := bs
    |>.map (fun b ↦ RBMap.single b 1)
    |>.foldl (RBMap.mergeWith (fun _ ↦ (·+·))) RBMap.empty
  let part2 := as.map (fun a ↦ a * mults.findD a 0) |> Nat.sum
  (part1, part2)
