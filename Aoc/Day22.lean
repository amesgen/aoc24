import Aoc.Common

namespace Day22

open Batteries

def parse (input : String) : List ℕ :=
  input.trim.splitOn "\n" |>.filterMap (·.toNat?)

def evolve : ℕ → ℕ :=
  let mixPrune (f : ℕ → ℕ) (n : ℕ) : ℕ := n.xor (f n) % 16777216
  mixPrune (· * 2048) ∘ mixPrune (· / 32) ∘ mixPrune (· * 64)

def slidingWindows {α} (n : ℕ) : List α → List (List α)
| [] => []
| xs@(_ :: ys) =>
    if xs.length < n then [] else
      xs.take n :: slidingWindows n ys

def run (input : String) : ℕ × ℕ :=
  let input := parse input
  let part1 := input.map (Nat.iterate evolve 2000) |>.sum
  let part2 := input.map (fun seed ↦
      let prizes := List.iterate evolve seed 2001 |>.map (· % 10)
      let prizeDiff a b := Int.ofNat a - Int.ofNat b
      let changes := prizes.drop 1 |>.zipWith prizeDiff prizes
      slidingWindows 4 changes |>.zip (prizes.drop 4)
        |> (HashMap.ofListWith · (fun p _ ↦ p)))
    |>.foldl (HashMap.mergeWith (fun _ ↦ (·+·))) ∅
    |>.toList.map (·.2) |>.max?.get!
  (part1, part2)

def ex0 := "
1
10
100
2024
"

/-- info: (37327623, 24) -/
#guard_msgs in #eval run ex0

def ex1 := "
1
2
3
2024
"

/-- info: (37990510, 23) -/
#guard_msgs in #eval run ex1
