import Aoc.Common

namespace Day2

open Batteries

def parse (input : String) : List (List ℕ) :=
  input.trim.splitOn "\n"
    |>.map (·.splitOn " " |>.filterMap (·.toNat?))

def run (input : String) : ℕ × ℕ :=
  let input := parse input
  let part1 := input.filter isSafe |>.length
  let part2 := input.filter (fun r ↦ withoutOne r |>.any isSafe) |>.length
  (part1, part2)
  where
    isSafe (xs : List ℕ) : Bool :=
      let ds := diffs <| xs.map Int.ofNat
      let c0 := ds.all (·>0) || ds.all (·<0)
      let c1 := ds.map (·.natAbs) |>.all (fun d ↦ 1 <= d && d <= 3)
      c0 && c1

    diffs (xs : List ℤ) : List ℤ :=
      xs.zip (xs.drop 1) |>.map (fun (x, y) ↦ y - x)

    withoutOne {α} (xs : List α) : List (List α) :=
      xs.inits.zipWith (fun i t ↦ i ++ t.drop 1) xs.tails |>.dropLast
