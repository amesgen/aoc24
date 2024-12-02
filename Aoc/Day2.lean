import Aoc.Common

namespace Day2

open Batteries

def parse (input : String) : List (List ℕ) :=
  input.trim.splitOn "\n"
    |>.map (·.splitOn " " |>.filterMap (·.toNat?))

def run (input : String) : ℕ × ℕ :=
  let input := parse input
  let count p := input.filter p |>.length
  let part1 := count isSafe
  let part2 := count (withoutOne · |>.any isSafe)
  (part1, part2)
  where
    isSafe (xs : List ℕ) : Bool :=
      let ds := diffs <| xs.map Int.ofNat
      let c0 := ds.all (·>0) || ds.all (·<0)
      let c1 := ds.all fun d ↦ let d := d.natAbs; 1 <= d && d <= 3
      c0 && c1

    diffs (xs : List ℤ) : List ℤ := xs.zipWith (·-·) (xs.drop 1)

    withoutOne {α} : List α → List (List α)
    | [] => []
    | a :: as => as :: ((a :: ·) <$> withoutOne as)

def ex := "
7 6 4 2 1
1 2 7 8 9
9 7 6 2 1
1 3 2 4 5
8 6 4 4 1
1 3 6 7 9
"

/-- info: (2, 4) -/
#guard_msgs in #eval run ex
