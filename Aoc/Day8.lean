import Aoc.Common

namespace Day8

open Batteries

def parse (input : String) : RBMap (ℤ × ℤ) Char :=
  input.trim.splitOn "\n"
    |>.mapIdx (fun y r ↦ r.toList.mapIdx fun x c ↦ ((x, y), c))
    |>.flatten
    |> (RBMap.ofList · _)

partial def run (input : String) : ℕ × ℕ :=
  let grid := parse input
  let antennas : RBMap Char (RBSet (ℤ × ℤ)) := grid.toList
    |>.filterMap (fun (pos, c) ↦ do guard <| c ≠ '.'; pure (c, pos))
    |> (RBMap.group · _ _)

  let countAnti (longRange : Bool) : ℕ := antennas.toList
    |>.flatMap (fun (_, poss) ↦ poss.toList
      |>.mapIdx (fun i p ↦ (p, ·) <$> poss.toList.drop (i + 1))
      |>.flatten
      |>.flatMap (fun (p, p') ↦
           let rec go (a b :  ℤ × ℤ) : List (ℤ × ℤ) :=
             if grid.contains a then a :: go (a + b) b else []
           let filterRange (xs : List (ℤ × ℤ)) :=
             if longRange then xs else xs.get? 2 |>.toList
           filterRange (go p (p' - p)) ++ filterRange (go p' (p - p'))))
    |> (RBSet.ofList · compare)
    |>.size

  let part1 := countAnti (longRange := false)
  let part2 := countAnti (longRange := true)
  (part1, part2)

def ex := "
............
........0...
.....0......
.......0....
....0.......
......A.....
............
............
........A...
.........A..
............
............
"

/-- info: (14, 34) -/
#guard_msgs in #eval run ex
