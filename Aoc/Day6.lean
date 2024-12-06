import Aoc.Common

namespace Day6

open Batteries

def parse (input : String) : List (List Char) :=
  input.trim.splitOn "\n" |>.map (·.toList)

partial def run (input : String) : ℕ × ℕ :=
  let input := parse input
  let grid : RBMap (ℤ × ℤ) Char :=
    input.mapIdx (fun y r ↦ r.mapIdx fun x c ↦ ((x, y), c))
      |>.join |> (RBMap.ofList · _)
  let initialGuard := grid.toList
    |>.find? (fun (_, c) ↦ c == '^') |>.map (·.1) |>.getD (0, 0)
  let initialDir : ℤ × ℤ := (0, -1)

  let step (grid : RBMap (ℤ × ℤ) Char) (pos dir : ℤ × ℤ)
    : Option ((ℤ × ℤ) × (ℤ × ℤ)) :=
    let  pos' := pos + dir
    grid.find? pos' |>.map fun
      | '#' =>
        let dir' := (- dir.2, dir.1)
        (pos, dir')
      | _ => (pos', dir)

  let visited (grid : RBMap (ℤ × ℤ) Char) : Option (RBSet (ℤ × ℤ)) :=
    let rec go (visited : RBSet ((ℤ × ℤ) × (ℤ × ℤ))) (pos dir : ℤ × ℤ)
      : Option (RBSet ((ℤ × ℤ) × (ℤ × ℤ))) :=
      if visited.contains (pos, dir) then none else
        let visited := visited.insert (pos, dir)
        match step grid pos dir with
        | some (pos', dir') => go visited pos' dir'
        | none => visited
    go ∅ initialGuard initialDir |>.map (·.map (·.1))

  let part1 := visited grid |>.map (·.size) |>.getD 0
  let part2 := grid.toList
    -- prune candidates more efficiently
    |>.filterMap (fun (p, c) ↦ do
       guard <| c == '.'
       guard <| visited (grid.insert p '#') |>.isNone
       pure p)
    |>.length
  (part1, part2)

def ex := "
....#.....
.........#
..........
..#.......
.......#..
..........
.#..^.....
........#.
#.........
......#...
"

/-- info: (41, 6) -/
#guard_msgs in #eval run ex
