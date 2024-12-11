import Aoc.Common

namespace Day6

open Batteries

def parse (input : String) : List (List Char) :=
  input.trim.splitOn "\n" |>.map (·.toList)

abbrev PosDir := (ℤ × ℤ) × (ℤ × ℤ)

structure WalkState where
  posdir : PosDir
  visited : Batteries.RBSet PosDir compare

partial def run (input : String) : ℕ × ℕ :=
  let input := parse input
  let grid : RBMap (ℤ × ℤ) Char :=
    input.mapIdx (fun y r ↦ r.mapIdx fun x c ↦ ((x, y), c))
      |>.flatten |> (RBMap.ofList · _)
  let initialGuard := grid.toList
    |>.find? (fun (_, c) ↦ c == '^') |>.map (·.1) |>.getD (0, 0)
  let initialDir : ℤ × ℤ := (0, -1)
  let initialState : WalkState := {
     posdir := (initialGuard, initialDir),
     visited := ∅
  }

  let step (grid : RBMap (ℤ × ℤ) Char) (posdir : PosDir) : Option PosDir :=
    let (pos, dir) := posdir
    let  pos' := pos + dir
    grid.find? pos' |>.map fun
      | '#' => (pos, (- dir.2, dir.1))
      | _ => (pos', dir)
  let rec walk (grid : RBMap (ℤ × ℤ) Char)
          (s : WalkState) : Option (List WalkState) :=
    if s.visited.contains s.posdir then none else
      let visited := s.visited.insert s.posdir
      match step grid s.posdir with
      | some posdir => (s :: ·) <$> walk grid { posdir, visited }
      | none => [s, { s with visited }]
  let walks := walk grid initialState |>.getD []

  let part1 := RBSet.ofList (walks.map (·.posdir.1)) compare |>.size

  let dirs : List (ℤ × ℤ) := [(1, 0), (0, 1), (-1, 0), (0, -1)]
  let obstrs := walks.filterMap fun s ↦ do
    let pos' := s.posdir.1 + s.posdir.2
    guard <| grid.find? pos' == '.'
    guard <| ! dirs.any fun d ↦ s.visited.contains (pos', d)
    guard <| walk (grid.insert pos' '#') s |>.isNone
    pure pos'
  let part2 := RBSet.ofList obstrs compare |>.size

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
