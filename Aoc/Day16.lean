import Aoc.Common

namespace Day16

open Batteries

def parse (input : String) : HashMap (ℤ × ℤ) Char :=
  input.trim.splitOn "\n"
    |>.mapIdx (fun y r ↦ r.toList.mapIdx fun x c ↦ ((x, y), c))
    |>.flatten |> HashMap.ofList

def dijkstra {α} [BEq α] [Hashable α] [Inhabited α]
  (s : α) (stop : α → Bool) (neighs : α → List (α × ℕ))
  : Option (α × ℕ × HashMap α (Std.HashSet α)) := Id.run do
  let mut done : Std.HashSet α := ∅
  let mut q : HashMap α ℕ := HashMap.ofList [(s, 0)]
  let mut prev : HashMap α (Std.HashSet α) := ∅
  while ¬q.isEmpty do
    let d := q.toList.map (·.2) |>.min?.get!
    let a := q.toList.find? (·.2 = d) |>.get!.1
    if stop a then return some (a, d, prev)
    q := q.erase a
    done := done.insert a
    for (b, l) in neighs a do
      if ¬ done.contains b then do
        let d' := d + l
        let (notLarger, smaller) := match q.find? b with
        | none => (true, true)
        | some d'' => (d' ≤ d'', d' < d'')
        if smaller then
          q := q.insert b d'
        if notLarger then
          let ba := HashMap.ofList [(b, {a})]
          prev := prev.mergeWith (fun _ ↦ (·.union)) ba
  pure none

abbrev Node := (ℤ × ℤ) × (ℤ × ℤ)

partial def run (input : String) : ℕ × ℕ :=
  let grid := parse input
  let findTile (c : Char) : ℤ × ℤ := grid.toList.find? (·.2 = c) |>.get!.1
  let st := findTile 'S'
  let en := findTile 'E'
  let neighs : Node → List (Node × ℕ)
  | (p, d) =>
    let walk :=
      let p' := p + d
      if grid.find? p' |>.any (· ≠ '#') then [((p', d), 1)] else []
    let turn := [(1, 0), (0, 1), (-1, 0), (0, -1)]
      |>.filter (· ≠ d)
      |>.map fun d' ↦ ((p, d'), 1000 * if d + d' = (0, 0) then 2 else 1)
    walk ++ turn
  let (en, part1, prev) := dijkstra (st, (1, 0)) (·.1 = en) neighs |>.get!
  let onBest : Std.HashSet (ℤ × ℤ) :=
    let rec go (s : Std.HashSet Node) : Std.HashSet Node :=
      let s' := s.toList.filterMap prev.find? |>.foldl (·.union ·) ∅
      if s'.isEmpty then s else s.union (go s')
    go {en} |>.toList.map (·.1) |> Std.HashSet.ofList
  let part2 := onBest.size
  (part1, part2)

def ex0 := "
###############
#.......#....E#
#.#.###.#.###.#
#.....#.#...#.#
#.###.#####.#.#
#.#.#.......#.#
#.#.#####.###.#
#...........#.#
###.#.#####.#.#
#...#.....#.#.#
#.#.#.###.#.#.#
#.....#...#.#.#
#.###.#.#.#.#.#
#S..#.....#...#
###############
"

/-- info: (7036, 45) -/
#guard_msgs in #eval run ex0

def ex1 := "
#################
#...#...#...#..E#
#.#.#.#.#.#.#.#.#
#.#.#.#...#...#.#
#.#.#.#.###.#.#.#
#...#.#.#.....#.#
#.#.#.#.#.#####.#
#.#...#.#.#.....#
#.#.#####.#.###.#
#.#.#.......#...#
#.#.###.#####.###
#.#.#...#.....#.#
#.#.#.#####.###.#
#.#.#.........#.#
#.#.#.#########.#
#S#.............#
#################
"

/-- info: (11048, 64) -/
#guard_msgs in #eval run ex1
