import Aoc.Common

namespace Day20

open Batteries

def parse (input : String) : HashMap (ℤ × ℤ) Char :=
  input.trim.splitOn "\n"
    |>.mapIdx (fun y r ↦ r.toList.mapIdx fun x c ↦ ((x, y), c))
    |>.flatten |> HashMap.ofList

def bfs {α} [BEq α] [Hashable α] [Inhabited α]
  (s : α) (neighs : α → List α) : HashMap α ℕ := Id.run do
  let mut dist : HashMap α ℕ := HashMap.ofList [(s, 0)]
  let mut q := Std.Queue.empty.enqueue s
  while ¬ q.isEmpty do
    let (v, q') := q.dequeue?.get!
    q := q'
    let d := dist.find! v
    for w in neighs v do
      if ¬ dist.contains w then
        dist := dist.insert w (d + 1)
        q := q.enqueue w
  pure dist

def run (input : String) : ℕ × ℕ :=
  let grid := parse input
  let findTile (c : Char) : ℤ × ℤ := grid.toList.find? (·.2 = c) |>.get!.1
  let (st, en) := (findTile 'S', findTile 'E')
  let dirs := [(1, 0), (0, 1), (-1, 0), (0, -1)]
  let neighs (v : ℤ × ℤ) : List (ℤ × ℤ) := dirs.filterMap fun d ↦ do
    let w := v + d
    guard <| grid.find? w |>.any fun c ↦ c ≠ '#'
    pure w
  let (stDist, enDist) := (bfs st neighs, bfs en neighs)
  let noCheat := stDist.find! en

  let fromOrigin (n : ℕ) : List (ℤ × ℤ) :=
    dirs.flatMap fun d ↦ List.range n |>.map fun i ↦
      let i := Int.ofNat i
      ((n - i) * d.1 - i * d.2, (n - i) * d.2 + i * d.1)
  let cheats (n : ℕ) : List ℕ :=
    let offs := List.range n |>.flatMap fun i ↦ fromOrigin (i + 1)
    stDist.toList.flatMap fun (v, distv) ↦ offs.filterMap fun d ↦ do
      let distw ← enDist.find? (v + d)
      let distCheat := distv + d.1.natAbs + d.2.natAbs + distw
      guard <| distCheat < noCheat
      pure <| noCheat - distCheat

  let solve n := (cheats n).filter (· ≥ 100) |>.length
  (solve 2, solve 20)

def ex := "
###############
#...#...#.....#
#.#.#.#.#.###.#
#S#...#.#.#...#
#######.#.#.###
#######.#.#...#
#######.#.###.#
###..E#...#...#
###.#######.###
#...###...#...#
#.#####.#.###.#
#.#...#.#.#...#
#.#.#.#.#.#.###
#...#...#...###
###############
"

/-- info: (0, 0) -/
#guard_msgs in #eval run ex
