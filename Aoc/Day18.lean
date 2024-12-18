import Aoc.Common

namespace Day18

open Batteries

def parse (input : String) : List (ℤ × ℤ) :=
  input.trim.splitOn "\n" |>.filterMap fun l ↦ do
    let [x, y] := l.splitOn "," | none
    pure (← x.toNat?, ← y.toNat?)

def bfs {α} [BEq α] [Hashable α] [Inhabited α]
  (s : α) (stop : α → Bool) (neighs : α → List α)
  : Option ℕ := Id.run do
  let mut dist : HashMap α ℕ := HashMap.ofList [(s, 0)]
  let mut q := Std.Queue.empty.enqueue s
  while ¬ q.isEmpty do
    let (v, q') := q.dequeue?.get!
    q := q'
    let d := dist.find! v
    if stop v then return some d
    for w in neighs v do
      if ¬ dist.contains w then
        dist := dist.insert w (d + 1)
        q := q.enqueue w
  pure none

def bisect {α} (p : List α → Bool) (xs : List α) : Option α :=
  let rec go (lb ub : ℕ) : Option α :=
    if lb + 1 < ub then
      let nb := (lb + ub) / 2
      if p (xs.take nb) then go nb ub else go lb nb
    else xs.get? (ub - 1)
  go 0 xs.length

def run (input : String)
  (space : ℕ × ℕ := (71, 71)) (part1Prefix : ℕ := 1024) : ℕ × String :=
  let bytes := parse input
  let run (bs : List (ℤ × ℤ)) : Option ℕ :=
    let bs := Std.HashSet.ofList bs
    let neighs (v : ℤ × ℤ) : List (ℤ × ℤ) :=
      [(1, 0), (0, 1), (-1, 0), (0, -1)].filterMap fun d ↦ do
        let w := v + d
        guard <| ¬ bs.contains w
        guard <| 0 ≤ w.1 ∧ 0 ≤ w.2 ∧ w.1 < space.1 ∧ w.2 < space.2
        pure w
    let s : ℤ × ℤ := (0, 0)
    let t : ℤ × ℤ := (space.1 - 1, space.2 - 1)
    bfs s (· = t) neighs

  let part1 := bytes.take part1Prefix |> run |>.get!

  let badByte := bisect (run · |>.isSome) bytes |>.get!
  let part2 := s!"{badByte.1},{badByte.2}"

  (part1, part2)

def ex := "
5,4
4,2
4,5
3,0
2,1
6,3
2,4
1,5
0,6
3,3
2,6
5,1
1,2
5,5
2,5
6,5
1,4
0,4
6,4
1,1
6,1
1,0
0,5
1,6
2,0
"

/-- info: (22, "6,1") -/
#guard_msgs in #eval run (space := (7, 7)) (part1Prefix := 12) ex
