import Aoc.Common

namespace Day10

open Batteries

def parse (input : String) : RBMap (ℤ × ℤ) ℕ :=
  input.trim.splitOn "\n"
    |>.mapIdx (fun y r ↦ r.toList.mapIdx fun x c ↦ ((x, y), c.toNat - '0'.toNat))
    |>.join |> (RBMap.ofList · _)

partial def run (input : String) : ℕ × ℕ :=
  let grid := parse input
  let zeroes : List ((ℤ × ℤ) × ℕ) := grid.toList.filter fun (_, h) ↦ h = 0

  let rate (f : ℕ → ℕ) : ℕ :=
    let dirs : List (ℤ × ℤ) := [(0, 1), (1, 0), (0, -1), (-1, 0)]
    let rec walk (z : (ℤ × ℤ) × ℕ) : StateM (RBMap (ℤ × ℤ) ℕ) ℕ := do
      match (← get).find? z.1 with
      | some n => pure (f n)
      | none => if z.2 = 9 then modify (·.insert z.1 1) *> pure 1 else do
        let mut r := 0
        for d in dirs do
          let pos' := z.1 + d
          match grid.find? pos' with
          | none => pure ()
          | some h' => if z.2 + 1 = h' then do
            r := r + (← walk (pos', h'))
        modify (·.insert z.1 r)
        pure r
    zeroes.map (walk · |>.run' ∅) |> Nat.sum

  let part1 := rate fun _ ↦ 0
  let part2 := rate id
  (part1, part2)

def ex := "
89010123
78121874
87430965
96549874
45678903
32019012
01329801
10456732
"

/-- info: (36, 81) -/
#guard_msgs in #eval run ex
