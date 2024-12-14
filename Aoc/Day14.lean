import Aoc.Common

namespace Day14

open Batteries
open Parser Char ASCII

structure Robot where
  p : ℤ × ℤ
  v : ℤ × ℤ
deriving Repr

def parse (input : String) : List Robot :=
  match Parser.run (p <* endOfInput) input with
  | .ok _ r => r
  | .error _ _ => []
  where
    p : P (List Robot) := do
      let robots ← takeMany (dropUntil pRobot anyToken)
      dropMany anyToken
      pure robots.toList

    pRobot : P Robot := do
      let p ← string "p=" *> pXY <* string " "
      let v ← string "v=" *> pXY <* lf
      pure { p, v }

    pXY : P (ℤ × ℤ) := do
      let x ← parseInt <* string ","
      let y ← parseInt
      pure (x, y)

def step (space : ℕ × ℕ) (r : Robot) : Robot :=
  let p' := r.p + r.v
  { r with p := (p'.1 % space.1, p'.2 % space.2) }

def quadr (space : ℕ × ℕ) (r : Robot) : Option (ℤ × ℤ) :=
  match compare r.p.1 (space.1 / 2), compare r.p.2 (space.2 / 2) with
  | .lt, .lt => some (0, 0)
  | .gt, .lt => some (1, 0)
  | .lt, .gt => some (0, 1)
  | .gt, .gt => some (1, 1)
  | _, _ => none

def run (input : String) (space : ℕ × ℕ := (101, 103)) : ℕ × ℕ :=
  let robots := parse input
  let part1 := robots.map (Nat.iterate (step space) 100)
    |>.filterMap (fun r ↦ do some (← quadr space r, 1))
    |> (RBMap.ofListWith · (·+·) compare)
    |>.valuesList.foldl (·*·) 1
  let n : ℤ := robots.length
  let part2 := List.iterate (List.map (step space)) robots (space.1 * space.2)
    |>.mapIdx (fun i rs ↦
      let c := rs.map (·.p) |>.foldl (·+·) (Int.ofNat 0, Int.ofNat 0)
      let c : ℤ × ℤ := (c.1 / n, c.2 / n)
      let dist (p : ℤ × ℤ) : ℕ := (p.1 - c.1).natAbs + (p.2 - c.2).natAbs
      (i, rs.map (dist ·.p) |>.sum))
    |>.sortOn (·.2) |>.head? |>.map (·.1) |>.getD 0
  (part1, part2)

def ex := "
p=0,4 v=3,-3
p=6,3 v=-1,-3
p=10,3 v=-1,2
p=2,0 v=2,-1
p=0,0 v=1,3
p=3,0 v=-2,-2
p=7,6 v=-1,-3
p=3,0 v=-1,-2
p=9,3 v=2,3
p=7,3 v=-1,2
p=2,4 v=2,-3
p=9,5 v=-3,-3
"

/-- info: (12, 24) -/
#guard_msgs in #eval run ex (space := (11, 7))
