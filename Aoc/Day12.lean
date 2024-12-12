import Aoc.Common

namespace Day12

open Batteries

def parse (input : String) : List (List Char) :=
  input.trim.splitOn "\n" |>.map (·.toList)

partial def run (input : String) : ℕ × ℕ :=
  let grid : RBMap (ℤ × ℤ) Char := parse input
    |>.mapIdx (fun y r ↦ r.mapIdx fun x c ↦ ((x, y), c))
    |>.flatten |> (RBMap.ofList · _)

  let dirs : List (ℤ × ℤ) := [(0, 1), (1, 0), (0, -1), (-1, 0)]
  let rec dfs (gp : (ℤ × ℤ) × Char) : StateM (RBSet (ℤ × ℤ)) Unit := do
    if (← get).contains gp.1 then pure () else do
      modify (·.insert gp.1)
      for d in dirs do
        let pos' := gp.1 + d
        match grid.find? pos' with
        | none => pure ()
        | some c' => if gp.2 = c' then do
          dfs (pos', c')
  let gps : List (Char × RBSet (ℤ × ℤ)) := Id.run <| (StateT.run' · ∅) <|
    grid.toList.traverse (fun gp ↦ do
        let pre : RBSet (ℤ × ℤ) ← get
        if pre.contains gp.1 then pure none else do
          dfs gp
          let new := (← get) \ pre
          pure <| some (gp.2, new))
      |> Functor.map (·.filterMap id)

  let area (gp : RBSet (ℤ × ℤ)) : ℕ := gp.size
  let peri (gp : RBSet (ℤ × ℤ)) : ℕ × ℕ :=
    let speri p := (p, ·) <$> dirs
    let compareLenient := compareOn fun a ↦
      if a.2.1 = -1 ∨ a.2.2 = -1
      then (a.1 + a.2, (-a.2.1, -a.2.2)) else a
    let runs : List ℤ → ℕ :=
      let rec go : Option ℤ → List ℤ → ℕ
      | o, [] => o.toList.length
      | none, x :: xs => go (some x) xs
      | some y, x :: xs => (if y + 1 = x then 0 else 1) + go x xs
      go none
    let peris :=
      gp.toList.flatMap (fun p ↦ (·, 1) <$> speri p)
        |> (RBMap.ofListWith · (·+·) compareLenient)
        |>.filter (fun _ ↦ (· = 1))
    let peri1 := peris.size
    let grouped : RBMap ((ℤ × ℤ) × ℤ) (RBSet ℤ) :=
      peris.keysList.map (fun (p, d) ↦
          let p := if d.2 = 0 then p else (p.2, p.1); ((d, p.1), p.2))
        |> (RBMap.group · _ _)
    let peri2 := grouped.valuesList.map (·.toList |> runs) |> List.sum
    (peri1, peri2)

  gps.map (fun (_, gp) ↦
      let (peri1, peri2) := peri gp
      let area := area gp
      (area * peri1, area * peri2))
    |>.foldl (·+·) (0, 0)

def ex0 := "
AAAA
BBCD
BBCC
EEEC
"

/-- info: (140, 80) -/
#guard_msgs in #eval run ex0

def ex1 := "
OOOOO
OXOXO
OOOOO
OXOXO
OOOOO
"

/-- info: (772, 436) -/
#guard_msgs in #eval run ex1

def ex2 := "
EEEEE
EXXXX
EEEEE
EXXXX
EEEEE
"

/-- info: (692, 236) -/
#guard_msgs in #eval run ex2

def ex3 := "
AAAAAA
AAABBA
AAABBA
ABBAAA
ABBAAA
AAAAAA
"

/-- info: (1184, 368) -/
#guard_msgs in #eval run ex3
