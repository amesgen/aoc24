import Aoc.Common

namespace Day9

open Batteries

def parse (input : String) : List ℕ :=
  input.trim.toList.map (·.toNat - '0'.toNat)

partial def run (input : String) : ℕ × ℕ :=
  let input := parse input

  let part1 :=
    let fs : List (Option ℕ) := input
      |>.mapIdx (fun i l ↦ List.replicate l (if i % 2 = 0 then some (i / 2) else none))
      |>.join
    let somes : List ℕ := fs.filterMap id
    let rec go1 {α} : List (Option α) → List α → List α
    | none :: xs, y :: ys => y :: go1 xs ys
    | none :: _, [] => []
    | some x :: xs, ys => x :: go1 xs ys
    | [], _ => []
    let defrag : List ℕ := go1 fs somes.reverse |>.take somes.length
    defrag.mapIdx (fun i c ↦ i * c) |> Nat.sum

  let part2 :=
    let fs : List (ℕ × Option ℕ) := input
      |>.mapIdx fun i l ↦ (l, do guard <| i % 2 = 0; some (i / 2))
    let rec go2 (lc : Option ℕ) : List (ℕ × Option ℕ) → List (ℕ × Option ℕ)
    | [] => []
    | x@(_, none) :: xs => x :: go2 lc xs
    | x@(l, lc'@(some c)) :: xs =>
      if lc.all (c < ·) then
        let rec go3 (foundGap : Bool) : List (ℕ × Option ℕ) → List (ℕ × Option ℕ)
        | [] => [if foundGap then (l, none) else x]
        | y@(l', none) :: ys =>
          if (!foundGap) && l ≤ l'
          then x :: (if l = l' then [] else [(l' - l, none)]) ++ go3 true ys
          else y :: go3 foundGap ys
        | y :: ys => y :: go3 foundGap ys
        let xs' := go3 false xs.reverse |>.reverse
        go2 lc' xs'
      else
        x :: go2 lc' xs
    let defrag := go2 none fs.reverse |>.reverse
    defrag.bind (fun (l, c) ↦ List.replicate l c)
      |>.mapIdx (fun i c ↦ i * c.getD 0) |> Nat.sum

  (part1, part2)

def ex := "2333133121414131402"

/-- info: (1928, 2858) -/
#guard_msgs in #eval run ex
