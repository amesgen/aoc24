import Aoc.Common

namespace Day4

open Batteries

def parse (input : String) : List (List Char) :=
  input.trim.splitOn "\n" |>.map (·.toList)

def run (input : String) : ℕ × ℕ :=
  let input := parse input

  let hori := input
  let vert := hori.transpose
  let allDiags := diags hori ++ diags (hori.map (·.reverse))
  let all  := andReverse <| hori ++ vert ++ allDiags
  let part1 := all.map countXmas |> List.sum

  let hori := input.mapIdx fun y r ↦ r.mapIdx fun x c ↦ ((y, x), c)
  let diags0 := andReverse <| diags hori
  let diags1 := andReverse <| diags <| hori.map (·.reverse)
  let mas0 := diags0.flatMap filterMas |> (RBSet.ofList · compare)
  let mas1 := diags1.flatMap filterMas |> (RBSet.ofList · compare)
  let mas : RBSet (ℕ × ℕ) := RBSet.intersectWith compare (fun _ ↦ id) mas0 mas1
  let part2 := mas.size

  (part1, part2)
  where
    andReverse {α} (xs : List (List α)) : List (List α) :=
      xs ++ xs.map (·.reverse)

    diags {α} (xs : List (List α)) : List (List α) :=
      let (d0, d1) := xs.mapIdx (fun i l ↦ l.splitAt i) |>.unzip
      (d0.map (·.reverse) |>.transpose) ++ d1.transpose

    countXmas : List Char → ℕ
    | 'X' :: 'M' :: 'A' :: 'S' :: xs => 1 + countXmas xs
    | _ :: xs => countXmas xs
    | [] => 0

    filterMas {α} : List (α × Char) → List α
    | (_, 'M') :: (a, 'A') :: (_, 'S') :: xs => a :: filterMas xs
    | _ :: xs => filterMas xs
    | [] => []

def ex := "
MMMSXXMASM
MSAMXMSMSA
AMXSXMAAMM
MSAMASMSMX
XMASAMXAMM
XXAMMXXAMA
SMSMSASXSS
SAXAMASAAA
MAMMMXMMMM
MXMXAXMASX
"

/-- info: (18, 9) -/
#guard_msgs in #eval run ex
