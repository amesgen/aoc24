import Aoc.Common

namespace Day19

open Batteries

def parse (input : String) : List String × List String :=
  Option.get! do
    let [tow, pat] := input.trim.splitOn "\n\n" | none
    pure (tow.splitOn ", ", pat.splitOn "\n")

def run (input : String) : ℕ × ℕ :=
  let (tows, pats) := parse input
  let (tows, pats) := (tows.map (·.toList), pats.map (·.toList))
  let possible (pat : List Char) : ℕ :=
    let rec go : List Char → HashMap (List Char) ℕ
    | [] => HashMap.empty.insert [] 1
    | pat@(_ :: pat') =>
      let occs := go pat'
      let occ := tows.filterMap (fun tow ↦
        do some <| occs.find! (← pat.dropPrefix? tow)) |>.sum
      occs.insert pat occ
    go pat |>.find! pat
  let possibles := pats.map possible
  let part1 := possibles.filter (· > 0) |>.length
  let part2 := possibles.sum
  (part1, part2)

def ex := "
r, wr, b, g, bwu, rb, gb, br

brwrr
bggr
gbbr
rrbgbr
ubwu
bwurrg
brgr
bbrgwb
"

/-- info: (6, 16) -/
#guard_msgs in #eval run ex
