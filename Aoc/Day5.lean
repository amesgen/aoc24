import Aoc.Common

namespace Day5

open Batteries

def parse (input : String) : List (ℕ × ℕ) × List (List ℕ) :=
  (Option.getD · ([], [])) do
    let [rules, updates] := input.trim.splitOn "\n\n" | none
    let rules := rules.splitOn "\n" |>.filterMap fun r ↦ do
      let [a, b] := r.splitOn "|" | none
      pure (← a.toNat?, ← b.toNat?)
    let updates :=
      updates.splitOn "\n" |>.map (·.splitOn "," |>.filterMap (·.toNat?))
    pure (rules, updates)

def run (input : String) : ℕ × ℕ :=
  let (rules, updates) := parse input
  let rulesMap: RBMap ℕ (RBSet ℕ) := RBMap.group rules _ _

  let isSorted (xs : List ℕ) : Bool :=
    xs.zip (xs.tails.drop 1) |>.all fun (x, ys) ↦ ys.all fun y ↦ 
      match rulesMap.find? y with
      | none => true
      | some r => ! r.contains x
  let (sorted, unsorted) := updates.partition isSorted

  let summarize (xs : List (List ℕ)) :=
    xs.map (fun u ↦ u.getD (u.length / 2) 0) |> List.sum

  let part1 := summarize sorted

  let specialSort (xs : List ℕ) : List ℕ :=
    let cmp (x y : ℕ) : Ordering :=
      let rx := rulesMap.findD x RBSet.empty
      let ry := rulesMap.findD y RBSet.empty
      match rx.contains y, ry.contains x with
      | true, true => .eq
      | true, false => .lt
      | false, true => .gt
      | false, false => .eq -- partial
    RBSet.ofList xs cmp |>.toList

  let part2 := summarize <| unsorted.map specialSort

  (part1, part2)

def ex := "
47|53
97|13
97|61
97|47
75|29
61|13
75|53
29|13
97|29
53|29
61|53
97|53
61|29
47|13
75|47
97|75
47|61
75|61
47|29
75|13
53|13

75,47,61,53,29
97,61,53,29,13
75,29,13
75,97,47,61,53
61,13,29
97,13,75,29,47
"

/-- info: (143, 123) -/
#guard_msgs in #eval run ex
