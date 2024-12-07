import Aoc.Common

namespace Day7

open Batteries

def parse (input : String) : List (ℕ × List ℕ) :=
  input.trim.splitOn "\n" |>.filterMap fun l ↦ do
    let [r, as] := l.splitOn ": " | none
    let as := as.splitOn " " |>.filterMap (·.toNat?)
    pure (← r.toNat?, as)

-- from mathlib
partial def log (b : ℕ) : ℕ → ℕ
| n => if b ≤ n ∧ 1 < b then log b (n / b) + 1 else 0

def conct (a b : ℕ): ℕ := a * (10 ^ (log 10 b + 1)) + b

def run (input : String) : ℕ × ℕ :=
  let input := parse input

  let test (ops : List (ℕ → ℕ → ℕ)) (r : ℕ) (as : List ℕ) : Bool :=
    let rec go (acc : ℕ) : List ℕ → Bool
    | [] => r = acc
    | a :: as => acc ≤ r ∧ ops.any fun op ↦ go (op acc a) as
    match as with
    | [] => false
    | a :: as => go a as

  let summarize ops :=
    input.filterMap (fun (r, as) ↦ do guard <| test ops r as; r) |> Nat.sum

  let ops1 := [(·+·), (·*·)]
  let ops2 := ops1.concat conct
  (summarize ops1, summarize ops2)

def ex := "
190: 10 19
3267: 81 40 27
83: 17 5
156: 15 6
7290: 6 8 6 15
161011: 16 10 13
192: 17 8 14
21037: 9 7 18 13
292: 11 6 16 20
"

/-- info: (3749, 11387) -/
#guard_msgs in #eval run ex
