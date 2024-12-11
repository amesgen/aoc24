import Aoc.Common

namespace Day11

open Batteries

def parse (input : String) : List ℕ :=
  input.trim.splitOn " " |>.filterMap (·.toNat?)

partial def log (b : ℕ) : ℕ → ℕ
  | n => if b ≤ n ∧ 1 < b then log b (n / b) + 1 else 0

def blink (n : ℕ) : List ℕ :=
  if n = 0 then [1] else
    let ds := 1 + log 10 n
    if ds % 2 = 0 then
      let x := 10 ^ (ds / 2)
      [n / x, n % x]
    else [n * 2024]

def blinks (s : RBMap ℕ ℕ) : RBMap ℕ ℕ :=
  s.toList.bind (fun (n, m) ↦ (·, m) <$> blink n)
    |> (RBMap.ofListWith · (·+·) _)

def iterate {α} (f : α → α) (n : ℕ) (a : α) : α :=
  match n with | 0 => a | Nat.succ n => iterate f n (f a)

def run (input : String) : ℕ × ℕ :=
  let input := RBMap.ofListWith ((·, 1) <$> parse input) (·+·) compare
  let blinking (n : ℕ) : ℕ := iterate blinks n input |>.valuesList |> Nat.sum
  let part1 := blinking 25
  let part2 := blinking 75
  (part1, part2)

def ex := "125 17"

/-- info: (55312, 65601038650482) -/
#guard_msgs in #eval run ex
