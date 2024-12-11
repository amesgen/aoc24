import Aoc.Common

namespace Day11

open Batteries

def parse (input : String) : List ℕ :=
  input.trim.splitOn " " |>.filterMap (·.toNat?)

def blink (n : ℕ) : List ℕ :=
  if n = 0 then [1] else
    let ds := 1 + Nat.log 10 n
    if ds % 2 = 0 then
      let x := 10 ^ (ds / 2)
      [n / x, n % x]
    else [n * 2024]

def blinks (s : RBMap ℕ ℕ) : RBMap ℕ ℕ :=
  s.toList.flatMap (fun (n, m) ↦ (·, m) <$> blink n)
    |> (RBMap.ofListWith · (·+·) _)

def run (input : String) : ℕ × ℕ :=
  let input := RBMap.ofListWith ((·, 1) <$> parse input) (·+·) compare
  let blinking (n : ℕ) : ℕ :=
    Nat.iterate blinks n input |>.valuesList |> List.sum
  let part1 := blinking 25
  let part2 := blinking 75
  (part1, part2)

def ex := "125 17"

/-- info: (55312, 65601038650482) -/
#guard_msgs in #eval run ex
