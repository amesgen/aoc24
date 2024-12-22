import Aoc.Common

namespace Day21

open Batteries
open Parser Char ASCII

inductive Numpad where
  | key (n : Fin 10) | act
deriving Repr, BEq, Hashable

def parse (input : String) : List (List Numpad) :=
  match Parser.run (p <* endOfInput) input.trim with
  | .ok _ r => r
  | .error _ _ => []
  where
    p : P (List (List Numpad)) := sepBy lf (takeMany pNumpad)
      |> Functor.map (·.toList.map (·.toList))

    pNumpad : P Numpad := first [
        pure .act <* char 'A',
        do pure <| .key (← digit)
      ]

inductive Dirpad where
  | up | down | left | right | act
deriving Repr, BEq, Hashable

def allDirpads : List Dirpad :=
  [Dirpad.up, .down, .left, .right, .act]

def dirPos : Dirpad → ℤ × ℤ
| .up => (1, 0)
| .down => (1, 1)
| .left => (0, 1)
| .right => (2, 1)
| .act => (2, 0)

def numPos : Numpad → ℤ × ℤ
| .key 7 => (0, 0)
| .key 8 => (1, 0)
| .key 9 => (2, 0)
| .key 4 => (0, 1)
| .key 5 => (1, 1)
| .key 6 => (2, 1)
| .key 1 => (0, 2)
| .key 2 => (1, 2)
| .key 3 => (2, 2)
| .key 0 => (1, 3)
| .act => (2, 3)

def dirpadsFor (d : ℤ × ℤ)
  (noXFirst := false) (noYFirst := false) : List (List Dirpad) :=
  let dx := List.replicate d.1.natAbs <| if d.1 > 0 then .right else .left
  let dy := List.replicate d.2.natAbs <| if d.2 > 0 then .down else .up
  let xFirst := if noXFirst then [] else [dx ++ dy]
  let yFirst := if noYFirst then [] else [dy ++ dx]
  xFirst ++ yFirst |> Std.HashSet.ofList |>.toList |>.map (·.concat .act)

partial def numPresses (n : ℕ) (p : List Numpad) : ℕ :=
  let (choices, numCache, dirCache) := Id.run do
    let mut choices : List (List ((ℤ × ℤ) × List Dirpad)) := []
    let mut numCache : HashMap (Numpad × Numpad) (List Dirpad) := ∅
    let mut dirCache : HashMap (Dirpad × Dirpad) (List Dirpad) := ∅
    for (a, b) in (Numpad.act :: p).zip p do
      let (pa, pb) := (numPos a, numPos b)
      let d := pb - pa
      let noXFirst : Bool := pa.2 = 3 ∧ pb.1 = 0
      let noYFirst : Bool := pa.1 = 0 ∧ pb.2 = 3
      match dirpadsFor d noXFirst noYFirst with
      | [dps] => numCache := numCache.insert (a, b) dps
      | dpss => choices := dpss.map (d, ·) :: choices
    for (a, b) in allDirpads.product allDirpads do
      let (pa, pb) := (dirPos a, dirPos b)
      let d := pb - pa
      let noXFirst : Bool := pa.2 = 0 ∧ pb.1 = 0
      let noYFirst : Bool := pa.1 = 0 ∧ pb.2 = 0
      match dirpadsFor d noXFirst noYFirst with
      | [dps] => dirCache := dirCache.insert (a, b) dps
      | dpss => choices := dpss.map (d, ·) :: choices
    pure (choices.sections, numCache, dirCache)
  choices.map (fun choices ↦
      let choices : HashMap (ℤ × ℤ) (List Dirpad) := HashMap.ofList choices
      let liftNum (nps : List Numpad) : List Dirpad :=
        .act :: nps |>.zip nps  |>.flatMap fun (a, b) ↦ Option.get! <|
          numCache.find? (a, b) <|> choices.find? (numPos b - numPos a)
      let liftDir (dps : List Dirpad) : List Dirpad :=
        .act :: dps |>.zip dps |>.flatMap fun (a, b) ↦ Option.get! <|
          dirCache.find? (a, b) <|> choices.find? (dirPos b - dirPos a)
      let toDirPats (dps : List Dirpad) : HashMap (List Dirpad) ℕ :=
        let rec go (xs : List Dirpad) : List (List Dirpad) :=
          if xs.isEmpty then [] else
          let (as, bs) := xs.span (· != .act)
          let (bs, xs) := bs.span (· == .act)
          (as ++ bs) :: go xs
        go dps |>.map (·, 1) |> (HashMap.ofListWith · (·+·))
      let liftDirBatch (dps : HashMap (List Dirpad) ℕ) : HashMap (List Dirpad) ℕ :=
        dps.toList
          |>.map (fun (dps, n) ↦ dps |> liftDir |> toDirPats |>.mapVal (fun _ k ↦ n * k))
          |>.foldl (HashMap.mergeWith (fun _ ↦ (·+·))) ∅
      liftNum p |> toDirPats |> Nat.iterate liftDirBatch n
        |>.toList.map (fun (dps, n) ↦ dps.length * n) |>.sum)
    |>.min?.get!

def numericPart (p : List Numpad) : ℕ :=
  p.filterMap (fun | .key n => some ↑n | .act => none)
    |>.foldl (fun a d ↦ 10 * a + d) 0

def run (input : String) : ℕ × ℕ :=
  let input := parse input
  let solve n := input
    |>.map (fun p ↦ numPresses n p * numericPart p) |>.sum
  let part1 := solve 2
  let part2 := solve 25
  (part1, part2)

def ex := "
029A
980A
179A
456A
379A
"

/-- info: (126384, 154115708116294) -/
#guard_msgs in #eval run ex
