import Aoc.Common

namespace Day24

open Batteries
open Parser Char ASCII

inductive Op where | and | xor | or
deriving Repr, BEq, Hashable

structure Gate where
  op : Op
  in1 : String
  in2 : String
  out : String
deriving Repr

instance : Inhabited Gate where default := { op := .and, in1 := "", in2 := "", out := "" }

structure Input where
  inputs: List (String × Bool)
  gates: List Gate
deriving Repr

def parse (input : String) : Input :=
  match Parser.run (p <* endOfInput) input with
  | .ok _ r => r
  | .error _ _ => { inputs := [], gates := [] }
  where
    p : P Input := do
      let inputs ← takeMany (dropUntil pInput anyToken) <* lf
      let gates ← takeMany (dropUntil pGate anyToken)
      let _ ← dropMany anyToken
      pure { inputs := inputs.toList, gates := gates.toList }

    pInput : P (String × Bool) := do
      let wire ← pWire <* string ": "
      let b ← binDigit <* lf
      pure (wire, match b with | 0 => false | 1 => true)

    pGate : P Gate := do
      let in1 ← pWire <* space
      let op ← first [
        pure .and <* string "AND",
        pure .xor <* string "XOR",
        pure .or <* string "OR"
      ] <* space
      let in2 ← pWire <* string " -> "
      let out ← pWire <* lf
      pure { op, in1, in2, out }

    pWire : P String := take 3 anyToken |> Functor.map (·.toList.asString)

def bfs {α} [BEq α] [Hashable α] [Inhabited α]
  (s : α) (neighs : α → List α) : Std.HashSet α := Id.run do
  let mut visited : Std.HashSet α := ∅
  let mut q := Std.Queue.empty.enqueue s
  while ¬ q.isEmpty do
    let (v, q') := q.dequeue?.get!
    q := q'
    for w in neighs v do
      if ¬ visited.contains w then
        visited := visited.insert w
        q := q.enqueue w
  pure visited

partial def eval (input : Input) : ℕ :=
  let gatesByOut : HashMap String Gate := input.gates
    |>.map (fun g ↦ (g.out, g)) |> HashMap.ofList
  let rec go (w : String) : StateM (HashMap String Bool) Bool := do
    match (← get).find? w with
    | some b => pure b
    | none =>
      let g := gatesByOut.find! w
      let in1 ← go g.in1
      let in2 ← go g.in2
      let op := match g.op with
      | .and => Bool.and
      | .xor => Bool.xor
      | .or => Bool.or
      pure <| op in1 in2
  let inputs := HashMap.ofList input.inputs
  let zWires := input.gates.map (·.out)
    |>.filter (·.startsWith "z") |>.sort
  let bs : List Bool := zWires.mapA go |>.run' inputs
  bs.foldr (fun b a ↦ 2 * a + (if b then 1 else 0)) 0

def swapOuts (w0 w1 : String) : List Gate → List Gate :=
  let swap (g : Gate) : Gate := { g with out :=
    if g.out = w0 then w1 else if g.out = w1 then w0 else g.out }
  (·.map swap)

def run (input : String) (skipPart2 := false) : ℕ × String :=
  let input := parse input

  let part1 := eval input

  let part2 := if skipPart2 then "" else
    -- This assumes a very specific format of the input, in particular that it
    -- is very close to a ripple-carry adder built out of "canonical" full
    -- adders, i.e.
    --
    -- xN XOR yN -> a
    -- xN AND yN -> b
    -- a XOR cin -> zN
    -- a AND cin -> d
    -- b OR d -> cout
    --
    -- where cin/cout are the carry bits.
    let input := input
    let filterWires p := input.inputs.map (·.1) ++ input.gates.map (·.out)
      |>.filter (·.startsWith p) |>.sort
    let (xWires, yWires, zWires) := (filterWires "x", filterWires "y", filterWires "z")
    let findGateOut (op : Op) (in1 in2 : String) (gates : List Gate) : Option String :=
      gates.find? (fun g ↦
        let i := (g.in1, g.in2)
        g.op == op ∧ (i = (in1, in2) ∨ i = (in2, in1))) |>.map (·.out)
    let numInputs := xWires.length
    Id.run do
      let mut gates := input.gates
      let cout0 :=
        let x0 := xWires.get! 0
        let y0 := yWires.get! 0
        findGateOut .and x0 y0 gates |>.get!
      let mut couts : HashMap ℕ String := HashMap.empty.insert 0 cout0
      let mut swaps : List String := []
      let mut i := 1
      while i < numInputs do
        let x := xWires.get! i
        let y := yWires.get! i
        let z := zWires.get! i
        let a := findGateOut .xor x y gates |>.get!
        let cin := couts.find! (i - 1)
        let a ← match findGateOut .xor a cin gates with
        | some zActual =>
          if z ≠ zActual then
            gates := swapOuts z zActual gates
            swaps := z :: zActual :: swaps
          pure a
        | none =>
          let zOutGate := gates.find? (·.out = z) |>.get!
          let a' := if zOutGate.in1 = cin then zOutGate.in2 else zOutGate.in1
          gates := swapOuts a a' gates
          swaps := a :: a' :: swaps
          pure a'
        let b := findGateOut .and x y gates |>.get!
        let d := findGateOut .and a cin gates |>.get!
        let cout := findGateOut .or b d gates |>.get!
        couts := couts.insert i cout
        i := i + 1
      pure <| swaps.sort |> String.intercalate ","

  (part1, part2)

def ex0 := "
x00: 1
x01: 1
x02: 1
y00: 0
y01: 1
y02: 0

x00 AND y00 -> z00
x01 XOR y01 -> z01
x02 OR y02 -> z02
"

/-- info: (4, "") -/
#guard_msgs in #eval run ex0 (skipPart2 := true)

def ex1 := "
x00: 1
x01: 0
x02: 1
x03: 1
x04: 0
y00: 1
y01: 1
y02: 1
y03: 1
y04: 1

ntg XOR fgs -> mjb
y02 OR x01 -> tnw
kwq OR kpj -> z05
x00 OR x03 -> fst
tgd XOR rvg -> z01
vdt OR tnw -> bfw
bfw AND frj -> z10
ffh OR nrd -> bqk
y00 AND y03 -> djm
y03 OR y00 -> psh
bqk OR frj -> z08
tnw OR fst -> frj
gnj AND tgd -> z11
bfw XOR mjb -> z00
x03 OR x00 -> vdt
gnj AND wpb -> z02
x04 AND y00 -> kjc
djm OR pbm -> qhw
nrd AND vdt -> hwm
kjc AND fst -> rvg
y04 OR y02 -> fgs
y01 AND x02 -> pbm
ntg OR kjc -> kwq
psh XOR fgs -> tgd
qhw XOR tgd -> z09
pbm OR djm -> kpj
x03 XOR y03 -> ffh
x00 XOR y04 -> ntg
bfw OR bqk -> z06
nrd XOR fgs -> wpb
frj XOR qhw -> z04
bqk OR frj -> z07
y03 OR x01 -> nrd
hwm AND bqk -> z03
tgd XOR rvg -> z12
tnw OR pbm -> gnj
"
