import Aoc.Common

namespace Day23

open Batteries

def parse (input : String) : List (String × String) :=
  input.trim.splitOn "\n" |>.filterMap fun l ↦ do
    let [v, w] := l.splitOn "-" | none
    pure (v, w)

partial def run (input : String) : ℕ × String :=
  let edges := parse input
  let adj : HashMap String (Std.HashSet String) := edges
    |>.flatMap (fun (v, w) ↦ [(v, {w}), (w, {v})])
    |> (HashMap.ofListWith · Std.HashSet.union)
  let nodes := adj.toList.map (·.1)

  let part1 := Id.run do
    let mut vDone : Std.HashSet String := ∅
    let mut c := 0
    for v in nodes.filter (·.startsWith "t") do
      let mut wDone : Std.HashSet String := ∅
      let vAdj := adj.find! v
      for w in vAdj do
        if ¬ vDone.contains w then
          for u in adj.find! w do
            if ¬ vDone.contains u ∧ ¬ wDone.contains u ∧ vAdj.contains u then
              c := c + 1
          wDone := wDone.insert w
        vDone := vDone.insert v
    pure c

  -- Folklore, e.g. Algorithm 1 in https://doi.org/10.1016/S0166-218X(01)00290-6
  let rec clique (u : Std.HashSet String) (cl : RBSet String)
    : StateM (RBSet String) Unit := do
    if u.isEmpty then
      if cl.size > (← get).size then
        set cl
      return ()
    let mut u := u
    while ¬ u.isEmpty do
      if cl.size + u.size ≤ (← get).size then
        return ()
      let v := nodes.find? u.contains |>.get!
      u := u.erase v
      let mut u' := adj.find! v
      for w in u' do
        if ¬ u.contains w then
          u' := u'.erase w
      clique u' (cl.insert v)

  let part2 := clique (Std.HashSet.ofList nodes) ∅ |>.run ∅
    |> Id.run |>.2.toList |> String.intercalate ","

  (part1, part2)

def ex := "
kh-tc
qp-kh
de-cg
ka-co
yn-aq
qp-ub
cg-tb
vc-aq
tb-ka
wh-tc
yn-cg
kh-ub
ta-co
de-co
tc-td
tb-wq
wh-td
ta-ka
td-qp
aq-cg
wq-ub
ub-vc
de-ta
wq-aq
wq-vc
wh-yn
ka-de
kh-ta
co-tc
wh-qp
tb-vc
td-yn
"

/-- info: (7, "co,de,ka,ta") -/
#guard_msgs in #eval run ex
