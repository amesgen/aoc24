import Aoc.Common

namespace Day15

open Batteries

def parse (input : String) : List String × List (ℤ × ℤ) := Option.get! do
  let [grid, moves] := input.trim.splitOn "\n\n" | none
  let grid := grid.splitOn "\n"
  let moves := moves.toList.filterMap fun
  | '>' => some (1, 0)
  | '<' => some (-1, 0)
  | 'v' => some (0, 1)
  | '^' => some (0, -1)
  | _ => none
  pure (grid, moves)

structure State where
  grid : HashMap (ℤ × ℤ) Char
  p : ℤ × ℤ

partial def step1 (m : ℤ × ℤ) : StateM State Unit := do
  let rec go (p : ℤ × ℤ) : StateM State Bool := do
    match (← get).grid.find? p with
    | none => pure false
    | '#' => pure false
    | 'O' => do
      let p' := p + m
      let r ← go p'
      if r then do
        modify fun s ↦ { s with grid := s.grid.insert p' 'O' }
      pure r
    | _ => pure true
  let p' := (← get).p + m
  if ← go p' then do
    modify fun s ↦ { grid := s.grid.insert p' '.', p := p' }

partial def step2 (m : ℤ × ℤ) : StateM State Unit := do
  let connected (grid : HashMap (ℤ × ℤ) Char) (p : ℤ × ℤ) : List (ℤ × ℤ) :=
    p :: match grid.find? p with
    | 'O' => [p + ((1, 0) : ℤ × ℤ)]
    | ']' => [p + ((-1, 0) : ℤ × ℤ)]
    | _ => []
  let rec goX (p : ℤ × ℤ) : StateM State Bool := do
    match (← get).grid.find? p with
    | none => pure false
    | some c => match c with
      | '#' => pure false
      | 'O' | ']' => do
        let p' := p + m
        let r ← goX p'
        if r then do
          modify fun s ↦ { s with grid := s.grid.insert p' c }
        pure r
      | _ => pure true
  let rec goY (ps : List (ℤ × ℤ)) : StateM State Bool := do
    let grid := (← get).grid
    let cs := ps.filterMap grid.find?
    if cs.any (· = '#') then pure false else
    if cs.all (fun c ↦ c = '.' ∨ c = '@') then pure true else
      let ps' := ps.zip cs
        |>.filterMap (fun (p, c) ↦ do guard <| c = 'O' ∨ c = ']'; some p)
        |>.flatMap (fun p ↦ connected grid (p + m))
        |> Std.HashSet.ofList |>.toList
      let r ← goY ps'
      if r then do
        let ps := Std.HashSet.ofList ps
        for p' in ps' do
          let p := p' - m
          let c := if ps.contains p then grid.find? p else '.'
          for c in c do modify fun s ↦ { s with grid := s.grid.insert p' c }
      pure r
  let s ← get
  let p' := s.p + m
  let ps' := if m.2 = 0 then [p'] else connected s.grid p'
  let r ← if m.2 = 0 then goX p' else goY ps'
  if r then do
    modify fun s ↦ { s with p := p' }
    for p' in ps' do
      modify fun s ↦ { s with grid := s.grid.insert p' '.' }

def run (input : String) : ℤ × ℤ :=
  let (rawGrid, moves) := parse input

  let summarize (grid : HashMap (ℤ × ℤ) Char) : ℤ :=
    grid.toList.filterMap (fun (p, c) ↦ do
        guard <| c = 'O'
        some <| 100 * p.2 + p.1)
      |>.sum

  let grid : HashMap (ℤ × ℤ) Char := rawGrid
    |>.mapIdx (fun y r ↦ r.toList.mapIdx fun x c ↦ ((x, y), c))
    |>.flatten |> HashMap.ofList
  let p := grid.toList.filterMap (fun (p, c) ↦ do guard <| c = '@'; some p) |>.head!
  let (_, s) := (for m in moves do step1 m).run { grid, p }
  let part1 := summarize s.grid

  let resize : Char → List Char
  | 'O' => ['O', ']']
  | '@' => ['@', '.']
  | c => [c, c]
  let grid : HashMap (ℤ × ℤ) Char := rawGrid
    |>.mapIdx (fun y r ↦ r.toList.flatMap resize |>.mapIdx fun x c ↦ ((x, y), c))
    |>.flatten |> HashMap.ofList
  let p := (p.1 * 2, p.2)
  let (_, s) := (for m in moves do step2 m).run { grid, p }
  let part2 := summarize s.grid

  (part1, part2)

def ex0 := "
########
#..O.O.#
##@.O..#
#...O..#
#.#.O..#
#...O..#
#......#
########

<^^>>>vv<v>>v<<
"

/-- info: (2028, 1751) -/
#guard_msgs in #eval run ex0

def ex1 := "
##########
#..O..O.O#
#......O.#
#.OO..O.O#
#..O@..O.#
#O#..O...#
#O..O..O.#
#.OO.O.OO#
#....O...#
##########

<vv>^<v^>v>^vv^v>v<>v^v<v<^vv<<<^><<><>>v<vvv<>^v^>^<<<><<v<<<v^vv^v>^
vvv<<^>^v^^><<>>><>^<<><^vv^^<>vvv<>><^^v>^>vv<>v<<<<v<^v>^<^^>>>^<v<v
><>vv>v^v^<>><>>>><^^>vv>v<^^^>>v^v^<^^>v^^>v^<^v>v<>>v^v^<v>v^^<^^vv<
<<v<^>>^^^^>>>v^<>vvv^><v<<<>^^^vv^<vvv>^>v<^^^^v<>^>vvvv><>>v^<<^^^^^
^><^><>>><>^^<<^^v>>><^<v>^<vv>>v>>>^v><>^v><<<<v>>v<v<v>vvv>^<><<>^><
^>><>^v<><^vvv<^^<><v<<<<<><^v<<<><<<^^<v<^^^><^>>^<v^><<<^>>^v<v^v<v^
>^>>^v>vv>^<<^v<>><<><<v<<v><>v<^vv<<<>^^v^>^^>>><<^v>>v^v><^^>>^<>vv^
<><^^>^^^<><vvvvv^v<v<<>^v<v>v<<^><<><<><<<^^<<<^<<>><<><^^^>^^<>^>v<>
^^>vv<^v^v<vv>^<><v<^v>^^^>>>^^vvv^>vvv<>>>^<^>>>>>^<<^v>^vvv<>^<><<v>
v^^>>><<^^<>>^v^<v^vv<>v^<<>^<^v^v><^<<<><<^<v><v<>vv>>v><v^<vv<>v^<<^
"

/-- info: (10092, 9021) -/
#guard_msgs in #eval run ex1

def ex2 := "
#######
#...#.#
#.....#
#..OO@#
#..O..#
#.....#
#######

<vv<<^^<<^^
"

/-- info: (908, 618) -/
#guard_msgs in #eval run ex2
