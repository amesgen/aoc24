import Aoc.Day1
import Aoc.Day2
import Aoc.Day3
import Aoc.Day4
import Aoc.Day5
import Aoc.Day6
import Aoc.Day7
import Aoc.Day8
import Aoc.Day9
import Aoc.Day10
import Aoc.Day11
import Aoc.Day12
import Aoc.Day13
import Aoc.Day14
import Aoc.Day15

def run (args : List String) : IO Unit := do
  let p := match args with
    | [] => fun _ ↦ true
    | dayName :: _ => (dayName == ·)
  for (dayName, runDay) in days do
    if p dayName then do
      let inputFile : System.FilePath := s!"./inputs/{dayName}"
      let outputFile : System.FilePath := s!"./outputs/{dayName}"
      let input ← IO.FS.readFile inputFile
      let start ← IO.monoMsNow
      let actualOutput := runDay input
      let elapsed := (← IO.monoMsNow) - start
      let report msg := println! "Day {dayName}: {actualOutput} {msg}"
      if ← outputFile.pathExists then
        let expectedOutput := (← IO.FS.readFile outputFile).trim
        if (expectedOutput == actualOutput) then
          report s!"✓ ({elapsed}ms)"
        else
          report s!"!!!, correct: {expectedOutput}"
      else
        report "?"
  where
    days : List (String × (String → String)) := [
        ("1", toString ∘ Day1.run),
        ("2", toString ∘ Day2.run),
        ("3", toString ∘ Day3.run),
        ("4", toString ∘ Day4.run),
        ("5", toString ∘ Day5.run),
        ("6", toString ∘ Day6.run),
        ("7", toString ∘ Day7.run),
        ("8", toString ∘ Day8.run),
        ("9", toString ∘ Day9.run),
        ("10", toString ∘ Day10.run),
        ("11", toString ∘ Day11.run),
        ("12", toString ∘ Day12.run),
        ("13", toString ∘ Day13.run),
        ("14", toString ∘ Day14.run),
        ("15", toString ∘ Day15.run)
      ]
