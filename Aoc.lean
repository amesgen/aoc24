import Aoc.Day1

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
        ("1", toString ∘ Day1.run)
      ]
