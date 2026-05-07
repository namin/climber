import Climber.Runner

/-- Usage: `lake exe runner [N]`
    N defaults to 3. -/
def main (args : List String) : IO Unit := do
  let nRounds : Nat := args.head?.bind (·.toNat?) |>.getD 3
  IO.println s!"climber runner: {nRounds} rounds"
  let bcfg : Climber.Bedrock.Config := {}
  let ecfg : Climber.Elab.Config :=
    { workingDir := some (← IO.currentDir).toString }
  let rcfg : Climber.Runner.Config := {}
  let mut admitted : List String := []
  let mut log : List Climber.Runner.RoundResult := []
  for i in [0:nRounds] do
    IO.println s!"\n========== ROUND {i+1}/{nRounds} =========="
    match ← Climber.Runner.runOneRound bcfg ecfg rcfg admitted with
    | none => IO.eprintln "(round skipped: Bedrock error)"
    | some r =>
      IO.println s!"VERDICT: {r.outcome}"
      log := log ++ [r]
      if r.outcome.isAdmitted then
        admitted := admitted ++ [r.formulaSrc]
  IO.println "\n========== SUMMARY =========="
  IO.println s!"Total rounds:  {log.length}"
  IO.println s!"Admitted:      {admitted.length}"
  let nErr := log.filter (fun r => match r.outcome with
    | .elabError _ => true | _ => false) |>.length
  IO.println s!"Elab errors:   {nErr}"
