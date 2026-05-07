import Climber.Bedrock

/-- One-shot Bedrock connectivity check. Sends a trivial prompt and
    prints `OK: <text>` or exits non-zero on error. -/
def main : IO Unit := do
  let cfg := Climber.Bedrock.defaultConfig
  match ← Climber.Bedrock.invoke cfg "Reply with the single word READY and nothing else." with
  | .ok text => IO.println s!"OK: {text}"
  | .error msg =>
    IO.eprintln s!"ERROR: {msg}"
    IO.Process.exit 1
