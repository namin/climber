/-
  Bedrock client for the climber's LLM proposer.

  Wraps `aws bedrock-runtime invoke-model` and parses the
  Anthropic-on-Bedrock response shape. Body and response are written
  through temp files (the CLI takes the request body via
  `fileb://...` and writes the response to a positional path).

  Dependencies: the `aws` CLI on PATH, AWS credentials in the
  standard chain (env vars or `~/.aws/credentials`), Bedrock access
  in the configured region.
-/

import Lean.Data.Json

namespace Climber.Bedrock

open Lean (Json)

structure Config where
  region    : String := "us-east-1"
  modelId   : String := "us.anthropic.claude-sonnet-4-6"
  maxTokens : Nat    := 1024
  bodyPath  : String := "/tmp/climber-bedrock-body.json"
  outPath   : String := "/tmp/climber-bedrock-out.json"

def defaultConfig : Config := {}

/-- Build the request body in Bedrock/Anthropic Messages API format. -/
private def bodyJson (cfg : Config) (prompt : String) : Json :=
  Json.mkObj [
    ("anthropic_version", Json.str "bedrock-2023-05-31"),
    ("max_tokens", Lean.toJson cfg.maxTokens),
    ("messages", Json.arr #[
      Json.mkObj [("role", Json.str "user"), ("content", Json.str prompt)]
    ])
  ]

/-- Extract `content[0].text` from the Bedrock response. -/
private def extractText (j : Json) : Except String String := do
  let content ← j.getObjVal? "content"
  let arr ← content.getArr?
  match arr[0]? with
  | none => .error "response.content is empty"
  | some first =>
    let textNode ← first.getObjVal? "text"
    textNode.getStr?

/-- Make a single Bedrock call. Returns the model's text or an
    error string describing CLI / JSON / response-shape failures. -/
def invoke (cfg : Config) (prompt : String) : IO (Except String String) := do
  IO.FS.writeFile cfg.bodyPath (bodyJson cfg prompt).pretty
  let out ← IO.Process.output {
    cmd := "aws"
    args := #[
      "bedrock-runtime", "invoke-model",
      "--region", cfg.region,
      "--model-id", cfg.modelId,
      "--content-type", "application/json",
      "--body", "fileb://" ++ cfg.bodyPath,
      cfg.outPath
    ]
  }
  if out.exitCode != 0 then
    return .error s!"aws CLI failed (exit {out.exitCode}):\n{out.stderr}"
  let respText ← IO.FS.readFile cfg.outPath
  match Json.parse respText with
  | .error e => return .error s!"JSON parse failed: {e}\nresponse was: {respText}"
  | .ok json => return extractText json

end Climber.Bedrock
