import Lean

/-!
Tag-rule loading. The user supplies a JSON file with a list of rules; each rule
matches by substring against a constant's module name and contributes a set of
`(key, value)` tag pairs. Multiple matching rules union.

Schema:
```
{
  "rules": [
    { "match": "Foo.Bar", "tags": { "workstream": "A" } },
    ...
  ]
}
```
-/

namespace Corpus

open Lean

structure TagRule where
  /-- Substring matched against the module name. -/
  pattern : String
  /-- Tags contributed when this rule matches. -/
  tags    : List (String × String)
  deriving Inhabited

structure TagConfig where
  rules : List TagRule
  deriving Inhabited

/-- Empty config — used as the default when no `--config` is given. -/
def TagConfig.empty : TagConfig := { rules := [] }

/-- Parse a single tag rule from JSON. Tolerates a missing `tags` object. -/
private def parseRule (j : Json) : Except String TagRule := do
  let pattern ← (j.getObjVal? "match").bind (·.getStr?)
  let tags : List (String × String) ←
    match j.getObjVal? "tags" with
    | .ok (Json.obj kvs) =>
        let acc := kvs.foldl (init := ([] : List (String × String))) fun acc k v =>
          match v with
          | Json.str s => acc ++ [(k, s)]
          | _          => acc
        .ok acc
    | .ok _    => .ok []
    | .error _ => .ok []
  return { pattern := pattern, tags := tags }

/-- Parse the top-level config object. -/
def parseConfig (j : Json) : Except String TagConfig := do
  let rulesJson ← j.getObjVal? "rules"
  let arr ← rulesJson.getArr?
  let rules ← arr.toList.mapM parseRule
  return { rules := rules }

/-- Load a tag config from a JSON file path. -/
def loadConfig (path : System.FilePath) : IO TagConfig := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .error e => throw <| IO.userError s!"failed to parse tag config {path}: {e}"
  | .ok j =>
    match parseConfig j with
    | .error e => throw <| IO.userError s!"invalid tag config {path}: {e}"
    | .ok cfg  => pure cfg

/-- Compute the union of tags from all rules whose pattern is a substring of
`moduleName`. Stable order: first occurrence of each key wins; rule order is
preserved. -/
def TagConfig.matchTags (cfg : TagConfig) (moduleName : String) :
    List (String × String) := Id.run do
  let mut out : List (String × String) := []
  let mut seen : Std.HashSet String := {}
  for rule in cfg.rules do
    let parts := moduleName.splitOn rule.pattern
    if parts.length ≥ 2 then
      for (k, v) in rule.tags do
        unless seen.contains k do
          seen := seen.insert k
          out := out ++ [(k, v)]
  return out

end Corpus
