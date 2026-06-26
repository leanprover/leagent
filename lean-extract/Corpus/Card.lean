import Lean
import Corpus.Records

/-!
Hugging Face dataset card support.

Loads a project-supplied JSON file describing the dataset's identity (name,
description, license, language, tags, homepage, citation, schema_version) and
renders a Markdown `README.md` with YAML frontmatter that the HF Hub UI can
consume.

This module is project-agnostic: every field except `name` is optional and is
omitted from the rendered card if absent.
-/

namespace Corpus

open Lean

/-- Project-supplied dataset identity. Mirrors the JSON schema described in
the module docstring. All fields except `name` are optional. -/
structure DatasetCardConfig where
  name           : String
  description    : Option String := none
  license        : Option String := none
  language       : Option (List String) := none
  tags           : Option (List String) := none
  homepage       : Option String := none
  citation       : Option String := none
  schemaVersion  : Option String := none
  deriving Inhabited

namespace DatasetCardConfig

private def getOptStr (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok v => v.getStr?.toOption
  | .error _ => none

private def getOptStrList (j : Json) (k : String) : Option (List String) :=
  match j.getObjVal? k with
  | .ok v =>
      match v.getArr? with
      | .ok arr =>
          let strs := arr.toList.filterMap (fun x => x.getStr?.toOption)
          some strs
      | .error _ => none
  | .error _ => none

/-- Parse a `DatasetCardConfig` from a parsed JSON value. -/
def fromJson? (j : Json) : Except String DatasetCardConfig := do
  let nameVal ← j.getObjVal? "name"
  let name ← nameVal.getStr?
  return {
    name           := name
    description    := getOptStr j "description"
    license        := getOptStr j "license"
    language       := getOptStrList j "language"
    tags           := getOptStrList j "tags"
    homepage       := getOptStr j "homepage"
    citation       := getOptStr j "citation"
    -- Accept either the JSON-native snake_case key or a camelCase fallback.
    schemaVersion  := (getOptStr j "schema_version").orElse fun _ => getOptStr j "schemaVersion"
  }

instance : FromJson DatasetCardConfig := ⟨fromJson?⟩

/-- Load a dataset card config from a JSON file path. -/
def load (path : System.FilePath) : IO DatasetCardConfig := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .error e => throw <| IO.userError s!"failed to parse dataset card config {path}: {e}"
  | .ok j =>
    match fromJson? j with
    | .error e => throw <| IO.userError s!"invalid dataset card config {path}: {e}"
    | .ok cfg  => pure cfg

end DatasetCardConfig

/-- Concrete numbers and shape that drive the rendered card body. -/
structure CardStats where
  /-- Total record count across every config (theorems + definitions). -/
  total            : Nat
  /-- Theorem count (the `theorems` config). -/
  theoremsTotal    : Nat
  /-- Definition count (the `definitions` config). -/
  definitionsTotal : Nat
  /-- Per-split counts for the theorems config in declaration order. Use
  `[("train", n)]` for unsplit. (HF reserves the name `all`.) -/
  theoremSplits    : List (String × Nat)
  /-- Combined kind counts across both configs, sorted by kind. -/
  kindCounts       : List (String × Nat)
  /-- Combined tag counts across both configs. Outer list sorted by tag key. -/
  tagCounts        : List (String × List (String × Nat))
  /-- Theorem example record (pretty-printed JSON). Preferred non-empty. -/
  theoremExample   : Option String
  /-- Definition example record (pretty-printed JSON). -/
  definitionExample : Option String
  deriving Inhabited

/-- Bucket record count into HF Hub `size_categories` labels. -/
private def sizeBucket (n : Nat) : String :=
  if n < 1000 then "n<1K"
  else if n < 10000 then "1K<n<10K"
  else if n < 100000 then "10K<n<100K"
  else if n < 1000000 then "100K<n<1M"
  else "n>1M"

/-- Conservative YAML scalar emitter: quote when the string contains chars
that confuse a minimal YAML parser, otherwise emit bare. We only ever feed
short user-provided metadata strings, so this avoids pulling in PyYAML-style
escape rules. -/
private def yamlScalar (s : String) : String :=
  let needsQuote :=
    s.isEmpty
    || s.trimAscii != s
    || s.any (fun c =>
        c == ':' || c == '#' || c == '"' || c == '\''
        || c == '\n' || c == '[' || c == ']'
        || c == '{' || c == '}' || c == ',' || c == '&'
        || c == '*' || c == '?' || c == '|' || c == '>'
        || c == '!' || c == '%' || c == '@' || c == '`')
  if needsQuote then (Json.str s).compress else s

/-- Render a single YAML key with either a scalar value or a list. -/
private def yamlKVScalar (key value : String) : String :=
  s!"{key}: {yamlScalar value}"

private def yamlKVList (key : String) (values : List String) : String :=
  let header := s!"{key}:"
  let items := values.map (fun v => s!"  - {yamlScalar v}")
  String.intercalate "\n" (header :: items)

/-- Build the YAML frontmatter for the dataset card.

We emit two HF Hub configs:
  * `theorems` — proof-bearing items, possibly split into train/valid/test.
  * `definitions` — context items (def/structure/inductive/abbrev/axiom/opaque),
    always a single `train` split (HF reserves the name `all`). -/
private def renderFrontmatter
    (cfg : DatasetCardConfig) (stats : CardStats) : String := Id.run do
  let mut lines : Array String := #["---"]
  if let some lic := cfg.license then
    lines := lines.push (yamlKVScalar "license" lic)
  if let some langs := cfg.language then
    lines := lines.push (yamlKVList "language" langs)
  if let some ts := cfg.tags then
    lines := lines.push (yamlKVList "tags" ts)
  lines := lines.push (yamlKVList "size_categories" [sizeBucket stats.total])
  lines := lines.push "configs:"
  lines := lines.push "- config_name: theorems"
  lines := lines.push "  data_files:"
  for (split, _) in stats.theoremSplits do
    lines := lines.push s!"  - split: {split}"
    lines := lines.push s!"    path: data/theorems/{split}.jsonl"
  lines := lines.push "- config_name: definitions"
  lines := lines.push "  data_files:"
  lines := lines.push "  - split: train"
  lines := lines.push "    path: data/definitions.jsonl"
  lines := lines.push "---"
  return String.intercalate "\n" lines.toList

/-- The schema documentation table. Static (one row per ConstRecord field). -/
private def schemaTable : String :=
  let header := "| Field | Type | Description |\n|---|---|---|"
  let rows : List (String × String × String) := [
    ("name", "string", "Fully-qualified Lean constant name."),
    ("kind", "string", "One of theorem/def/axiom/opaque/quot/inductive/structure/ctor/rec; prefixed with 'private ' when applicable."),
    ("module", "string", "Originating Lean module."),
    ("file", "string?", "Source file path joined under the extractor's source root."),
    ("start_line", "int?", "1-based start line; extended upward to cover doc comments and attribute decorators."),
    ("start_col", "int?", "Codepoint column for start_line (0-indexed)."),
    ("end_line", "int?", "1-based end line."),
    ("end_col", "int?", "Codepoint column for end_line (exclusive)."),
    ("source_text", "string?", "Verbatim source slice."),
    ("type", "string", "Pretty-printed type (line width 120)."),
    ("value", "string?", "Pretty-printed term-level body, when applicable."),
    ("doc", "string?", "Docstring, if any."),
    ("deps", "string[]", "Direct dependencies (constants in type union value), sorted, deduped, self excluded."),
    ("premises", "string[]", "Transitive premise cone reachable from the value through dependencies, restricted to owned (in-project) constants. Non-empty for theorems and defs with bodies; empty for axioms / opaques / inductives / structures."),
    ("axioms", "string[]", "Transitive axioms (Lean.collectAxioms); only populated for theorems."),
    ("is_protected", "bool", "Lean.isProtected."),
    ("is_private", "bool", "Lean.isPrivateName."),
    ("tags", "object", "Free-form key/value tags from the extractor's tag config.")
  ]
  let body := String.intercalate "\n" (rows.map fun (n, t, d) =>
    s!"| `{n}` | `{t}` | {d} |")
  header ++ "\n" ++ body

private def kindCountsTable (rows : List (String × Nat)) : String :=
  if rows.isEmpty then ""
  else
    let header := "| Kind | Count |\n|---|---|"
    let body := String.intercalate "\n"
      (rows.map fun (k, n) => s!"| `{k}` | {n} |")
    header ++ "\n" ++ body

private def tagCountsBlock (key : String) (rows : List (String × Nat)) : String :=
  let header := s!"### Counts by tag `{key}`\n\n| Value | Count |\n|---|---|"
  let body := String.intercalate "\n"
    (rows.map fun (v, n) => s!"| `{v}` | {n} |")
  header ++ "\n" ++ body

private def splitsTable (rows : List (String × Nat)) : String :=
  let header := "| Split | Records |\n|---|---|"
  let body := String.intercalate "\n"
    (rows.map fun (s, n) => s!"| `{s}` | {n} |")
  header ++ "\n" ++ body

/-- Two-row statistics table covering the two HF configs. -/
private def configStatsTable (stats : CardStats) : String :=
  let header := "| Config | Records |\n|---|---|"
  let body := String.intercalate "\n" [
    s!"| `theorems` | {stats.theoremsTotal} |",
    s!"| `definitions` | {stats.definitionsTotal} |"
  ]
  header ++ "\n" ++ body

/-- Render the full Markdown card. The output ends with a trailing newline. -/
def renderCard (cfg : DatasetCardConfig) (stats : CardStats) : String := Id.run do
  let mut parts : Array String := #[]
  parts := parts.push (renderFrontmatter cfg stats)
  parts := parts.push ""
  parts := parts.push s!"# {cfg.name}"
  if let some d := cfg.description then
    parts := parts.push ""
    parts := parts.push d
  if let some hp := cfg.homepage then
    parts := parts.push ""
    parts := parts.push s!"Homepage: {hp}"
  parts := parts.push ""
  parts := parts.push "## Configs"
  parts := parts.push ""
  parts := parts.push "This dataset ships with two Hugging Face configs:"
  parts := parts.push ""
  parts := parts.push "- `theorems` — proof-bearing items (`theorem` and `private theorem`). Stratified train/valid/test splits when produced with `--split-by-tag`, otherwise a single `train` split (HF reserves the name `all`)."
  parts := parts.push "- `definitions` — context items (`def`, `structure`, `inductive`, `abbrev`, `axiom`, `opaque`, and their `private` variants). Always a single `train` split."
  parts := parts.push ""
  parts := parts.push "Theorem records' `premises` field references constant names in the same project; many of those names appear as records in the `definitions` config."
  parts := parts.push ""
  parts := parts.push "## Schema"
  parts := parts.push ""
  parts := parts.push schemaTable
  if let some sv := cfg.schemaVersion then
    parts := parts.push ""
    parts := parts.push s!"Schema version: `{sv}`."
  parts := parts.push ""
  parts := parts.push "## Statistics"
  parts := parts.push ""
  parts := parts.push s!"Total records: **{stats.total}**."
  parts := parts.push ""
  parts := parts.push "Per config:"
  parts := parts.push ""
  parts := parts.push (configStatsTable stats)
  parts := parts.push ""
  parts := parts.push "Theorem splits:"
  parts := parts.push ""
  parts := parts.push (splitsTable stats.theoremSplits)
  parts := parts.push ""
  parts := parts.push "## Counts by kind"
  parts := parts.push ""
  parts := parts.push "Combined across both configs."
  parts := parts.push ""
  parts := parts.push (kindCountsTable stats.kindCounts)
  for (key, vals) in stats.tagCounts do
    parts := parts.push ""
    parts := parts.push (tagCountsBlock key vals)
  match stats.theoremExample, stats.definitionExample with
  | none, none => pure ()
  | _, _ =>
    parts := parts.push ""
    parts := parts.push "## Example records"
    if let some ex := stats.theoremExample then
      parts := parts.push ""
      parts := parts.push "Theorem:"
      parts := parts.push ""
      parts := parts.push s!"```json\n{ex}\n```"
    if let some ex := stats.definitionExample then
      parts := parts.push ""
      parts := parts.push "Definition:"
      parts := parts.push ""
      parts := parts.push s!"```json\n{ex}\n```"
  if let some cit := cfg.citation then
    parts := parts.push ""
    parts := parts.push "## Citation"
    parts := parts.push ""
    parts := parts.push s!"```\n{cit.trimAscii}\n```"
  return String.intercalate "\n" parts.toList ++ "\n"

end Corpus
