-- Root module for the Corpus extractor library.
-- A general-purpose tool that walks a Lean project's elaborated environment
-- and emits JSONL records for downstream packaging (HuggingFace datasets,
-- LeanDojo-style premise tracking, etc.).

import Corpus.Records
import Corpus.Tags
import Corpus.Card
import Corpus.Extract
