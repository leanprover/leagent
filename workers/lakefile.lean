import Lake
open Lake DSL

package workers

@[default_target]
lean_lib Workers where
  -- Consumer code; cheap to precompile and faster to import downstream.
  precompileModules := true

/-- Worker-side plugins: each is a `.so` whose `initialize` block registers an
LSP request handler (`$/lean/declManifest`, `$/lean/corpusManifest`, …) when
loaded by `lean --worker --plugin=...`.

Build a plugin artifact with e.g. `lake build WorkerPlugins.DeclManifest:dynlib`;
the result is `.lake/build/lib/lean/workers_WorkerPlugins_DeclManifest.so`.

Why no `precompileModules` here: lake normally only emits per-module `.so` files when a
downstream lean process imports the module. We never import a plugin module from
the `Workers` library (the plugin runs *inside* the worker, not the consumer), so the dynlib
facet is invoked explicitly by the consumer's build pipeline.

`roots` lists each plugin module plus the shared helpers (`Common`,
`ReverseElab`). Each plugin is built into its OWN `.so` via the `:dynlib` facet,
so loading one does not fire another's `initialize` block. `Common` and
`ReverseElab` have no `initialize` block (pure helpers), so they are safe as
roots; do NOT add an umbrella module that imports several plugins at once, as
that WOULD double-fire their `initialize` blocks. -/
lean_lib WorkerPlugins where
  roots := #[`WorkerPlugins.Common, `WorkerPlugins.ReverseElab,
             `WorkerPlugins.DeclManifest, `WorkerPlugins.CorpusManifest]
