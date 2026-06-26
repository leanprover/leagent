# Lean Workers

This library provides some infrastructure for driving `lean --worker`
subprocesses. In addition, there are some extensions to the workers which are
built as plugins that provide additional request handlers. These two things are
structured as two independent `lean_lib`s in the lake file.

- **`Workers`** - a version-agnostic library for spawning, pooling, and
  synchronizing `lean --worker` subprocesses and talking to them over the
  internal LSP-like protocol used by the Lean LSP watch dog process.

- **`WorkerPlugins`** - version-dependent plugins providing custom
  functionality within the file workers.

With this setup, new functionality can be added to the Lean `FileWorker`, and
accessed using the `Workers` library.j A driver (using `Workers`) sends a
custom request like `$/lean/corpusManifest`, and a plugin (from
`WorkerPlugins`, loaded into the worker) intercepts this request and answers
using the full context of the file being managed by the worker. This boundary
deliberately quarantines version-specific code inside the plugin, while the
driver consumes a stable JSON API.

## Layout

```
workers/
├─ Workers.lean              single import of the driver library
├─ Workers/
│  ├─ Worker.lean            single-worker driver
│  ├─ WorkerPool.lean        LRU pool of workers keyed by file URI
│  ├─ Sync.lean              path-based synchronization (see lean-mcp for usage example)
│  ├─ Document.lean          generated LSP edits from text diff
│  ├─ Cache.lean             search-path / olean-upload cache
│  └─ CacheFetch.lean        `lake update` + `lake cache get` for a package
└─ WorkerPlugins/
   ├─ Common.lean            common code shared by plugins
   ├─ ReverseElab.lean       [proof-script simplification](docs/proof-simplification.md)
   ├─ DeclManifest.lean      per-file audit
   └─ CorpusManifest.lean    dataset generation (for lean-extract)
```

The `Workers` library is thin, in-process driver for managing Lean File
Workers. This is similar to, but much smaller than the built-in Lean LSP
watchdog process. Here, the "client" is a tool call: each request either gets
its response or fails.

### Typical driver flow

```lean
open Workers
-- forwardArgs carry the plugin flags (see below)
let pool ← WorkerPool.new (maxSize := 4) (forwardArgs := pluginArgs)
             (projectRoot? := some projectRoot) (cache? := none)
let w ← pool.acquire uri text          -- spawns + initialize + didOpen
match (← w.waitForDiagnostics timeoutMs) with
| .done =>
    let slot ← w.sendRequest "id/1" "$/lean/corpusManifest" params
    match (← w.awaitResponse slot) with
    | .response _ payload => /- decode payload -/
    | _ => /- handle error -/
| .timeout | .workerExited => /- handle -/
pool.closeAll
```

## The `WorkerPlugins` library

Each plugin module is compiled to a **`.so`** (via Lake's `:dynlib` facet) and
loaded into the worker with `--plugin=`. Its `initialize` block calls
`registerLspRequestHandler`, after which the worker dispatches the custom
request exactly like a built-in one. The handler runs *inside* the worker, so
it has the post-elaboration `Environment`.

### Building plugins

By default, `lake build` only builds the `Workers` library. Plugins are
produced only by the explicit `:dynlib` facet.

```bash
lake build WorkerPlugins.CorpusManifest:dynlib \
           WorkerPlugins.ReverseElab:dynlib \
           WorkerPlugins.Common:dynlib
# → .lake/build/lib/lean/workers_WorkerPlugins_<Module>.so
```

### Loading plugins into a worker

A plugin `.so` references the `initialize` symbols of every shared helper it
imports---they are not statically bundled. So the worker must `--load-dynlib`
every helper *before* the `--plugin` for the handler: the order of the `.so`
loads matters. For example,

```
lean --worker \
  --load-dynlib=…workers_WorkerPlugins_Common.so \
  --load-dynlib=…workers_WorkerPlugins_ReverseElab.so \
  --plugin=…workers_WorkerPlugins_CorpusManifest.so \
  file://…/Foo.lean
```

This complexity is handled by the Workers library, but when adding new plugins
make sure to check everything loads properly at runtime.
