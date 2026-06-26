/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Paul Govereau
-/
import Workers.Worker
import Workers.WorkerPool
import Workers.Cache
import Workers.CacheFetch
import Workers.Document
import Workers.Sync

/-!
`Workers` — generic FileWorker driver library.

A consumer-agnostic, in-process API for spawning, pooling, and synchronizing
`lean --worker` subprocesses. Out-of-tree consumers (lean-mcp, lean-verify, lean-agent)
build on this library; nothing in here knows about MCP, JSON-RPC framing, batch verifier
shapes, or any other particular caller.

The library is layered:

- `Workers.Worker`     — single-worker subprocess driver (spawn, didOpen/didChange,
                         sendRequest/awaitResponse, waitForDiagnostics, shutdown).
- `Workers.WorkerPool` — LRU pool of workers keyed by URI; project-root resolution;
                         `LEAN_PATH` derived from a Cache.
- `Workers.Cache`      — agent/consumer-supplied search-path + olean upload directory.
- `Workers.CacheFetch` — drive `lake update` + `lake cache get` against a synthetic workspace.
- `Workers.Document`   — UTF-8 text-diff utility producing a single LSP range edit.
- `Workers.Sync`       — path-based glue: read file, acquire worker, diff/didChange,
                         wait for elaboration; pluggable `onSync?` per-call hook.

Companion package `WorkerPlugins` ships in this same project — a separate `lean_lib` whose
modules are loaded as plugins inside the `lean --worker` process to register additional LSP
request handlers (e.g. `$/lean/declManifest`).
-/
