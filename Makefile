# Builds the two tools: lean_extract (corpus extraction) and lean_reassemble
# (materializing records back into Lean artifacts).
#
#   make               both binaries, symlinked into bin/
#   make extract       just lean_extract
#   make reassemble    just lean_reassemble
#   make example       build examples/tree-project (needed by examples/README.md)
#   make test          run the four test executables
#   make artifacts     run the documented extract -> reassemble pipeline
#   make clean         drop build trees, keep the toolchain
#   make help          list targets
#
# Every build target delegates to lake rather than gating on timestamps: lake
# tracks freshness by content hash, which is strictly more accurate than mtime,
# and a no-op run costs about half a second. This Makefile exists to name the
# targets and to give the binaries a stable path, not to re-implement dependency
# tracking.

EXTRACT_PKG    := lean-extract
REASSEMBLE_PKG := reassemble
# reassemble `require`s workers (LeanReassemble.Rewrite uses Workers.WorkerPool to
# validate a rewritten file), so its build tree is produced here even though it
# has no target of its own.
WORKERS_PKG    := workers
EXAMPLE_PKG    := examples/tree-project
# reassemble/TestProject is a fixture package the reassemble tests build and
# extract from; it is a lake package in its own right, so it carries its own
# lean-toolchain and must move in lockstep with the rest.
FIXTURE_PKG    := $(REASSEMBLE_PKG)/TestProject

# Every package here is wired to its siblings by path `require`s, so lake
# resolves them into ONE workspace and they must all name the same toolchain.
# This list is the single place that knows the full set.
ALL_PKGS := $(EXTRACT_PKG) $(WORKERS_PKG) $(REASSEMBLE_PKG) $(FIXTURE_PKG) $(EXAMPLE_PKG)

TOOLCHAIN := $(shell cat $(EXTRACT_PKG)/lean-toolchain)

# The pinned toolchain's Lean library directory (holds libleanshared.so). Baked
# as the build-time DT_RUNPATH default so a locally-built binary loads its runtime
# with no environment. Resolved from within the package so elan honours the
# package's lean-toolchain rather than the ambient default.
LIBDIR := $(shell cd $(EXTRACT_PKG) && lean --print-libdir)

BINDIR := bin

# Where `make artifacts` writes. Outside the repo by default: the docs are
# explicit that the pipeline writes nothing into the working tree, and
# `materialize-*` refuses an output directory inside the source root anyway.
ARTIFACTS_DIR ?= /tmp/leagent-artifacts

# The grind modes need Lean v4.31+ (see lean-extract/Corpus/Compat.lean); below
# that they exit non-zero by design. `make artifacts` skips them there rather
# than treating a correct refusal as a failure. Compares the minor version, so
# this holds for 4.31 through 4.99 and any 5.x.
LEAN_MINOR := $(shell sed -n 's/.*lean4:v4\.\([0-9]*\).*/\1/p' $(EXTRACT_PKG)/lean-toolchain)
LEAN_MAJOR := $(shell sed -n 's/.*lean4:v\([0-9]*\)\..*/\1/p' $(EXTRACT_PKG)/lean-toolchain)
GRIND_OK   := $(shell [ "$(LEAN_MAJOR)" -gt 4 ] 2>/dev/null && echo yes || \
                     { [ "$(LEAN_MAJOR)" = 4 ] && [ "$(LEAN_MINOR)" -ge 31 ] 2>/dev/null && echo yes; })

.DEFAULT_GOAL := all

# reassemble `require`s the sibling packages, so parallel lake invocations would
# race on shared build trees. Lake parallelises within a package already.
.NOTPARALLEL:

.PHONY: all extract reassemble strip example test artifacts clean distclean help toolchain set-toolchain

all: extract reassemble

# lean_reassemble `require`s $(EXTRACT_PKG) and $(WORKERS_PKG) as path
# dependencies; lake builds those itself, so there is no ordering to enforce here.
#
# The binaries link libleanshared.so from the toolchain dynamically (see the
# lakefiles) rather than embedding a ~100 MB static copy. That library is not on
# the default loader path, so the lakefiles bake a DT_RUNPATH into each binary:
# `$ORIGIN` entries (for a binary placed beside a toolchain) plus, when built
# through this Makefile, the build-time absolute library directory ($(LIBDIR)),
# passed in as a Lake `-K` config option. A locally-built binary therefore finds
# its runtime with zero environment. The RUNPATH uses new dtags, so a user whose
# baked path does not exist (e.g. a downloaded release) overrides it with
# `LD_LIBRARY_PATH=$$(lean --print-libdir)`.
# `-R` (reconfigure) is required so a changed `-K libdir` is actually re-read:
# Lake caches the elaborated config and does not treat `-K` options as a config
# input, so without it a stale run's value would stick. Reconfiguring only
# re-elaborates the lakefile (sub-second); module builds stay content-hashed, so
# nothing recompiles when the value is unchanged.
extract: | $(BINDIR)
	cd $(EXTRACT_PKG) && lake build -R -K libdir=$(LIBDIR) lean_extract
	ln -sf ../$(EXTRACT_PKG)/.lake/build/bin/lean_extract $(BINDIR)/lean_extract

reassemble: | $(BINDIR)
	cd $(REASSEMBLE_PKG) && lake build -R -K libdir=$(LIBDIR) lean_reassemble
	ln -sf ../$(REASSEMBLE_PKG)/.lake/build/bin/lean_reassemble $(BINDIR)/lean_reassemble

$(BINDIR):
	mkdir -p $@

# Strip the built binaries in place (following the symlinks into the build trees).
# `--strip-all` drops .symtab/debug but keeps .dynsym, which the in-process
# interpreter (supportInterpreter := true) resolves against — so this is safe and
# roughly halves each binary. The release workflow strips its own dist/ copies;
# this target is for producing a stripped local build to measure or ship by hand.
strip:
	@for l in lean_extract lean_reassemble; do \
	  t=$(BINDIR)/$$l; \
	  if [ -e "$$t" ]; then \
	    r=$$(readlink -f "$$t"); \
	    echo "strip $$r ($$(du -h "$$r" | cut -f1) ->"; \
	    strip --strip-all "$$r"; \
	    echo "  $$(du -h "$$r" | cut -f1))"; \
	  fi; \
	done

# The extractor imports the target project's .oleans, so the example must be
# built before examples/README.md will work — including after `make clean`, which
# cleans it too. Without this, extraction fails with "extraction failed for N
# file(s)" rather than anything pointing at the missing build.
example:
	cd $(EXAMPLE_PKG) && lake build

# Run the documented pipeline end to end: extract with every mode this toolchain
# supports, then reassemble the results both ways. This is the integration test
# for `examples/quickstart.md` — the unit suites cover the pieces in isolation, so
# without this the whole extract -> reassemble path (and every command in the
# walkthrough) can break with CI still green.
#
# Both `materialize-*` commands verify their own output before exiting, so a
# silent exit 0 here means the generated Lean actually compiled against a pristine
# .olean cache. That is the assertion; the files left in $(ARTIFACTS_DIR) are for
# inspection.
#
# Writes outside the tree (see ARTIFACTS_DIR) and rebuilds from scratch each time,
# because `materialize-*` refuse a pre-existing output directory.
artifacts: all example
	rm -rf $(ARTIFACTS_DIR)
	@echo "=== extract: plain"
	./$(BINDIR)/lean_extract --source-root ./$(EXAMPLE_PKG) --modules Trees \
	    --output $(ARTIFACTS_DIR)/plain
	@echo "=== extract: reverse-elab"
	./$(BINDIR)/lean_extract --source-root ./$(EXAMPLE_PKG) --modules Trees \
	    --output $(ARTIFACTS_DIR)/rev-elab --reverse-elab
	@echo "=== extract: proof-metrics"
	./$(BINDIR)/lean_extract --source-root ./$(EXAMPLE_PKG) --modules Trees \
	    --output $(ARTIFACTS_DIR)/metrics --proof-metrics
	@echo "=== extract: proof-metrics + reverse-elab (tactic family from rev-elab body)"
	./$(BINDIR)/lean_extract --source-root ./$(EXAMPLE_PKG) --modules Trees \
	    --output $(ARTIFACTS_DIR)/metrics-rev --proof-metrics --reverse-elab
	@echo "=== extract: decl closure"
	./$(BINDIR)/lean_extract --source-root ./$(EXAMPLE_PKG) --modules Trees \
	    --output $(ARTIFACTS_DIR)/decl --decl Trees.Tree.total_mirror
	@echo "=== extract: proof states"
	./$(BINDIR)/lean_extract --source-root ./$(EXAMPLE_PKG) --modules Trees \
	    --output $(ARTIFACTS_DIR)/proof-states --proof-states
ifeq ($(GRIND_OK),yes)
	@echo "=== extract: grind manifest"
	./$(BINDIR)/lean_extract --source-root ./$(EXAMPLE_PKG) --modules Trees \
	    --output $(ARTIFACTS_DIR)/grind --grind-manifest
	@echo "=== extract: grind in proof"
	./$(BINDIR)/lean_extract --source-root ./$(EXAMPLE_PKG) --modules Trees \
	    --output $(ARTIFACTS_DIR)/grind-in-proof --grind-in-proof
else
	@echo "=== extract: grind modes SKIPPED (needs Lean v4.31+, have $(TOOLCHAIN))"
endif
	@echo "=== reassemble: repo (all 9 theorems holed in one project)"
	./$(BINDIR)/lean_reassemble materialize-repo \
	    --source-root ./$(EXAMPLE_PKG) \
	    --records $(ARTIFACTS_DIR)/plain/data/theorems/train.jsonl \
	    --output $(ARTIFACTS_DIR)/reasm/repo
	@echo "=== reassemble: units (one task per theorem)"
	./$(BINDIR)/lean_reassemble materialize-units \
	    --source-root ./$(EXAMPLE_PKG) \
	    --records $(ARTIFACTS_DIR)/plain/data/theorems/train.jsonl \
	    --output $(ARTIFACTS_DIR)/reasm/units
	@echo "=== reassemble: single task from the decl closure's target"
	./$(BINDIR)/lean_reassemble materialize-units \
	    --source-root ./$(EXAMPLE_PKG) \
	    --records $(ARTIFACTS_DIR)/decl/Trees.Tree.total_mirror/data/target.jsonl \
	    --output $(ARTIFACTS_DIR)/reasm/decl-unit
	@echo "=== reassemble: per-theorem manifest (delete + keep + default sorry)"
	printf '{"format":"lean-reassemble-manifest.v1","theorems":{"Trees.Tree.total_mirror":"delete","Trees.Tree.mirror_mirror":"keep"}}' \
	    > $(ARTIFACTS_DIR)/manifest.json
	./$(BINDIR)/lean_reassemble materialize-repo \
	    --source-root ./$(EXAMPLE_PKG) \
	    --records $(ARTIFACTS_DIR)/plain/data/theorems/train.jsonl \
	    --manifest $(ARTIFACTS_DIR)/manifest.json \
	    --output $(ARTIFACTS_DIR)/reasm/manifest-repo
	@echo "=== reassemble: repo with --on-failure backoff (clean records: no-op)"
	./$(BINDIR)/lean_reassemble materialize-repo \
	    --source-root ./$(EXAMPLE_PKG) \
	    --records $(ARTIFACTS_DIR)/plain/data/theorems/train.jsonl \
	    --on-failure backoff \
	    --output $(ARTIFACTS_DIR)/reasm/backoff-repo
	@echo "=== artifacts in $(ARTIFACTS_DIR)"

# `lake clean` leaves the toolchain and any fetched packages in place.
clean:
	cd $(EXTRACT_PKG) && lake clean
	cd $(REASSEMBLE_PKG) && lake clean
	cd $(WORKERS_PKG) && lake clean
	cd $(EXAMPLE_PKG) && lake clean
	rm -rf $(BINDIR)

# Nuclear option: also drops .lake/packages and every cached artifact.
distclean:
	rm -rf $(EXTRACT_PKG)/.lake $(REASSEMBLE_PKG)/.lake $(WORKERS_PKG)/.lake \
	       $(EXAMPLE_PKG)/.lake $(BINDIR)

# Run every test executable. Each `lake exe` builds its target first, so this
# also serves as the compile check for the test roots, which `make all` (binaries
# only) does not cover.
#
# The reassemble suite asserts that materialization leaves the fixture source
# tree pristine — specifically that TestProject/.lake does NOT exist. A stale
# fixture build tree (from someone running `lake build` in there, or an earlier
# aborted run) therefore fails the suite with "source build cache unchanged"
# no matter what the code does, so drop it first.
test:
	rm -rf $(FIXTURE_PKG)/.lake
	cd $(EXTRACT_PKG) && lake exe resume_tests
	cd $(EXTRACT_PKG) && lake exe decl_closure_tests
	cd $(EXTRACT_PKG) && lake exe proof_states_tests
	cd $(EXTRACT_PKG) && lake exe proof_metrics_tests
	cd $(REASSEMBLE_PKG) && lake exe reassemble_tests

# Fetch the pinned toolchain up front rather than mid-build.
toolchain:
	elan toolchain install $(TOOLCHAIN)

# Repoint every package at TOOLCHAIN, e.g.
#   make set-toolchain TOOLCHAIN=leanprover/lean4:v4.32.2
# This is what the CI matrix calls to test a version other than the committed
# pin; locally prefer `lake +<toolchain> build`, or a separate git worktree, since
# both leave the checked-in files alone. Note that flipping the toolchain in place
# invalidates every build trace (the toolchain is a trace input), so the next
# build is a full rebuild.
set-toolchain:
	@for pkg in $(ALL_PKGS); do \
	  echo "$(TOOLCHAIN)" > $$pkg/lean-toolchain; \
	  echo "$$pkg/lean-toolchain <- $(TOOLCHAIN)"; \
	done

help:
	@echo "Targets (Lean toolchain: $(TOOLCHAIN))"
	@echo "  all          lean_extract + lean_reassemble -> $(BINDIR)/"
	@echo "  extract      lean_extract only"
	@echo "  reassemble   lean_reassemble only"
	@echo "  example      build $(EXAMPLE_PKG)"
	@echo "  test         run all four test executables"
	@echo "  artifacts    run the full extract -> reassemble pipeline"
	@echo "  strip        strip .symtab/debug from the built binaries in place"
	@echo "  toolchain    install $(TOOLCHAIN) via elan"
	@echo "  set-toolchain  repoint all packages (make set-toolchain TOOLCHAIN=...)"
	@echo "  clean        lake clean + drop $(BINDIR)/"
	@echo "  distclean    also remove .lake trees"
