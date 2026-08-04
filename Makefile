# Builds the two tools: lean_extract (corpus extraction) and lean_reassemble
# (materializing records back into Lean artifacts).
#
#   make               both binaries, symlinked into bin/
#   make extract       just lean_extract
#   make reassemble    just lean_reassemble
#   make example       build examples/tree-project (needed by examples/README.md)
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

BINDIR := bin

.DEFAULT_GOAL := all

# reassemble `require`s the sibling packages, so parallel lake invocations would
# race on shared build trees. Lake parallelises within a package already.
.NOTPARALLEL:

.PHONY: all extract reassemble example test clean distclean help toolchain set-toolchain

all: extract reassemble

# lean_reassemble `require`s $(EXTRACT_PKG) and $(WORKERS_PKG) as path
# dependencies; lake builds those itself, so there is no ordering to enforce here.
extract: | $(BINDIR)
	cd $(EXTRACT_PKG) && lake build lean_extract
	ln -sf ../$(EXTRACT_PKG)/.lake/build/bin/lean_extract $(BINDIR)/lean_extract

reassemble: | $(BINDIR)
	cd $(REASSEMBLE_PKG) && lake build lean_reassemble
	ln -sf ../$(REASSEMBLE_PKG)/.lake/build/bin/lean_reassemble $(BINDIR)/lean_reassemble

$(BINDIR):
	mkdir -p $@

# The extractor imports the target project's .oleans, so the example must be
# built before examples/README.md will work — including after `make clean`, which
# cleans it too. Without this, extraction fails with "extraction failed for N
# file(s)" rather than anything pointing at the missing build.
example:
	cd $(EXAMPLE_PKG) && lake build

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
	@echo "  toolchain    install $(TOOLCHAIN) via elan"
	@echo "  set-toolchain  repoint all packages (make set-toolchain TOOLCHAIN=...)"
	@echo "  clean        lake clean + drop $(BINDIR)/"
	@echo "  distclean    also remove .lake trees"
