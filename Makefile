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

TOOLCHAIN := $(shell cat $(EXTRACT_PKG)/lean-toolchain)

BINDIR := bin

.DEFAULT_GOAL := all

# reassemble `require`s the sibling packages, so parallel lake invocations would
# race on shared build trees. Lake parallelises within a package already.
.NOTPARALLEL:

.PHONY: all extract reassemble example clean distclean help toolchain

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

# Fetch the pinned toolchain up front rather than mid-build.
toolchain:
	elan toolchain install $(TOOLCHAIN)

help:
	@echo "Targets (Lean toolchain: $(TOOLCHAIN))"
	@echo "  all          lean_extract + lean_reassemble -> $(BINDIR)/"
	@echo "  extract      lean_extract only"
	@echo "  reassemble   lean_reassemble only"
	@echo "  example      build $(EXAMPLE_PKG)"
	@echo "  toolchain    install $(TOOLCHAIN) via elan"
	@echo "  clean        lake clean + drop $(BINDIR)/"
	@echo "  distclean    also remove .lake trees"
