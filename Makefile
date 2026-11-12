# Lake owns Lean dependencies and incremental compilation. This file stages tools
# and provides short commands for the release checks.
.DEFAULT_GOAL := tools
LAKE ?= lake
PYTHON ?= python3
CARGO ?= cargo
PROJECT_TARGET = $(or $(CARGO_TARGET_DIR),tools/silmaril-project/target)
WASM_TOOLS := wasm-as wasm-dis wasm-opt wasm-merge wasm-shell wasm-ctor-eval wasm-metadce

.PHONY: tools stage library cache scope check release-check process-check process-gates project-lean project-tool project-check demo demo-process demo-sha256 help

tools:
	$(LAKE) build --wfail $(WASM_TOOLS)
	$(MAKE) stage

stage:
	@mkdir -p build/bin
	@for tool in $(WASM_TOOLS); do \
		test -x ".lake/build/bin/$$tool" || { echo "Missing $$tool; run make tools" >&2; exit 1; }; \
	done
	@for tool in $(WASM_TOOLS); do ln -sf "../../.lake/build/bin/$$tool" "build/bin/$$tool"; done
	cp scripts/sil build/bin/sil
	chmod +x build/bin/sil

library:
	$(LAKE) build --wfail Silmaril SilmarilSpecTec SilmarilWasiWit

# Everything `make check` builds; a recorded build publishes exactly these. A pull
# request narrows it to what its diff can change (`make scope`).
CHECK_TARGETS ?= Silmaril SilmarilSpecTec SilmarilWasiWit ProjectSelfTest $(WASM_TOOLS) wasm-shell-lean

# Files Lake never reads; only the source gates in `make check` read them.
SCOPE_EXCLUDE := 'docs/**' '**/*.md' 'scripts/**' 'apps/**' 'problems/**' 'specs/wasm/**' \
	'tools/process-release/**' 'tools/verification-projects/**' 'tools/silmaril-project/**' \
	policy.toml regions.toml

# Print CHECK_TARGETS, narrowed to what the change from BASE can affect when BASE is set.
scope:
	@if [ -n "$(BASE)" ]; then \
		cov-lake-cache scope --base "$(BASE)" $(addprefix --exclude ,$(SCOPE_EXCLUDE)) -- $(CHECK_TARGETS); \
	else \
		echo $(CHECK_TARGETS); \
	fi

# With the pool bucket, start from main's published seed (the whole recorded
# build in bulk streams, dependencies included) and build CHECK_TARGETS. Naming
# the targets installs only the mappings they need: 6 s, against 16 s for all.
cache:
	@if [ -n "$(LAKE_CI_BUCKET)" ]; then \
		cov-lake-cache get --seed --repository hiloopai/silmaril-lean -- $(CHECK_TARGETS); \
	else \
		cov-lake-cache dependencies; \
		echo 'No remote artifact bucket configured; public dependencies are ready.'; \
	fi

# The release suites run when CHECK_TARGETS holds the executables. A change scoped to a library
# that wasm-opt imports puts only wasm-opt in scope, so the other release binaries are built first.
RELEASE_BINARIES := wasm-opt wasm-as wasm-dis wasm-merge wasm-shell wasm-ctor-eval wasm-metadce wasm-shell-lean

check:
	scripts/check-layout.sh
	@if [ -n "$(LAKE_CACHE_RECORD)" ]; then \
		cov-lake-cache build --repository hiloopai/silmaril-lean --record "$(LAKE_CACHE_RECORD)" -- $(CHECK_TARGETS); \
	elif [ -n "$(strip $(CHECK_TARGETS))" ]; then \
		$(LAKE) build --wfail $(CHECK_TARGETS); \
	fi
	$(MAKE) process-gates
	$(if $(filter wasm-opt,$(CHECK_TARGETS)),$(LAKE) build --wfail $(RELEASE_BINARIES) && $(MAKE) release-check)

release-check:
	$(PYTHON) tools/binaryen-lean/check-release.py --jobs $$(nproc) --report build/wasm-checks.json
	$(MAKE) stage
	build/bin/sil --help >/dev/null
	build/bin/sil wasm opt --print-presets >/dev/null

process-check:
	$(LAKE) build --wfail \
		Silmaril.Process.Thms \
		Silmaril.Process.Model.Thms \
		Silmaril.Process.Shapes.Thms \
		Silmaril.Process.Syscalls.Linux.Thms \
		Silmaril.Process.Syscalls.X86.Thms \
		Silmaril.Process.X86.Thms \
		Silmaril.Process.RiscV.Thms \
		Silmaril.Process.Probes.Thms \
		Silmaril.Process.Musl.Thms \
		Silmaril.Process.Sha256.Thms \
		Silmaril.Process.LPS.Problems.GnuSha256sum.Close
	$(MAKE) process-gates

# Source-only process gates; they read no build output.
process-gates:
	$(PYTHON) tools/process-release/facts.py --check
	$(PYTHON) tools/process-release/check_headers.py
	$(PYTHON) apps/sha256sum-min/build.py --verify-only
	$(PYTHON) tools/verification-projects/x86_probe_problems.py check
	@if [ "$$(uname -s)" = Linux ]; then \
		$(PYTHON) -B tools/verification-projects/lps_probes.py check --offline; \
	else \
		echo 'lps probe ELF rebuild skipped on non-Linux host; CI runs the Linux offline and native gates'; \
	fi

# The project framework, its format adapters and shapes, and the self-test module (its own
# library, see lakefile.toml). `make project-check` also runs the Rust CLI over them.
project-lean:
	$(LAKE) build --wfail \
		Silmaril.Project.Defs \
		Silmaril.Project.Formats.Thms \
		Silmaril.Project.Shapes.Format.Thms \
		Silmaril.Project.Shapes.Elf.Thms \
		Silmaril.Project.Shapes.X86.Thms \
		Silmaril.Project.Shapes.Cli.Thms \
		Silmaril.Project.Room.Thms \
		ProjectSelfTest

project-tool:
	$(CARGO) build --release --locked --manifest-path tools/silmaril-project/Cargo.toml
	@mkdir -p build/bin
	cp "$(PROJECT_TARGET)/release/silmaril-project" build/bin/silmaril-project
	cp scripts/sil build/bin/sil
	chmod +x build/bin/sil

project-check: project-tool
	LAKE="$(LAKE)" SIL=build/bin/silmaril-project examples/project/selftest.sh

demo: tools
	$(PYTHON) tools/binaryen-lean/test-release-demo.py --bin-dir build/bin

demo-process:
	$(LAKE) build --wfail Silmaril.Process.Thms

demo-sha256:
	$(LAKE) build --wfail Silmaril.Process.CLI.Sha256Cli.Binary Silmaril.Process.LPS.Problems.Sha256Cli.EndToEnd
	$(LAKE) build --wfail Silmaril.Process.LPS.Problems.GnuSha256sum.Close

help:
	@echo 'make tools    Build seven native Wasm tools and stage build/bin/sil'
	@echo 'make library  Check every included Lean library module'
	@echo 'make cache    Restore dependencies; with LAKE_CI_BUCKET, the seed of main and the check targets'
	@echo 'make check    Build library, tools and proof roots; run native regressions'
	@echo 'make project-tool   Build sil project (Cargo) and stage it in build/bin'
	@echo 'make project-check  Run the sil project self-test: init, lock, lint, dump, check, explore'
	@echo 'make demo     Build tools; run the assemble/optimize/link/execute example'
	@echo 'make demo-process  Build the public process headers and theorem slice'
	@echo 'make demo-sha256   Build the sha256-cli and GNU sha256sum-min end-to-end proofs'
	@echo 'make process-check Run process facts, layout, catalogue and probe gates'
	@echo 'make stage    Stage already-built tools without compiling'
