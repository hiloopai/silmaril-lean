# Lake owns Lean dependencies and incremental compilation. This file stages tools
# and provides short commands for the release checks.
.DEFAULT_GOAL := tools
LAKE ?= lake
PYTHON ?= python3
CARGO ?= cargo
PROJECT_TARGET = $(or $(CARGO_TARGET_DIR),tools/silmaril-project/target)
WASM_TOOLS := wasm-as wasm-dis wasm-opt wasm-merge wasm-shell wasm-ctor-eval wasm-metadce

.PHONY: compiler-explorer-check logic-graph-check lean-ndjson-check json-loading-check tools stage library cache scope check release-check process-check process-gates project-lean project-tool project-registry project-check acceptor-report pages elf-check demo demo-process demo-sha256 help

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
	$(LAKE) build --wfail Silmaril SilmarilSpecTec SilmarilSpecTecMeta SilmarilWasiWit SilmarilWasmProject SilmarilLogicGraphData

# Everything `make check` builds; a recorded build publishes exactly these. A pull
# request narrows it to what its diff can change (`make scope`).
# The Cerberus tests and executables (docs/projects/cerberus.md).
CERBERUS_TARGETS := CerberusTests cerb-lean ail-lean core-lean core-elab cfront \
	ci_cerberus_genuine_oracle ci_cerberus_elaboration_oracle ci_cerberus_integer_cast \
	ci_cerberus_parameter_call
# The C compiler's executables (docs/projects/ccomp.md).
CCOMP_TARGETS := ccomp ccomp-legacy ccomp-verified csem decompile
CHECK_TARGETS ?= Silmaril SilmarilSpecTec SilmarilSpecTecMeta SilmarilWasiWit SilmarilWasmProject SilmarilLogicGraphData ProjectSelfTest wasm-pages elf-pages wasm-region-map $(WASM_TOOLS) wasm-shell-lean $(CERBERUS_TARGETS) SysVTvExample CompilesToExamples cexplorer-export $(CCOMP_TARGETS)

# Files Lake never reads; only the source gates in `make check` read them.
SCOPE_EXCLUDE := 'docs/**' '**/*.md' 'scripts/**' 'apps/**' 'problems/**' 'specs/wasm/**' \
	'tools/process-release/**' 'tools/verification-projects/**' 'tools/silmaril-project/**' \
	'tools/c-tv/**' 'tools/x86-lift/**' 'tools/litmus-x86/**' 'tools/litmus-run/**' 'examples/litmus-c/**' \
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
	$(PYTHON) -I scripts/check-wasm-spec.py
	$(PYTHON) -I scripts/check-wasm-checkers.py
	node examples/wasm-checkers/test-lrat.mjs
	$(PYTHON) -I scripts/check-wasm-sim.py
	$(PYTHON) -I tools/compiler-explorer/tests/test_cexplorer.py
	node --test tools/compiler-explorer/tests/view.test.mjs
	$(MAKE) json-loading-check
	@if [ -n "$(LAKE_CACHE_RECORD)" ]; then \
		cov-lake-cache build --repository hiloopai/silmaril-lean --record "$(LAKE_CACHE_RECORD)" -- $(CHECK_TARGETS); \
	elif [ -n "$(strip $(CHECK_TARGETS))" ]; then \
		$(LAKE) build --wfail $(CHECK_TARGETS); \
	fi
	$(MAKE) process-gates
	$(if $(filter Silmaril,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/formats/DrislDebug.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/NullPointerEquality.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/BitwiseRuntime.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/MemberRuntime.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/ShiftRuntime.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonPredicateContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/GnuDefaultVisibility.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/MimallocOsContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/MimallocOsFlagsContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/SqliteBuildQueriesContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/SqliteGlobalVersionExecution.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/SqliteGlobalVersionMachine.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/DarkhttpdLogEncodingContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonArraySizeContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonSuffixContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(PYTHON) -I tools/corpus/check_cjson_suffix_native.py)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonDetachContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonDetachMachine.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/cerberus/CjsonArrayItemObservation.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonArrayItemContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonArrayItemMachine.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(PYTHON) -I tools/corpus/check_cjson_array_item_native.py)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/cerberus/CjsonInsertObservation.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonInsertContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonInsertMachine.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(PYTHON) -I tools/corpus/check_cjson_insert_native.py)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(PYTHON) -I tools/corpus/check_cjson_array_item_inputs.py)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonArrayEquivalence.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(PYTHON) -I tools/corpus/check_cjson_array_equivalence_native.py)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonDetachEquivalence.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(PYTHON) -I tools/corpus/check_cjson_detach_equivalence_native.py)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(PYTHON) -I tools/corpus/check_cjson_detach_native.py)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/LoopControl.lean)
	$(if $(filter ci_cerberus_genuine_oracle,$(CHECK_TARGETS)),$(MAKE) cerberus-oracle)
	$(if $(filter wasm-opt,$(CHECK_TARGETS)),$(LAKE) build --wfail $(RELEASE_BINARIES) && $(MAKE) release-check)
	$(if $(filter elf-pages,$(CHECK_TARGETS)),$(MAKE) elf-check)
	$(if $(filter SilmarilLogicGraphData,$(CHECK_TARGETS)),$(MAKE) logic-graph-check)
	$(if $(filter cexplorer-export CompilesToExamples,$(CHECK_TARGETS)),$(MAKE) compiler-explorer-check)

# The Lean-NDJSON fixture is what lean4export writes now (docs/projects/formal-rows.md).
lean-ndjson-check:
	scripts/lean-ndjson/export-fixtures.sh --check

json-loading-check:
	$(LAKE) build --wfail Silmaril.Formats.Json.Fast.Elab
	$(LAKE) env lean -DautoImplicit=false -E warning tests/json-loading/Regression.lean

# The compiler explorer end to end: the exporter on every manifest, the statuses against
# examples/compiler-explorer/expected-status.txt, the database and view tests
# (docs/projects/compiler-explorer.md).
compiler-explorer-check:
	LAKE="$(LAKE)" PYTHON="$(PYTHON)" tools/compiler-explorer/check.sh

# The logic graph's records files: editing a records file
# rebuilds its loader incrementally (docs/projects/logic-graph.md).
logic-graph-check:
	LAKE="$(LAKE)" scripts/logic-graph/test-incremental.sh

# The ELF reader's pinned files, generated modules and explorer data (docs/projects/elf-reader.md).
ELF_PINNED := $(foreach n,HelloGcc HelloClang Sha256sum ZlibChecksums ZlibLibz GlibcLibm GlibcLibc,\
	Silmaril.Elf.Staged.Pinned.$(n).Thms Silmaril.Elf.Staged.Pinned.$(n).Functions)
elf-check:
	examples/elf/pin.sh --check
	$(LAKE) build --wfail elf-staged elf-pages Silmaril.Elf.Staged.Reader.Examples \
		$(ELF_PINNED) Silmaril.Elf.Staged.Pinned.ZlibChecksums.Contracts
	scripts/elf-reader/gen.sh --check
	scripts/elf-reader/test-pages.sh

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
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/NullPointerEquality.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/BitwiseRuntime.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/MemberRuntime.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/ShiftRuntime.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonPredicateContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/GnuDefaultVisibility.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/MimallocOsContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/MimallocOsFlagsContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/SqliteBuildQueriesContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/SqliteGlobalVersionExecution.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/SqliteGlobalVersionMachine.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/DarkhttpdLogEncodingContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonArraySizeContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonSuffixContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(PYTHON) -I tools/corpus/check_cjson_suffix_native.py)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonDetachContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonDetachMachine.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/cerberus/CjsonArrayItemObservation.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonArrayItemContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonArrayItemMachine.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(PYTHON) -I tools/corpus/check_cjson_array_item_native.py)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/cerberus/CjsonInsertObservation.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonInsertContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonInsertMachine.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(PYTHON) -I tools/corpus/check_cjson_insert_native.py)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(PYTHON) -I tools/corpus/check_cjson_array_item_inputs.py)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonArrayEquivalence.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(PYTHON) -I tools/corpus/check_cjson_array_equivalence_native.py)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonDetachEquivalence.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(PYTHON) -I tools/corpus/check_cjson_detach_equivalence_native.py)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(PYTHON) -I tools/corpus/check_cjson_detach_native.py)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/LoopControl.lean)

# Source-only process gates; they read no build output.
process-gates:
	$(PYTHON) -I tools/corpus/check_cjson_predicate_inputs.py
	$(PYTHON) -I tools/corpus/check_mimalloc_os_inputs.py
	$(PYTHON) -I tools/corpus/check_mimalloc_os_flag_inputs.py
	$(PYTHON) -I tools/corpus/check_sqlite_build_query_inputs.py
	$(PYTHON) -I tools/corpus/check_darkhttpd_logencoding_inputs.py
	$(PYTHON) -I tools/corpus/check_cjson_array_size_inputs.py
	$(PYTHON) -I tools/corpus/check_cjson_suffix_inputs.py
	$(PYTHON) -I tools/corpus/check_cjson_detach_inputs.py
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
		Silmaril.Project.Shapes.Language.Thms \
		Silmaril.Project.Shapes.Consequence.Thms \
		Silmaril.Project.Languages.Wasm.Defs \
		Silmaril.Project.Shapes.Elf.Thms \
		Silmaril.Project.Shapes.X86.Thms \
		Silmaril.Project.Shapes.Cli.Thms \
		Silmaril.Project.Room.Thms \
		Silmaril.Project.Shapes.SysV.Thms \
		Silmaril.Project.Shapes.C.Thms \
		Silmaril.Project.Shapes.SysV.Rtl.Defs \
		Silmaril.Project.Shapes.CompilesTo.Thms \
		Silmaril.LogicGraph.Consequence.Containers.Defs \
		Silmaril.LogicGraph.Audit.Defs \
		Silmaril.LogicGraph.Catalogue.Defs \
		ProjectSelfTest \
		SysVTvExample \
		CompilesToExamples

project-tool:
	$(CARGO) build --release --locked --manifest-path tools/silmaril-project/Cargo.toml
	@mkdir -p build/bin
	cp "$(PROJECT_TARGET)/release/silmaril-project" build/bin/silmaril-project
	cp scripts/sil build/bin/sil
	chmod +x build/bin/sil

# The explorer page and its database in _site (.github/workflows/pages.yml), from the built
# libraries of the project's modules (silmaril.toml). With PAGES_SOURCE_REV, a commit of
# PAGES_SOURCE_URL that holds these sources (the Pages workflow passes the pushed commit), the page
# links problems and answers to their Lean sources there. It is not guessed from the checkout: a
# local or build-service HEAD may be a commit GitHub does not have, and its links would be broken.
PAGES_SOURCE_URL ?= https://github.com/hiloopai/silmaril-lean
PAGES_SOURCE_REV ?=
# Compress only the worker-to-runner transport; Pages still serves the original
# SQLite bytes after extraction. This keeps large public catalogs below the
# prove service's per-output-file transfer limit without changing that limit.
.PHONY: pages-archive
pages-archive: pages
	tar -czf pages-site.tar.gz _site

pages: project-tool
	build/bin/silmaril-project dump --lake lake
	build/bin/silmaril-project check
	build/bin/silmaril-project sqlite --httpvfs > /dev/null
	mkdir -p _site
	# Add the public corpus to the same DB the published Corpus tab opens.
	rm -f _site/project.sqlite
	PYTHONPATH="$(CURDIR)/scripts/corpus" $(PYTHON) scripts/corpus/database.py --base .lake/silmaril/project.sqlite --output _site/project.sqlite \
	  $(if $(PAGES_SOURCE_REV),--source-rev $(PAGES_SOURCE_REV))
	build/bin/silmaril-project explore --db _site/project.sqlite --out _site/index.html \
	  $(if $(PAGES_SOURCE_REV),--source-url $(PAGES_SOURCE_URL) --source-rev $(PAGES_SOURCE_REV))
	$(PYTHON) tools/compiler-explorer/pages.py --project _site/project.sqlite --out _site/compiler
	# The Wasm component, module and function pages read static files next to the page.
	lake build wasm-pages
	.lake/build/bin/wasm-pages silmaril/artifacts.toml _site
	# The acceptor section reads the committed Wasmtime harness report (make acceptor-report).
	cp tools/wasm-acceptor-harness/report.json _site/acceptor-runs.json
	# The ELF pages read the checked theorem modules of the pinned files (tools/elf-pages).
	lake build --wfail elf-pages $(ELF_PINNED) Silmaril.Elf.Staged.Pinned.ZlibChecksums.Contracts
	lake env .lake/build/bin/elf-pages _site

# The committed runtime report of the acceptor components (tools/wasm-acceptor-harness/report.json):
# every suite under Wasmtime, by this fixed command (the report records it and has no timestamps,
# so a rerun on the same files writes the same bytes). CI reruns it and fails on any difference.
acceptor-report:
	cd tools/wasm-acceptor-harness && CARGO_TARGET_DIR=target $(CARGO) build --release --locked
	cd tools/wasm-acceptor-harness && LC_ALL=C target/release/wasm-acceptor-harness suites/*.json --out report.json

# The registry and records checks, without Lean (what CI runs when their inputs change).
project-registry: project-tool
	SIL=build/bin/silmaril-project examples/project/registry-check.sh

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
	@echo 'make project-registry  Run the sil project checks that need no Lean: init, lock, lint'
	@echo 'make project-check  Run the sil project self-test: init, lock, lint, dump, check, explore'
	@echo 'make acceptor-report  Run the Wasm acceptor suites under Wasmtime and write tools/wasm-acceptor-harness/report.json'
	@echo 'make pages    Write the explorer page and its database to _site (needs the project libraries built)'
	@echo 'make demo     Build tools; run the assemble/optimize/link/execute example'
	@echo 'make demo-process  Build the public process headers and theorem slice'
	@echo 'make demo-sha256   Build the sha256-cli and GNU sha256sum-min end-to-end proofs'
	@echo 'make process-check Run process facts, layout, catalogue and probe gates'
	@echo 'make stage    Stage already-built tools without compiling'

# The Cerberus oracle replays over benchmarks/cerberus-elaboration/oracle (docs/projects/cerberus.md).
CERBERUS_ORACLE := benchmarks/cerberus-elaboration/oracle
.PHONY: cerberus-oracle
cerberus-oracle:
	.lake/build/bin/ci_cerberus_genuine_oracle $(CERBERUS_ORACLE)
	.lake/build/bin/ci_cerberus_elaboration_oracle $(CERBERUS_ORACLE)
	.lake/build/bin/ci_cerberus_integer_cast $(CERBERUS_ORACLE)
	.lake/build/bin/ci_cerberus_parameter_call $(CERBERUS_ORACLE)/call-id/core.sexp.gz
