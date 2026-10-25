# Lake owns Lean dependencies and incremental compilation. This file stages tools
# and provides short commands for the release checks.
.DEFAULT_GOAL := tools
LAKE ?= lake
PYTHON ?= python3
WASM_TOOLS := wasm-as wasm-dis wasm-opt wasm-merge wasm-shell wasm-ctor-eval wasm-metadce

.PHONY: tools stage library cache check demo help

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
	$(LAKE) build --wfail Silmaril

cache:
	$(LAKE) exe cache get

check:
	$(PYTHON) scripts/source-manifest.py
	scripts/check-layout.sh
	$(PYTHON) tools/binaryen-lean/check-release.py --build --report build/wasm-checks.json
	$(MAKE) stage

demo: tools
	$(PYTHON) tools/binaryen-lean/test-release-demo.py --bin-dir build/bin

help:
	@echo 'make tools    Build seven native Wasm tools and stage build/bin/sil'
	@echo 'make library  Check every included Lean library module'
	@echo 'make cache    Fetch pinned public dependency artifacts'
	@echo 'make check    Build library, tools and proof roots; run native regressions'
	@echo 'make demo     Build tools; run the assemble/optimize/link/execute example'
	@echo 'make stage    Stage already-built tools without compiling'
