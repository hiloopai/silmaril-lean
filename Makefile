# Lake owns Lean dependencies and incremental compilation. This file stages tools
# and provides short commands for the release checks.
.DEFAULT_GOAL := tools
LAKE ?= lake
PYTHON ?= python3
CARGO ?= cargo
PROJECT_TARGET = $(or $(CARGO_TARGET_DIR),tools/silmaril-project/target)
WASM_TOOLS := wasm-as wasm-dis wasm-opt wasm-merge wasm-shell wasm-ctor-eval wasm-metadce

.PHONY: compiler-explorer-check compiler-explorer-unit-check compiler-explorer-evidence-check compiler-explorer-serve logic-graph-check lean-ndjson-check tools stage library cache scope check release-check process-check process-gates project-lean project-tool project-registry project-check acceptor-report pages elf-check demo demo-process demo-sha256 help

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
	ci_cerberus_parameter_call ci_cjson_array_size_context ci_cjson_array_item_context ci_cjson_array_item_machine
# The C compiler's executables (docs/projects/ccomp.md).
CCOMP_TARGETS := ccomp ccomp-legacy ccomp-verified csem decompile
CHECK_TARGETS ?= sqlite_file_format_compatibility sqlite_lean sqlite_image_lean Silmaril SilmarilSpecTec SilmarilSpecTecMeta SilmarilWasiWit SilmarilWasmProject SilmarilLogicGraphData ProjectSelfTest wasm-pages elf-pages wasm-region-map $(WASM_TOOLS) wasm-shell-lean $(CERBERUS_TARGETS) SysVTvExample CompilesToExamples cexplorer-export $(CCOMP_TARGETS)
CHECK_TARGETS += +Silmaril.Wasm.Execution.Core.MemoryProfile.Thms LetIterPackingImportTests LetIterWeakTreeSoundnessTests PEGCoreTests
CHECK_TARGETS += PEGIRBridgeTests PEGForwardCFGTests
CHECK_TARGETS += PeggyDialectTests
CHECK_TARGETS += PeggyEggTests
CHECK_TARGETS += PeggyInstitutionTests
CHECK_TARGETS += PeggyEquationalTests

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

CHECK_TARGETS += PEGStructuredThetaTests

# The release suites run when CHECK_TARGETS holds the executables. A change scoped to a library
# that wasm-opt imports puts only wasm-opt in scope, so the other release binaries are built first.
RELEASE_BINARIES := wasm-opt wasm-as wasm-dis wasm-merge wasm-shell wasm-ctor-eval wasm-metadce wasm-shell-lean

check:
	scripts/check-layout.sh
	$(PYTHON) -I scripts/check-wasm-spec.py
	$(PYTHON) -I scripts/check-wasm-checkers.py
	node examples/wasm-checkers/test-lrat.mjs
	$(PYTHON) -I scripts/check-wasm-sim.py
	$(if $(filter cexplorer-export CompilesToExamples,$(CHECK_TARGETS)),,$(MAKE) compiler-explorer-unit-check)
	@if [ -n "$(LAKE_CACHE_RECORD)" ]; then \
		cov-lake-cache build --repository hiloopai/silmaril-lean --record "$(LAKE_CACHE_RECORD)" -- $(CHECK_TARGETS); \
	elif [ -n "$(strip $(CHECK_TARGETS))" ]; then \
		$(LAKE) build --wfail $(CHECK_TARGETS); \
	fi
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) build --wfail ci_cjson_array_size_context ci_cjson_array_item_context ci_cjson_array_item_machine)
	$(MAKE) -j2 check-runtime check-integrations

# Runtime observations read the completed build. Integration suites own their separate
# generated outputs; overlap the two bounded groups and propagate either failure.
.PHONY: check-runtime check-integrations tla-import-check
check-runtime:
	$(MAKE) process-gates
	$(if $(filter Silmaril +Silmaril.Logic.Temporal.TLA.Surface.Parser.%,$(CHECK_TARGETS)),LAKE="$(LAKE)" $(PYTHON) -I tests/semantics/tla-parser/check.py)
	$(if $(filter Silmaril +Silmaril.Logic.Temporal.TLA.Import.% +Silmaril.Logic.Temporal.TLA.Surface.Parser.% +Silmaril.Logic.Temporal.TLA.Elaborator.% +Silmaril.Logic.Temporal.TLA.Kernel.%,$(CHECK_TARGETS)),$(MAKE) tla-import-check)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.Institution.% +Silmaril.Proofs.SSA.RVSDG.Institution.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.Institution.Categorical.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGInstitution.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.% +Silmaril.Proofs.SSA.RVSDG.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDG.lean)
	$(if $(filter Silmaril +Silmaril.Project.Registry.IR.Defs +Silmaril.LogicGraph.Nodes.SSA.MLIR.Defs,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.LogicGraph.Nodes.SSA.MLIR.Defs +Silmaril.SSA.MLIR.Institution.Arith.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/IRRegistry.lean)
	$(if $(filter Silmaril +Silmaril.SSA.SeaOfNodes.Pure.% +Silmaril.Proofs.SSA.SeaOfNodes.Pure.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.SeaOfNodes.Pure.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/SeaOfNodesPure.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.NestedTheta.Petri.% +Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGNestedPetri.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.Petri.% +Silmaril.Proofs.SSA.RVSDG.Petri.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.Petri.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGPetri.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.Isomorphism.% +Silmaril.Proofs.SSA.RVSDG.Isomorphism.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.Isomorphism.Petri.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGIsomorphism.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.LambdaSSA.% +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.Gamma.Thms +Mathlib.CategoryTheory.Limits.Types.Coproducts && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGLambdaSSA.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.LambdaSSA.Region.% +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Region.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.Region.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGSingleExit.lean)
	$(if $(filter Silmaril +Silmaril.SSA.Isotope.LambdaSSA.% +Silmaril.Proofs.SSA.Isotope.LambdaSSA.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms +Silmaril.SSA.Isotope.LambdaSSA.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/LambdaSSAEffectfulReplacement.lean)
	$(if $(filter Silmaril +Silmaril.SSA.Isotope.LambdaSSA.% +Silmaril.Proofs.SSA.Isotope.LambdaSSA.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/LambdaSSANeutralPacking.lean)
	$(if $(filter Silmaril +Silmaril.SSA.Isotope.LambdaSSA.% +Silmaril.Proofs.SSA.Isotope.LambdaSSA.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Feedback.Thms +Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/LambdaSSAPaperImports.lean)
	$(if $(filter Silmaril +Silmaril.SSA.Isotope.LambdaSSA.% +Silmaril.Proofs.SSA.Isotope.LambdaSSA.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms +Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.InstructionFree.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/LambdaSSAUnaryReturn.lean)
	$(if $(filter sqlite_file_format_compatibility,$(CHECK_TARGETS)),bash tests/formats/sqlite-tranche/run.sh)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.% +Silmaril.Proofs.SSA.RVSDG.NestedTheta.Isomorphism.% +Silmaril.SSA.RVSDG.NestedTheta.Partial.Isomorphism.% +Silmaril.Proofs.SSA.RVSDG.NestedTheta.Partial.Isomorphism.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.NestedTheta.Partial.Isomorphism.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGNestedThetaIsomorphism.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.% +Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Isomorphism.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGNestedPetriIsomorphism.lean)
	$(if $(filter sqlite_lean,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Cli.Spec.LeanSqliteShell.Thms && $(PYTHON) -I tests/formats/sqlite-shell/check.py)
	$(if $(filter sqlite_image_lean,$(CHECK_TARGETS)),$(LAKE) build --wfail sqlite_lean sqlite_write_profile_tests && $(PYTHON) -I tests/formats/sqlite-shell/check.py --writer)
	$(if $(filter Silmaril +Silmaril.Formats.Sqlite.VirtualTable.% +Silmaril.Proofs.Formats.Sqlite.VirtualTable.%,$(CHECK_TARGETS)),LAKE="$(LAKE)" tests/formats/sqlite-virtual-table/run.sh)
	$(if $(filter Silmaril +Silmaril.Crypto.Blake3.Range.Check.Defs +Silmaril.Containers.Cas.Blake3.Thms,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Crypto.Blake3.Range.Check.Defs +Silmaril.Containers.Cas.Blake3.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/crypto/Blake3Range.lean)
	$(if $(filter Silmaril +Silmaril.Crypto.Blake3.Range.Extension.Thms +Silmaril.Crypto.Blake3.Range.Extension.Counterexample.Thms,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Crypto.Blake3.Range.Extension.Counterexample.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/crypto/Blake3ObservationExtension.lean)
	$(if $(filter Silmaril +Silmaril.Formats.Blake3Cas.Thms +Silmaril.Containers.Cas.Blake3Wire.Thms +Silmaril.Formats.Iroh.Vectors,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Containers.Cas.Blake3Wire.Thms +Silmaril.Formats.Iroh.Vectors && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/formats/Blake3Cas.lean)
	$(if $(filter Silmaril,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/formats/DrislDebug.lean)
	$(if $(filter Silmaril +Silmaril.ProofFormats.DaslSyntax.Database.Examples.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/formats/DaslDatabase.lean)
	$(if $(filter Silmaril +Silmaril.Formats.Dasl.IndexSequence.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/formats/DaslIndexSequence.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.V1.Intrinsic.Scalar.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/wasm/profiles/V1Intrinsic.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Lime1.Execution.Callout +Silmaril.Wasm.Lime1.Execution.Instantiation +Silmaril.Wasm.Lime1.ToCore,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Lime1.Execution.Callout +Silmaril.Wasm.Lime1.Execution.Instantiation +Silmaril.Wasm.Lime1.ToCore && $(LAKE) env lean -DwarningAsError=true tests/wasm/profiles/LimeFloat.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Validation.Generic.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/wasm/inductive-generic/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Validation.Generic.SSA.Thms +Silmaril.Wasm.Validation.Generic.Signature.Lowering,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/wasm/inductive-generic/TypeBoundary.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Profiles.Thms +Silmaril.Wasm.Profiles.Binary,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/wasm/profiles/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Profiles.ISA.Binary +Silmaril.Wasm.Profiles.ISA.Versions,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/wasm/profiles/ISA.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Profiles.Functional.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/wasm/profiles/Functional.lean)
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
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),.lake/build/bin/ci_cjson_array_size_context)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonSuffixContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(PYTHON) -I tools/corpus/check_cjson_suffix_native.py)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonDetachContext.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/cerberus/CjsonDetachMachine.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/cerberus/CjsonArrayItemObservation.lean)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),.lake/build/bin/ci_cjson_array_item_context)
	$(if $(filter CerberusTests,$(CHECK_TARGETS)),.lake/build/bin/ci_cjson_array_item_machine)
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
	$(if $(filter Silmaril +Silmaril.Wasm.Profiles.Injections.Thms,$(CHECK_TARGETS)),$(LAKE) build +Silmaril.Wasm.V1.Validation.Examples --wfail && $(LAKE) env lean -DwarningAsError=true tests/wasm/profiles/Injections.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Profiles.Syntax.Thms +Silmaril.Wasm.Profiles.Syntax.LimeScalar.Thms,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Profiles.Syntax.LimeScalar.Thms +Silmaril.Wasm.Validation.Intrinsic.Reify +Silmaril.Wasm.Verify.Kernel.Defs +Silmaril.Wasm.Lime1.Execution.Callout +Silmaril.Wasm.Lime1.Execution.Instantiation && $(LAKE) env lean -DwarningAsError=true tests/wasm/profiles/IndexedSyntax.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Sublanguages.Link.Thms,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.V1.Validation.Examples +Silmaril.Wasm.Verify.Kernel.Defs && $(LAKE) env lean -DwarningAsError=true tests/wasm/profiles/Sublanguages.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Sublanguages.Strict.Thms +Silmaril.Wasm.Sublanguages.Strict.Link.Thms,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Sublanguages.Strict.Link.Thms +Silmaril.Wasm.Verify.Kernel.Defs && $(LAKE) env lean -DwarningAsError=true tests/wasm/profiles/OpenStrict.lean)
	$(if $(filter Silmaril +Silmaril.Formats.PER.EGraph.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/formats/GuardedEGraph.lean)
	$(if $(filter Silmaril +Silmaril.Formats.Dasl.EGraph.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/formats/DaslEGraphBridge.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.Theta.% +Silmaril.Proofs.SSA.RVSDG.Theta.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.Theta.Thms +Silmaril.SSA.RVSDG.Theta.Petri.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGTheta.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.Theta.Categorical.% +Silmaril.Proofs.SSA.RVSDG.Theta.Categorical.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.Theta.Categorical.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGThetaCategorical.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.NestedTheta.% +Silmaril.Proofs.SSA.RVSDG.NestedTheta.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGNestedTheta.lean && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGNestedThetaOrderedState.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.NestedTheta.Institution.% +Silmaril.Proofs.SSA.RVSDG.NestedTheta.Institution.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.NestedTheta.Institution.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGNestedThetaInstitution.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial.% +Silmaril.Proofs.SSA.RVSDG.NestedTheta.Institution.Partial.% +Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial.% +Silmaril.Proofs.SSA.RVSDG.NestedTheta.OrderedState.Partial.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial.Thms +Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGNestedThetaPartialInstitution.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless.% +Silmaril.Proofs.SSA.RVSDG.NestedTheta.Institution.Stateless.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGNestedThetaStatelessInstitution.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.% +Silmaril.Proofs.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.% +Silmaril.SSA.RVSDG.NestedTheta.Institution.Wires.% +Silmaril.Proofs.SSA.RVSDG.NestedTheta.Institution.Wires.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.NestedTheta.Institution.Wires.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGNestedThetaPartialWires.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.Interprocedural.% +Silmaril.Proofs.SSA.RVSDG.Interprocedural.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGInterprocedural.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.% +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Isomorphism.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGInterproceduralIsomorphism.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.Interprocedural.Terms.% +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Terms,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGInterproceduralTerms.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.% +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGRuntimeIsomorphism.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.% +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.%,$(CHECK_TARGETS)),$(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGRecursiveIsomorphism.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.Interprocedural.Runtime.% +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Linking +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Invocation,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGModuleLinking.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Defs +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.% +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Recursive,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGPhiCalls.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.% +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGRecursiveTail.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Prefix.% +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.% +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Prefix.% +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.% +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.TailCall.% +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.TailCall.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Prefix.Thms +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.TailCall.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGRecursivePrimitivePrefix.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.% +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGRecursiveContinuations.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.% +Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGRecursiveDescent.lean)

tla-import-check:
	$(LAKE) build --wfail +Silmaril.Logic.Temporal.TLA.Import.Defs +Silmaril.Logic.Temporal.TLA.Kernel.Thms +Silmaril.Logic.Temporal.TLA.Elaborator.Thms +Silmaril.ProofFormats.TLA.SurfaceSExp.Defs
	cd tests/semantics/tla-quint && sha256sum -c SHA256SUMS
	$(LAKE) env lean -DautoImplicit=false -DwarningAsError=true --run tests/semantics/tla-quint/Import.lean
	$(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/semantics/tla-quint/Temporal.lean
	$(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/semantics/tla-quint/ServiceCycle.lean

check-integrations:
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.OrderedRuntime.% +Silmaril.Proofs.SSA.RVSDG.OrderedRuntime.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.OrderedRuntime.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGOrderedRuntime.lean)
	$(if $(filter ci_cerberus_genuine_oracle,$(CHECK_TARGETS)),$(MAKE) cerberus-oracle)
	$(if $(filter Silmaril +Silmaril.Wasm.Component.Reference.Validation.FunctionPorts.Thms,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Component.Reference.Validation.FunctionPorts.Thms && $(LAKE) env lean -DwarningAsError=true tests/wasm/profiles/LimeFunctionPorts.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Profiles.Syntax.Components.Thms,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Component.Reference.Litmus.Thms +Silmaril.Wasm.Sublanguages.Thms +Silmaril.Wasm.Validation.Check.ValidateFinal && $(LAKE) env lean -DwarningAsError=true tests/wasm/profiles/ComponentSyntax.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Component.IntrinsicWiring.Thms +Silmaril.Wasm.Component.IntrinsicWiring.Lift.Thms +Silmaril.Wasm.Component.IntrinsicWiring.Lift.Observation.Thms +Silmaril.Wasm.Component.Reference.DirectLift.Init.Thms +Silmaril.Wasm.Institution.DirectLiftTerminal.Thms,$(CHECK_TARGETS)),$(LAKE) build --wfail \
		+Silmaril.Wasm.Component.IntrinsicWiring.Lift.Thms +Silmaril.Wasm.Validation.Intrinsic.ReifyThms +Silmaril.Wasm.ModuleParts.Thms \
		+Silmaril.Wasm.Component.Reference.Thms +Silmaril.Wasm.Component.Reference.Embedding.Thms +Silmaril.Wasm.Component.Reference.Example.Defs +Silmaril.Wasm.Component.Reference.DirectLift.Init.Thms \
		+Silmaril.Wasm.Execution.Core.Entry.Thms +Silmaril.Wasm.Execution.Core.Exec.InstantiateIff +Silmaril.Wasm.Execution.Core.Exec.ValCheck \
		+Silmaril.Wasm.Game.Machine.Thms +Silmaril.Wasm.Game.Strategy.Thms +Silmaril.Wasm.Institution.DirectLiftTerminal.Thms \
		+Silmaril.Wasm.SingleThreaded.Exec.CheckedRun +Silmaril.Wasm.Verify.Kernel.Thms && \
		$(LAKE) env lean -DwarningAsError=true tests/wasm/inductive-component/Regression.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.OrderedRuntime.Structured.% +Silmaril.Proofs.SSA.RVSDG.OrderedRuntime.Structured.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGStructuredRuntime.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.% +Silmaril.Proofs.SSA.RVSDG.OrderedRuntime.Structured.Theta.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGStructuredRuntimeTheta.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Component.IntrinsicWiring.Lift.Observation.Thms,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Component.Reference.Litmus.Thms +Silmaril.Wasm.Validation.Intrinsic.ReifyThms && $(LAKE) env lean -DwarningAsError=true tests/wasm/inductive-component/Exposure.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Component.Reference.DirectLift.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/wasm/inductive-component/DirectLift.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.% +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.TwoBlock.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Thms +Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Partial.Thms +Silmaril.Raw.SSA.Isotope.Semantics.Model && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGLambdaSSATwoExit.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.% +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.ThreeBlock.% +Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.% +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.LinearChain.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Thms +Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.State.Thms +Silmaril.Raw.SSA.Isotope.Semantics.Model && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGLambdaSSAThreeBlock.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.LambdaSSA.Diamond.% +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Diamond.% +Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Dispatcher.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Categorical.Thms +Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime.Thms +Silmaril.SSA.Isotope.LambdaSSA.Kleisli.Thms +Silmaril.Raw.SSA.Isotope.Semantics.Model && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGLambdaSSADiamond.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.% +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Thms +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Thms +Mathlib.Tactic.FinCases && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGLambdaSSAAcyclic.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.% +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Categorical.Thms +Silmaril.Raw.SSA.Isotope.Semantics.Model && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGLambdaSSAAcyclicTheta.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.% +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Renumbered.Thms +Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms +Silmaril.Raw.SSA.Isotope.Semantics.Model && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGLambdaSSAAcyclicToken.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.% +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Wires.Thms +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Atomic.Thms +Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Defs +Silmaril.Raw.SSA.Isotope.Semantics.Model && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGLambdaSSAAcyclicSequentialTheta.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.% +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Thms +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Thms +Silmaril.Raw.SSA.Isotope.Semantics.Model && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGLambdaSSASerialCuts.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.% +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Reverse.Thms +Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Defs +Silmaril.Raw.SSA.Isotope.Semantics.Model && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGLambdaSSAConditionalTheta.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.% +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.% +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Fork.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Reverse.Thms +Silmaril.SSA.RVSDG.Isomorphism.Defs +Silmaril.Raw.SSA.Isotope.Semantics.Model && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGLambdaSSALoopDiamond.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.% +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.OrderedTheta.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms +Silmaril.Raw.SSA.Isotope.Semantics.Model && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGLambdaSSAOrderedTheta.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.% +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.TwoBlock.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Thms +Silmaril.Raw.SSA.Isotope.Semantics.Model && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGLambdaSSATwoBlock.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Execution.Core.Entry.Thms +Silmaril.Wasm.Execution.Core.Entry.Program.Thms,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Execution.Core.Exec.InstantiateIff +Silmaril.Wasm.Validation.Intrinsic.Thms +Silmaril.Wasm.Execution.Core.Entry.Program.Thms && $(LAKE) env lean -DwarningAsError=true tests/wasm/module-entry/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Execution.Core.Entry.Program.Versions.Thms,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Execution.Core.Exec.InstantiateIff && $(LAKE) env lean -DwarningAsError=true tests/wasm/operational-program/Version.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Execution.Core.Intrinsic.Normalize.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/wasm/intrinsic-machine/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Execution.Core.Intrinsic.LiveLift.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/wasm/intrinsic-machine/LiveLift.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Execution.Core.Intrinsic.Observation.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/wasm/intrinsic-machine/Observation.lean)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.Theta.Institution.% +Silmaril.Proofs.SSA.RVSDG.Theta.Institution.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.Theta.Institution.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGThetaInstitution.lean)
	$(if $(filter Silmaril +Silmaril.Semantics.Operational.Policy.Thms +Silmaril.Wasm.Execution.Core.Intrinsic.OpSem.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/semantics/operational-policy/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Semantics.Operational.Program.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/semantics/operational-program/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Core.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Compile.Locals.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/integer-local-compiler/Regression.lean && LAKE="$(LAKE)" $(PYTHON) -I tests/languages/python/integer-local-compiler/check_branches.py)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Core.Rules.Thms,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Logic.Operational.SOS.Marked.Policy.Thms +Silmaril.Logic.Operational.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/sos/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Compile.Closure.Call.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/closure-compiler/Call.lean)
	$(if $(filter Silmaril +Silmaril.Logic.Operational.Machines.Thms +Silmaril.X86.OperationalInstitution.Thms +Silmaril.Wasm.Institution.Operational.Thms,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Logic.Operational.Machines.Thms +Silmaril.X86.OperationalInstitution.Thms +Silmaril.Wasm.Institution.Operational.Thms && $(LAKE) env lean -DwarningAsError=true tests/semantics/operational-institutions/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.CallResolution.% +Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.CallResolution.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/direct-call-sos/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.% +Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/indirect-call-resolution/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.% +Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/indirect-call-context/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.% +Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Source.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.Thms +Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/indirect-call-source/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.% +Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional.Thms +Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control.Thms +Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/indirect-graph-entry/Regression.lean && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/indirect-graph-entry/Nested.lean && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/indirect-graph-entry/Loop.lean && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/indirect-graph-entry/LoopResume.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.MemoryGrow.% +Silmaril.Proofs.Wasm.Institution.Operational.MemoryGrow.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.MemoryGrow.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/memory32-grow-sos/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.CallFrame.% +Silmaril.Proofs.Wasm.Institution.Operational.CallFrame.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/typed-call-frame-sos/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.CallContinuation.% +Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/call-continuation-sos/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.% +Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/straight-line-call-continuation/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Declaration.% +Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.% +Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.% +Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.% +Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.% +Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.% +Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Thms +Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/checked-direct-call-sequence/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.% +Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/rank-recursive-calls/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.% +Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Nested.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/nested-call-sos/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.% +Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/typed-outer-call-sos/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.% +Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/computed-inner-call-sos/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.% +Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.% +Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.% +Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/compositional-call-arguments/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.% +Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/composed-outer-call-continuation/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.Division.% +Silmaril.Proofs.Wasm.Institution.Operational.Division.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.Division.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/guarded-division-sos/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.MemoryQuery.% +Silmaril.Proofs.Wasm.Institution.Operational.MemoryQuery.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/memory32-query-sos/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.MemoryWrite.% +Silmaril.Proofs.Wasm.Institution.Operational.MemoryWrite.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/memory32-write-sos/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.LegacyDivision.% +Silmaril.Proofs.Wasm.Institution.Operational.LegacyDivision.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.LegacyDivision.V1.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/v1-division-sos/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.LegacyDivision.% +Silmaril.Proofs.Wasm.Institution.Operational.LegacyDivision.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.LegacyDivision.Transport.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/lime1-division-sos/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.Locals.% +Silmaril.Proofs.Wasm.Institution.Operational.Locals.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.Locals.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/typed-locals-sos/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.Blocks.% +Silmaril.Proofs.Wasm.Institution.Operational.Blocks.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.Blocks.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/scalar-block-sos/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.Blocks.% +Silmaril.Proofs.Wasm.Institution.Operational.Blocks.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/indexed-block-sos/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.Blocks.% +Silmaril.Proofs.Wasm.Institution.Operational.Blocks.% +Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.% +Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.Blocks.Context.Thms +Silmaril.Wasm.Institution.Operational.Blocks.Native.Thms +Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/structured-label-context/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.BranchExit.% +Silmaril.Proofs.Wasm.Institution.Operational.BranchExit.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.BranchExit.Native.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/nested-branch-sos/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Institution.Operational.Loops.% +Silmaril.Proofs.Wasm.Institution.Operational.Loops.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Institution.Operational.Loops.Native.Thms +Silmaril.Wasm.V1.Validation.Instructions && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/wasm/scalar-loop-native/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Semantics.SOS.% +Silmaril.Proofs.Semantics.SOS.% +Silmaril.Logic.Operational.SOS.% +Silmaril.Proofs.Logic.Operational.SOS.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Logic.Operational.SOS.Thms +Silmaril.Logic.Operational.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/semantics/sos/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Logic.Operational.SOS.Marked.% +Silmaril.Proofs.Logic.Operational.SOS.Marked.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Logic.Operational.SOS.Marked.Policy.Thms +Silmaril.Logic.Operational.Thms && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true --run tests/semantics/sos-marked/Regression.lean)
	$(if $(filter Silmaril +Silmaril.RiscV.OperationalInstitution.LPS.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.RiscV.OperationalInstitution.LPS.Thms +Silmaril.X86.OperationalInstitution.Thms +Silmaril.Wasm.Institution.Operational.Thms && $(LAKE) env lean -DwarningAsError=true tests/semantics/rv64-operational/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Semantics.Operational.Determinism.Fuel.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/semantics/operational-determinism/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Source.Scope.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/source-scope/Regression.lean && LAKE="$(LAKE)" $(PYTHON) -I tests/languages/python/source-scope/check_intake.py)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Source.Closure.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/source-closure/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Source.Closure.Frame.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/source-frame-layout/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Compile.Closure.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/closure-compiler/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Compile.Closure.Body.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/closure-compiler/BodyTheorems.lean && LAKE="$(LAKE)" $(PYTHON) -I tests/languages/python/source-scope/check_intake.py --closure-bodies)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Compile.Closure.Link.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/closure-compiler/Link.lean)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Compile.Closure.CodeNames.Defs +Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Thms,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Languages.Python.Compile.Closure.CodeNames.Defs +Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs && LAKE="$(LAKE)" $(PYTHON) -I tests/languages/python/closure-compiler/check_conames.py)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Compile.Closure.Run.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/closure-compiler/RunnerTheorems.lean && LAKE="$(LAKE)" $(PYTHON) -I tests/languages/python/closure-compiler/check_runs.py && LAKE="$(LAKE)" $(PYTHON) -I tests/languages/python/closure-compiler/check_freevars.py && LAKE="$(LAKE)" $(PYTHON) -I tests/languages/python/closure-compiler/check_cellvars.py)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Compile.Closed.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/closed-source/Regression.lean && LAKE="$(LAKE)" $(PYTHON) -I tests/languages/python/source-scope/check_intake.py --closed-compiler)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Compile.ModuleEntry.Thms,$(CHECK_TARGETS)),LAKE="$(LAKE)" $(PYTHON) -I tests/languages/python/source-module-entry/check_intake.py)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Compile.ModuleEntry.Run.Thms,$(CHECK_TARGETS)),LAKE="$(LAKE)" $(PYTHON) -I tests/languages/python/source-module-entry/check_run.py)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Thms,$(CHECK_TARGETS)),LAKE="$(LAKE)" $(PYTHON) -I tests/languages/python/source-module-entry/check_functions.py)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Thms,$(CHECK_TARGETS)),LAKE="$(LAKE)" $(PYTHON) -I tests/languages/python/source-module-entry/check_function_run.py)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Compile.Closure.VarNames.Defs +Silmaril.Languages.Python.Compile.Closure.VarNames.Thms +Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Thms,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Languages.Python.Compile.Closure.VarNames.Thms +Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Thms +Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms && LAKE="$(LAKE)" $(PYTHON) -I tests/languages/python/source-module-entry/check_varnames.py)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Thms +Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms +Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Thms && LAKE="$(LAKE)" $(PYTHON) -I tests/languages/python/source-module-entry/check_keyword_default.py)
	$(if $(filter Silmaril +Silmaril.Languages.Python.Compile.Closure.Run.Thms +Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Languages.Python.Compile.Closure.Run.Thms +Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Thms +Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms && LAKE="$(LAKE)" $(PYTHON) -I tests/languages/python/source-module-entry/check_return_local_call.py && LAKE="$(LAKE)" $(PYTHON) -I tests/languages/python/source-module-entry/check_factory_results.py && LAKE="$(LAKE)" $(PYTHON) -I tests/languages/python/source-module-entry/check_nested_lambdas.py && LAKE="$(LAKE)" $(PYTHON) -I tests/languages/python/source-module-entry/check_none_factory.py)
	$(if $(filter Silmaril +Silmaril.Wasm.Execution.Core.Entry.Determinism.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/wasm/operational-determinism/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Execution.Core.GlobalProfile.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/wasm/global-profile/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Execution.Core.Entry.ClosedFunctional.Thms,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.Wasm.Det.NaN.Litmus.Thms +Silmaril.Wasm.Execution.Core.Exec.InstantiateIff && $(LAKE) env lean -DwarningAsError=true tests/wasm/closed-functional/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Execution.Core.Intrinsic.OpSem.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true tests/wasm/intrinsic-machine/OpSem.lean && $(LAKE) env lean -DwarningAsError=true tests/wasm/intrinsic-machine/Call.lean)
	$(if $(filter +Silmaril.Wasm.Execution.Core.MemoryProfile.Thms,$(CHECK_TARGETS)),$(LAKE) env lean -DwarningAsError=true --run tests/wasm/memory-profile/Regression.lean)
	$(if $(filter Silmaril +Silmaril.Wasm.Binaryen.Intrinsic.% +Silmaril.Proofs.Wasm.Binaryen.Intrinsic.%,$(CHECK_TARGETS)),LAKE="$(LAKE)" bash tests/wasm/binaryen-intrinsic/check.sh)
	$(if $(filter wasm-opt,$(CHECK_TARGETS)),$(LAKE) build --wfail $(RELEASE_BINARIES) && $(MAKE) release-check)
	$(if $(filter elf-pages,$(CHECK_TARGETS)),$(MAKE) elf-check)
	$(if $(filter SilmarilLogicGraphData,$(CHECK_TARGETS)),$(MAKE) logic-graph-check)
	$(if $(filter cexplorer-export CompilesToExamples,$(CHECK_TARGETS)),$(MAKE) compiler-explorer-check)
	$(if $(filter Silmaril +Silmaril.SSA.RVSDG.LambdaSSA.Theta.% +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Theta.%,$(CHECK_TARGETS)),$(LAKE) build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.Theta.Categorical.Thms +Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Categorical.Kleisli && $(LAKE) env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGLambdaSSATheta.lean)

# The Lean-NDJSON fixture is what lean4export writes now (docs/projects/formal-rows.md).
lean-ndjson-check:
	scripts/lean-ndjson/export-fixtures.sh --check

# The compiler explorer end to end: the exporter on every manifest, the statuses against
# examples/compiler-explorer/expected-status.txt, the database and view tests
# (docs/projects/compiler-explorer.md).
compiler-explorer-check:
	$(MAKE) -j2 compiler-explorer-unit-check compiler-explorer-evidence-check

compiler-explorer-evidence-check:
	LAKE="$(LAKE)" PYTHON="$(PYTHON)" tools/compiler-explorer/check.sh

compiler-explorer-unit-check:
	$(PYTHON) -I tools/compiler-explorer/tests/test_cexplorer.py
	node --test tools/compiler-explorer/tests/view.test.mjs

COMPILER_EXPLORER_DB ?= .lake/compiler-explorer/explorer.sqlite
compiler-explorer-serve:
	@mkdir -p "$(dir $(COMPILER_EXPLORER_DB))"
	$(PYTHON) -I tools/compiler-explorer/cexplorer.py ingest "$(COMPILER_EXPLORER_DB)" examples/compiler-explorer/manifests/*.json
	$(PYTHON) -I tools/compiler-explorer/cexplorer.py serve "$(COMPILER_EXPLORER_DB)"

# The logic graph's records files: editing a records file
# rebuilds its loader incrementally (docs/projects/logic-graph.md).
logic-graph-check:
	LAKE="$(LAKE)" scripts/logic-graph/test-incremental.sh

# The ELF reader's pinned files, generated modules and explorer data (docs/projects/elf-reader.md).
ELF_PINNED := $(foreach n,HelloGcc HelloClang Sha256sum ZlibChecksums ZlibLibz GlibcLibm GlibcLibc,\
	Silmaril.Elf.Staged.Pinned.$(n).Thms Silmaril.Elf.Staged.Pinned.$(n).Functions)
ELF_REGION_PROOFS := Silmaril.Elf.Staged.Pinned.HelloGcc.Regions.Examples.Thms \
	Silmaril.Machine.Region.X86.CFG.Semantic.Thms Silmaril.Machine.Region.X86.CFG.View.Thms
elf-check:
	examples/elf/pin.sh --check
	$(LAKE) build --wfail elf-staged elf-pages Silmaril.Elf.Staged.Reader.Examples \
		$(ELF_PINNED) $(ELF_REGION_PROOFS) Silmaril.Elf.Staged.Pinned.ZlibChecksums.Contracts
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
	# The component-test page reads the binaries, their WAT, the report and the oracle's results.
	mkdir -p _site/component-tests
	cp examples/component-tests/*.wasm examples/component-tests/*.wat examples/component-tests/*.json _site/component-tests/
	$(PYTHON) -I tools/compiler-explorer/fixtures.py viewer --out _site
	$(PYTHON) -I tools/compiler-explorer/pages.py --project _site/project.sqlite --out _site/compiler
	# The Wasm component, module and function pages read static files next to the page.
	lake build wasm-pages
	.lake/build/bin/wasm-pages silmaril/artifacts.toml _site
	# The acceptor section reads the committed Wasmtime harness report (make acceptor-report).
	cp tools/wasm-acceptor-harness/report.json _site/acceptor-runs.json
	# The Containers tab reads the descriptions of the worked examples (docs/projects/containers-examples.md).
	lake build --wfail Silmaril.Containers.Noop.Thms Silmaril.Containers.Fixtures.Thms Silmaril.Containers.Mini.Thms Silmaril.Containers.Http.Thms Silmaril.Containers.HttpServe.Thms
	lake env lean --run examples/containers/Examples.lean --json _site/containers-examples.json
	# The ELF pages read the checked theorem modules of the pinned files (tools/elf-pages).
	lake build --wfail elf-pages $(ELF_PINNED) $(ELF_REGION_PROOFS) Silmaril.Elf.Staged.Pinned.ZlibChecksums.Contracts
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
	@echo 'make compiler-explorer-serve  Browse compiler fixtures locally (127.0.0.1:8765)'
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
