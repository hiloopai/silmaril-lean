module

@[expose] public section

/-! # Binaryen pass coverage of silmaril-lean and the verified stages

Status against Binaryen version_133's default `-O2`/`-Os` function and module
passes (plus a few commonly requested ones), as of the pinned silmaril-lean
revision. "silmaril" means a verified, *restricted* implementation exists in
silmaril-lean (`Silmaril/Wasm/Binaryen/Pass/*`, `Exe.FunctionStageId`), which is
not upstream algorithm parity; "verified stages" means a verified restricted subrule added
here; "none" means no verified implementation in either. Every verified stage listed
here is certified (exact export equivalence) at every numerical profile.

| Binaryen pass | status | implementation and restriction |
|---|---|---|
| dce | silmaril | `dce`: checked dead-suffix cut |
| remove-unused-names | silmaril | `remove-unused-names` |
| remove-unused-brs | silmaril | `remove-unused-brs`: guard inversion only |
| optimize-instructions | silmaril + verified stages | silmaril `optimize-instructions`: `if (eqz c)` arm swap; local subrules `const-branch`, `const-select`, `add-chain`; verified stage `neutral-ops` (`x op k` with a neutral constant, consumed by an integer op) and `eqz-pair` (`eqz (eqz c)` before `br_if`/`select`/`eqz`) |
| precompute / precompute-propagate | silmaril | `precompute`: anchored integer-addition folding; no propagation |
| simplify-locals(-nostructure, -notee) | silmaril + verified stages | silmaril `simplify-locals`: `local.tee x; drop` ⟶ `local.set x`; verified stage `tee-form`: `local.set x; local.get x` ⟶ `local.tee x` |
| vacuum | silmaril + verified stages | silmaril `vacuum`: anchored `nop`/dropped-constant removal; verified stage `drop-get`: `local.get x; drop` ⟶ `nop` |
| coalesce-locals | silmaril | `coalesce-locals`: adjacent dead overwrite only, no coalescing |
| code-folding | silmaril | `code-folding` |
| merge-blocks | silmaril | `merge-blocks` |
| simplify-globals(-optimizing) | silmaril | `simplify-globals` |
| directize | silmaril | `directize` |
| inlining(-optimizing) | silmaril | small/leaf-callee inlining, guarded |
| remove-unused-module-elements | silmaril | `rume` |
| rse (redundant-set-elimination) | silmaril + verified stages | silmaril's `rse-line` run function (`local.get x; local.set x` ⟶ `local.get x; drop`, self-tee ⟶ get), unwired in silmaril; proved here (every profile) and wires it as `rse-line` |
| untee | none | the inverse of `tee-form`; not useful for size, not added |
| local-cse, merge-locals, reorder-locals | none | |
| pick-load-signs | none | |
| optimize-added-constants | none | folding `i32.add x k` into a load/store offset changes behaviour when `x + k` wraps (Binaryen requires `--low-memory-unused`); not exact |
| code-pushing, constraint-analysis, dae-optimizing | none | |
| ssa-nomerge, flatten | (verified stages, opt-in) | not Binaryen's passes; the Wasm lambda-SSA optimiser (`Silmaril/Wasm/SSA`) is available as the opt-in `ssa` stage with **exact export equivalence at every profile** (closed host, `SsaStage.ssaRun_exportEquiv` via the caller-side simulation `SSA.behaviours_srel`; rewrites only modules without imports and strict leaf functions) |
| duplicate-function-elimination, merge-similar-functions | none | needs function-index renaming equivalence |
| duplicate-import-elimination, remove-unused-types, reorder-functions, reorder-globals | none | index renaming |
| memory-packing, once-reduction, const-hoisting | none | |
| strip-debug / strip-producers | (implicit) | silmaril's decoder drops custom sections, so every output (even with no stages) lacks `name`/`producers`; not a pass |
| heap2local | none | GC |

The same information is available at run time as `coverage`
(`wasm-opt --print-coverage`).
-/

namespace Silmaril.Wasm.Binaryen.Coverage

inductive Status where
  | silmaril
  | verified
  | silmarilAndVerified
  | none
  deriving DecidableEq, Repr

def Status.name : Status → String
  | .silmaril => "silmaril"
  | .verified => "verified stages"
  | .silmarilAndVerified => "silmaril + verified stages"
  | .none => "none"

structure Row where
  pass : String
  status : Status
  note : String

def coverage : List Row := [
  ⟨"dce", .silmaril, "checked dead-suffix cut"⟩,
  ⟨"remove-unused-names", .silmaril, ""⟩,
  ⟨"remove-unused-brs", .silmaril, "guard inversion only"⟩,
  ⟨"optimize-instructions", .silmarilAndVerified,
    "silmaril: if-eqz arm swap, const-branch, const-select, add-chain; verified stages: neutral-ops, eqz-pair"⟩,
  ⟨"precompute(-propagate)", .silmaril, "anchored integer addition; no propagation"⟩,
  ⟨"simplify-locals(-nostructure/-notee)", .silmarilAndVerified,
    "silmaril: tee/drop; verified stages: tee-form"⟩,
  ⟨"vacuum", .silmarilAndVerified,
    "silmaril: anchored nop/dropped-constant removal; verified stages: drop-get"⟩,
  ⟨"coalesce-locals", .silmaril, "adjacent dead overwrite only"⟩,
  ⟨"code-folding", .silmaril, ""⟩,
  ⟨"merge-blocks", .silmaril, ""⟩,
  ⟨"simplify-globals(-optimizing)", .silmaril, ""⟩,
  ⟨"directize", .silmaril, ""⟩,
  ⟨"inlining(-optimizing)", .silmaril, "small/leaf callees"⟩,
  ⟨"remove-unused-module-elements", .silmaril, ""⟩,
  ⟨"rse", .silmarilAndVerified, "silmaril's rse-line, proved and wired as a verified stage"⟩,
  ⟨"untee", .none, "inverse of tee-form; not useful for size"⟩,
  ⟨"local-cse, merge-locals, reorder-locals", .none, ""⟩,
  ⟨"pick-load-signs", .none, ""⟩,
  ⟨"optimize-added-constants", .none, "not exact without a low-memory assumption"⟩,
  ⟨"code-pushing, constraint-analysis, dae-optimizing", .none, ""⟩,
  ⟨"ssa-nomerge, flatten", .none,
    "the Wasm SSA optimiser is the opt-in `ssa` stage, exact export equivalence at every profile (rewrites closed modules, strict leaf functions)"⟩,
  ⟨"duplicate-function-elimination, merge-similar-functions", .none, "index renaming"⟩,
  ⟨"duplicate-import-elimination, remove-unused-types, reorder-functions, reorder-globals",
    .none, "index renaming"⟩,
  ⟨"memory-packing, once-reduction, const-hoisting", .none, ""⟩,
  ⟨"strip-debug, strip-producers", .none, "implicit: the decoder drops custom sections"⟩,
  ⟨"heap2local", .none, "GC"⟩]

def report : String :=
  String.intercalate "\n" (coverage.map fun r =>
    r.pass ++ ": " ++ r.status.name ++ (if r.note.isEmpty then "" else " (" ++ r.note ++ ")"))

end Silmaril.Wasm.Binaryen.Coverage
