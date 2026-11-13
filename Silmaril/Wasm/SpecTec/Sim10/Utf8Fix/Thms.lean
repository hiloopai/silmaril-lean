module

public import Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Fix10Env
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Fix10Name
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Fix10Wit
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Fix10Ext
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Fix10Clean
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Fix10Typ
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Fix10Pairs
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Fix10Task

/-!
# The `$utf8` erratum for wasm-1.0: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim10.Utf8Fix`; see `docs/projects/spectec/README.md`, "utf8
".

* `Utf8Fix10Env`: the fixed script `fixedU10` has the lookups of the environment-level erratum:
  `$utf8` with no clauses (`findDef?_utf8Env10T`), and otherwise the definitions, types,
  relations and grammars of `simEnv10T B` (`findDef?_utf8Env10T_of_ne`, `findTyp?_utf8Env10T`,
  `findRel?_utf8Env10T`, `findGram?_utf8Env10T`); primitives `withUtf8 B`.
* `Utf8Fix10Name`: **`hasTyp_name10U`**: every string with fewer than `2 ^ 32` UTF-8 bytes is a
  `name`; `typedV_name10U_not_10T`: a non-empty one is a `name` here and not in `simEnv10T B`.
* `Utf8Fix10Wit`: **`typed10U_add`**: the invocation of `addModule`'s export `"add"` is
  `Typed10` in `utf8Env10T B` (`add_typed_iff_erratum`: and not in `simEnv10T B`).

* `Utf8Fix10Ext`: **`envExt10T`**: the pair `simEnv10T B`/`utf8Env10T B` is a
  `Sim20.Utf8Mono.EnvExt` at `$utf8` (`utf8_le10`: the 1.0 `$utf8` answers at most what the
  primitive answers).
* `Utf8Fix10Clean`, `Utf8Fix10Typ`: `clean10T` and `hasTyp_u10T_iff` (kernel checks
  `refFree10T`, `typsOffB_badU10`).
* `Utf8Fix10Pairs`, `Utf8Fix10Task`: the `otherwise` pairs of 1.0's `Step_read` and `Step_pure`
  pass `pairOkN` (kernel), so **`elseMonoR10T`** and **`sstepB_utf8_10T`**: every step of
  `simEnv10T B` is a step of `utf8Env10T B`; **`wholeRunFwd10T_utf8`**: round 4's 1.0 forward
  run theorem holds in the fixed script.

Not proved here: the 1.0 forward theorem at configurations with non-empty export names (the 1.0
form of `Sim20.Utf8Strip.Task.unstripStep20`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.findDef?_utf8Env10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.findDef?_utf8Env10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.hasTyp_name10U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.hasTyp_name10U

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.add_typed_iff_erratum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.add_typed_iff_erratum

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.sstepB_utf8_10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.sstepB_utf8_10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.wholeRunFwd10T_utf8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.wholeRunFwd10T_utf8
