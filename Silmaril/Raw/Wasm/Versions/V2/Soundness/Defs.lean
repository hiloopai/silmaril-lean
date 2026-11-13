module

public import Silmaril.Raw.Wasm.Versions.V2.Soundness.Store

/-!
# WebAssembly 2.0 soundness: shared definitions

`ResultTyped` and the host contract `HostOk`, the 2.0 analogues of
`Silmaril/Wasm/Execution/Core/Soundness/Defs.lean`. The runtime typing they
build on — `RefOk`, `ValOk`, `StoreOk`, `Extend` and friends — is in
`Silmaril/Wasm/V2/Soundness/Store.lean`, which this module re-exports: importing
`Silmaril.Wasm.V2.Soundness.Defs` gives the whole store-typing layer.

**Deviation (no SpecTec source).** As explained at length in
`Soundness/Store.lean`, the pinned SpecTec wasm-2.0 sources contain no
`7-soundness` file, so neither judgment here has a 2.0 SpecTec rule. Both are
transcribed from Core 3.0 (`Silmaril/Wasm/Execution/Core/Soundness/Defs.lean`),
adapted down: a 2.0 `result` is `_VALS val*` or `TRAP` (`4-runtime:46`) — there
is no `THROW_REF` case — and a 2.0 `functype` is a plain
`resulttype -> resulttype`, so `HostOk` reads the host function's parameter and
result types off `fi.type` with no `Expand` step.

**Deviation (host functions).** SpecTec 2.0 has no host functions at all
(`4-runtime:60`); `HostSemantics` and the two `Step` rules `callAddrHost` /
`callAddrHostDiv` are deviation 3 of `Execution/Step.lean`. `HostOk` is the
contract those rules need in order to preserve `StoreOk`, and it is stated
exactly as Core 3.0 states it: on a well-typed store with well-typed arguments
the host *admits* an outcome (this is what progress needs), and *every*
admitted outcome is either divergence or a well-typed, store-extending result
(this is what preservation needs). With `H = Empty` the whole contract is
vacuously satisfiable.
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Execution

open Silmaril.Wasm.V2.Validation

variable {H : Type}

/-- A `result` (`4-runtime:46`) typed by a result type. `TRAP` is typed by
every result type: a trapping configuration is sound whatever was expected. -/
def ResultTyped (s : Store H) : Result → CResultType → Prop
  | .values vs, ts => ValsOk s vs ts
  | .trap, _ => True

@[simp] theorem resultTyped_trap {s : Store H} {ts : CResultType} :
    ResultTyped s .trap ts := trivial

@[simp] theorem resultTyped_values {s : Store H} {vs : List Val} {ts : CResultType} :
    ResultTyped s (.values vs) ts ↔ ValsOk s vs ts := Iff.rfl

/-- Results stay typed under store extension. -/
theorem ResultTyped.extend {s s' : Store H} {r : Result} {ts : CResultType} (he : Extend s s')
    (h : ResultTyped s r ts) : ResultTyped s' r ts := by
  cases r with
  | values vs => exact ValsOk.extend he h
  | trap => trivial

/-- The host contract (see the module docstring).

The hypotheses are exactly the side conditions of `Step.callAddrHost` and
`Step.callAddrHostDiv`: `fi` is an instance of the store, its code is the host
function `h`, and the arguments are typed by `fi.type.params`. -/
def HostOk (host : HostSemantics H) : Prop :=
  ∀ (s : Store H) (fi : FuncInst H) (h : H) (vs : List Val),
    StoreOk s → fi ∈ s.funcs → fi.code = .host h →
    List.Forall₂ (ValOk s) vs fi.type.params →
      (∃ out, host h s vs out) ∧
      ∀ out, host h s vs out → match out with
        | .diverged => True
        | .returned s' r =>
          StoreOk s' ∧ Extend s s' ∧ ResultTyped s' r (liftResult fi.type.results)

/-- The progress half of `HostOk`: a host call that the machine may perform has
at least one outcome. -/
theorem HostOk.exists_outcome {host : HostSemantics H} (hh : HostOk host) {s : Store H}
    {fi : FuncInst H} {h : H} {vs : List Val} (hs : StoreOk s) (hfi : fi ∈ s.funcs)
    (hcode : fi.code = .host h) (hvs : List.Forall₂ (ValOk s) vs fi.type.params) :
    ∃ out, host h s vs out := (hh s fi h vs hs hfi hcode hvs).1

/-- The preservation half of `HostOk`, specialised to a returning call. -/
theorem HostOk.returned {host : HostSemantics H} (hh : HostOk host) {s s' : Store H}
    {fi : FuncInst H} {h : H} {vs : List Val} {r : Result} (hs : StoreOk s) (hfi : fi ∈ s.funcs)
    (hcode : fi.code = .host h) (hvs : List.Forall₂ (ValOk s) vs fi.type.params)
    (hout : host h s vs (.returned s' r)) :
    StoreOk s' ∧ Extend s s' ∧ ResultTyped s' r (liftResult fi.type.results) :=
  (hh s fi h vs hs hfi hcode hvs).2 _ hout

end Silmaril.Wasm.V2.Execution
