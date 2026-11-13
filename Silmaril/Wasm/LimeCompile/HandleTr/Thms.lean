module

public import Silmaril.Wasm.LimeCompile.HandleTr.Defs
public import Silmaril.Proofs.Wasm.LimeCompile.HandleTr.Example

/-!
# The 3.0 → Lime compiler with `i32` handles: results

Proofs in `Silmaril.Proofs.Wasm.LimeCompile.HandleTr.{Api,NoHost,Run,Invoke,Inst,Pair,Lists,Sess,
Equiv,Fwd,Example}`.

**API.** `compile_api`: every output of the handle compiler has the `Handle.handleApi`
translation of its input's export API (`funcref`/`externref` parameters, results and globals
become `i32`). `compile_limePreserving`: Lime-only input is returned unchanged.

**The untyped statement is false.** `not_handleCorrectOn`: an earlier `Handle.HandleCorrectOn`
(every handle table, a handle may denote any reference) fails for this compiler already on the
`externref` identity `idExtern`: with the table `[ref.func 1]` the target accepts handle `0` and
returns, while the source rejects the dangling function reference, so its session stops.

**Restated and proved on a fragment.** `HandleCorrectOnT` asks for a handle table
(`HandleTable`: handle `0` is null, no other handle is) and store-independent typed handles
(`HandleOk`: null, or an external host reference at `externref`). **`fwd_handleCorrect`**:
`HandleCorrectOnT FwdFrag compile`, for every handle table, profile and code-parametric host.
`FwdFrag` (forwarders): valid modules with only types (2.0 function types), functions and exports,
every function without locals and with a body of `local.get`s, whose compiled image validates.
The proof computes every run of a forwarding invocation in both modules (`Sh.step`: every step,
for every profile and host, goes to the next of four shapes), so the two sessions match call by
call with results related by `ResRel σ`. `fwdFrag_idExtern`: the fragment is not empty, and on
`idExtern` the output is `(func (param i32) (result i32) local.get 0)` (`compile_idExtern`), not
the input.

**Open.** `Task.handleCorrect` (frozen): `HandleCorrectOnT` on every valid import-free input;
the validity of the compiled image is a hypothesis of `FwdFrag`, not derived; non-null function
references as handles (store-dependent) are not covered by `HandleOk`; handles allocated during
a session (sources that create references) are not modelled (`compile` rejects such sources).

New statements over `Silmaril.Proofs.Wasm.LimeCompile.HandleTr`.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.HandleTr

open Silmaril.Wasm
open Silmaril.Proofs.Wasm.LimeCompile.HandleTr

/-- **The export API is translated by `handleApi`.** -/
theorem compile_api' {M : Module} {l : Lime1.Module} (h : compile M = some l) :
    Handle.handleApi (Preserve.Module.exportApi M) = some (Preserve.Module.exportApi l.toCore) :=
  compile_api h

/-- **The handle compiler is Lime-preserving.** -/
theorem compile_limePreserving : Preserve.LimePreserving compile :=
  Preserve.limePres_preserving compile0

/-- **Correctness up to typed handles on the forwarder fragment.** -/
theorem fwd_handleCorrect' : HandleCorrectOnT FwdFrag compile :=
  fwd_handleCorrect

/-- The forwarder fragment is not empty: the `externref` identity. -/
theorem fwdFrag_idExtern' : FwdFrag idExtern := fwdFrag_idExtern

/-- On `idExtern` the compiler rewrites the types: the output is the Lime1 reading of
`tgtM idExtern`, `(func (param i32) (result i32) local.get 0)`. -/
theorem compile_idExtern' :
    ∃ l, compile idExtern = some l ∧ l.toCore = tgtM idExtern ∧ tgtM idExtern ≠ idExtern := by
  obtain ⟨l, hl, ht⟩ := compile_idExtern_some
  refine ⟨l, hl, ht, fun h => ?_⟩
  have := congrArg Module.types h
  simp [tgtM, idExtern, hRec, hSub, hComp, hFT, hv, Handle.handleRef] at this
  cases this

/-- **Refutation**: an earlier untyped `Handle.HandleCorrectOn` fails for the compiler. -/
theorem not_handleCorrectOn' : ¬ Handle.HandleCorrectOn (· = idExtern) compile :=
  not_handleCorrectOn

/-- info: 'Silmaril.Wasm.LimeCompile.HandleTr.fwd_handleCorrect'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwd_handleCorrect'

/-- info: 'Silmaril.Wasm.LimeCompile.HandleTr.not_handleCorrectOn'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_handleCorrectOn'

/-- info: 'Silmaril.Wasm.LimeCompile.HandleTr.compile_idExtern'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compile_idExtern'

end Silmaril.Wasm.LimeCompile.HandleTr
