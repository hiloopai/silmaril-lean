module

public import Silmaril.Proofs.Wasm.FX.Logic.Typed.Basic

/-!
# The every-run WasmFX logic for typed `resume` (`StepFXR`): statements

`SafeR`/`TSafeR` (`Silmaril.Wasm.FX.Logic.Typed.Defs`) are the every-run predicates over `StepFXR`
(typed `cont.bind` and `resume`), without host calls, at every profile; proofs in
`Silmaril.Proofs.Wasm.FX.Logic.Typed.Basic`.

* **`TSafe.toR`**, `Safe.toR`: every `StepFXR` step is a `StepFX'` step, so a proof in the
  untyped logic is a proof in the typed one (every rule of `Silmaril.Wasm.FX.Logic.EveryRun`
  transfers);
* **`TSafeR.resume`**: the typed `resume` rule asks only for the split whose arguments have the
  continuation type's arity (`ResumeArity`), where `TSafe.resume` asks for every split;
* adequacy: `TSafeR.behaviours_eq`, and `TSafe.behavioursR_sub` (every typed behaviour of code
  proved in the untyped logic satisfies the postcondition).

Open: the context rules (sequence, label, frame, handler) for `TSafeR` directly; with them the
typed rules could be used inside blocks and handlers.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Logic.Typed

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXResumeT (behavioursFXR)
open Silmaril.Wasm.Models.FXResume (ResumeArity)
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts)
open Silmaril.Wasm.FX.Logic.EveryRun (TSafe)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX} {Q : PostFX H}

/-- **The untyped logic proves typed safety.** -/
theorem TSafe.toR {c : ConfigFX H} (h : TSafe P fx Q c) : TSafeR P fx Q c :=
  Silmaril.Proofs.Wasm.FX.Logic.Typed.tsafe_toR h

/-- **Typed `resume`** (total correctness): only the typed split. -/
theorem TSafeR.resume {s : Store H} {K : Conts} {f : Frame} {V : List FVal} {k : Nat}
    {C : ContFX} {ct : TypeIdx} {hos : List OnClause} {hs' : List HClause}
    (hk : K[k]? = some (some C)) (hr : hos.mapM (resolve s f) = some hs')
    (h : ∀ V₁ vs, V = V₁ ++ vs → ResumeArity f.module ct vs.length →
      TSafeR P fx Q ⟨s, K.set k none, f, fvals V₁ ++ [.handler hs' (C.plug (fvals vs))]⟩) :
    TSafeR P fx Q ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.fx (.resume ct hos)]⟩ :=
  Silmaril.Proofs.Wasm.FX.Logic.Typed.tsafeR_resume hk hr h

/-- **Exact typed behaviours** from typed total safety and one typed run. -/
theorem TSafeR.behaviours_eq {c : ConfigFX H} {r₀ : Result} (h : TSafeR P fx Q c)
    (hQ : ∀ s K f o, Q s K f o → o = OutcomeFX.ofResult r₀)
    (hm : r₀.toBehaviour ∈ behavioursFXR P noHost fx c) :
    behavioursFXR P noHost fx c = {r₀.toBehaviour} :=
  Silmaril.Proofs.Wasm.FX.Logic.Typed.tsafeR_behaviours_eq h hQ hm

/-- **Every typed behaviour is the intended one**, from a proof in the untyped logic. -/
theorem TSafe.behavioursR_sub {c : ConfigFX H} {r₀ : Result} (h : TSafe P fx Q c)
    (hQ : ∀ s K f o, Q s K f o → o = OutcomeFX.ofResult r₀) :
    behavioursFXR P noHost fx c ⊆ {r₀.toBehaviour} :=
  Silmaril.Proofs.Wasm.FX.Logic.Typed.tsafe_behavioursR_sub h hQ

/-- info: 'Silmaril.Wasm.FX.Logic.Typed.TSafeR.resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TSafeR.resume

end Silmaril.Wasm.FX.Logic.Typed
