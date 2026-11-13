module

public import Silmaril.Proofs.Wasm.Component.Reference.InstImpPhase
public import Silmaril.Proofs.Wasm.Component.Reference.CallPhaseI

/-!
# Soundness with imports, assembled

`simpleI_sound`: the instantiation phase (`instPhaseI`: instantiating `c.toRef` from the store
of host functions of its imports only reaches `afterInst P cs (c.afterFuncs P addr)` with
export `i` at function `n + i`, the core store renaming to the instance's store under `trampIdx`
and holding only trampolines) and the call phase (`callPhaseI`, from exactly that configuration)
give, for every behaviour of `exportBehavioursI` over `core3P P` with the host `answerHost P g`,
what the IR denotation over `impSem P` must exhibit (`IRObsI`). The export map finds export `j`
at function `n + j` because export names are distinct (`SimpleI.Good`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Numerics (Profile)

/-- The export map of `c.toRef` finds export `j` at function `n + j`. -/
theorem exportMapI_lookup {c : SimpleI} (hc : c.Good) (j : Nat) (hj : j < c.exports.length) :
    (exportMapI c).lookup c.exports[j].name = some ⟨c.imports.length + j⟩ :=
  lookup_mapIdx_val (·.name) (fun i => (⟨i⟩ : FuncId)) c.imports.length c.exports j hj hc.names

/-- **Soundness of the component IR with imports answered by a stateful host** (every profile
and component choice profile): for a float-free component with imports within the flat
arities, wired as `SimpleI.toRef` assumes (`SimpleI.Inst`), and a stateful host `g` answering in
the IR's types in every state, every behaviour of instantiating `c.toRef` with its imports bound
to the host functions of `g`, from host state `s₀`, and calling export `j` on the reference
images of well-typed IR values, over `core3P P` with `answerHostS P g`, is matched by the IR
denotation over `impSem P` (`IRObsIS`): a returned call is a play asking export `j`, making
component import calls answered by `g` with the host state threaded from `s₀`, and answering
the results; a trap is such a play answering `none`. -/
theorem simpleI_soundS (P : Profile) (prof : ProfileKind) (c : SimpleI) (hc : c.Good)
    (hi : c.Inst) (hff : c.FloatFree) (har : c.Arity) {σ : Type}
    (g : σ → HostFuncId → List Silmaril.Wasm.Component.Value.Val →
      Option (List Silmaril.Wasm.Component.Value.Val × σ)) (hg : c.HostOkS g) (s₀ : σ)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) :
    ∀ b ∈ exportBehavioursI prof (answerHostS P g) s₀ c.toRef c.imports c.exports[j].name
        (vs.map toRefVal),
      IRObsIS (c.toComp.den (impSem P)) ⟨j, by simp [SimpleI.toComp]⟩ vs g s₀ b := by
  obtain ⟨I, cs, hI, hcs, htr, hinst⟩ := instPhaseIS P prof c hc hi har
  have hcall := callPhaseIS P prof c hc hff har I hI cs hcs htr σ g hg s₀ j vs hvs
  intro b hb
  rcases hb with ⟨m₁, inst, es, f, hr, hl, hb⟩ | ⟨-, hr⟩ | ⟨-, hr⟩
  · have he : InstResult.instance m₁ inst es = .instance (afterInstH P cs
        (c.afterFuncs P fun k => I.addrs.getD k 0) s₀) ⟨0⟩ (exportMapI c) := hinst σ _ s₀ _ hr
    obtain ⟨rfl, rfl, rfl⟩ : m₁ = afterInstH P cs (c.afterFuncs P fun k => I.addrs.getD k 0) s₀ ∧
        inst = ⟨0⟩ ∧ es = exportMapI c := by
      simpa only [InstResult.instance.injEq] using he
    have hf : f = ⟨c.imports.length + j⟩ :=
      Option.some.inj (hl.symm.trans (exportMapI_lookup hc j j.isLt))
    exact hcall b (hf ▸ hb)
  · exact absurd (hinst σ _ s₀ _ hr) (by simp)
  · exact absurd (hinst σ _ s₀ _ hr) (by simp)

/-- **Soundness of the component IR with imports answered by a host** (every profile and
component choice profile): for a float-free component with imports within the flat arities,
wired as `SimpleI.toRef` assumes (`SimpleI.Inst`), and a host `g` answering in the IR's types,
every behaviour of instantiating `c.toRef` with its imports bound to the host functions of `g`
and calling export `j` on the reference images of well-typed IR values, over `core3P P` with
`answerHost P g`, is matched by the IR denotation over `impSem P` (`IRObsI`): a returned call
is a play asking export `j`, making component import calls answered by `g`, and answering the
results; a trap is such a play answering `none`. The stateless instance of `simpleI_soundS`. -/
theorem simpleI_sound (P : Profile) (prof : ProfileKind) (c : SimpleI) (hc : c.Good)
    (hi : c.Inst) (hff : c.FloatFree) (har : c.Arity)
    (g : HostFuncId → List Silmaril.Wasm.Component.Value.Val →
      Option (List Silmaril.Wasm.Component.Value.Val)) (hg : c.HostOk g)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) :
    ∀ b ∈ exportBehavioursI prof (answerHost P g) () c.toRef c.imports c.exports[j].name
        (vs.map toRefVal),
      IRObsI (c.toComp.den (impSem P)) ⟨j, by simp [SimpleI.toComp]⟩ vs g b :=
  fun b hb => irObsI_of_S (simpleI_soundS P prof c hc hi hff har (statelessG g)
    (hostOkS_stateless hg) () j vs hvs b hb)

end Silmaril.Proofs.Wasm.Component.Reference
