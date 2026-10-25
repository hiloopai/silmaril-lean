module

public import Silmaril.Wasm.Binaryen.InlDeadFuncInst

@[expose] public section

/-! # Appending a dead function

Appending a defined function to a module is an export equivalence
(`exportEquiv_append_unreferenced_func`), under every code-respecting typed host, when the
module's function types take numeric parameters (without that side condition it is false,
`InlDFCex.exportEquiv_append_unreferenced_func_false`). The original module
cannot name the new function (its index is out of range for the original module, which is
valid), so nothing of the extended module names it either: its instance is the original
instance with one more trailing `funcs` entry, and its store has one more function instance
at the end.

The proof is a lockstep simulation relating stores and frames up to that instance extension
(not a renaming; `InlDeadFuncRel.lean`, `InlDeadFuncSim.lean`): existing function addresses
are unchanged, and calls and `ref.func` resolve to the same addresses. Host calls never
return (`InlDF.host_never_returns`), so the host cannot observe the extra function
(`InlDeadFuncHost.lean`, `InlDeadFuncRun.lean`). Sessions and observations correspond (`InlDeadFuncObs.lean`), and so
do instantiations (`InlDeadFuncConst.lean`, `InlDeadFuncInst.lean`).
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics

theorem lower_append_func (m : BModule) (f : BFunc) :
    ({ m with funcs := m.funcs ++ [f] } : BModule).lower =
      InlDF.appendFunc m.lower (Declaration.Func.mapBody BExpr.lowerList f) := by
  simp [BModule.lower, InlDF.appendFunc]

/-- **Appending an unreferenced function is an equivalence.**

`m₁` is `m` with one more defined function `f`. Since `m` is valid, its code, segments,
start function and exports cannot name the new index, so `f` is unreferenced in `m₁`.

The parameters of the module's function types must be numeric (`hparams`). Otherwise a
session may pass a reference to the extra function's address, which is a typed argument in
`m₁`'s store but not in `m`'s: with an exported function taking a `funcref`, `m₁` runs the
invocation while `m` stops the session (`Session.stop`). This is formalised in
`InlDFCex.exportEquiv_append_unreferenced_func_false`. -/
-- FLAG(statement-change): relative to the specified statement, `hparams` (numeric
-- parameters) is added: without it the statement is false,
-- `InlDFCex.exportEquiv_append_unreferenced_func_false`. The hypotheses that the new index
-- occurs in no call, `ref.func`, segment, start or export of `m₁` are dropped, since they
-- follow from `hm`.
theorem exportEquiv_append_unreferenced_func {m m₁ : BModule} {f : BFunc}
    (h₁ : m₁ = { m with funcs := m.funcs ++ [f] })
    (hparams : ∀ st ∈ m.base.typeDefinitions, ∀ ft : FuncType, st.body = .func ft →
      ∀ t ∈ ft.params, ∃ nt, t = .num nt)
    (hm : m.Ok) (hm₁ : m₁.Ok)
    (o : GrowKind → Nat → Nat → Nat → Bool) {H : Type} (host : HostSemantics H)
    (hhost : HostRespectsCode host) (hhostOk : HostOk host) :
    ExportEquiv (· = ·) (Profile.deterministic o) host m₁.lower m.lower := by
  subst h₁
  rw [lower_append_func]
  obtain ⟨⟨xtI, xtE⟩, hM⟩ := hm
  obtain ⟨⟨xtI₁, xtE₁⟩, hM₁⟩ := hm₁
  rw [lower_append_func] at hM₁
  have hp : ∀ d ∈ allocTypes m.lower.types, InlDF.NumParams d :=
    InlDF.numParams_types (M := m.lower) hparams
  refine ⟨⟨fun s xas c hs hi => ?_, fun s xas script hs bs hbs => ?_⟩,
    ⟨fun s xas c' hs hi' => ?_, fun s xas script hs bs hbs => ?_⟩⟩
  · obtain ⟨c', hi', -⟩ := InlDF.inst_fwd hM₁ hi
    exact ⟨c', hi'⟩
  · obtain ⟨c', hi', hobs⟩ := hbs
    obtain ⟨c, hi, hrel⟩ := InlDF.inst_back hM hi'
    have hinv := InlDF.inst_left_facts hs hp hi
    have hc := Instantiate.ok hhostOk hs hi
    have hc' := Instantiate.ok hhostOk hs hi'
    exact ⟨bs, ⟨c, hi, (InlDF.df_obs_corr hhost hhostOk hc hc' hrel hinv script bs).2
      hobs⟩, SessionRel.refl (fun _ => rfl) bs⟩
  · obtain ⟨c, hi, -⟩ := InlDF.inst_back hM hi'
    exact ⟨c, hi⟩
  · obtain ⟨c, hi, hobs⟩ := hbs
    obtain ⟨c', hi', hrel⟩ := InlDF.inst_fwd hM₁ hi
    have hinv := InlDF.inst_left_facts hs hp hi
    have hc := Instantiate.ok hhostOk hs hi
    have hc' := Instantiate.ok hhostOk hs hi'
    exact ⟨bs, ⟨c', hi', (InlDF.df_obs_corr hhost hhostOk hc hc' hrel hinv script bs).1
      hobs⟩, SessionRel.refl (R := fun b b' => (fun x1 x2 => x1 = x2) b' b) (fun _ => rfl) bs⟩

end Silmaril.Wasm.Binaryen
