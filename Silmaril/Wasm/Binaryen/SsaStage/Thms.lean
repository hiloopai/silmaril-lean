module

public import Silmaril.Wasm.Binaryen.SsaStage.Defs
public import Silmaril.Wasm.SSA.CoreCert.Thms
public import Silmaril.Wasm.Binaryen.ArbitraryProfile

@[expose] public section

/-! # The SSA stage: what is proved

* `ssaRun_spec`: on a valid module the stage returns a valid module with the same
  non-function sections and the same number of functions, in which every function is either
  the original one or a replacement that is
  - fragment-equivalent (`FragEquivAt`: both recognised in the SSA fragment at the function's
    type, with exactly the same terminating outcomes in the fragment semantics), and
  - **Core-equivalent on invocations** (`CoreEquivAt`): in the stores that silmaril's
    executable instantiation allocates for the input and the output (both closed and valid),
    every typed invocation of the function has the same Core 3.0 behaviours, closed host, at
    **every** numerical profile, divergence included (`SSA.optimizeFuncLocal_replace`, from
    `Interp.native_adequacy` on the stub module and `SSA.behaviours_local`).

* **Export equivalence** (`ssaRun_exportEquiv`): on a valid module, `ssaRun m` is exactly
  export-equivalent to `m` (`ExportEquiv (· = ·) P closedHost`) at every numerical profile `P`
  (`SSA.replace_exportEquiv`: the rewritten functions are strict leaves with equal canonical
  callee behaviours, and the caller-side simulation relates every invocation of every export,
  callers included, instantiation and sessions included). `ssaP P` is the stage as silmaril's
  shared pass `ArbitraryProfile.EquivPass`.
-/

namespace Silmaril.Wasm.Binaryen.SsaStage

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

/-- `bf'` is a fragment-equivalent replacement of defined function `g` of `m`. -/
def FragEquivAt (m : BModule) (g : Nat) (bf' : BFunc) : Prop :=
  ∃ bf ft f f', m.funcs[g]? = some bf ∧ m.funcType? bf.type = some ft ∧
    Silmaril.Wasm.SSA.ofBFunc? ft bf = some f ∧ Silmaril.Wasm.SSA.ofBFunc? ft bf' = some f' ∧
    ∀ args o, f.Run args o ↔ f'.Run args o

/-- Invocations of function `g` have the same Core 3.0 behaviours, every profile, in the
allocated stores of `m` and `m'`. -/
def CoreEquivAt (m m' : BModule) (g : Nat) : Prop :=
  ∃ s s' : Store Empty, Silmaril.Wasm.SSA.allocStore? m = some s ∧
    Silmaril.Wasm.SSA.allocStore? m' = some s' ∧ ∀ (P : Numerics.Profile) (vs : List Val),
      InvokeOk s g vs → behaviours P closedHost s g vs = behaviours P closedHost s' g vs

/-- The per-function guarantee of the SSA stage from `m` to `m'`. -/
def SsaSpec (m m' : BModule) : Prop :=
  m'.base = m.base ∧ m'.funcs.length = m.funcs.length ∧
    ∀ g bf', m'.funcs[g]? = some bf' →
      m.funcs[g]? = some bf' ∨ (FragEquivAt m g bf' ∧ CoreEquivAt m m' g)

theorem SsaSpec.refl (m : BModule) : SsaSpec m m :=
  ⟨rfl, rfl, fun _ _ h => .inl h⟩

/-- The candidates: the original function or the certified replacement. -/
theorem ssaFuncs_get {m : BModule} {g : Nat} {bf' : BFunc} (h : (ssaFuncs m)[g]? = some bf') :
    m.funcs[g]? = some bf' ∨ Silmaril.Wasm.SSA.optimizeFuncExport m g = some bf' := by
  simp only [ssaFuncs, List.getElem?_mapIdx, Option.map_eq_some_iff] at h
  obtain ⟨f, hf, rfl⟩ := h
  cases ho : Silmaril.Wasm.SSA.optimizeFuncExport m g with
  | none => exact .inl (by simpa [ho] using hf)
  | some b => exact .inr (by simp)

/-- What `ssaAccept` checked, at a rewritten function. -/
theorem ssaAccept_at {m m' : BModule} (h : ssaAccept m m' = true) :
    Silmaril.Wasm.SSA.closedValid m' = true ∧
      ∀ g bf', Silmaril.Wasm.SSA.optimizeFuncExport m g = some bf' → m'.funcs[g]? = some bf' →
        ∀ bf ft, m.funcs[g]? = some bf → m.funcType? bf.type = some ft →
          Silmaril.Wasm.SSA.runCert m' g ft bf' = true := by
  simp only [ssaAccept, Bool.and_eq_true] at h
  refine ⟨h.1, fun g bf' ho hbf' bf ft hbf hft => ?_⟩
  have hlt : g < m.funcs.length := (List.getElem?_eq_some_iff.mp hbf).1
  have hg := List.all_eq_true.mp h.2 g (List.mem_range.mpr hlt)
  have hsrc : srcType? m g = some ft := by simp [srcType?, hbf, hft]
  simpa [ho, hsrc, hbf'] using hg

/-- **The SSA stage keeps validity and rewrites functions with a Core certificate.** -/
theorem ssaRun_spec {m : BModule} (hm : m.Ok) : (ssaRun m).Ok ∧ SsaSpec m (ssaRun m) := by
  unfold ssaRun
  split
  · exact ⟨hm, SsaSpec.refl m⟩
  · dsimp only
    split
    · next hacc =>
      obtain ⟨hv', hready⟩ := ssaAccept_at hacc
      refine ⟨Silmaril.Wasm.SSA.ok_of_closedValid hv', rfl, by simp [ssaFuncs], ?_⟩
      intro g bf' h
      rcases ssaFuncs_get h with hsame | ho
      · exact .inl hsame
      · have hl := Silmaril.Wasm.SSA.optimizeFuncExport_local ho
        exact .inr ⟨Silmaril.Wasm.SSA.optimizeFuncLocal_frag hl,
          Silmaril.Wasm.SSA.optimizeFuncLocal_replace hl h (hready g bf' ho h)⟩
    · exact ⟨hm, SsaSpec.refl m⟩

/-- **The SSA stage is exactly export-equivalent at every numerical profile** (closed host). -/
theorem ssaRun_exportEquiv {H : Type} {m : BModule} (hm : m.Ok) (P : Numerics.Profile) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (ssaRun m).lower m.lower := by
  have hok := (ssaRun_spec hm).1
  revert hok
  unfold ssaRun
  split
  · intro _
    exact ⟨ExportRefines.refl (fun _ => rfl) _,
      (ExportRefines.refl (fun _ => rfl) _).mono fun _ _ h => h.symm⟩
  · dsimp only
    split
    · next hacc =>
      intro hok
      obtain ⟨-, hready⟩ := ssaAccept_at hacc
      refine Silmaril.Wasm.SSA.replace_exportEquiv (m := m) (m' := { m with funcs := ssaFuncs m }) rfl
        (by simp [ssaFuncs]) hm hok ?_ P
      intro g bf' h
      rcases ssaFuncs_get h with hsame | ho
      · exact .inl hsame
      · exact .inr ⟨ho, hready g bf' ho h⟩
    · intro _
      exact ⟨ExportRefines.refl (fun _ => rfl) _,
        (ExportRefines.refl (fun _ => rfl) _).mono fun _ _ h => h.symm⟩

/-- **The SSA stage as a shared pass** with exact export equivalence at profile `P`. -/
def ssaP {H : Type} (P : Numerics.Profile) :
    Silmaril.Wasm.Binaryen.ArbitraryProfile.EquivPass P (closedHost (H := H)) where
  run := ssaRun
  inv_run hm := (ssaRun_spec hm).1
  sound hm := ssaRun_exportEquiv hm P

@[simp] theorem ssaP_run {H : Type} (P : Numerics.Profile) : (ssaP (H := H) P).run = ssaRun := rfl

end Silmaril.Wasm.Binaryen.SsaStage
