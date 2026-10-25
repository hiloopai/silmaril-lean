module

public import Silmaril.Wasm.Binaryen.InlProfileEquiv
public import Silmaril.Wasm.Binaryen.InlReverseComplete
public import Silmaril.Wasm.Binaryen.Exe.PipelineSound
public import Silmaril.Wasm.Binaryen.PassAPI.Shared

@[expose] public section

/-! # The existing executable inliner at arbitrary numerical profiles

The complete chosen reverse simulation discharges the observation layer's local
obligation. These theorems apply to the existing `inlineSite`, site search,
heuristic and finite-fuel loop without changing their executable definitions or
removing functionality. They retain exact closed-host export equivalence,
including module initialization, persistent calls, chosen numerical outcomes,
exceptions and divergence, for every numerical profile and host-state type.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics SingleThreaded

/-- Inlining is an equivalence, from `retGoodL` of the callee. -/
theorem inlineSite_sound_of_good_profile {m m' : BModule} {g : Nat} {K : BCtx} {args : List BExpr}
    {f : FuncIdx} (hm : m.Ok) (hsite : m.body? g = some (K.plug [.op (.call f) args]))
    (hB : ∀ fn, m.defFunc? f.toNat = some fn →
      BExpr.structuredList fn.body = true ∧ NoTailCalls fn.body)
    (hgd : ∀ fn, m.defFunc? f.toNat = some fn → InlineTy.retGoodL 0 (BExpr.lowerList fn.body))
    (h : inlineSite m g K args f = some m')
    (P : Profile) {H : Type} :
    ExportEquiv (· = ·) P (closedHost (H := H)) m'.lower m.lower := by
  obtain ⟨mt, hmt⟩ := hm
  obtain ⟨cg, cg', cf, hg, hf, hty, hM', hgood⟩ := inlineSite_siteGood hmt hsite hB hgd h
  have hval : ∀ mt', ModuleOk m.lower mt' ↔
      ModuleOk { m.lower with funcs := m.lower.funcs.set g cg' } mt' := by
    intro mt'
    rw [← hM']
    constructor
    · intro h'
      exact inlineSite_valid_mt h' hsite hB hgd h
    · intro h'
      have h₀ := inlineSite_valid_mt hmt hsite hB hgd h
      rw [ModuleOk.unique h' h₀]
      exact hmt
  rw [hM']
  exact InlR.exportEquiv_of_instCorr_profile
    (fun _ good => InlR.chosenReverseStep_of_good good)
    (InlR.instCorr_of_set_profile hg hf hty hval hgood)

end Silmaril.Wasm.Binaryen

namespace Silmaril.Wasm.Binaryen.Exe

open Execution.Core Validation Numerics

/-- One actual executable inlining step retains validity and exact export
behavior at the same arbitrary profile. Callee applicability checks are unchanged. -/
theorem inlineStep_spec_profile (P : Profile) {H : Type}
    {budget : Nat} {m m' : BModule} (hok : m.Ok)
    (h : Inl.inlineStep budget m = some m') :
    m'.Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H)) m'.lower m.lower := by
  rw [Inl.inlineStep_eq] at h
  rcases hs : Inl.findSite (Inl.calleeOk budget m) m with _ | ⟨g, K, args, f⟩
  · simp [hs] at h
  · simp only [hs] at h
    obtain ⟨hsite, hc⟩ := Inl.findSite_spec hs
    rw [Inl.inlineSite_eq] at h
    have good := fun fn (hfn : m.defFunc? f.toNat = some fn) => calleeOk_good hc hfn
    constructor
    · obtain ⟨mt, hmt⟩ := hok
      exact ⟨mt, inlineSite_valid_mt hmt hsite (fun fn hfn => (good fn hfn).1)
        (fun fn hfn => (good fn hfn).2) h⟩
    · exact inlineSite_sound_of_good_profile hok hsite (fun fn hfn => (good fn hfn).1)
        (fun fn hfn => (good fn hfn).2) h P

/-- Every finite iteration of the actual site-search/heuristic loop is sound.
Module validity is the only input invariant. -/
theorem inlineSmall_spec_profile (P : Profile) {H : Type} (budget : Nat) :
    ∀ (fuel : Nat) (m : BModule), m.Ok →
      (Inl.inlineSmall budget fuel m).Ok ∧
        ExportEquiv (· = ·) P (closedHost (H := H))
          (Inl.inlineSmall budget fuel m).lower m.lower
  | 0, m, hok => ⟨hok, exportEquiv_refl _⟩
  | fuel + 1, m, hok => by
    unfold Inl.inlineSmall
    rcases hs : Inl.inlineStep budget m with _ | m'
    · exact ⟨hok, exportEquiv_refl _⟩
    · obtain ⟨valid, equiv⟩ := inlineStep_spec_profile P hok hs
      obtain ⟨valid', equiv'⟩ := inlineSmall_spec_profile P budget fuel m' valid
      exact ⟨valid', ExportEquiv.trans_eq equiv' equiv⟩

/-- The actual inlining loop, requiring only module validity. Its site search,
callee eligibility, size heuristic and fuel are unchanged; unrelated type-section
features do not suppress an eligible call site. -/
def inlineValidProfileP (P : Profile) (H : Type) (budget fuel : Nat) :
    PassAPI.Pass (PassAPI.equivContract P (closedHost (H := H))) where
  run := Inl.inlineSmall budget fuel
  inv_run hm := (inlineSmall_spec_profile P (H := H) budget fuel _ hm).1
  sound hm := (inlineSmall_spec_profile P (H := H) budget fuel _ hm).2

@[simp] theorem inlineValidProfileP_run (P : Profile) (H : Type) (budget fuel : Nat) :
    (inlineValidProfileP P H budget fuel).run = Inl.inlineSmall budget fuel := rfl

/-- The validity-only inliner through the compiler-wide shared pass API. -/
def inlineValidProfileSharedP (P : Profile) (H : Type) (budget fuel : Nat) :
    Silmaril.Compile.PassAPI.Pass
      (PassAPI.equivContract P (closedHost (H := H))).toShared :=
  (inlineValidProfileP P H budget fuel).toShared

@[simp] theorem inlineValidProfileSharedP_run (P : Profile) (H : Type)
    (budget fuel : Nat) :
    (inlineValidProfileSharedP P H budget fuel).run = Inl.inlineSmall budget fuel := rfl

/-- The existing public executable wrapper retains its type-section guard and
its exact output; the proof needs no deterministic numerical profile. -/
theorem inlineSmall_sound_profile (P : Profile) {H : Type} (budget fuel : Nat)
    {m : BModule} (hm : m.Ok) :
    (inlineSmall budget fuel m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        (inlineSmall budget fuel m).lower m.lower := by
  unfold inlineSmall
  split
  · exact inlineSmall_spec_profile P budget fuel m hm
  · exact ⟨hm, exportEquiv_refl _⟩

/-- The original stage contract now holds for any host-state type; the host
itself remains closed. This specializes the stronger arbitrary-profile result. -/
theorem inline_stageOk_closed {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}
    (budget : Nat) : StageOk o H (inlineSmall budget inlineFuel) :=
  fun _ hm => inlineSmall_sound_profile (Profile.deterministic o) budget inlineFuel hm.ok

/-- A pass for the existing executable wrapper, under the common exact
export-equivalence contract and validity invariant. -/
def inlineProfileP (P : Profile) (H : Type) (budget fuel : Nat) :
    PassAPI.Pass (PassAPI.equivContract P (closedHost (H := H))) where
  run := inlineSmall budget fuel
  inv_run hm := (inlineSmall_sound_profile P (H := H) budget fuel hm).1
  sound hm := (inlineSmall_sound_profile P (H := H) budget fuel hm).2

@[simp] theorem inlineProfileP_run (P : Profile) (H : Type) (budget fuel : Nat) :
    (inlineProfileP P H budget fuel).run = inlineSmall budget fuel := rfl

/-- Losslessly view the same inliner through the compiler-wide shared pass API. -/
def inlineProfileSharedP (P : Profile) (H : Type) (budget fuel : Nat) :
    Silmaril.Compile.PassAPI.Pass
      (PassAPI.equivContract P (closedHost (H := H))).toShared :=
  (inlineProfileP P H budget fuel).toShared

@[simp] theorem inlineProfileSharedP_run (P : Profile) (H : Type) (budget fuel : Nat) :
    (inlineProfileSharedP P H budget fuel).run = inlineSmall budget fuel := rfl

end Silmaril.Wasm.Binaryen.Exe
