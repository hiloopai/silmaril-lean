module

public import Silmaril.Compiler.C.Sem.TargetsCoreCompArgs.Defs
@[expose] public section

/-!
# core-comp's `compile_sound` at any enum registry and any arguments (proofs)

Proofs of the statements of `Silmaril.Compile.C.Sem.TargetsCoreCompArgs`. The one real lemma is
`allowed_mem_allowsAt`: every observation that core-comp's `Spec.Allowed doc args` admits is in the
process contract `CoreX86.allows` of the document's Core behaviours run with `args`
(`Core.Source.beh`), for every registry and every argument list. Everything else is
`CoreX86`'s composition API.

The frozen statements of `TargetsCoreComp` (documents without enum registry, default arguments)
follow as the instances at `Startup.execArguments` (`sound_spec_enumFree`,
`compile_valid_enumFree`, `route_valid_enumFree`).
-/

namespace Silmaril.Compile.C.Sem.CoreComp

open Silmaril.Cerberus Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compile.Category Silmaril.Compile.C.Sem.CoreX86 CategoryTheory

/-- A state reachable in core-comp's sense is reached by a multistep transition from
`Spec.coreStart`. -/
theorem coreReach_mTr {doc : Codec.Document} {args : List String} {t : State}
    (hr : Compile.Core.Spec.CoreReach doc args t) :
    ∃ s labels acts, Compile.Core.Spec.coreStart doc args = .ok (s, labels) ∧
      (lts doc.file labels).MTr s acts t := by
  obtain ⟨s, labels, hs, hrt⟩ := hr
  obtain ⟨acts, hm⟩ := (Cslib.LTS.reflTransGen_unlabelledTr_iff _).1 hrt
  exact ⟨s, labels, acts, hs, hm⟩

/-- core-comp's exit statuses are those of csem's `Core.exitOf`. -/
theorem exitStatuses_mem_exitOf {v : Val} {k : Nat} (h : Compile.Core.Spec.exitStatuses v k) :
    Exit.status k ∈ Compile.Core.exitOf v := by
  unfold Compile.Core.Spec.exitStatuses at h
  split at h <;> simp_all [Compile.Core.exitOf]

/-- **The source bridge.** `Spec.Allowed doc args` lies inside the process contract of the
document's Core behaviours run with `args`. -/
theorem allowed_mem_allowsAt {doc : Codec.Document} {args : List String}
    {o : Compile.Core.Spec.Obs} (ho : Compile.Core.Spec.Allowed doc args o) :
    o ∈ allows (modelAt args) ((Compile.Core.Source.ofDoc doc).beh args) := by
  rcases ho with rfl | hub | hbeh
  · exact .inl rfl
  · rcases hub with ⟨loc, ub, hs⟩ | ⟨t, loc, ub, hr, hc⟩
    · simp [Compile.Core.Spec.coreStart, initial] at hs
    · obtain ⟨s, labels, acts, hs, hm⟩ := coreReach_mTr hr
      cases ho' : (modelAt args).process o with
      | none => exact .inl ho'
      | some x =>
        refine .inr ⟨x, ?_, ho'⟩
        rw [Compile.Core.ofDoc_beh_of_coreStart hs, Compile.Core.behFrom_of_ub hm hc]
        trivial
  · cases hbeh with
    | @exit t v k hr hc hk =>
      obtain ⟨s, labels, acts, hs, hm⟩ := coreReach_mTr hr
      refine .inr ⟨_, ?_, rfl⟩
      rw [Compile.Core.ofDoc_beh_of_coreStart hs]
      refine Compile.Core.behFrom_of_final hm ?_
      simp only [Compile.Core.finalObs, hc]
      exact ⟨rfl, exitStatuses_mem_exitOf hk⟩
    | @abort t hr hc =>
      obtain ⟨s, labels, acts, hs, hm⟩ := coreReach_mTr hr
      refine .inr ⟨_, ?_, rfl⟩
      rw [Compile.Core.ofDoc_beh_of_coreStart hs]
      refine Compile.Core.behFrom_of_final hm ?_
      simp only [Compile.Core.finalObs, hc]
      exact ⟨rfl, rfl⟩
    | @diverges s labels hs hinf =>
      refine .inr ⟨_, ?_, rfl⟩
      rw [Compile.Core.ofDoc_beh_of_coreStart hs]
      exact .inr (.inr ⟨rfl, hinf⟩)

/-- Exact validity criterion at `c_SourceX86`, as `core_x86_valid_iff` for `c_CoreX86`. -/
theorem source_x86_valid_iff (args : List String) (M : X86Model) (q : Compile.Core.Source)
    (a : M.Artifact) :
    Valid (c_SourceX86 args M) q a ↔
      M.lang.beh a ⊆ allows M (q.beh args) ∧
      ((∃ x ∈ M.lang.beh a, M.process x = none) → (q.beh args).Nonempty) := by
  rw [valid_iff_beh (c_SourceX86 args M) q a]
  constructor
  · intro h
    constructor
    · intro x hx
      obtain ⟨o, ho, hm⟩ := h.2 hx
      exact hm.elim Or.inl (fun he => .inr ⟨o, ho, he⟩)
    · rintro ⟨x, hx, _⟩
      obtain ⟨o, ho, _⟩ := h.2 hx
      exact ⟨o, ho⟩
  · intro h
    refine ⟨rfl, ?_⟩
    intro x hx
    rcases h.1 hx with hn | ⟨o, ho, he⟩
    · obtain ⟨o, ho⟩ := h.2 ⟨x, hx, hn⟩
      exact ⟨o, ho, Or.inl hn⟩
    · exact ⟨o, ho, Or.inr he⟩

/-- On a document without enum registry, at the default arguments, `c_SourceX86` is
`c_CoreX86` of its file. -/
theorem valid_source_iff_enumFree {doc : Codec.Document} (h : doc.enumBindings.getD [] = [])
    (a : Compile.Core.Spec.Artifact) :
    Valid (c_SourceX86 Core.Startup.execArguments model) (Compile.Core.Source.ofDoc doc) a ↔
      Valid (c_CoreX86 model) doc.file a := by
  refine (source_x86_valid_iff _ model _ a).trans
    (Iff.trans ?_ (core_x86_valid_iff model doc.file a).symm)
  rw [Compile.Core.ofDoc_beh_of_enumFree h]

/-- C → Core sources → x86 is the direct C → x86 convention. -/
theorem cAS_comp_c_SourceX86 (S : Semantics) (M : X86Model) :
    Compile.Core.cAS S ≫ c_SourceX86 Core.Startup.execArguments M = c_Cx86 S M :=
  Convention.ext rfl Relation.eq_comp

/-- `ArgsOk` accepts Cerberus's default arguments. -/
theorem argsOk_execArguments : Compile.Core.Spec.ArgsOk Core.Startup.execArguments := by
  refine ⟨by simp [Core.Startup.execArguments], ?_, ?_⟩
  · simp [Core.Startup.execArguments]
  · simp [Compile.Core.Spec.argBlock, Compile.Core.Spec.le8, Compile.Core.Spec.minArgSize,
      Core.Startup.execArguments]
    decide +kernel

end Silmaril.Compile.C.Sem.CoreComp

namespace Silmaril.Compile.Targets.Proofs

open Silmaril.Cerberus
open Silmaril.Compile.Category Silmaril.Compile.C.Sem
open Silmaril.Compile.C.Sem.CoreX86 Silmaril.Compile.C.Sem.CoreComp CategoryTheory

theorem core_comp_sound_spec_args : Targets.core_comp_sound_spec_args :=
  fun _ hc args hargs doc a ha _ hl _ hx =>
    allowed_mem_allowsAt ((hc doc a ha).2 _ _ _ hl args hargs _ _ _ hx)

theorem core_comp_compile_valid_args : Targets.core_comp_compile_valid_args :=
  fun _ hc args hargs doc a ha hne =>
    (source_x86_valid_iff args (modelAt args) _ a).2
      ⟨fun _ ⟨ctx, hl, hx⟩ => core_comp_sound_spec_args _ hc args hargs doc a ha ctx hl _ hx,
        fun _ => hne⟩

theorem core_comp_route_valid_enums : Targets.core_comp_route_valid_enums := by
  intro S _ hc p doc a helab ha hne
  rw [← cAS_comp_c_SourceX86]
  exact valid_comp_le (Compile.Core.cAS S) (c_SourceX86 Core.Startup.execArguments model) p a
    ⟨_, helab, core_comp_compile_valid_args _ hc _ argsOk_execArguments doc a ha hne⟩

end Silmaril.Compile.Targets.Proofs

namespace Silmaril.Compile.C.Sem.CoreComp

open Silmaril.Cerberus
open Silmaril.Compile.Category Silmaril.Compile.C.Sem.CoreX86

/-! ## The frozen statements as instances -/

/-- `Targets.core_comp_sound_spec` is `core_comp_sound_spec_args` at the default arguments. -/
theorem sound_spec_enumFree : Targets.core_comp_sound_spec := by
  intro compile hc d a ha
  rw [← Compile.Core.ofDoc_beh_of_enumFree d.2]
  exact Targets.Proofs.core_comp_sound_spec_args compile hc _ argsOk_execArguments d.1 a ha

/-- `Targets.core_comp_compile_valid` is `core_comp_compile_valid_args` at the default
arguments. -/
theorem compile_valid_enumFree : Targets.core_comp_compile_valid := by
  intro compile hc doc a ha h hne
  rw [← Compile.Core.ofDoc_beh_of_enumFree h] at hne
  exact (valid_source_iff_enumFree h a).1
    (Targets.Proofs.core_comp_compile_valid_args compile hc _ argsOk_execArguments doc a ha hne)

/-- `Targets.core_comp_route_valid` is `core_comp_route_valid_enums` on the empty registry. -/
theorem route_valid_enumFree : Targets.core_comp_route_valid := by
  intro S compile hc p doc a helab ha h hne
  exact c_x86_of_core helab (compile_valid_enumFree compile hc doc a ha h hne)

end Silmaril.Compile.C.Sem.CoreComp
