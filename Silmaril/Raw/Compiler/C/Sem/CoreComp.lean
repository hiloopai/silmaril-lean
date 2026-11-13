module

public import Silmaril.Compiler.C.Sem.TargetsCoreComp.Defs
@[expose] public section

/-!
# core-comp's `compile_sound` gives `Valid c_CoreX86` (proofs)

Proofs of the statements of `Silmaril.Compile.C.Sem.TargetsCoreComp`. The one real lemma is
`allowed_mem_allows`: on a document without enum registry, run with Cerberus's default
arguments, every observation that core-comp's `Spec.Allowed` admits is in the process contract
`CoreX86.allows` of csem's `Core.beh`. Everything else is `CoreX86`'s composition API.
-/

namespace Silmaril.Compile.C.Sem.CoreComp

open Silmaril.Cerberus Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compile.Category Silmaril.Compile.C.Sem.CoreX86 CategoryTheory

/-- Without enum registry, `Spec.coreStart` with the default arguments is the start of
`Core.beh`. -/
theorem coreStart_eq {doc : Codec.Document} (h : doc.enumBindings.getD [] = []) :
    Compile.Core.Spec.coreStart doc Core.Startup.execArguments = initial doc.file := by
  simp only [Compile.Core.Spec.coreStart, h]
  rfl

/-- `Core.beh` of a file is `behFrom` its start state. -/
theorem beh_eq {file : Program} {s : State} {labels : Labels}
    (h : initial file = .ok (s, labels)) : Compile.Core.beh file = Compile.Core.behFrom file labels s := by
  simp only [Compile.Core.beh, h]

/-- A state reachable in core-comp's sense is reached by a multistep transition. -/
theorem mTr_of_coreReach {doc : Codec.Document} (h : doc.enumBindings.getD [] = [])
    {t : State} (hr : Compile.Core.Spec.CoreReach doc Core.Startup.execArguments t) :
    ∃ s labels acts, initial doc.file = .ok (s, labels) ∧ (lts doc.file labels).MTr s acts t := by
  obtain ⟨s, labels, hs, hrt⟩ := hr
  rw [coreStart_eq h] at hs
  obtain ⟨acts, hm⟩ := (Cslib.LTS.reflTransGen_unlabelledTr_iff _).1 hrt
  exact ⟨s, labels, acts, hs, hm⟩

/-- core-comp's exit statuses are those of csem's `Core.exitOf`. -/
theorem status_mem_exitOf {v : Val} {k : Nat} (h : Compile.Core.Spec.exitStatuses v k) :
    Exit.status k ∈ Compile.Core.exitOf v := by
  unfold Compile.Core.Spec.exitStatuses at h
  split at h <;> simp_all [Compile.Core.exitOf]

/-- **The source bridge.** On a document without enum registry, run with Cerberus's default
arguments, `Spec.Allowed` lies inside the process contract of `Core.beh`. -/
theorem allowed_mem_allows {doc : Codec.Document} (h : doc.enumBindings.getD [] = [])
    {o : Compile.Core.Spec.Obs} (ho : Compile.Core.Spec.Allowed doc Core.Startup.execArguments o) :
    o ∈ allows model (Compile.Core.beh doc.file) := by
  rcases ho with rfl | hub | hbeh
  · exact .inl rfl
  · rcases hub with ⟨loc, ub, hs⟩ | ⟨t, loc, ub, hr, hc⟩
    · rw [coreStart_eq h] at hs
      simp [initial] at hs
    · obtain ⟨s, labels, acts, hs, hm⟩ := mTr_of_coreReach h hr
      cases ho' : model.process o with
      | none => exact .inl ho'
      | some x =>
        refine .inr ⟨x, ?_, ho'⟩
        rw [beh_eq hs, Compile.Core.behFrom_of_ub hm hc]
        trivial
  · cases hbeh with
    | @exit t v k hr hc hk =>
      obtain ⟨s, labels, acts, hs, hm⟩ := mTr_of_coreReach h hr
      refine .inr ⟨_, ?_, rfl⟩
      rw [beh_eq hs]
      refine Compile.Core.behFrom_of_final hm ?_
      simp only [Compile.Core.finalObs, hc]
      exact ⟨rfl, status_mem_exitOf hk⟩
    | @abort t hr hc =>
      obtain ⟨s, labels, acts, hs, hm⟩ := mTr_of_coreReach h hr
      refine .inr ⟨_, ?_, rfl⟩
      rw [beh_eq hs]
      refine Compile.Core.behFrom_of_final hm ?_
      simp only [Compile.Core.finalObs, hc]
      exact ⟨rfl, rfl⟩
    | @diverges s labels hs hinf =>
      rw [coreStart_eq h] at hs
      refine .inr ⟨_, ?_, rfl⟩
      rw [beh_eq hs]
      exact .inr (.inr ⟨rfl, hinf⟩)

/-- core-comp's specification gives the abstract `CoreX86.SoundSpec` of its model. -/
theorem sound_spec {compile : Codec.Document → Option Compile.Core.Spec.Artifact}
    (hc : Compile.Core.Spec.SoundSpec compile) :
    CoreX86.SoundSpec model (fun d : EnumFree => d.1.file) (fun d => compile d.1) :=
  fun d a ha ctx hl x hx => allowed_mem_allows d.2 ((hc d.1 a ha).2 _ _ _ hl _ args_ok _ _ _ hx)
where
  args_ok : Compile.Core.Spec.ArgsOk Core.Startup.execArguments := by
    refine ⟨by simp [Core.Startup.execArguments], ?_, ?_⟩
    · simp [Core.Startup.execArguments]
    · simp [Compile.Core.Spec.argBlock, Compile.Core.Spec.le8, Compile.Core.Spec.minArgSize,
        Core.Startup.execArguments]
      decide +kernel

/-- **Milestone (b).** core-comp's `compile_sound` makes every accepted document with a Core
behaviour (and no enum registry) a valid compilation at `c_CoreX86 model`. -/
theorem compile_valid {compile : Codec.Document → Option Compile.Core.Spec.Artifact}
    (hc : Compile.Core.Spec.SoundSpec compile) {doc : Codec.Document}
    {a : Compile.Core.Spec.Artifact} (ha : compile doc = some a)
    (h : doc.enumBindings.getD [] = []) (hne : (Compile.Core.beh doc.file).Nonempty) :
    Valid (c_CoreX86 model) doc.file a :=
  (core_x86_valid_iff model doc.file a).2
    ⟨fun _ ⟨ctx, hl, hx⟩ => sound_spec hc ⟨doc, h⟩ a ha ctx hl _ hx, fun _ => hne⟩

/-- The route C → Core → x86 with core-comp's backend: the local lemmas compose. -/
theorem route_valid {S : Semantics} {compile : Codec.Document → Option Compile.Core.Spec.Artifact}
    (hc : Compile.Core.Spec.SoundSpec compile) {p : Ail.TypedProgram} {doc : Codec.Document}
    {a : Compile.Core.Spec.Artifact} (helab : Valid (Compile.Core.cAC S) p doc.file)
    (ha : compile doc = some a) (h : doc.enumBindings.getD [] = [])
    (hne : (Compile.Core.beh doc.file).Nonempty) :
    Valid (c_Cx86 S model) p a :=
  c_x86_of_core helab (compile_valid hc ha h hne)

end Silmaril.Compile.C.Sem.CoreComp
