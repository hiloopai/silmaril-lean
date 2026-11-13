module

public import Silmaril.Proofs.Wasm.Component.Reference.CallBase

/-!
# The core phase of a call: inverting runs of a core activation

A core activation `⟨th, .core t K, segs⟩` on top of the control chain takes internal core steps
(`coreInternal`, label `core`), which change only the core store and the thread, until its
status is a result or a callout. This module inverts machine runs and divergence from such a
configuration (`coreCfg B th K segs rest x`, with core store and thread `x`), for any engine:

* `coreCfg_steps_inv`: a run stays in the core phase (along `E.Internal` steps), or leaves it
  at a returned, trapped or calling-out status and continues from the next configuration;
* `coreCfg_diverges_inv`: divergence is divergence of the core activation, or divergence after
  it left the core phase.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → P E σ (Ret E)}

/-- A core store and a core thread. -/
abbrev CoreSt (E : CoreEngine) : Type := E.Store (CanonHost E) × E.Thread (CanonHost E)

/-- The configuration `B` running the core activation `x.2` (core store `x.1`) with
continuation `K`. -/
def coreCfg (B : Config E σ) (th : Option ThreadId) (K : List FlatValue → P E σ (Ret E))
    (segs : List (Seg E σ)) (rest : List (Activation E σ)) (x : CoreSt E) : Config E σ :=
  { B with store := { B.store with core := x.1 }, ctl := ⟨th, .core x.2 K, segs⟩ :: rest }

/-- The configuration after the core activation returned `vs`. -/
def retCfg (B : Config E σ) (th : Option ThreadId) (K : List FlatValue → P E σ (Ret E))
    (segs : List (Seg E σ)) (rest : List (Activation E σ)) (x : CoreSt E)
    (vs : List FlatValue) : Config E σ :=
  { B with store := { B.store with core := x.1 }, ctl := ⟨th, .prog (K vs), segs⟩ :: rest }

/-- An internal core step allowed by the machine. -/
def CoreStep (E : CoreEngine) (x y : CoreSt E) : Prop :=
  (E.status x.1 x.2 = .running ∨ E.status x.1 x.2 = .stuck) ∧ E.Internal x y

/-- The ways a step leaves the core phase. -/
def CoreExit (B : Config E σ) (th : Option ThreadId) (K : List FlatValue → P E σ (Ret E))
    (segs : List (Seg E σ)) (rest : List (Activation E σ)) (x : CoreSt E) (l : Label E σ)
    (m' : Config E σ) : Prop :=
  (∃ vs, E.status x.1 x.2 = .returned (.values vs) ∧ l = .tau ∧
      m' = retCfg B th K segs rest x vs) ∨
    (E.status x.1 x.2 = .returned .trap ∧ l = .trap .coreTrap ∧
      m' = trapCfg (coreCfg B th K segs rest x)) ∨
    (∃ h args, E.status x.1 x.2 = .callout h args)

/-- **One step of a core activation**: an internal core step, or an exit. -/
theorem coreCfg_step_inv {B : Config E σ} {th : Option ThreadId}
    {K : List FlatValue → P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} {x : CoreSt E} {l : Label E σ} {m' : Config E σ}
    (h : Step prof hr dispatch (coreCfg B th K segs rest x) l m') :
    (l = .core ∧ ∃ y, CoreStep E x y ∧ m' = coreCfg B th K segs rest y) ∨
      CoreExit B th K segs rest x l m' := by
  cases h with
  | coreInternal hc hs hi =>
    cases hc
    exact .inl ⟨rfl, _, ⟨hs, hi⟩, rfl⟩
  | coreReturned hc hs =>
    cases hc
    exact .inr (.inl ⟨_, hs, rfl, rfl⟩)
  | coreTrap hc hs =>
    cases hc
    exact .inr (.inr (.inl ⟨hs, rfl, rfl⟩))
  | coreCallout hc hs =>
    cases hc
    exact .inr (.inr (.inr ⟨_, _, hs⟩))
  | fault hf => cases hf <;> simp_all [coreCfg]
  | hostInvoke hh => exact absurd hh.1 (List.cons_ne_nil _ _)
  | hostTick hh => exact absurd hh.1 (List.cons_ne_nil _ _)
  | hostCancel hh => exact absurd hh.1 (List.cons_ne_nil _ _)
  | hostRun hh => exact absurd hh.1 (List.cons_ne_nil _ _)
  | _ => simp_all [coreCfg]

/-- **Runs of a core activation**: they stay in the core phase, or leave it once. -/
theorem coreCfg_steps_inv {B : Config E σ} {th : Option ThreadId}
    {K : List FlatValue → P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} {x : CoreSt E} {tr : List (Label E σ)} {m' : Config E σ}
    (h : Steps prof hr dispatch (coreCfg B th K segs rest x) tr m') :
    (∃ y, Relation.ReflTransGen (CoreStep E) x y ∧ m' = coreCfg B th K segs rest y ∧
        ∀ l ∈ tr, l = .core) ∨
      ∃ y pre l m₁ tr₂, Relation.ReflTransGen (CoreStep E) x y ∧ (∀ l ∈ pre, l = .core) ∧
        tr = pre ++ l :: tr₂ ∧ CoreExit B th K segs rest y l m₁ ∧
        Steps prof hr dispatch m₁ tr₂ m' := by
  generalize hm : coreCfg B th K segs rest x = m at h
  induction h generalizing x with
  | refl => exact .inl ⟨x, .refl, hm.symm, fun _ h => nomatch h⟩
  | cons s r ih =>
    subst hm
    rcases coreCfg_step_inv s with ⟨rfl, y, hy, rfl⟩ | hx
    · rcases ih rfl with ⟨z, hz, e, hl⟩ | ⟨z, pre, l, m₁, tr₂, hz, hp, e, hx, r'⟩
      · refine .inl ⟨z, .head hy hz, e, ?_⟩
        intro l hl'
        rcases List.mem_cons.mp hl' with rfl | hl'
        · rfl
        · exact hl l hl'
      · refine .inr ⟨z, .core :: pre, l, m₁, tr₂, .head hy hz, ?_, by rw [e]; rfl, hx, r'⟩
        intro l' hl'
        rcases List.mem_cons.mp hl' with rfl | hl'
        · rfl
        · exact hp l' hl'
    · have hnil : ∀ l ∈ ([] : List (Label E σ)), l = .core := fun _ h => nomatch h
      exact .inr ⟨x, [], _, _, _, .refl, hnil, rfl, hx, r⟩

/-- **Divergence of a core activation**: the core activation diverges, or the run leaves the
core phase and diverges afterwards. -/
theorem coreCfg_diverges_inv {B : Config E σ} {th : Option ThreadId}
    {K : List FlatValue → P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} {x : CoreSt E}
    (h : Diverges prof hr dispatch (coreCfg B th K segs rest x)) :
    Silmaril.InfiniteTrace (CoreStep E) x ∨
      ∃ y l m₁, Relation.ReflTransGen (CoreStep E) x y ∧ CoreExit B th K segs rest y l m₁ ∧
        Diverges prof hr dispatch m₁ := by
  have hd := Silmaril.InfiniteTrace.context_decompose (CoreStep E)
    (InternalStep prof hr dispatch) (coreCfg B th K segs rest)
    (fun a b => ∃ l, CoreExit B th K segs rest a l b) (fun a b ⟨l, _, s⟩ => by
      rcases coreCfg_step_inv s with ⟨-, y, hy, rfl⟩ | hx
      · exact .inl ⟨y, hy, rfl⟩
      · exact .inr ⟨l, hx⟩) h
  rcases hd with hi | ⟨y, m₁, hy, ⟨l, hx⟩, d⟩
  · exact .inl hi
  · exact .inr ⟨y, l, m₁, hy, hx, d⟩

end Silmaril.Proofs.Wasm.Component.Reference
