module

public import Silmaril.Wasm.Models.FX.Defs

/-!
# CoreFX is conservative over Core 3.0: one step

* `isCore`, `all_isCore_ofCore`: Core code is the FX code whose instructions are all `core`;
* `step_ofCore`: an FX step from a Core configuration whose store has no FX functions is the
  image of a Core step (with the host `blockFX host fx`). Every FX rule other than `core`,
  `seq`, `trapSeq`, `throwSeq` and `invoke` has a non-Core instruction on its left; `seq` is
  Core's `ctxt-instrs` by induction, `trapSeq` and `throwSeq` are Core's `trap-instrs` and
  `throw_ref-instrs`, and `invoke` needs an FX function;
* `ofCore_step`: conversely, every Core step lifts;
* `blockFX_noFX`: without FX functions the Core host is unchanged.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- A Core administrative instruction in FX code. -/
def isCore : AdminFX → Bool
  | .core _ => true
  | _ => false

theorem core_injective : Function.Injective AdminFX.core := fun _ _ h => by cases h; rfl

theorem map_core_inj {l l' : List Admin} (h : l.map AdminFX.core = l'.map AdminFX.core) :
    l = l' :=
  List.map_injective_iff.mpr core_injective h

@[simp] theorem all_isCore_map (l : List Admin) : (l.map AdminFX.core).all isCore = true := by
  simp [List.all_map, Function.comp_def, isCore]

@[simp] theorem all_isCore_cvals (vs : List Val) : (cvals vs).all isCore = true :=
  all_isCore_map _

@[simp] theorem all_isCore_cthrowing (a : Nat) : (cthrowing a).all isCore = true :=
  all_isCore_map _

/-- Split Core code along an FX decomposition `cvals vs ++ es ++ rest`. -/
theorem split3 {cs : List Admin} {pre es rest : List AdminFX}
    (h : pre ++ es ++ rest = cs.map AdminFX.core) :
    ∃ A B C, cs = A ++ B ++ C ∧ A.map AdminFX.core = pre ∧ B.map AdminFX.core = es ∧
      C.map AdminFX.core = rest := by
  obtain ⟨AB, C, rfl, hAB, hC⟩ := List.map_eq_append_iff.mp h.symm
  obtain ⟨A, B, rfl, hA, hB⟩ := List.map_eq_append_iff.mp hAB
  exact ⟨A, B, C, rfl, hA, hB, hC⟩

theorem ofCore_eq {c : Config H} {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {L : List AdminFX} (h : (⟨s, K, f, L⟩ : ConfigFX H) = ofCore c) :
    s = c.store ∧ K = [] ∧ f = c.frame ∧ L = c.code.map AdminFX.core := by
  simp only [ofCore, ConfigFX.mk.injEq] at h
  exact h

/-- `ofCore` of a configuration given by its fields. -/
theorem ofCore_mk (s : Store H) (f : Frame) (cs : List Admin) :
    ofCore (⟨s, f, cs⟩ : Config H) = ⟨s, [], f, cs.map AdminFX.core⟩ := rfl

/-- A Core configuration given by its fields. -/
theorem config_eta (c : Config H) {cs : List Admin} (h : c.code = cs) :
    c = ⟨c.store, c.frame, cs⟩ := by
  cases c
  simp only at h
  rw [h]

/-- `rest ≠ []` transports along `map core`. -/
theorem hne_map {vs : List Val} {C : List Admin} {rest : List AdminFX}
    (hC : C.map AdminFX.core = rest) (hne : vs ≠ [] ∨ rest ≠ []) : vs ≠ [] ∨ C ≠ [] := by
  rcases hne with hv | hr
  · exact Or.inl hv
  · exact Or.inr fun hC' => hr (by rw [← hC, hC', List.map_nil])

/-- The `core` case: a lifted Core step. -/
theorem case_core {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
    {s s' : Store H} {K : List (Option ContFX)} {f f' : Frame} {cs cs' : List Admin}
    (h : Step P (blockFX host fx) ⟨s, f, cs⟩ ⟨s', f', cs'⟩) (c : Config H)
    (hx : (⟨s, K, f, cs.map .core⟩ : ConfigFX H) = ofCore c) :
    ∃ c', Step P (blockFX host fx) c c' ∧ (⟨s', K, f', cs'.map .core⟩ : ConfigFX H) = ofCore c' := by
  obtain ⟨hs, hK, hf, hL⟩ := ofCore_eq hx
  have hcc : c = ⟨s, f, cs⟩ := by
    rw [config_eta c (map_core_inj hL).symm, hs, hf]
  refine ⟨⟨s', f', cs'⟩, hcc ▸ h, ?_⟩
  rw [hK]
  rfl

/-- The `seq` case: Core's `ctxt-instrs`. -/
theorem case_seq {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
    {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame} {vs : List Val}
    {es es' rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ [])
    (ih : ∀ c : Config H, (⟨s, K, f, es⟩ : ConfigFX H) = ofCore c → NoFX fx c.store →
      ∃ c', Step P (blockFX host fx) c c' ∧ (⟨s', K', f', es'⟩ : ConfigFX H) = ofCore c')
    (c : Config H) (hx : (⟨s, K, f, cvals vs ++ es ++ rest⟩ : ConfigFX H) = ofCore c)
    (hno : NoFX fx c.store) :
    ∃ c', Step P (blockFX host fx) c c' ∧
      (⟨s', K', f', cvals vs ++ es' ++ rest⟩ : ConfigFX H) = ofCore c' := by
  obtain ⟨hs, hK, hf, hL⟩ := ofCore_eq hx
  obtain ⟨A, B, C, hc, hA, hB, hC⟩ := split3 hL
  have hA' : A = vals vs := map_core_inj hA
  have hin : (⟨s, K, f, es⟩ : ConfigFX H) = ofCore ⟨s, f, B⟩ := by rw [ofCore_mk, hB, hK]
  obtain ⟨c₁, hstep, hy⟩ := ih ⟨s, f, B⟩ hin (hs ▸ hno)
  obtain ⟨hs₁, hK₁, hf₁, hes'⟩ := ofCore_eq hy
  have hcc : c = ⟨s, f, vals vs ++ B ++ C⟩ := by rw [config_eta c (hc.trans (by rw [hA'])), hs, hf]
  have hstep' : Step P (blockFX host fx) ⟨s, f, B⟩ ⟨c₁.store, c₁.frame, c₁.code⟩ := by
    cases c₁
    exact hstep
  refine ⟨⟨c₁.store, c₁.frame, vals vs ++ c₁.code ++ C⟩, hcc ▸ Step.ctxtInstrs hstep'
    (hne_map hC hne), ?_⟩
  show (⟨s', K', f', cvals vs ++ es' ++ rest⟩ : ConfigFX H) =
    ⟨c₁.store, [], c₁.frame, (vals vs ++ c₁.code ++ C).map .core⟩
  rw [hs₁, hK₁, hf₁, hes', ← hC]
  simp only [cvals, List.map_append]

/-- The `trapSeq` case: Core's `trap-instrs`. -/
theorem case_trapSeq {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
    {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val} {rest : List AdminFX}
    (hne : vs ≠ [] ∨ rest ≠ []) (c : Config H)
    (hx : (⟨s, K, f, cvals vs ++ [.core .trap] ++ rest⟩ : ConfigFX H) = ofCore c) :
    ∃ c', Step P (blockFX host fx) c c' ∧ (⟨s, K, f, [.core .trap]⟩ : ConfigFX H) = ofCore c' := by
  obtain ⟨hs, hK, hf, hL⟩ := ofCore_eq hx
  obtain ⟨A, B, C, hc, hA, hB, hC⟩ := split3 hL
  have hA' : A = vals vs := map_core_inj hA
  have hB' : B = [.trap] := map_core_inj (l' := [.trap]) hB
  have hcc : c = ⟨s, f, vals vs ++ [.trap] ++ C⟩ := by
    rw [config_eta c (hc.trans (by rw [hA', hB'])), hs, hf]
  refine ⟨⟨s, f, [.trap]⟩, hcc ▸ Step.trapInstrs (hne_map hC hne), ?_⟩
  rw [hK]
  rfl

/-- The `throwSeq` case: Core's `throw_ref-instrs`. -/
theorem case_throwSeq {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
    {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val} {a : Nat}
    {rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ []) (c : Config H)
    (hx : (⟨s, K, f, cvals vs ++ cthrowing a ++ rest⟩ : ConfigFX H) = ofCore c) :
    ∃ c', Step P (blockFX host fx) c c' ∧ (⟨s, K, f, cthrowing a⟩ : ConfigFX H) = ofCore c' := by
  obtain ⟨hs, hK, hf, hL⟩ := ofCore_eq hx
  obtain ⟨A, B, C, hc, hA, hB, hC⟩ := split3 hL
  have hA' : A = vals vs := map_core_inj hA
  have hB' : B = throwing a := map_core_inj hB
  have hcc : c = ⟨s, f, vals vs ++ throwing a ++ C⟩ := by
    rw [config_eta c (hc.trans (by rw [hA', hB'])), hs, hf]
  refine ⟨⟨s, f, throwing a⟩, hcc ▸ Step.throwRefInstrs (hne_map hC hne), ?_⟩
  rw [hK]
  rfl

/-- A configuration with a non-Core instruction is not a Core configuration. -/
theorem not_ofCore {x : ConfigFX H} (hx : x.code.all isCore = false) (c : Config H) :
    x ≠ ofCore c := by
  intro h
  have h2 : (ofCore c).code.all isCore = true := all_isCore_map _
  rw [← h, hx] at h2
  exact Bool.false_ne_true h2

/-- **An FX step from a Core configuration is a Core step.** -/
theorem step_ofCore {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
    {x y : ConfigFX H} (h : StepFX P host fx x y) :
    ∀ c : Config H, x = ofCore c → NoFX fx c.store →
      ∃ c', Step P (blockFX host fx) c c' ∧ y = ofCore c' := by
  induction h with
  | core h => exact fun c hx _ => case_core h c hx
  | seq _ hne ih => exact case_seq hne ih
  | trapSeq hne => exact fun c hx _ => case_trapSeq hne c hx
  | throwSeq hne => exact fun c hx _ => case_throwSeq hne c hx
  | @invoke s K f c₀ vs a fi h₀ F hc hf hcode hfx hn =>
    intro c hx hno
    have hs : s = c.store := (ofCore_eq hx).1
    have hnone : (none : Option FuncFX) = some F := (hno a fi h₀ (hs ▸ hf) hcode).symm.trans hfx
    exact absurd hnone (by simp)
  | _ => exact fun c hx _ => absurd hx (not_ofCore (by simp [isCore, cvals]) c)

/-- **Every Core step lifts to an FX step.** -/
theorem ofCore_step {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
    {c c' : Config H} (h : Step P (blockFX host fx) c c') :
    StepFX P host fx (ofCore c) (ofCore c') := by
  cases c
  cases c'
  exact StepFX.core h

/-- Without FX functions the Core host is unchanged. -/
theorem blockFX_noFX (host : HostSemantics H) : blockFX host (noFX (H := H)) = host := by
  funext h s vs out
  simp [blockFX, noFX]

theorem noFX_store (s : Store H) : NoFX noFX s := fun _ _ _ _ _ => rfl

end Silmaril.Proofs.Wasm.Models.FX
