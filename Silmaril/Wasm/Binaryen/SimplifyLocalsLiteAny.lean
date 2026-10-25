module

public import Silmaril.Wasm.Binaryen.SimplifyLocalsLiteMacro
public import Silmaril.Wasm.Execution.Core.Sim.TeeRank

@[expose] public section

/-! # Full tee/drop pass equivalence for every numerical profile

The reverse simulation retains the tee expansion as an explicit phase. Its first
step stutters using a payload-independent rank; both local stores then step to
the same frame, and the trailing drop stutters. The generic closure lifts these
phases through contexts, calls, instantiation and sessions of module exports.
-/

namespace Silmaril.Wasm.Binaryen.SimplifyLocalsLite

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Runtime phases of the reverse simulation, with the tee on the left. -/
inductive tdReverseB : List Admin → List Admin → Prop where
  | tee (x : LocalIdx) : tdReverseB [.plain (.localTee x), .plain .drop] [.plain (.localSet x)]
  | expanded (v : Val) (x : LocalIdx) :
      tdReverseB [v.toAdmin, v.toAdmin, .plain (.localSet x), .plain .drop]
        [v.toAdmin, .plain (.localSet x)]
  | drop (v : Val) : tdReverseB [v.toAdmin, .plain .drop] []

/-- The full reverse base simulation, using a rank that pays for tee expansion. -/
theorem tdReverseBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P host F (fun a b => tdBI b a) tdReverseB teeCodeRank where
  src := by
    rintro _ _ ⟨x, rfl, rfl⟩
    exact .tee x
  step := by
    intro s t s' f f' vs a b rest rest' es' hst hab hrest hstep
    cases hab with
    | tee x =>
      have h' : Step P host ⟨s, f, vals vs ++ .plain (.localTee x) :: (.plain .drop :: rest)⟩
          ⟨s', f', es'⟩ := by simpa [List.append_assoc] using hstep
      obtain ⟨pre, args, cfg, hV, hh, hc⟩ := inert_head_inv rfl (by simp) rfl h'
      obtain ⟨v, rfl, rfl⟩ := head_localTee hh
      simp only [Config.mk.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      subst hV
      refine ⟨t, vals (pre ++ [v]) ++ [.plain (.localSet x)] ++ rest',
        Or.inr ⟨rfl, rfl, rfl, ?_⟩, hst, ?_⟩
      · have h := LawfulCodeRank.context_lt (rank := teeCodeRank) (vals pre)
          (.plain .drop :: rest) (teeCodeRank_expand v x)
        simpa [vals, List.append_assoc] using h
      · simpa [vals, List.append_assoc] using
          ((AdminsRel.refl (vals pre)).append (AdminsRel.base (.expanded v x))).append hrest
    | expanded v x =>
      have h' : Step P host
          ⟨s, f, vals (vs ++ [v, v]) ++ .plain (.localSet x) :: (.plain .drop :: rest)⟩
          ⟨s', f', es'⟩ := by simpa [vals, List.append_assoc] using hstep
      obtain ⟨pre, args, cfg, hV, hh, hc⟩ := inert_head_inv rfl (by simp) rfl h'
      obtain ⟨w, rfl, hx, rfl⟩ := head_localSet hh
      have hV' : (vs ++ [v]) ++ [v] = pre ++ [w] := by simpa using hV
      obtain ⟨rfl, rfl⟩ := Det.append_singleton_inj.mp hV'
      simp only [Config.mk.injEq, List.append_nil] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      refine ⟨t, vals vs ++ rest', Or.inl (.single ?_), hst, ?_⟩
      · simpa using Step.append_right (Step.vals_left
          (Step.variable (P := P) (host := host) (VariableStep.localSet (v := v) hx)) vs) rest'
      · simpa [vals, List.append_assoc] using
          ((AdminsRel.refl (vals vs)).append (AdminsRel.base (.drop v))).append hrest
    | drop v =>
      have hc := drop_step_unique hstep
      simp only [Config.mk.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      refine ⟨t, vals vs ++ rest', Or.inr ⟨rfl, rfl, by simp, ?_⟩, hst,
        (AdminsRel.refl (vals vs)).append hrest⟩
      exact LawfulCodeRank.infix_lt (vals vs) [v.toAdmin, .plain .drop] rest (by simp)
  exit := by
    intro s t f vs us a b k j hst hab hk he
    exfalso
    cases hab with
    | tee x =>
      exact GuardSim.not_exit (W := vs) (e₀ := .plain (.localTee x))
        rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
        (by simpa using he)
    | expanded v x =>
      exact GuardSim.not_exit (W := vs ++ [v, v]) (e₀ := .plain (.localSet x))
        rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
        (by simpa [vals, List.append_assoc] using he)
    | drop v =>
      exact GuardSim.not_exit (W := vs ++ [v]) (e₀ := .plain .drop)
        rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
        (by simpa [vals, List.append_assoc] using he)
  values := by
    intro s t f vs us a b hst hab ha
    exfalso
    have hall := congrArg (fun es => es.all Admin.isVal) ha
    cases hab <;> simp [Admin.isVal, Admin.val?] at hall

/-- The original module refines the rewritten module for the same arbitrary profile. -/
theorem teeDrop_reverse_refines {m : BModule} (hm : m.Ok) (host : HostSemantics H)
    (hhost : HostRespects (FuncRel (fun a b => tdBI b a)) host) :
    ExportRefines (· = ·) P host m.lower (teeDrop m).lower :=
  exportRefines_of_bodiesRel tdReverseBaseSim hhost (teeDrop_bodiesRel m).flip hm (teeDrop_ok hm)

/-- Full tee/drop module equivalence for any profile and a code-parametric host. -/
theorem teeDrop_sound_parametric {m : BModule} (hm : m.Ok) (host : HostSemantics H)
    (hhost : HostParametric host) :
    ExportEquiv (· = ·) P host (teeDrop m).lower m.lower :=
  ⟨teeDrop_refines hm host (hhost.respects (fun f => FuncRel.refl f)),
    (teeDrop_reverse_refines hm host (hhost.respects (fun f => FuncRel.refl f))).mono
      (fun _ _ h => h.symm)⟩

/-- Full tee/drop module equivalence under the closed host, with no numerical restriction. -/
theorem teeDrop_sound_any {m : BModule} (hm : m.Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (teeDrop m).lower m.lower :=
  ⟨teeDrop_refines hm _ (closedHost_respects _),
    (teeDrop_reverse_refines hm _ (closedHost_respects _)).mono fun _ _ h => h.symm⟩

end Silmaril.Wasm.Binaryen.SimplifyLocalsLite
