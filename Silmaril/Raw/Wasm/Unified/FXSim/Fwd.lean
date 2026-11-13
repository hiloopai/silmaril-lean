module

public import Silmaril.Raw.Wasm.Unified.FXSim.Basic
public import Silmaril.Wasm.Models.FX.Thms

/-!
# CoreFX steps of FX code that reads as Core code are Core steps (unrefined)

`fwd`: a step of CoreFX without FX functions, from FX code that reads as Core code (`LiftAs`),
is one Core step of that Core code, to Core code that the result reads as. Every FX rule has a
Core twin on such code: `core` is the Core step itself, `seq`, `ctxLabel` and the structured
rules (`block`, `loop`, `if`, label values, `br`, `return`, traps and exceptions through FX
labels) are Core's rules on the corresponding Core forms. FX frames, handlers, stack-switching
instructions and continuation references do not read as Core code, and `invoke` needs an FX
function.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.Unified.FXSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Unified.Versions
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem liftAs_single_core (c : Admin) : LiftAs [.core c] [c] := .cons (.core c) .nil

theorem LiftAs.single_core {c : Admin} {cs : List Admin} (h : LiftAs [.core c] cs) : cs = [c] :=
  LiftAs.eq_of_map_core (cs₀ := [c]) h

theorem LiftAs.cvals_left {vs : List Val} {cs : List Admin} (h : LiftAs (cvals vs) cs) :
    cs = vals vs :=
  LiftAs.eq_of_map_core (cs₀ := vals vs) h

theorem LiftAs.cthrowing_left {a : Nat} {cs : List Admin} (h : LiftAs (cthrowing a) cs) :
    cs = throwing a :=
  LiftAs.eq_of_map_core (cs₀ := throwing a) h

/-- FX code that reads as Core code has only liftable instructions. -/
theorem LiftAs.not_mem {es : List AdminFX} {cs : List Admin} (h : LiftAs es cs) {a : AdminFX}
    (ha : a ∈ es) : ¬ Liftable a → False :=
  fun hn => hn (LiftAs.liftable h a ha)

set_option maxHeartbeats 1000000 in
/-- **A CoreFX step from FX code that reads as Core code is a Core step.** -/
theorem fwd {x y : ConfigFX H} (h : StepFX P host noFX x y) :
    ∀ cs, LiftAs x.code cs →
      ∃ cs', Step P host ⟨x.store, x.frame, cs⟩ ⟨y.store, y.frame, cs'⟩ ∧ LiftAs y.code cs' := by
  induction h with
  | @core s s' K f f' cs₀ cs₀' hc =>
    intro cs hl
    have hcs : cs = cs₀ := LiftAs.eq_of_map_core hl
    subst hcs
    rw [blockFX_noFX] at hc
    exact ⟨cs₀', hc, liftAs_map_core cs₀'⟩
  | @seq s s' K K' f f' vs es es' rest h' hne ih =>
    intro cs hl
    obtain ⟨AB, C, rfl, hAB, hC⟩ := LiftAs.append_left hl
    obtain ⟨A, B, rfl, hA, hB⟩ := LiftAs.append_left hAB
    have hA' : A = vals vs := LiftAs.cvals_left hA
    subst hA'
    obtain ⟨B', hst, hB'⟩ := ih B hB
    exact ⟨vals vs ++ B' ++ C, Step.ctxtInstrs hst (LiftAs.hne hC hne),
      LiftAs.append (LiftAs.append (liftAs_cvals vs) hB') hC⟩
  | @ctxLabel s s' K K' f f' n k es es' h' ih =>
    intro cs hl
    obtain ⟨c, rfl, hc⟩ := LiftAs.singleton_left hl
    cases hc with
    | label hk hes =>
      obtain ⟨cs', hst, hcs'⟩ := ih _ hes
      exact ⟨_, Step.ctxtLabel hst, .cons (.label hk hcs') .nil⟩
  | ctxFrame _ _ =>
    intro cs hl
    obtain ⟨c, -, hc⟩ := LiftAs.singleton_left hl
    cases hc
  | ctxHandler _ _ =>
    intro cs hl
    obtain ⟨c, -, hc⟩ := LiftAs.singleton_left hl
    cases hc
  | @block s K f bt body vs t₁ t₂ hbt hm =>
    intro cs hl
    obtain ⟨A, B, rfl, hA, hB⟩ := LiftAs.append_left hl
    have hA' : A = vals vs := LiftAs.cvals_left hA
    subst hA'
    obtain ⟨c, rfl, hc⟩ := LiftAs.singleton_left hB
    cases hc with
    | block hb =>
      exact ⟨_, Step.block hbt hm,
        .cons (.label .nil (LiftAs.append (liftAs_cvals vs) (LiftIs.toAdmin hb))) .nil⟩
  | @loop s K f bt body vs t₁ t₂ hbt hm =>
    intro cs hl
    obtain ⟨A, B, rfl, hA, hB⟩ := LiftAs.append_left hl
    have hA' : A = vals vs := LiftAs.cvals_left hA
    subst hA'
    obtain ⟨c, rfl, hc⟩ := LiftAs.singleton_left hB
    cases hc with
    | loop hb =>
      exact ⟨_, Step.loop hbt hm,
        .cons (.label (.cons (.loop hb) .nil)
          (LiftAs.append (liftAs_cvals vs) (LiftIs.toAdmin hb))) .nil⟩
  | @ifTrue s K f c bt b₁ b₂ hc =>
    intro cs hl
    cases hl with
    | cons ha ht =>
      cases ha
      obtain ⟨d, rfl, hd⟩ := LiftAs.singleton_left ht
      cases hd with
      | if_ h₁ h₂ => exact ⟨_, Step.ifTrue hc, .cons (.block h₁) .nil⟩
  | @ifFalse s K f bt b₁ b₂ =>
    intro cs hl
    cases hl with
    | cons ha ht =>
      cases ha
      obtain ⟨d, rfl, hd⟩ := LiftAs.singleton_left ht
      cases hd with
      | if_ h₁ h₂ => exact ⟨_, Step.ifFalse, .cons (.block h₂) .nil⟩
  | @labelVals s K f n k vs =>
    intro cs hl
    obtain ⟨c, rfl, hc⟩ := LiftAs.singleton_left hl
    cases hc with
    | label hk hes =>
      have he : _ = vals vs := LiftAs.cvals_left hes
      subst he
      exact ⟨_, Step.labelVals, liftAs_cvals vs⟩
  | @brLabelZero s K f n k vs' vs l rest hl0 hn =>
    intro cs hl
    obtain ⟨c, rfl, hc⟩ := LiftAs.singleton_left hl
    cases hc with
    | label hk hes =>
      obtain ⟨ABX, R, rfl, hABX, -⟩ := LiftAs.append_left hes
      obtain ⟨AB, X, rfl, hAB, hX⟩ := LiftAs.append_left hABX
      obtain ⟨A, B, rfl, hA, hB⟩ := LiftAs.append_left hAB
      rw [LiftAs.cvals_left hA, LiftAs.cvals_left hB, LiftAs.single_core hX]
      exact ⟨_, Step.brLabelZero hl0 hn, LiftAs.append (liftAs_cvals vs) (LiftIs.toAdmin hk)⟩
  | @brLabelSucc s K f n k vs l rest hl0 =>
    intro cs hl
    obtain ⟨c, rfl, hc⟩ := LiftAs.singleton_left hl
    cases hc with
    | label hk hes =>
      obtain ⟨AX, R, rfl, hAX, -⟩ := LiftAs.append_left hes
      obtain ⟨A, X, rfl, hA, hX⟩ := LiftAs.append_left hAX
      rw [LiftAs.cvals_left hA, LiftAs.single_core hX]
      exact ⟨_, Step.brLabelSucc hl0, LiftAs.append (liftAs_cvals vs) (liftAs_single_core _)⟩
  | @returnLabel s K f n k vs rest =>
    intro cs hl
    obtain ⟨c, rfl, hc⟩ := LiftAs.singleton_left hl
    cases hc with
    | label hk hes =>
      obtain ⟨AX, R, rfl, hAX, -⟩ := LiftAs.append_left hes
      obtain ⟨A, X, rfl, hA, hX⟩ := LiftAs.append_left hAX
      rw [LiftAs.cvals_left hA, LiftAs.single_core hX]
      exact ⟨_, Step.returnLabel, LiftAs.append (liftAs_cvals vs) (liftAs_single_core _)⟩
  | @trapSeq s K f vs rest hne =>
    intro cs hl
    obtain ⟨AX, C, rfl, hAX, hC⟩ := LiftAs.append_left hl
    obtain ⟨A, X, rfl, hA, hX⟩ := LiftAs.append_left hAX
    rw [LiftAs.cvals_left hA, LiftAs.single_core hX]
    exact ⟨_, Step.trapInstrs (LiftAs.hne hC hne), liftAs_single_core _⟩
  | @trapLabel s K f n k =>
    intro cs hl
    obtain ⟨c, rfl, hc⟩ := LiftAs.singleton_left hl
    cases hc with
    | label hk hes =>
      rw [LiftAs.single_core hes]
      exact ⟨_, Step.trapLabel, liftAs_single_core _⟩
  | @throwSeq s K f vs a rest hne =>
    intro cs hl
    obtain ⟨AX, C, rfl, hAX, hC⟩ := LiftAs.append_left hl
    obtain ⟨A, X, rfl, hA, hX⟩ := LiftAs.append_left hAX
    rw [LiftAs.cvals_left hA, LiftAs.cthrowing_left hX]
    exact ⟨_, Step.throwRefInstrs (LiftAs.hne hC hne), liftAs_map_core _⟩
  | @throwLabel s K f n k a =>
    intro cs hl
    obtain ⟨c, rfl, hc⟩ := LiftAs.singleton_left hl
    cases hc with
    | label hk hes =>
      rw [LiftAs.cthrowing_left hes]
      exact ⟨_, Step.throwRefLabel, liftAs_map_core _⟩
  | invoke _ _ _ hfx _ =>
    intro cs _
    exact absurd hfx (by simp [noFX])
  | _ =>
    intro cs hl
    exfalso
    first
      | (apply LiftAs.not_mem hl
          (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
         exact id)
      | (apply LiftAs.not_mem hl (List.mem_cons_of_mem _ (List.mem_singleton_self _))
         exact id)
      | (apply LiftAs.not_mem hl (List.mem_singleton_self _)
         exact id)

end Silmaril.Raw.Wasm.Unified.FXSim
