module

public import Silmaril.Proofs.Wasm.Resource.ExternClient.TightStep

/-!
# The `externref` client invariant of a thread

* `Step.clientU`: `Step.client` (`Silmaril.Wasm.Resource.Client`) with a reachability invariant
  whose set `G` contains the host functions of the three imports. A call of one of them is a
  `BadStep`; every other step keeps `CPost`. The proof follows `Step.client`, rule by rule.
* `okA_gl`: without handle pairs the check depends on no global (`C.ps = []`).
* `InvU`: the reachability invariant at `G` (`CallPl R bad fs`), `Tight R`, sound facts and the
  check of the code. `GuardedU`: a thread stopped at a call of one of the three imports, prepared
  for every answer in every store keeping the instance.
* **`step_invU`**: one host-free step from an invariant thread, in a store keeping the instance.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.ExternClient

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Resource Silmaril.Wasm.Resource.Client
  Silmaril.Wasm.Resource.ExternExamples
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (CfgIn CodeIn FrameIn StoreIn RefIn PlOK PlainOK CallPl BadStep FuncsClosed
  Avoids refFuncs isHost callPl_plainOK hostIn_noHost)

/-! ## `Step.client` with the imports in the reachable set -/

section Fork
variable {H : Type} {C : Cfg}

attribute [-simp] Silmaril.Wasm.Logic.Hoare.toAdmin_i32

/-- A `call` that is not a call of the three imports. -/
theorem post_callU {G : Nat → Prop} {fs : List Nat} {Pl : Instr → Prop} {bad : Nat → Bool}
    {L : List Val} {s : Store H} {f₀ : Frame} {x : FuncIdx} {a : Nat} {d : DefType}
    (hfs : C.fs = fs)
    (hG : ∀ a, G a → bad a = false → C.isU a = false ∧ C.isF a = false ∧ C.isA a = false)
    (hx : f₀.module.funcs[x.toNat]? = some a) (hc : CfgIn G fs Pl ⟨s, f₀, [.plain (.call x)]⟩)
    (hc' : CfgIn G fs Pl ⟨s, f₀, [.ref (.func a), .callRefType d]⟩)
    (hnb : ¬ BadStep (fun a => bad a = true) fs (⟨s, f₀, [.plain (.call x)]⟩ : Config H)
      ⟨s, f₀, [.ref (.func a), .callRefType d]⟩) :
    CPost C L L (⟨s, f₀, [.plain (.call x)]⟩ : Config H) ⟨s, f₀, [.ref (.func a), .callRefType d]⟩ := by
  have ha : G a := by simpa [refFuncs] using hc'.2.2.ref_of_mem (r := .func a) (by simp)
  have hx' : fs[x.toNat]? = some a := hc.2.1.resolve hx
  have hb : bad a = false := by
    cases hb : bad a
    · rfl
    · exact absurd ⟨.top [] [], x, a, d, by simp [Ctx.fill, vals], by simp [Ctx.fill, vals], hx',
        hb⟩ hnb
  exact post_call (hfs ▸ hx') (hG a ha hb)

set_option linter.unusedTactic false in
/-- **Every host-free Core 3.0 step other than a call of the three imports keeps the client
invariant** (every profile), when the reachability invariant holds before and after the step and
the functions of `G` outside `bad` are not the three imports. -/
theorem Step.clientU {G : Nat → Prop} {fs : List Nat} {Pl : Instr → Prop} {bad : Nat → Bool}
    {P : Profile} {L : List Val} {c c' : Config H}
    (h : Step P (fun _ _ _ _ => False) c c') (hP : PairsOK C.ps) (hfs : C.fs = fs)
    (hG : ∀ a, G a → bad a = false → C.isU a = false ∧ C.isF a = false ∧ C.isA a = false) :
    CfgIn G fs Pl c → CfgIn G fs Pl c' → BodiesC G C c.store.funcs →
      ¬ BadStep (fun a => bad a = true) fs c c' → CPost C L L c c' := by
  induction h with
  | parametric h => exact fun _ _ _ _ => ParametricStep.client h
  | numeric h => exact fun _ _ _ _ => NumericStep.client h
  | vector h => exact fun _ _ _ _ => VectorStep.client h
  | «variable» h =>
    intro _ _ _ _
    cases h with
    | localGet hx => exact post_localGet hx
    | localSet hx => exact post_localSet hx
    | localTee => exact post_localTee
    | globalGet hx => exact post_globalGet hx
    | globalSet hx => exact post_globalSet hP hx
  | table h => exact fun _ _ _ _ => TableStep.client h
  | memory h => exact fun _ _ _ _ => MemoryStep.client h
  | reference h => exact fun _ _ _ _ => RefStep.client h
  | aggregate h => exact fun _ _ _ _ => AggregateStep.client h
  | ctxtInstrs _ _ ih =>
    intro hc hc' hbf hnb
    exact post_ctxtInstrs (ih ⟨hc.1, hc.2.1, (CodeIn.append.1 (CodeIn.append.1 hc.2.2).1).2⟩
      ⟨hc'.1, hc'.2.1, (CodeIn.append.1 (CodeIn.append.1 hc'.2.2).1).2⟩ hbf
      (fun hb => hnb (BadStep.ctxtInstrs hb)))
  | ctxtLabel hst ih =>
    intro hc hc' hbf hnb
    exact post_ctxtLabel (ih ⟨hc.1, hc.2.1, (CodeIn.label_iff.1 hc.2.2).2⟩
      ⟨hc'.1, hc'.2.1, (CodeIn.label_iff.1 hc'.2.2).2⟩ hbf (fun hb => hnb (BadStep.ctxtLabel hb)))
      (congrArg ModuleInst.globals (Step.module_eq hst))
  | ctxtHandler hst ih =>
    intro hc hc' hbf hnb
    exact post_ctxtHandler (ih ⟨hc.1, hc.2.1, CodeIn.handler_iff.1 hc.2.2⟩
      ⟨hc'.1, hc'.2.1, CodeIn.handler_iff.1 hc'.2.2⟩ hbf (fun hb => hnb (BadStep.ctxtHandler hb)))
      (congrArg ModuleInst.globals (Step.module_eq hst))
  | ctxtFrame _ ih =>
    intro hc hc' hbf hnb
    exact post_ctxtFrame
      (ih ⟨hc.1, (CodeIn.frame_iff.1 hc.2.2).1, (CodeIn.frame_iff.1 hc.2.2).2⟩
        ⟨hc'.1, (CodeIn.frame_iff.1 hc'.2.2).1, (CodeIn.frame_iff.1 hc'.2.2).2⟩ hbf
        (fun hb => hnb (BadStep.ctxtFrame hb)))
  | block => exact fun _ _ _ _ => post_block
  | loop => exact fun _ _ _ _ => post_loop
  | tryTable => exact fun _ _ _ _ => post_tryTable
  | ifTrue hc₀ => exact fun _ _ _ _ => post_ifTrue hc₀
  | ifFalse => exact fun _ _ _ _ => post_ifFalse
  | brLabelZero => exact fun _ _ _ _ => post_brLabelZero
  | call hx _ => exact fun hc hc' _ hnb => post_callU hfs hG hx hc hc' hnb
  | @callRefFunc _ _ _ _ a _ _ _ _ hcr hf _ _ hcode =>
    intro hc _ hbf _
    have ha : G a := by simpa [refFuncs] using hc.2.2.ref_of_mem (r := .func a) (by simp)
    exact post_callRefFunc hcr (hbf _ _ _ ha hf hcode)
  | callRefHost _ _ _ _ _ hhost => exact hhost.elim
  | callRefHostDiv _ _ _ _ _ hhost => exact hhost.elim
  | returnCall => exact fun _ _ _ _ => post_returnCall
  | throw => exact fun _ _ _ _ => post_throwingR rfl _
  | throwRefInstrs => exact fun _ _ _ _ => post_throwingR rfl _
  | throwRefLabel => exact fun _ _ _ _ => post_throwingR rfl _
  | throwRefFrame => exact fun _ _ _ _ => post_throwingR rfl _
  | throwRefHandlerEmpty => exact fun _ _ _ _ => post_throwingR rfl _
  | throwRefHandlerNext => exact fun _ _ _ _ => post_handlerNext
  | returnCallRefLabel hcr =>
    exact fun _ _ _ _ => post_kill rfl rfl rfl (killP_nest trivial)
      (freeP_vals (by simp [vals]) (freeP_retCallRef hcr))
  | returnCallRefHandler hcr =>
    exact fun _ _ _ _ => post_kill rfl rfl rfl (killP_nest trivial)
      (freeP_vals (by simp [vals]) (freeP_retCallRef hcr))
  | returnCallRefFrameAddr hcr =>
    exact fun _ _ _ _ => post_kill rfl rfl rfl (killP_nest trivial) (freeP_vals (by simp [vals])
      (freeP_vals (V := [.ref (.func _)]) (by simp) (freeP_retToCallIn _ hcr)))
  | callIndirect =>
    exact fun _ _ _ _ => post_kill rfl rfl rfl (killP_plain rfl fun _ _ _ => rfl)
      (freeP_of_free (by verify_mem_split; all_goals client_free_one))
  | returnCallIndirect =>
    exact fun _ _ _ _ => post_kill rfl rfl rfl (killP_plain rfl fun _ _ _ => rfl)
      (freeP_of_free (by verify_mem_split; all_goals client_free_one))
  | _ =>
    intro _ _ _ _
    first
      | (exact post_trapR rfl; done)
      | (client_keep_tac; done)
      | (client_nest_tac; done)

end Fork

/-! ## No handle pairs: the check depends on no global -/

section Globals
variable {C : Cfg} {L : List Val} {gl gl' : List GlobalInst}

theorem Ab_gl (hps : C.ps = []) {t : CTop} {v : Val} (h : Ab C.ps L gl t v) :
    Ab C.ps L gl' t v := by
  cases t with
  | flag k => obtain ⟨p, hp, -⟩ := h; simp [hps] at hp
  | fr => exact ⟨h.1, fun p hp => by simp [hps] at hp⟩
  | _ => exact h

theorem soundF_gl (hps : C.ps = []) {lc : List (Option Val)} {F : List Fact}
    (h : SoundF C.ps L gl lc F) : SoundF C.ps L gl' lc F :=
  soundF_congr (fun q hq => by simp [hps] at hq) h

mutual

theorem okX_gl (hps : C.ps = []) : ∀ {gs : List Nat} {lc : List (Option Val)} (x : Admin),
    okX C L gl gs lc x → okX C L gl' gs lc x
  | _, _, .label n k b, h => by
    rw [okX_label] at h ⊢
    obtain ⟨hk, F, hF, hb⟩ := h
    exact ⟨hk, F, soundF_gl hps hF, okA_gl hps b hb⟩
  | _, _, .handler n cs b, h => by
    rw [okX_handler] at h ⊢
    obtain ⟨F, hF, hb⟩ := h
    exact ⟨F, soundF_gl hps hF, okA_gl hps b hb⟩
  | _, _, .frame n fr b, h => by
    rw [okX_frame] at h ⊢
    obtain ⟨F, hF, hb⟩ := h
    exact ⟨F, soundF_gl hps hF, okA_gl hps b hb⟩
  | _, _, .plain _, _ | _, _, .ref _, _ | _, _, .trap, _ | _, _, .callRefType _, _
  | _, _, .returnCallRefType _, _ => by simp [okX]

theorem okA_gl (hps : C.ps = []) : ∀ {gs : List Nat} {lc : List (Option Val)} {st : CSt}
    (l : List Admin), okA C L gl gs lc st l → okA C L gl' gs lc st l
  | _, _, _, [], _ => trivial
  | gs, lc, st, x :: l, h => by
    simp only [okA] at h ⊢
    rcases h with h | ⟨v, hv, hp, t, hab, h⟩ | ⟨hnv, h⟩
    · exact .inl h
    · exact .inr (.inl ⟨v, hv, hp, t, Ab_gl hps hab, okA_gl hps l h⟩)
    · refine .inr (.inr ⟨hnv, ?_⟩)
      rcases h with ⟨i, hi, hok, h⟩ | ⟨r, hr, h⟩ | h | ⟨hn, hp, hx, h⟩
      · exact .inl ⟨i, hi, hok, okA_gl hps l h⟩
      · exact .inr (.inl ⟨r, hr, okA_gl hps l h⟩)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr ⟨hn, hp, okX_gl hps x hx, okA_gl hps l h⟩))

end

end Globals

end Silmaril.Wasm.Resource.ExternClient
