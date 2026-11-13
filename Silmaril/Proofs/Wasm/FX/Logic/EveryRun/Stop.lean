module

public import Silmaril.Proofs.Wasm.FX.Logic.EveryRun.Ctx

/-!
# Stopped code and the codes that end a run

* the outcome of stopped code is read off the code: `stops_fvals`, `stops_br`, `stops_ret`,
  `stops_trapish`, `stops_throwish`, and `not_stops` for code whose first non-value cannot
  stop (`NotStop`); `stops_wrap`: a label, frame or handler under values stops only with an
  effect from its body;
* the codes that end a run do not step (`no_step_blocked`: a branch or `return` at the top), or
  step only towards a bare `trap` or exception, keeping the store and the frame
  (`step_trapish`, `step_throwish`, from silmaril-lean's `Sim.Step.trap_redex_aux` and
  `Sim.Step.throwRef_redex_aux`);
* safety of such codes from their postcondition: `tsafe_vals`, `tsafe_br`, `tsafe_ret`,
  `tsafe_trap`, `tsafe_throw` and the step-indexed `safe_*`, through the closure lemmas
  `tsafe_closed` and `safe_closed`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Logic.EveryRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts)
open Silmaril.Wasm.FX.Logic.EveryRun (Unhandled suspCode switchCode Stops Safe TSafe)
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval? fnvF fnvF_fvals_append fnvF_cons_none
  fvals_append_cons_inj fvals_inj no_step_fvals')
open Silmaril.Proofs.Wasm.Models.FXAsyncSus (canon Wrp)
open Silmaril.Proofs.Wasm.Models.FXAsyncBack (IsWrap)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

/-! ## Shapes -/

theorem fvals_ne_cons {V W : List FVal} {a : AdminFX} {R : List AdminFX} (ha : fval? a = none) :
    fvals V ≠ fvals W ++ a :: R := by
  intro h
  have h1 := congrArg (fun l => (fnvF l).2) h
  simp [fnvF_fvals_append, fnvF_cons_none ha] at h1

theorem trap_eq : ([.core .trap] : List AdminFX) = fvals [] ++ .core .trap :: [] := rfl

theorem cthrowing_eq (b : Nat) :
    cthrowing b = fvals [.val (.ref (.exn b))] ++ .core (.plain .throwRef) :: [] := rfl

theorem cthrowing_app (ws : List FVal) (b : Nat) (r : List AdminFX) :
    fvals ws ++ cthrowing b ++ r = fvals (ws ++ [.val (.ref (.exn b))]) ++ .core (.plain .throwRef) :: r := by
  simp [cthrowing, throwing, FVal.toAdmin, Val.toAdmin]

/-- A wrapper around a context. -/
def wrpCtx : Wrp → CtxV → CtxV
  | .label n k, E => .label n k E
  | .frame n f, E => .frame n f E
  | .handler hs, E => .handler hs E

theorem wrpCtx_plug (w : Wrp) (E : CtxV) (c : List AdminFX) :
    (wrpCtx w E).plug c = [w.wrap (E.plug c)] := by
  cases w <;> rfl

/-- An instruction that is not a final form of any outcome. -/
def NotStop (a : AdminFX) : Prop :=
  fval? a = none ∧ ¬ IsWrap a ∧ (∀ x, a ≠ .core (.plain (.br x))) ∧ a ≠ .core (.plain .return_) ∧
    a ≠ .core .trap ∧ a ≠ .core (.plain .throwRef) ∧ (∀ x, a ≠ .fx (.suspend x)) ∧
    ∀ ct x, a ≠ .fx (.switch ct x)

/-! ## The outcome of stopped code -/

section Stops

variable {s : Store H} {f : Frame}

theorem not_stops {a : AdminFX} (h : NotStop a) {o : OutcomeFX} {V : List FVal}
    {R : List AdminFX} : ¬ Stops s f o (fvals V ++ a :: R) := by
  intro hs
  obtain ⟨ha, hw, hbr, hret, htr, hth, hsu, hsw⟩ := h
  cases o with
  | normal vs => exact fvals_ne_cons ha (Eq.symm hs)
  | br l vs =>
    obtain ⟨x, rest, -, hc⟩ := hs
    exact hbr x (fvals_append_cons_inj hc ha rfl).2.1
  | ret vs =>
    obtain ⟨rest, hc⟩ := hs
    exact hret (fvals_append_cons_inj hc ha rfl).2.1
  | trap => exact htr (fvals_append_cons_inj (Eq.trans hs trap_eq) ha rfl).2.1
  | throw b => exact hth (fvals_append_cons_inj (Eq.trans hs (cthrowing_eq b)) ha rfl).2.1
  | susp E vs x => exact (plug_focus (e := .fx (.suspend x)) rfl ha hs.1.symm).elim (hsu x) hw
  | swtch E vs k ct x =>
    have h1 : E.plug (fvals (vs ++ [.cont k]) ++ [.fx (.switch ct x)]) = fvals V ++ a :: R := by
      rw [← switchCode_eq]; exact hs.1.symm
    exact (plug_focus rfl ha h1).elim (hsw ct x) hw

theorem stops_fvals {o : OutcomeFX} {V : List FVal} (hs : Stops s f o (fvals V)) :
    o = .normal V := by
  cases o with
  | normal vs => exact congrArg OutcomeFX.normal (fvals_inj hs).symm
  | br l vs => obtain ⟨x, rest, -, hc⟩ := hs; exact absurd hc (fvals_ne_cons rfl)
  | ret vs => obtain ⟨rest, hc⟩ := hs; exact absurd hc (fvals_ne_cons rfl)
  | trap => exact absurd (Eq.trans hs trap_eq) (fvals_ne_cons rfl)
  | throw b => exact absurd (Eq.trans hs (cthrowing_eq b)) (fvals_ne_cons rfl)
  | susp E vs x => exact absurd hs.1.symm (plug_ne_fvals (e := .fx (.suspend x)) rfl E V)
  | swtch E vs k ct x =>
    have h1 := hs.1.symm
    rw [switchCode_eq] at h1
    exact absurd h1 (plug_ne_fvals rfl E V)

/-- What stopped code with first non-value `a` says about its outcome. -/
def FocusOf : OutcomeFX → List FVal → AdminFX → List AdminFX → Prop
  | .normal _, _, _, _ => False
  | .br l vs, V, a, _ => vs = V ∧ ∃ x : LabelIdx, x.toNat = l ∧ a = .core (.plain (.br x))
  | .ret vs, V, a, _ => vs = V ∧ a = .core (.plain .return_)
  | .trap, V, a, R => V = [] ∧ a = .core .trap ∧ R = []
  | .throw b, V, a, R => V = [.val (.ref (.exn b))] ∧ a = .core (.plain .throwRef) ∧ R = []
  | .susp _ _ x, _, a, _ => a = .fx (.suspend x) ∨ IsWrap a
  | .swtch _ _ _ ct x, _, a, _ => a = .fx (.switch ct x) ∨ IsWrap a

theorem stops_focus {o : OutcomeFX} {V : List FVal} {a : AdminFX} {R : List AdminFX}
    (ha : fval? a = none) (hs : Stops s f o (fvals V ++ a :: R)) : FocusOf o V a R := by
  cases o with
  | normal vs => exact fvals_ne_cons ha (Eq.symm hs)
  | br l vs =>
    obtain ⟨x, rest, hx, hc⟩ := hs
    obtain ⟨h1, h2, -⟩ := fvals_append_cons_inj hc ha rfl
    exact ⟨h1.symm, x, hx, h2⟩
  | ret vs =>
    obtain ⟨rest, hc⟩ := hs
    obtain ⟨h1, h2, -⟩ := fvals_append_cons_inj hc ha rfl
    exact ⟨h1.symm, h2⟩
  | trap => exact fvals_append_cons_inj (Eq.trans hs trap_eq) ha rfl
  | throw b => exact fvals_append_cons_inj (Eq.trans hs (cthrowing_eq b)) ha rfl
  | susp E vs x => exact plug_focus (e := .fx (.suspend x)) rfl ha hs.1.symm
  | swtch E vs k ct x =>
    have h1 : E.plug (fvals (vs ++ [.cont k]) ++ [.fx (.switch ct x)]) = fvals V ++ a :: R := by
      rw [← switchCode_eq]; exact hs.1.symm
    exact plug_focus rfl ha h1

theorem stops_br {o : OutcomeFX} {V : List FVal} {x : LabelIdx} {R : List AdminFX}
    (hs : Stops s f o (fvals V ++ .core (.plain (.br x)) :: R)) : o = .br x.toNat V := by
  have h := stops_focus rfl hs
  cases o <;> simp_all [FocusOf, IsWrap]

theorem stops_ret {o : OutcomeFX} {V : List FVal} {R : List AdminFX}
    (hs : Stops s f o (fvals V ++ .core (.plain .return_) :: R)) : o = .ret V := by
  have h := stops_focus rfl hs
  cases o <;> simp_all [FocusOf, IsWrap]

theorem stops_trapish {o : OutcomeFX} {V : List FVal} {R : List AdminFX}
    (hs : Stops s f o (fvals V ++ .core .trap :: R)) : o = .trap := by
  have h := stops_focus rfl hs
  cases o <;> simp_all [FocusOf, IsWrap]

theorem stops_throwish {o : OutcomeFX} {V : List FVal} {b : Nat} {R : List AdminFX}
    (hs : Stops s f o (fvals V ++ cthrowing b ++ R)) : o = .throw b := by
  rw [cthrowing_app] at hs
  have h := stops_focus rfl hs
  cases o with
  | throw a =>
    have h1 : V ++ [.val (.ref (.exn b))] = [] ++ [.val (.ref (.exn a))] := h.1
    have h2 : FVal.val (.ref (.exn b)) = .val (.ref (.exn a)) :=
      List.singleton_inj.mp (List.append_inj' h1 rfl).2
    have h3 : b = a := by simpa using h2
    rw [h3]
  | _ => simp_all [FocusOf, IsWrap]

/-- The `suspend` arm of `stops_wrap`. -/
theorem wrap_susp {us : List FVal} {w : Wrp} {b : List AdminFX} {E : CtxV} {vs : List FVal}
    {x : TagIdx} (h : fvals us ++ [w.wrap b] = E.plug (suspCode vs x)) :
    ∃ E' : CtxV, b = E'.plug (suspCode vs x) ∧ canon E = canon (.seq us (wrpCtx w E') []) := by
  obtain ⟨E₀, h₀⟩ := plug_vals_wrp_inv (e := .fx (.suspend x)) rfl id E (wrap_isWrap w b) h.symm
  obtain ⟨E', hE'⟩ := plug_wrp_inv (e := .fx (.suspend x)) rfl id E₀ h₀.symm
  have hp : (CtxV.seq us (wrpCtx w E') []).plug (suspCode vs x) = fvals us ++ [w.wrap b] := by
    rw [hE']; simp [CtxV.plug, wrpCtx_plug, suspCode]
  exact ⟨E', hE', canon_of_susp (h.symm.trans hp.symm)⟩

/-- The `switch` arm of `stops_wrap`. -/
theorem wrap_swtch {us : List FVal} {w : Wrp} {b : List AdminFX} {E : CtxV} {vs : List FVal}
    {k : Nat} {ct : TypeIdx} {x : TagIdx} (h : fvals us ++ [w.wrap b] = E.plug (switchCode vs k ct x)) :
    ∃ E' : CtxV, b = E'.plug (switchCode vs k ct x) ∧ canon E = canon (.seq us (wrpCtx w E') []) := by
  have h1 : E.plug (fvals (vs ++ [.cont k]) ++ [.fx (.switch ct x)]) = fvals us ++ [w.wrap b] := by
    rw [← switchCode_eq]; exact h.symm
  obtain ⟨E₀, h₀⟩ := plug_vals_wrp_inv rfl id E (wrap_isWrap w b) h1
  obtain ⟨E', hE'⟩ := plug_wrp_inv rfl id E₀ h₀.symm
  have hp : (CtxV.seq us (wrpCtx w E') []).plug (switchCode vs k ct x) = fvals us ++ [w.wrap b] := by
    rw [switchCode_eq, hE']; simp [CtxV.plug, wrpCtx_plug]
  exact ⟨E', by rw [switchCode_eq]; exact hE', canon_of_switch (h.symm.trans hp.symm)⟩

/-- **A wrapper under values stops only with an effect of its body.** -/
theorem stops_wrap {o : OutcomeFX} {us : List FVal} {w : Wrp} {b : List AdminFX}
    (hs : Stops s f o (fvals us ++ [w.wrap b])) :
    (∃ E vs x, o = .susp E vs x ∧ Unhandled s f E x ∧ ∃ E' : CtxV,
      b = E'.plug (suspCode vs x) ∧ canon E = canon (.seq us (wrpCtx w E') [])) ∨
    (∃ E vs k ct x, o = .swtch E vs k ct x ∧ Unhandled s f E x ∧ ∃ E' : CtxV,
      b = E'.plug (switchCode vs k ct x) ∧ canon E = canon (.seq us (wrpCtx w E') [])) := by
  have hfoc := stops_focus (wrap_fval w b) hs
  cases o with
  | susp E vs x => exact Or.inl ⟨E, vs, x, rfl, hs.2, wrap_susp hs.1⟩
  | swtch E vs k ct x => exact Or.inr ⟨E, vs, k, ct, x, rfl, hs.2, wrap_swtch hs.1⟩
  | _ => cases w <;> simp_all [FocusOf, Wrp.wrap]

end Stops

/-! ## Codes that end a run -/

section Ends

variable {s : Store H} {K : Conts} {f : Frame}

theorem blocked_not_trap : ¬ Silmaril.Wasm.SingleThreaded.Det.Blocked .trap := by
  simp [Silmaril.Wasm.SingleThreaded.Det.Blocked, Admin.IsReturnCallRef]

theorem blocked_not_throwRef : ¬ Silmaril.Wasm.SingleThreaded.Det.Blocked (.plain .throwRef) := by
  simp [Silmaril.Wasm.SingleThreaded.Det.Blocked, Admin.IsReturnCallRef]

theorem blocked_not_drop : ¬ Silmaril.Wasm.SingleThreaded.Det.Blocked (.plain .drop) := by
  simp [Silmaril.Wasm.SingleThreaded.Det.Blocked, Admin.IsReturnCallRef]

theorem root_blocked {V : List FVal} {e : Admin} {y : ConfigFX H}
    (he : Silmaril.Wasm.SingleThreaded.Det.Blocked e) (hc : ¬ e.IsCallRef)
    (hr : Root P fx s K f V (.core e) y) : False := by
  cases hr with
  | core h => exact Silmaril.Wasm.Logic.Hoare.not_step_blocked (rest := []) he h
  | dropCont => exact blocked_not_drop he
  | trapSeq => exact blocked_not_trap he
  | throwSeq => exact blocked_not_throwRef he
  | invoke hc' => exact hc hc'

/-- **A branch or `return` at the top does not step.** -/
theorem no_step_blocked {V : List FVal} {e : Admin} {R : List AdminFX} {y : ConfigFX H}
    (he : Silmaril.Wasm.SingleThreaded.Det.Blocked e) (hc : ¬ e.IsCallRef)
    (h : StepFX' P noHost fx ⟨s, K, f, fvals V ++ .core e :: R⟩ y) : False := by
  have hv : fval? (.core e) = none := by
    simp [fval?, Silmaril.Wasm.Logic.Hoare.blocked_val_none he]
  rcases step_split h V _ R hv rfl with ⟨V₁, V₂, L₀, -, hs, -⟩ | ⟨ha, -⟩ | ⟨ha, -⟩
  · obtain ⟨V₃, V₄, y', -, hr, -⟩ := step_last hs V₂ _ hv rfl
    exact root_blocked he hc hr
  · exact blocked_not_trap (AdminFX.core.inj ha ▸ he)
  · exact blocked_not_throwRef (AdminFX.core.inj ha ▸ he)

theorem no_step_br {V : List FVal} {x : LabelIdx} {R : List AdminFX} {y : ConfigFX H}
    (h : StepFX' P noHost fx ⟨s, K, f, fvals V ++ .core (.plain (.br x)) :: R⟩ y) : False :=
  no_step_blocked (Or.inl ⟨x, rfl⟩) (by simp [Admin.IsCallRef]) h

theorem no_step_ret {V : List FVal} {R : List AdminFX} {y : ConfigFX H}
    (h : StepFX' P noHost fx ⟨s, K, f, fvals V ++ .core (.plain .return_) :: R⟩ y) : False :=
  no_step_blocked (Or.inr (Or.inl rfl)) (by simp [Admin.IsCallRef]) h

theorem map_trap_eq (W : List Val) :
    (vals W ++ [Admin.trap]).map AdminFX.core = fvals (liftV W) ++ [.core .trap] := by
  simp [map_core_vals]

/-- A root step at a `trap` drops values below it. -/
theorem trapish_root {V : List FVal} {y : ConfigFX H} (hr : Root P fx s K f V (.core .trap) y) :
    y.store = s ∧ y.conts = K ∧ y.frame = f ∧
      ∃ V', y.code = fvals V' ++ [.core .trap] ∧ V'.length < V.length := by
  cases hr with
  | @core W _ s' f' cs' h =>
    obtain ⟨hs, hf, p, w, q, hW, hw, hc⟩ := Sim.Step.trap_redex_aux h W rfl
    refine ⟨hs, rfl, hf, liftV (p ++ q), ?_, ?_⟩
    · have hc' : cs' = vals (p ++ q) ++ [Admin.trap] := hc
      show cs'.map AdminFX.core = _
      rw [hc', map_trap_eq]
    · have hw' : 0 < w.length := List.length_pos_iff.mpr hw
      simp [liftV, hW]; omega
  | trapSeq hne => exact ⟨rfl, rfl, rfl, [], rfl, List.length_pos_iff.mpr hne⟩
  | invoke hc => exact absurd hc (by simp [Admin.IsCallRef])

/-- **A trap inside a sequence steps only towards a bare `trap`.** -/
theorem step_trapish {ws : List FVal} {r : List AdminFX} {y : ConfigFX H}
    (h : StepFX' P noHost fx ⟨s, K, f, fvals ws ++ .core .trap :: r⟩ y) :
    y.store = s ∧ y.conts = K ∧ y.frame = f ∧ ∃ ws' r', y.code = fvals ws' ++ .core .trap :: r' ∧
      ws'.length + r'.length < ws.length + r.length := by
  rcases step_split h ws _ r rfl rfl with ⟨V₁, V₂, L₀, rfl, hs, hc⟩ |
      ⟨-, hs, hK, hf, ws', us, r₁, r', rfl, rfl, hne, hc⟩ | ⟨ha, -⟩
  · obtain ⟨V₃, V₄, y', rfl, hr, hy⟩ := step_last hs V₂ _ rfl rfl
    obtain ⟨hs', hK', hf', V', hc', hlt⟩ := trapish_root hr
    have hy' : y.store = y'.store ∧ y.conts = y'.conts ∧ y.frame = y'.frame ∧
        L₀ = fvals V₃ ++ y'.code := by simpa using hy
    refine ⟨hy'.1.trans hs', hy'.2.1.trans hK', hy'.2.2.1.trans hf', V₁ ++ V₃ ++ V', r, ?_, ?_⟩
    · rw [hc, hy'.2.2.2, hc']; simp
    · simp; omega
  · refine ⟨hs, hK, hf, ws', r', hc, ?_⟩
    rcases hne with hne | hne <;> have := List.length_pos_iff.mpr hne <;> simp <;> omega
  · exact absurd ha (by simp)

theorem map_throw_eq (W : List Val) (a : Nat) :
    (vals W ++ throwing a).map AdminFX.core = fvals (liftV W) ++ cthrowing a := by
  simp [map_core_vals, cthrowing]

theorem last_exn {V : List FVal} {W : List Val} {b : Nat} {u : List Val} {r : Ref}
    (h : liftV W = V ++ [.val (.ref (.exn b))]) (hW : W = u ++ [.ref r]) : r = .exn b := by
  rw [hW] at h
  simp [liftV] at h
  exact h.2

/-- A root step at the `throw_ref` of an exception drops values below it. -/
theorem throwish_root {V V' : List FVal} {b : Nat} {y : ConfigFX H}
    (hr : Root P fx s K f V (.core (.plain .throwRef)) y) (hV : V = V' ++ [.val (.ref (.exn b))]) :
    y.store = s ∧ y.conts = K ∧ y.frame = f ∧
      ∃ V'', y.code = fvals V'' ++ cthrowing b ∧ V''.length < V'.length := by
  cases hr with
  | @core W _ s' f' cs' h =>
    obtain ⟨hs, hf, ⟨p, w, q, a, hW, hw, hc⟩ | ⟨u, u', hW, -⟩⟩ :=
      Sim.Step.throwRef_redex_aux h W rfl
    · have ha : Ref.exn a = .exn b := last_exn (u := p ++ w ++ q) hV (by simp [hW])
      have ha' : a = b := by simpa using ha
      refine ⟨hs, rfl, hf, liftV (p ++ q), ?_, ?_⟩
      · rw [← ha', ← map_throw_eq]; exact congrArg (List.map AdminFX.core) hc
      · have hl : (liftV W).length = V'.length + 1 := by rw [hV]; simp
        have hw' : 0 < w.length := List.length_pos_iff.mpr hw
        simp only [liftV, List.length_map, List.length_append, hW, List.length_singleton] at hl ⊢
        omega
    · exact absurd (last_exn hV hW) (by simp)
  | @throwSeq vs a hne =>
    obtain ⟨rfl, hab⟩ := List.append_inj' hV rfl
    have hab' : a = b := by simpa using hab
    exact ⟨rfl, rfl, rfl, [], by rw [hab']; rfl, List.length_pos_iff.mpr hne⟩
  | invoke hc => exact absurd hc (by simp [Admin.IsCallRef])

theorem suffix_last {α : Type} {A B C : List α} {z : α} (h : A ++ [z] = B ++ C) (hC : C ≠ []) :
    ∃ C', C = C' ++ [z] ∧ A = B ++ C' := by
  obtain ⟨C', x, rfl⟩ := List.eq_nil_or_concat C |>.resolve_left hC
  have h' : A ++ [z] = (B ++ C') ++ [x] := by rw [h]; simp
  obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
  exact ⟨C', by rw [List.singleton_inj.mp h2, List.concat_eq_append], h1⟩

theorem throwish_root_nil {V : List FVal} {y : ConfigFX H}
    (hr : Root P fx s K f V (.core (.plain .throwRef)) y) (hV : V = []) : False := by
  cases hr with
  | @core W _ s' f' cs' h =>
    have hW0 : W = [] := by simpa [liftV] using hV
    obtain ⟨-, -, ⟨p, w, q, a, hW, -⟩ | ⟨u, u', hW, -⟩⟩ := Sim.Step.throwRef_redex_aux h W rfl
    · rw [hW0] at hW; simp at hW
    · rw [hW0] at hW; simp at hW
  | throwSeq hne => simp at hV
  | invoke hc => exact absurd hc (by simp [Admin.IsCallRef])

theorem throwish_last_nil {y : ConfigFX H}
    (h : StepFX' P noHost fx ⟨s, K, f, fvals [] ++ [.core (.plain .throwRef)]⟩ y) : False := by
  obtain ⟨V₃, V₄, y', hV, hr, -⟩ := step_last h [] _ rfl rfl
  exact throwish_root_nil hr (List.append_eq_nil_iff.mp hV.symm).2

theorem throwish_last {C' : List FVal} {b : Nat} {s' : Store H} {K' : Conts} {f' : Frame}
    {L₀ : List AdminFX}
    (h : StepFX' P noHost fx ⟨s, K, f, fvals (C' ++ [.val (.ref (.exn b))]) ++ [.core (.plain .throwRef)]⟩
      ⟨s', K', f', L₀⟩) :
    s' = s ∧ K' = K ∧ f' = f ∧ ∃ V'', L₀ = fvals V'' ++ cthrowing b ∧ V''.length < C'.length := by
  obtain ⟨V₃, V₄, y', hV, hr, hy⟩ := step_last h _ _ rfl rfl
  have hy' : s' = y'.store ∧ K' = y'.conts ∧ f' = y'.frame ∧ L₀ = fvals V₃ ++ y'.code := by
    simpa using hy
  by_cases h4 : V₄ = []
  · exact (throwish_root_nil hr h4).elim
  · obtain ⟨V₄', rfl, hC⟩ := suffix_last hV h4
    obtain ⟨hs, hK, hf, V'', hc, hlt⟩ := throwish_root hr rfl
    refine ⟨hy'.1.trans hs, hy'.2.1.trans hK, hy'.2.2.1.trans hf, V₃ ++ V'', ?_, ?_⟩
    · rw [hy'.2.2.2, hc]; simp
    · rw [hC]; simp; omega

/-- **An exception inside a sequence steps only towards a bare exception.** -/
theorem step_throwish {ws : List FVal} {b : Nat} {r : List AdminFX} {y : ConfigFX H}
    (h : StepFX' P noHost fx ⟨s, K, f, fvals ws ++ cthrowing b ++ r⟩ y) :
    y.store = s ∧ y.conts = K ∧ y.frame = f ∧ ∃ ws' r', y.code = fvals ws' ++ cthrowing b ++ r' ∧
      ws'.length + r'.length < ws.length + r.length := by
  rw [cthrowing_app] at h
  rcases step_split h _ _ r rfl rfl with ⟨V₁, V₂, L₀, hV, hs, hc⟩ | ⟨ha, -⟩ |
      ⟨-, hs, hK, hf, ws', us, b', r₁, r', hV, rfl, hne, hc⟩
  · by_cases h2 : V₂ = []
    · rw [h2] at hs; exact (throwish_last_nil hs).elim
    · obtain ⟨C', rfl, hws⟩ := suffix_last hV h2
      obtain ⟨hs', hK', hf', V'', hL, hlt⟩ := throwish_last hs
      refine ⟨hs', hK', hf', V₁ ++ V'', r, ?_, ?_⟩
      · rw [hc, hL]; simp
      · rw [hws]; simp; omega
  · exact absurd ha (by simp)
  · obtain ⟨hws, hb⟩ := List.append_inj' (show ws ++ [.val (.ref (.exn b))] = (ws' ++ us) ++
        [.val (.ref (.exn b'))] by simp [hV]) rfl
    have hb' : b' = b := by simpa using hb.symm
    refine ⟨hs, hK, hf, ws', r', by rw [hc, hb'], ?_⟩
    rw [hws]
    rcases hne with hne | hne <;> have := List.length_pos_iff.mpr hne <;> simp <;> omega

/-! ## Safety of the codes that end a run -/

variable {Q : PostFX H}

/-- **Total safety of a step-closed set** with a decreasing measure. -/
theorem tsafe_closed (S : ConfigFX H → Prop) (μ : ConfigFX H → Nat)
    (hstep : ∀ c c', S c → StepFX' P noHost fx c c' → S c' ∧ μ c' < μ c)
    (hstop : ∀ c o, S c → Stops c.store c.frame o c.code → Q c.store c.conts c.frame o) :
    ∀ c, S c → TSafe P fx Q c := by
  intro c
  induction hm : μ c using Nat.strong_induction_on generalizing c with
  | _ m ih =>
    intro hc
    refine .intro (fun o ho => hstop c o hc ho) fun c' hs => ?_
    obtain ⟨hc', hlt⟩ := hstep c c' hc hs
    exact ih (μ c') (hm ▸ hlt) c' rfl hc'

/-- **Step-indexed safety of a step-closed set.** -/
theorem safe_closed (S : ConfigFX H → Prop)
    (hstep : ∀ c c', S c → StepFX' P noHost fx c c' → S c')
    (hstop : ∀ c o, S c → Stops c.store c.frame o c.code → Q c.store c.conts c.frame o) :
    ∀ n c, S c → Safe P fx Q n c
  | 0, _, _ => trivial
  | n + 1, c, hc => ⟨fun o ho => hstop c o hc ho,
      fun c' hs => safe_closed S hstep hstop n c' (hstep c c' hc hs)⟩

/-- The set of one configuration that does not step. -/
theorem tsafe_stuck {c : ConfigFX H} (hn : ∀ c', ¬ StepFX' P noHost fx c c')
    (hq : ∀ o, Stops c.store c.frame o c.code → Q c.store c.conts c.frame o) : TSafe P fx Q c :=
  .intro hq fun c' hs => (hn c' hs).elim

theorem safe_stuck {c : ConfigFX H} (hn : ∀ c', ¬ StepFX' P noHost fx c c')
    (hq : ∀ o, Stops c.store c.frame o c.code → Q c.store c.conts c.frame o) :
    ∀ n, Safe P fx Q n c
  | 0 => trivial
  | _ + 1 => ⟨hq, fun c' hs => (hn c' hs).elim⟩

theorem tsafe_vals {V : List FVal} (hq : Q s K f (.normal V)) : TSafe P fx Q ⟨s, K, f, fvals V⟩ :=
  tsafe_stuck (fun _ hs => no_step_fvals' hs V rfl) fun _ ho => (stops_fvals ho) ▸ hq

theorem safe_vals {V : List FVal} (hq : Q s K f (.normal V)) (n : Nat) :
    Safe P fx Q n ⟨s, K, f, fvals V⟩ :=
  safe_stuck (fun _ hs => no_step_fvals' hs V rfl) (fun _ ho => (stops_fvals ho) ▸ hq) n

theorem tsafe_br {V : List FVal} {x : LabelIdx} {R : List AdminFX} (hq : Q s K f (.br x.toNat V)) :
    TSafe P fx Q ⟨s, K, f, fvals V ++ .core (.plain (.br x)) :: R⟩ :=
  tsafe_stuck (fun _ hs => no_step_br hs) fun _ ho => (stops_br ho) ▸ hq

theorem safe_br {V : List FVal} {x : LabelIdx} {R : List AdminFX} (hq : Q s K f (.br x.toNat V))
    (n : Nat) : Safe P fx Q n ⟨s, K, f, fvals V ++ .core (.plain (.br x)) :: R⟩ :=
  safe_stuck (fun _ hs => no_step_br hs) (fun _ ho => (stops_br ho) ▸ hq) n

theorem tsafe_ret {V : List FVal} {R : List AdminFX} (hq : Q s K f (.ret V)) :
    TSafe P fx Q ⟨s, K, f, fvals V ++ .core (.plain .return_) :: R⟩ :=
  tsafe_stuck (fun _ hs => no_step_ret hs) fun _ ho => (stops_ret ho) ▸ hq

theorem safe_ret {V : List FVal} {R : List AdminFX} (hq : Q s K f (.ret V)) (n : Nat) :
    Safe P fx Q n ⟨s, K, f, fvals V ++ .core (.plain .return_) :: R⟩ :=
  safe_stuck (fun _ hs => no_step_ret hs) (fun _ ho => (stops_ret ho) ▸ hq) n

/-- The configurations with a trap inside a sequence, at `s, K, f`. -/
def Trapish (s : Store H) (K : Conts) (f : Frame) (c : ConfigFX H) : Prop :=
  c.store = s ∧ c.conts = K ∧ c.frame = f ∧ ∃ ws r, c.code = fvals ws ++ .core .trap :: r

theorem trapish_step {c c' : ConfigFX H} (hc : Trapish s K f c) (hs : StepFX' P noHost fx c c') :
    Trapish s K f c' ∧ c'.code.length < c.code.length := by
  obtain ⟨rfl, rfl, rfl, ws, r, hcode⟩ := hc
  rw [show c = ⟨c.store, c.conts, c.frame, fvals ws ++ .core .trap :: r⟩ by rw [← hcode]] at hs
  obtain ⟨h1, h2, h3, ws', r', hc', hlt⟩ := step_trapish hs
  exact ⟨⟨h1, h2, h3, ws', r', hc'⟩, by rw [hc', hcode]; simp; omega⟩

theorem trapish_stop {c : ConfigFX H} {o : OutcomeFX} (hq : Q s K f .trap) (hc : Trapish s K f c)
    (ho : Stops c.store c.frame o c.code) : Q c.store c.conts c.frame o := by
  obtain ⟨rfl, rfl, rfl, ws, r, hcode⟩ := hc
  rw [hcode] at ho
  exact (stops_trapish ho) ▸ hq

theorem tsafe_trap {ws : List FVal} {r : List AdminFX} (hq : Q s K f .trap) :
    TSafe P fx Q ⟨s, K, f, fvals ws ++ .core .trap :: r⟩ :=
  tsafe_closed (Trapish s K f) (fun c => c.code.length) (fun _ _ hc hs => trapish_step hc hs)
    (fun _ _ hc ho => trapish_stop hq hc ho) _ ⟨rfl, rfl, rfl, ws, r, rfl⟩

theorem safe_trap {ws : List FVal} {r : List AdminFX} (hq : Q s K f .trap) (n : Nat) :
    Safe P fx Q n ⟨s, K, f, fvals ws ++ .core .trap :: r⟩ :=
  safe_closed (Trapish s K f) (fun _ _ hc hs => (trapish_step hc hs).1)
    (fun _ _ hc ho => trapish_stop hq hc ho) n _ ⟨rfl, rfl, rfl, ws, r, rfl⟩

/-- The configurations with the exception `b` inside a sequence, at `s, K, f`. -/
def Throwish (s : Store H) (K : Conts) (f : Frame) (b : Nat) (c : ConfigFX H) : Prop :=
  c.store = s ∧ c.conts = K ∧ c.frame = f ∧ ∃ ws r, c.code = fvals ws ++ cthrowing b ++ r

theorem throwish_step {b : Nat} {c c' : ConfigFX H} (hc : Throwish s K f b c)
    (hs : StepFX' P noHost fx c c') : Throwish s K f b c' ∧ c'.code.length < c.code.length := by
  obtain ⟨rfl, rfl, rfl, ws, r, hcode⟩ := hc
  rw [show c = ⟨c.store, c.conts, c.frame, fvals ws ++ cthrowing b ++ r⟩ by rw [← hcode]] at hs
  obtain ⟨h1, h2, h3, ws', r', hc', hlt⟩ := step_throwish hs
  exact ⟨⟨h1, h2, h3, ws', r', hc'⟩, by rw [hc', hcode]; simp [cthrowing]; omega⟩

theorem throwish_stop {b : Nat} {c : ConfigFX H} {o : OutcomeFX} (hq : Q s K f (.throw b))
    (hc : Throwish s K f b c) (ho : Stops c.store c.frame o c.code) :
    Q c.store c.conts c.frame o := by
  obtain ⟨rfl, rfl, rfl, ws, r, hcode⟩ := hc
  rw [hcode] at ho
  exact (stops_throwish ho) ▸ hq

theorem tsafe_throw {ws : List FVal} {b : Nat} {r : List AdminFX} (hq : Q s K f (.throw b)) :
    TSafe P fx Q ⟨s, K, f, fvals ws ++ cthrowing b ++ r⟩ :=
  tsafe_closed (Throwish s K f b) (fun c => c.code.length) (fun _ _ hc hs => throwish_step hc hs)
    (fun _ _ hc ho => throwish_stop hq hc ho) _ ⟨rfl, rfl, rfl, ws, r, rfl⟩

theorem safe_throw {ws : List FVal} {b : Nat} {r : List AdminFX} (hq : Q s K f (.throw b))
    (n : Nat) : Safe P fx Q n ⟨s, K, f, fvals ws ++ cthrowing b ++ r⟩ :=
  safe_closed (Throwish s K f b) (fun _ _ hc hs => (throwish_step hc hs).1)
    (fun _ _ hc ho => throwish_stop hq hc ho) n _ ⟨rfl, rfl, rfl, ws, r, rfl⟩

end Ends

end Silmaril.Proofs.Wasm.FX.Logic.EveryRun
