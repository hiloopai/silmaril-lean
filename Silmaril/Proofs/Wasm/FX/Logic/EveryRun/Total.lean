module

public import Silmaril.Proofs.Wasm.FX.Logic.EveryRun.Stop
public import Silmaril.Proofs.Wasm.FX.Logic.EveryRun.Head

/-!
# The total-correctness rules of the every-run WasmFX logic

Rules for `TSafe` (`Silmaril.Wasm.FX.Logic.EveryRun.Defs`), each proved by induction on the
`TSafe` derivation of the inner code and the inversions of `StepFX'` (`step_split`,
`step_last`, `Root`):

* `Inv` holds of every postcondition built by the context rules (`Inv.seqPost`, …);
* structural: `tsafe_mono`, **`tsafe_seq`**, **`tsafe_label`**, **`tsafe_frame`**, and
  **`tsafe_handler`**, the handler rule: a `suspend` caught by the handler branches to its
  label with the payload and a new continuation, a `switch` continues with the target;
* instructions: `tsafe_inert` (any plain instruction without a host call, through its Core head
  steps), `tsafe_block`, `tsafe_contNew`, **`tsafe_resume`**, `tsafe_invoke` (an FX function),
  `tsafe_suspend` (an unhandled `suspend` stops), `tsafe_dropCont`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Logic.EveryRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts newCont)
open Silmaril.Wasm.FX.Logic.EveryRun (Unhandled suspCode switchCode Stops Safe TSafe Inv seqPost
  labelPost framePost handlerPost totJ safeJ)
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval? fnvF fnvF_cases fvals_append_cons_inj fvals_inj
  no_step_fvals')
open Silmaril.Proofs.Wasm.Models.FXAsyncSus (canon Wrp plug_eq_of_canon)
open Silmaril.Proofs.Wasm.Models.FXAsyncBack (IsWrap)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

/-! ## Invariance under plug-equal contexts -/

section Inv

variable {Q : PostFX H}

theorem inv_susp (hQ : Inv Q) {s : Store H} {K : Conts} {f : Frame} {E E' : CtxV}
    {vs : List FVal} {x : TagIdx} (h : canon E = canon E') (hq : Q s K f (.susp E vs x)) :
    Q s K f (.susp E' vs x) :=
  hQ.1 s K f E E' vs x (congrFun (plug_eq_of_canon h) _) hq

theorem inv_swtch (hQ : Inv Q) {s : Store H} {K : Conts} {f : Frame} {E E' : CtxV}
    {vs : List FVal} {k : Nat} {ct : TypeIdx} {x : TagIdx} (h : canon E = canon E')
    (hq : Q s K f (.swtch E vs k ct x)) : Q s K f (.swtch E' vs k ct x) :=
  hQ.2 s K f E E' vs k ct x (congrFun (plug_eq_of_canon h) _) hq

theorem inv_seqPost (hQ : Inv Q) (J : Store H → Conts → Frame → List AdminFX → Prop)
    (c₂ : List AdminFX) : Inv (seqPost J c₂ Q) :=
  ⟨fun s K f _ _ vs x h hq => hQ.1 s K f _ _ vs x (by simp [CtxV.plug, h]) hq,
    fun s K f _ _ vs k ct x h hq => hQ.2 s K f _ _ vs k ct x (by simp [CtxV.plug, h]) hq⟩

theorem inv_labelPost (hQ : Inv Q) (J : Store H → Conts → Frame → List AdminFX → Prop) (n : Nat)
    (k : List InstrFX) (us : List FVal) : Inv (labelPost J n k us Q) :=
  ⟨fun s K f _ _ vs x h hq => hQ.1 s K f _ _ vs x (by simp [CtxV.plug, h]) hq,
    fun s K f _ _ vs j ct x h hq => hQ.2 s K f _ _ vs j ct x (by simp [CtxV.plug, h]) hq⟩

theorem inv_framePost (hQ : Inv Q) (n : Nat) (f : Frame) (us : List FVal) :
    Inv (framePost n f us Q) :=
  ⟨fun s K F _ _ vs x h hq => hQ.1 s K f _ _ vs x (by simp [CtxV.plug, h]) hq,
    fun s K F _ _ vs k ct x h hq => hQ.2 s K f _ _ vs k ct x (by simp [CtxV.plug, h]) hq⟩

theorem handlerPost_susp_inv (hQ : Inv Q) {J : Store H → Conts → Frame → List AdminFX → Prop}
    {hs : List HClause} {us : List FVal} {s : Store H} {K : Conts} {f : Frame} {E E' : CtxV}
    {vs : List FVal} {x : TagIdx} (h : E.plug (suspCode vs x) = E'.plug (suspCode vs x))
    (hq : handlerPost J hs us Q s K f (.susp E vs x)) :
    handlerPost J hs us Q s K f (.susp E' vs x) := by
  have hc : canon E = canon E' := canon_of_susp h
  have hp : E.plug = E'.plug := plug_eq_of_canon hc
  have hch : canon (.handler hs E) = canon (.handler hs E') :=
    canon_of_susp (vs := vs) (x := x) (by simp [CtxV.plug, h])
  refine ⟨fun ta ti l ht hE hcl => ?_, fun hu => ?_⟩
  · rw [← frameAt_of_canon hc] at ht
    have := hq.1 ta ti l ht ((handles_of_canon hc ta).not.mpr hE) hcl
    rwa [hp] at this
  · have h1 := hq.2 (Unhandled.of_canon hch.symm hu)
    exact inv_susp hQ (E := .seq us (.handler hs E) []) (by simp only [canon, hc]) h1

theorem handlerPost_swtch_inv (hQ : Inv Q) {J : Store H → Conts → Frame → List AdminFX → Prop}
    {hs : List HClause} {us : List FVal} {s : Store H} {K : Conts} {f : Frame} {E E' : CtxV}
    {vs : List FVal} {k : Nat} {ct : TypeIdx} {x : TagIdx}
    (h : E.plug (switchCode vs k ct x) = E'.plug (switchCode vs k ct x))
    (hq : handlerPost J hs us Q s K f (.swtch E vs k ct x)) :
    handlerPost J hs us Q s K f (.swtch E' vs k ct x) := by
  have hc : canon E = canon E' := canon_of_switch h
  have hp : E.plug = E'.plug := plug_eq_of_canon hc
  have hch : canon (.handler hs E) = canon (.handler hs E') :=
    canon_of_switch (vs := vs) (k := k) (ct := ct) (x := x) (by simp [CtxV.plug, h])
  refine ⟨fun C ta ti hk ht hE hcl => ?_, fun hu => ?_⟩
  · rw [← frameAt_of_canon hc] at ht
    have := hq.1 C ta ti hk ht ((handles_of_canon hc ta).not.mpr hE) hcl
    rwa [hp] at this
  · have h1 := hq.2 (Unhandled.of_canon hch.symm hu)
    exact inv_swtch hQ (E := .seq us (.handler hs E) []) (by simp only [canon, hc]) h1

theorem inv_handlerPost (hQ : Inv Q) (J : Store H → Conts → Frame → List AdminFX → Prop)
    (hs : List HClause) (us : List FVal) : Inv (handlerPost J hs us Q) :=
  ⟨fun _ _ _ _ _ _ _ h hq => handlerPost_susp_inv hQ h hq,
    fun _ _ _ _ _ _ _ _ _ h hq => handlerPost_swtch_inv hQ h hq⟩

/-- A postcondition that ignores effects altogether. -/
theorem inv_of_noEff (hs : ∀ s K f E vs x, ¬ Q s K f (.susp E vs x))
    (hw : ∀ s K f E vs k ct x, ¬ Q s K f (.swtch E vs k ct x)) : Inv Q :=
  ⟨fun s K f E _ vs x _ hq => (hs s K f E vs x hq).elim,
    fun s K f E _ vs k ct x _ hq => (hw s K f E vs k ct x hq).elim⟩

end Inv

/-! ## Structural rules -/

section Struct

variable {Q : PostFX H}

theorem _root_.Silmaril.Wasm.FX.Logic.EveryRun.TSafe.stops {c : ConfigFX H} (h : TSafe P fx Q c) :
    ∀ o, Stops c.store c.frame o c.code → Q c.store c.conts c.frame o := by
  cases h with
  | intro hq _ => exact hq

theorem _root_.Silmaril.Wasm.FX.Logic.EveryRun.TSafe.steps {c : ConfigFX H} (h : TSafe P fx Q c) :
    ∀ c', StepFX' P noHost fx c c' → TSafe P fx Q c' := by
  cases h with
  | intro _ hs => exact hs

theorem tsafe_mono {Q' : PostFX H} (hQ : ∀ s K f o, Q s K f o → Q' s K f o) :
    ∀ {c : ConfigFX H}, TSafe P fx Q c → TSafe P fx Q' c := by
  intro c h
  induction h with
  | intro hq _ ih => exact .intro (fun o ho => hQ _ _ _ _ (hq o ho)) ih

/-- The trap postcondition of code with a trap inside a sequence. -/
theorem tsafe_trap_post {Q' : PostFX H} {c : ConfigFX H}
    (hq : ∀ o, Stops c.store c.frame o c.code → Q' c.store c.conts c.frame o)
    (hs : ∀ c', StepFX' P noHost fx c c' → TSafe P fx Q' c') {V : List FVal} {R : List AdminFX}
    (hc : c.code = fvals V ++ .core .trap :: R) : Q' c.store c.conts c.frame .trap := by
  by_cases hne : V ≠ [] ∨ R ≠ []
  · have hst : StepFX' P noHost fx c ⟨c.store, c.conts, c.frame, [.core .trap]⟩ := by
      have := StepFX'.trapSeq (P := P) (host := noHost) (fx := fx) (s := c.store) (K := c.conts)
        (f := c.frame) hne
      rw [show c = ⟨c.store, c.conts, c.frame, fvals V ++ [.core .trap] ++ R⟩ by
        rw [List.append_assoc, List.singleton_append, ← hc]]
      exact this
    exact (hs _ hst).stops .trap rfl
  · have hv : V = [] ∧ R = [] := by simpa only [ne_eq, not_or, not_not] using hne
    exact hq .trap (by rw [hc, hv.1, hv.2]; rfl)

/-- The throw postcondition of code with an exception inside a sequence. -/
theorem tsafe_throw_post {Q' : PostFX H} {c : ConfigFX H}
    (hq : ∀ o, Stops c.store c.frame o c.code → Q' c.store c.conts c.frame o)
    (hs : ∀ c', StepFX' P noHost fx c c' → TSafe P fx Q' c') {V : List FVal} {b : Nat}
    {R : List AdminFX} (hc : c.code = fvals V ++ cthrowing b ++ R) :
    Q' c.store c.conts c.frame (.throw b) := by
  by_cases hne : V ≠ [] ∨ R ≠ []
  · have hst : StepFX' P noHost fx c ⟨c.store, c.conts, c.frame, cthrowing b⟩ := by
      have := StepFX'.throwSeq (P := P) (host := noHost) (fx := fx) (s := c.store) (K := c.conts)
        (f := c.frame) (a := b) hne
      rw [show c = ⟨c.store, c.conts, c.frame, fvals V ++ cthrowing b ++ R⟩ by rw [← hc]]
      exact this
    exact (hs _ hst).stops (.throw b) rfl
  · have hv : V = [] ∧ R = [] := by simpa only [ne_eq, not_or, not_not] using hne
    exact hq (.throw b) (by
      rw [hc, hv.1, hv.2]; show fvals [] ++ cthrowing b ++ [] = cthrowing b; simp)

end Struct

/-! ## Sequencing -/

section Seq

variable {Q : PostFX H} {J : Store H → Conts → Frame → List AdminFX → Prop} {c₂ : List AdminFX}

theorem seq_stops_susp (hQ : Inv Q) {s : Store H} {K : Conts} {f : Frame} {c₁ : List AdminFX}
    (hq : ∀ o, Stops s f o c₁ → seqPost J c₂ Q s K f o) (hU : ∀ U, c₁ ≠ fvals U) {E : CtxV}
    {vs : List FVal} {x : TagIdx} (ho : Stops s f (.susp E vs x) (c₁ ++ c₂)) :
    Q s K f (.susp E vs x) := by
  obtain ⟨E₁, hE₁⟩ := plug_app_inv (e := .fx (.suspend x)) rfl E ho.1.symm hU
  have hp : (CtxV.seq [] E₁ c₂).plug (suspCode vs x) = E.plug (suspCode vs x) := by
    rw [← ho.1]; simp [CtxV.plug, suspCode, hE₁]
  have hc : canon E = canon (.seq [] E₁ c₂) := canon_of_susp hp.symm
  have hu : Unhandled s f E₁ x := Unhandled.of_canon (E' := .seq [] E₁ c₂) hc ho.2
  exact inv_susp hQ hc.symm (hq (.susp E₁ vs x) ⟨hE₁, hu⟩)

theorem seq_stops_swtch (hQ : Inv Q) {s : Store H} {K : Conts} {f : Frame} {c₁ : List AdminFX}
    (hq : ∀ o, Stops s f o c₁ → seqPost J c₂ Q s K f o) (hU : ∀ U, c₁ ≠ fvals U) {E : CtxV}
    {vs : List FVal} {k : Nat} {ct : TypeIdx} {x : TagIdx}
    (ho : Stops s f (.swtch E vs k ct x) (c₁ ++ c₂)) : Q s K f (.swtch E vs k ct x) := by
  have h1 : E.plug (fvals (vs ++ [.cont k]) ++ [.fx (.switch ct x)]) = c₁ ++ c₂ := by
    rw [← switchCode_eq]; exact ho.1.symm
  obtain ⟨E₁, hE₁⟩ := plug_app_inv rfl E h1 hU
  have hp : (CtxV.seq [] E₁ c₂).plug (switchCode vs k ct x) = E.plug (switchCode vs k ct x) := by
    rw [← ho.1, switchCode_eq]; simp [CtxV.plug, hE₁]
  have hc : canon E = canon (.seq [] E₁ c₂) := canon_of_switch hp.symm
  have hu : Unhandled s f E₁ x := Unhandled.of_canon (E' := .seq [] E₁ c₂) hc ho.2
  exact inv_swtch hQ hc.symm (hq (.swtch E₁ vs k ct x) ⟨by rw [switchCode_eq]; exact hE₁, hu⟩)

theorem seq_stop_br {s : Store H} {K : Conts} {f : Frame} {c₁ : List AdminFX}
    (hq : ∀ o, Stops s f o c₁ → seqPost J c₂ Q s K f o) {V : List FVal} {a : AdminFX}
    {R₁ : List AdminFX} (hc : c₁ = fvals V ++ a :: R₁) {l : Nat} {vs : List FVal}
    (hfoc : FocusOf (.br l vs) V a (R₁ ++ c₂)) : Q s K f (.br l vs) := by
  obtain ⟨rfl, x, hx, rfl⟩ := hfoc
  exact hq (.br l vs) ⟨x, R₁, hx, hc⟩

theorem seq_stop_ret {s : Store H} {K : Conts} {f : Frame} {c₁ : List AdminFX}
    (hq : ∀ o, Stops s f o c₁ → seqPost J c₂ Q s K f o) {V : List FVal} {a : AdminFX}
    {R₁ : List AdminFX} (hc : c₁ = fvals V ++ a :: R₁) {vs : List FVal}
    (hfoc : FocusOf (.ret vs) V a (R₁ ++ c₂)) : Q s K f (.ret vs) := by
  obtain ⟨rfl, rfl⟩ := hfoc
  exact hq (.ret vs) ⟨R₁, hc⟩

theorem seq_stop_trap {s : Store H} {K : Conts} {f : Frame} {c₁ : List AdminFX}
    (hq : ∀ o, Stops s f o c₁ → seqPost J c₂ Q s K f o) {V : List FVal} {a : AdminFX}
    {R₁ : List AdminFX} (hc : c₁ = fvals V ++ a :: R₁)
    (hfoc : FocusOf .trap V a (R₁ ++ c₂)) : Q s K f .trap := by
  obtain ⟨rfl, rfl, hR⟩ := hfoc
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hR
  exact hq .trap hc

theorem seq_stop_throw {s : Store H} {K : Conts} {f : Frame} {c₁ : List AdminFX}
    (hq : ∀ o, Stops s f o c₁ → seqPost J c₂ Q s K f o) {V : List FVal} {a : AdminFX}
    {R₁ : List AdminFX} (hc : c₁ = fvals V ++ a :: R₁) {b : Nat}
    (hfoc : FocusOf (.throw b) V a (R₁ ++ c₂)) : Q s K f (.throw b) := by
  obtain ⟨rfl, rfl, hR⟩ := hfoc
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hR
  exact hq (.throw b) hc

/-- The stopped outcomes of `c₁ ++ c₂`, when `c₁` is not all values. -/
theorem seq_stops (hQ : Inv Q) {s : Store H} {K : Conts} {f : Frame} {c₁ : List AdminFX}
    (hq : ∀ o, Stops s f o c₁ → seqPost J c₂ Q s K f o) {V : List FVal} {a : AdminFX}
    {R₁ : List AdminFX} (hc : c₁ = fvals V ++ a :: R₁) (ha : fval? a = none) :
    ∀ o, Stops s f o (c₁ ++ c₂) → Q s K f o := by
  have hU : ∀ U, c₁ ≠ fvals U := fun U h => fvals_ne_cons ha (h.symm.trans hc)
  intro o ho
  have ho' : Stops s f o (fvals V ++ a :: (R₁ ++ c₂)) := by rw [hc] at ho; simpa using ho
  have hfoc : FocusOf o V a (R₁ ++ c₂) := stops_focus ha ho'
  cases o with
  | normal vs => exact hfoc.elim
  | br l vs => exact seq_stop_br hq hc hfoc
  | ret vs => exact seq_stop_ret hq hc hfoc
  | trap => exact seq_stop_trap hq hc hfoc
  | throw b => exact seq_stop_throw hq hc hfoc
  | susp E vs x => exact seq_stops_susp hQ hq hU ho
  | swtch E vs k ct x => exact seq_stops_swtch hQ hq hU ho

theorem tsafe_seq_step {Q' : PostFX H} {c y : ConfigFX H}
    (hq : ∀ o, Stops c.store c.frame o c.code → Q' c.store c.conts c.frame o)
    (hs : ∀ c', StepFX' P noHost fx c c' → TSafe P fx Q' c')
    (ih : ∀ c', StepFX' P noHost fx c c' → TSafe P fx Q ⟨c'.store, c'.conts, c'.frame, c'.code ++ c₂⟩)
    (hQ' : ∀ s K f, Q' s K f .trap → Q s K f .trap)
    (hQ'' : ∀ s K f b, Q' s K f (.throw b) → Q s K f (.throw b))
    {V : List FVal} {a : AdminFX} {R₁ : List AdminFX} (hc : c.code = fvals V ++ a :: R₁)
    (ha : fval? a = none)
    (hy : StepFX' P noHost fx ⟨c.store, c.conts, c.frame, c.code ++ c₂⟩ y) : TSafe P fx Q y := by
  have hc' : c = ⟨c.store, c.conts, c.frame, fvals V ++ a :: R₁⟩ := by rw [← hc]
  rw [hc] at hy
  rcases step_split_app ha hy with ⟨c₁', hst, hcode⟩ | ⟨rfl, hs', hK, hf, ws, r', hcode⟩ |
      ⟨rfl, hs', hK, hf, ws, V', b, r', rfl, hcode⟩
  · have hst' : StepFX' P noHost fx c ⟨y.store, y.conts, y.frame, c₁'⟩ := by rw [hc']; exact hst
    have h1 := ih _ hst'
    rw [show y = ⟨y.store, y.conts, y.frame, c₁' ++ c₂⟩ by rw [← hcode]]
    exact h1
  · have ht : Q' c.store c.conts c.frame .trap := tsafe_trap_post hq hs hc
    rw [show y = ⟨c.store, c.conts, c.frame, fvals ws ++ .core .trap :: r'⟩ by
      rw [← hs', ← hK, ← hf, ← hcode]]
    exact tsafe_trap (hQ' _ _ _ ht)
  · have ht : Q' c.store c.conts c.frame (.throw b) :=
      tsafe_throw_post hq hs (R := R₁) (by rw [hc, cthrowing_app])
    rw [show y = ⟨c.store, c.conts, c.frame, fvals ws ++ cthrowing b ++ r'⟩ by
      rw [← hs', ← hK, ← hf, ← hcode]]
    exact tsafe_throw (hQ'' _ _ _ _ ht)

/-- **Sequencing** (total correctness). -/
theorem tsafe_seq (hQ : Inv Q) :
    ∀ {c : ConfigFX H}, TSafe P fx (seqPost (totJ P fx Q) c₂ Q) c →
      TSafe P fx Q ⟨c.store, c.conts, c.frame, c.code ++ c₂⟩ := by
  intro c h
  induction h with
  | @intro c hq hs ih =>
    rcases fnvF_cases c.code with ⟨U, hU⟩ | ⟨V, a, R₁, hc, ha⟩
    · have h1 : TSafe P fx Q ⟨c.store, c.conts, c.frame, fvals U ++ c₂⟩ := hq (.normal U) hU
      rw [hU]; exact h1
    · exact .intro (seq_stops hQ hq hc ha) fun y hy =>
        tsafe_seq_step hq hs ih (fun _ _ _ h => h) (fun _ _ _ _ h => h) hc ha hy

theorem tsafe_seq' (hQ : Inv Q) {s : Store H} {K : Conts} {f : Frame} {c₁ : List AdminFX}
    (h : TSafe P fx (seqPost (totJ P fx Q) c₂ Q) ⟨s, K, f, c₁⟩) : TSafe P fx Q ⟨s, K, f, c₁ ++ c₂⟩ :=
  tsafe_seq hQ h

end Seq

/-! ## Labels, frames and handlers -/

section Wrap

variable {Q : PostFX H}

theorem unhandled_of {s : Store H} {f : Frame} {E : CtxV} {x : TagIdx} {ta : Nat} {ti : TagInst}
    (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta) : Unhandled s f E x := by
  intro ta' ti' ht'
  rw [ht] at ht'
  cases ht'
  exact hE

theorem unhandled_handler {s : Store H} {f : Frame} {hs : List HClause} {E : CtxV} {x : TagIdx}
    (h : Unhandled s f (.handler hs E) x) : Unhandled s f E x :=
  fun ta ti ht hE => h ta ti ht (Or.inr hE)

/-- The stopped outcomes of a wrapper are effects of its body: the context rules' arm. -/
theorem wrap_stops (hQ : Inv Q) {s : Store H} {K : Conts} {f F : Frame} {us : List FVal} {w : Wrp}
    {b : List AdminFX} {Q' : PostFX H}
    (hs : ∀ E vs x, Unhandled s f (wrpCtx w E) x → Stops s F (.susp E vs x) b →
      Q' s K F (.susp E vs x) → Q s K f (.susp (.seq us (wrpCtx w E) []) vs x))
    (hw : ∀ E vs k ct x, Unhandled s f (wrpCtx w E) x → Stops s F (.swtch E vs k ct x) b →
      Q' s K F (.swtch E vs k ct x) → Q s K f (.swtch (.seq us (wrpCtx w E) []) vs k ct x))
    (hF : ∀ E x, Unhandled s f (wrpCtx w E) x → Unhandled s F E x)
    (hq : ∀ o, Stops s F o b → Q' s K F o) :
    ∀ o, Stops s f o (fvals us ++ [w.wrap b]) → Q s K f o := by
  intro o ho
  rcases stops_wrap ho with ⟨E, vs, x, rfl, hu, E', hb, hc⟩ | ⟨E, vs, k, ct, x, rfl, hu, E', hb, hc⟩
  · have hu' : Unhandled s f (wrpCtx w E') x := Unhandled.of_canon (E' := .seq us (wrpCtx w E') []) hc hu
    have hst : Stops s F (.susp E' vs x) b := ⟨hb, hF E' x hu'⟩
    exact inv_susp hQ hc.symm (hs E' vs x hu' hst (hq _ hst))
  · have hu' : Unhandled s f (wrpCtx w E') x := Unhandled.of_canon (E' := .seq us (wrpCtx w E') []) hc hu
    have hst : Stops s F (.swtch E' vs k ct x) b := ⟨hb, hF E' x hu'⟩
    exact inv_swtch hQ hc.symm (hw E' vs k ct x hu' hst (hq _ hst))

theorem label_stops (hQ : Inv Q) {J : Store H → Conts → Frame → List AdminFX → Prop} {s : Store H}
    {K : Conts} {f : Frame} {n : Nat} {k : List InstrFX} {us : List FVal} {b : List AdminFX}
    (hq : ∀ o, Stops s f o b → labelPost J n k us Q s K f o) :
    ∀ o, Stops s f o (fvals us ++ [.label n k b]) → Q s K f o :=
  wrap_stops (w := .label n k) hQ (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ _ _ h => h)
    (fun _ _ h => h) hq

theorem frame_stops (hQ : Inv Q) {s : Store H} {K : Conts} {f F : Frame} {n : Nat}
    {us : List FVal} {b : List AdminFX} (hq : ∀ o, Stops s F o b → framePost n f us Q s K F o) :
    ∀ o, Stops s f o (fvals us ++ [.frame n F b]) → Q s K f o :=
  wrap_stops (w := .frame n F) hQ (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ _ _ h => h)
    (fun _ _ h => h) hq

theorem handler_stops (hQ : Inv Q) {J : Store H → Conts → Frame → List AdminFX → Prop}
    {s : Store H} {K : Conts} {f : Frame} {hs : List HClause} {us : List FVal} {b : List AdminFX}
    (hq : ∀ o, Stops s f o b → handlerPost J hs us Q s K f o) :
    ∀ o, Stops s f o (fvals us ++ [.handler hs b]) → Q s K f o :=
  wrap_stops (w := .handler hs) hQ (fun _ _ _ hu _ h => h.2 hu) (fun _ _ _ _ _ hu _ h => h.2 hu)
    (fun _ _ h => unhandled_handler h) hq

/-- The `br (l+1)` arm of the label rule. -/
theorem label_brSucc {J : Store H → Conts → Frame → List AdminFX → Prop} {s : Store H} {K : Conts}
    {f : Frame} {n : Nat} {k : List InstrFX} {us vs : List FVal} {l : LabelIdx}
    {rest : List AdminFX}
    (hq : ∀ o, Stops s f o (fvals vs ++ [.core (.plain (.br l))] ++ rest) →
      labelPost J n k us Q s K f o) (hl : 0 < l.toNat) :
    TSafe P fx Q ⟨s, K, f, fvals (us ++ vs) ++ .core (.plain (.br (labelPred l))) :: []⟩ := by
  obtain ⟨m, hm⟩ : ∃ m, l.toNat = m + 1 := ⟨l.toNat - 1, by omega⟩
  have h1 := hq (.br l.toNat vs) ⟨l, rest, rfl, by simp⟩
  rw [hm] at h1
  have hp : (labelPred l).toNat = m := by
    have h' : l.toNat - 1 = m := by omega
    simpa [labelPred, Idx.toNat] using h'
  have h2 : Q s K f (.br (labelPred l).toNat (us ++ vs)) := hp ▸ h1
  exact tsafe_br h2

/-- A root step at a wrapper uses no values. -/
theorem wrap_root_vals {s : Store H} {K : Conts} {f : Frame} {us V₁ V₂ : List FVal} {a : AdminFX}
    {y : ConfigFX H} (hr : Root P fx s K f V₂ a y) (hw : IsWrap a) (hV : us = V₁ ++ V₂) :
    V₂ = [] ∧ V₁ = us := by
  cases hr <;> first | exact ⟨rfl, by simpa using hV.symm⟩ | exact absurd hw id

theorem tsafe_label_root {s : Store H} {K : Conts} {f : Frame} {n : Nat}
    {k : List InstrFX} {us : List FVal} {b : List AdminFX} {y : ConfigFX H}
    (hq : ∀ o, Stops s f o b → labelPost (totJ P fx Q) n k us Q s K f o)
    (ih : ∀ c', StepFX' P noHost fx ⟨s, K, f, b⟩ c' →
      TSafe P fx Q ⟨c'.store, c'.conts, c'.frame, fvals us ++ [.label n k c'.code]⟩)
    {V₂ : List FVal} (hr : Root P fx s K f V₂ (.label n k b) y) :
    TSafe P fx Q ⟨y.store, y.conts, y.frame, fvals us ++ y.code⟩ := by
  cases hr with
  | ctxLabel h => exact ih _ h
  | @labelVals _ _ vs =>
    have h1 : Q s K f (.normal (us ++ vs)) := hq (.normal vs) rfl
    simpa using tsafe_vals (P := P) (fx := fx) h1
  | @brLabelZero _ _ vs' vs l rest hl hn =>
    have h1 := hq (.br l.toNat (vs' ++ vs)) ⟨l, rest, rfl, by simp⟩
    rw [hl] at h1
    have h2 : TSafe P fx Q ⟨s, K, f, fvals (us ++ vs) ++ k.map InstrFX.toAdmin⟩ := h1 vs' vs rfl hn
    simpa using h2
  | @brLabelSucc _ _ vs l rest hl => simpa using label_brSucc (P := P) (fx := fx) hq hl
  | @returnLabel _ _ vs rest =>
    have h1 : Q s K f (.ret (us ++ vs)) := hq (.ret vs) ⟨rest, by simp⟩
    simpa using tsafe_ret (P := P) (fx := fx) (R := []) h1
  | trapLabel =>
    have h1 : Q s K f .trap := hq .trap rfl
    simpa using tsafe_trap (P := P) (fx := fx) (ws := us) (r := []) h1
  | @throwLabel _ _ a =>
    have h1 : Q s K f (.throw a) := hq (.throw a) rfl
    simpa using tsafe_throw (P := P) (fx := fx) (ws := us) (r := []) h1

/-- **Labels** (total correctness), with values below. -/
theorem tsafe_label (hQ : Inv Q) {n : Nat} {k : List InstrFX} {us : List FVal} :
    ∀ {c : ConfigFX H}, TSafe P fx (labelPost (totJ P fx Q) n k us Q) c →
      TSafe P fx Q ⟨c.store, c.conts, c.frame, fvals us ++ [.label n k c.code]⟩ := by
  intro c h
  induction h with
  | @intro c hq hs ih =>
    rcases c with ⟨s, K, f, b⟩
    refine .intro (label_stops hQ hq) fun y hy => ?_
    obtain ⟨V₁, V₂, y', hV, hr, rfl⟩ := step_last hy us _ rfl rfl
    obtain ⟨-, rfl⟩ := wrap_root_vals hr trivial hV
    exact tsafe_label_root hq ih hr

theorem tsafe_frame_root {s : Store H} {K : Conts} {f F : Frame} {n : Nat} {us : List FVal}
    {b : List AdminFX} {y : ConfigFX H}
    (hq : ∀ o, Stops s F o b → framePost n f us Q s K F o)
    (ih : ∀ c', StepFX' P noHost fx ⟨s, K, F, b⟩ c' →
      TSafe P fx Q ⟨c'.store, c'.conts, f, fvals us ++ [.frame n c'.frame c'.code]⟩)
    {V₂ : List FVal} (hr : Root P fx s K f V₂ (.frame n F b) y) :
    TSafe P fx Q ⟨y.store, y.conts, y.frame, fvals us ++ y.code⟩ := by
  cases hr with
  | ctxFrame h => exact ih _ h
  | @frameVals _ _ vs hn =>
    have h1 : Q s K f (.normal (us ++ vs)) := hq (.normal vs) rfl hn
    simpa using tsafe_vals (P := P) (fx := fx) h1
  | @returnFrame _ _ vs' vs rest hn =>
    have h1 : Q s K f (.normal (us ++ vs)) := hq (.ret (vs' ++ vs)) ⟨rest, by simp⟩ vs' vs rfl hn
    simpa using tsafe_vals (P := P) (fx := fx) h1
  | trapFrame =>
    have h1 : Q s K f .trap := hq .trap rfl
    simpa using tsafe_trap (P := P) (fx := fx) (ws := us) (r := []) h1
  | @throwFrame _ _ a =>
    have h1 : Q s K f (.throw a) := hq (.throw a) rfl
    simpa using tsafe_throw (P := P) (fx := fx) (ws := us) (r := []) h1

/-- **Function frames** (total correctness), with values below. -/
theorem tsafe_frame (hQ : Inv Q) {n : Nat} {f : Frame} {us : List FVal} :
    ∀ {c : ConfigFX H}, TSafe P fx (framePost n f us Q) c →
      TSafe P fx Q ⟨c.store, c.conts, f, fvals us ++ [.frame n c.frame c.code]⟩ := by
  intro c h
  induction h with
  | @intro c hq hs ih =>
    rcases c with ⟨s, K, F, b⟩
    refine .intro (frame_stops hQ hq) fun y hy => ?_
    obtain ⟨V₁, V₂, y', hV, hr, rfl⟩ := step_last hy us _ rfl rfl
    obtain ⟨-, rfl⟩ := wrap_root_vals hr trivial hV
    exact tsafe_frame_root hq ih hr

theorem tsafe_handler_root {s : Store H} {K : Conts} {f : Frame} {hs : List HClause}
    {us : List FVal} {b : List AdminFX} {y : ConfigFX H}
    (hq : ∀ o, Stops s f o b → handlerPost (totJ P fx Q) hs us Q s K f o)
    (ih : ∀ c', StepFX' P noHost fx ⟨s, K, f, b⟩ c' →
      TSafe P fx Q ⟨c'.store, c'.conts, c'.frame, fvals us ++ [.handler hs c'.code]⟩)
    {V₂ : List FVal} (hr : Root P fx s K f V₂ (.handler hs b) y) :
    TSafe P fx Q ⟨y.store, y.conts, y.frame, fvals us ++ y.code⟩ := by
  cases hr with
  | ctxHandler h => exact ih _ h
  | @brHandler _ vs l rest =>
    have h1 : Q s K f (.br l.toNat (us ++ vs)) := hq (.br l.toNat vs) ⟨l, rest, rfl, by simp⟩
    simpa using tsafe_br (P := P) (fx := fx) (R := []) h1
  | @returnHandler _ vs rest =>
    have h1 : Q s K f (.ret (us ++ vs)) := hq (.ret vs) ⟨rest, by simp⟩
    simpa using tsafe_ret (P := P) (fx := fx) (R := []) h1
  | @handlerVals _ vs =>
    have h1 : Q s K f (.normal (us ++ vs)) := hq (.normal vs) rfl
    simpa using tsafe_vals (P := P) (fx := fx) h1
  | trapHandler =>
    have h1 : Q s K f .trap := hq .trap rfl
    simpa using tsafe_trap (P := P) (fx := fx) (ws := us) (r := []) h1
  | @throwHandler _ a =>
    have h1 : Q s K f (.throw a) := hq (.throw a) rfl
    simpa using tsafe_throw (P := P) (fx := fx) (ws := us) (r := []) h1
  | @suspend _ E vs x ta ti l ht hE hc =>
    have h1 : Q s (K ++ [some ⟨E.plug⟩]) f (.br l.toNat (us ++ vs ++ [.cont K.length])) :=
      (hq (.susp E vs x) ⟨rfl, unhandled_of ht hE⟩).1 ta ti l ht hE hc
    simpa [FVal.toAdmin] using tsafe_br (P := P) (fx := fx) (R := []) h1
  | @switch _ E vs k C ct x ta ti hk ht hE hc =>
    exact (hq (.swtch E vs k ct x) ⟨rfl, unhandled_of ht hE⟩).1 C ta ti hk ht hE hc

/-- **The handler rule** (total correctness), with values below. -/
theorem tsafe_handler (hQ : Inv Q) {hs : List HClause} {us : List FVal} :
    ∀ {c : ConfigFX H}, TSafe P fx (handlerPost (totJ P fx Q) hs us Q) c →
      TSafe P fx Q ⟨c.store, c.conts, c.frame, fvals us ++ [.handler hs c.code]⟩ := by
  intro c h
  induction h with
  | @intro c hq hs ih =>
    rcases c with ⟨s, K, f, b⟩
    refine .intro (handler_stops hQ hq) fun y hy => ?_
    obtain ⟨V₁, V₂, y', hV, hr, rfl⟩ := step_last hy us _ rfl rfl
    obtain ⟨-, rfl⟩ := wrap_root_vals hr trivial hV
    exact tsafe_handler_root hq ih hr

end Wrap

/-! ## Instructions -/

section Instr

variable {Q : PostFX H} {s : Store H} {K : Conts} {f : Frame}

theorem notStop_core_plain {i : Instr} (hv : (Admin.plain i).val? = none) (ht : i ≠ .throwRef)
    (hb : ∀ l, i ≠ .br l) (hr : i ≠ .return_) : NotStop (.core (.plain i)) := by
  refine ⟨by simp [fval?, hv], id, fun l h => hb l (by simpa using h), fun h => hr (by simpa using h),
    by simp, fun h => ht (by simpa using h), by simp, by simp⟩

/-- Stopped code is never code whose first non-value cannot stop. -/
theorem stops_notStop {a : AdminFX} (ha : NotStop a) {V : List FVal} {R : List AdminFX} :
    ∀ o, Stops s f o (fvals V ++ a :: R) → Q s K f o :=
  fun _ ho => (not_stops ha ho).elim

theorem lastRes_y {V : List FVal} {a : AdminFX} {y : ConfigFX H}
    (h : StepFX' P noHost fx ⟨s, K, f, fvals V ++ [a]⟩ y) (ha : fval? a = none) :
    ∃ V₁ V₂ y', V = V₁ ++ V₂ ∧ Root P fx s K f V₂ a y' ∧
      y = ⟨y'.store, y'.conts, y'.frame, fvals V₁ ++ y'.code⟩ :=
  step_last h V a ha rfl

theorem inert_root {V₂ : List FVal} {i : Instr} {y' : ConfigFX H}
    (hi : Silmaril.Wasm.Logic.Hoare.Inert i) (hd : i ≠ .drop)
    (hr : Root P fx s K f V₂ (.core (.plain i)) y') :
    ∃ vs args c₀, V₂ = liftV (vs ++ args) ∧ Silmaril.Wasm.SingleThreaded.Det.Head P s f args (.plain i) c₀ ∧
      y' = ⟨c₀.store, K, c₀.frame, fvals (liftV vs) ++ c₀.code.map .core⟩ := by
  cases hr with
  | @core W _ s' f' cs' h =>
    obtain ⟨vs, args, c₀, rfl, hh, hc⟩ :=
      Silmaril.Wasm.SingleThreaded.inert_head_inv (rest := []) hi.1 hi.2.1 hi.2.2 h
    refine ⟨vs, args, c₀, rfl, hh, ?_⟩
    have hc' : s' = c₀.store ∧ f' = c₀.frame ∧ cs' = vals vs ++ c₀.code := by simpa using hc
    rw [hc'.1, hc'.2.1, hc'.2.2]
    simp [map_core_vals]
  | dropCont => exact absurd rfl hd
  | throwSeq => exact absurd rfl hi.2.1
  | invoke hc => exact absurd (Admin.isCallRef_of_IsCallRef hc) (by simp [hi.2.2])

/-- **A plain instruction without a host call** (`nop`, `i32.add`, `ref.func`, `call`, …): every
head step of its Core semantics leads to safe code. -/
theorem tsafe_inert {V : List FVal} {i : Instr} (hi : Silmaril.Wasm.Logic.Hoare.Inert i)
    (hd : i ≠ .drop) (hb : ∀ l, i ≠ .br l) (hr : i ≠ .return_)
    (h : ∀ V₁ args c₀, V = V₁ ++ liftV args →
      Silmaril.Wasm.SingleThreaded.Det.Head P s f args (.plain i) c₀ →
      TSafe P fx Q ⟨c₀.store, K, c₀.frame, fvals V₁ ++ c₀.code.map .core⟩) :
    TSafe P fx Q ⟨s, K, f, fvals V ++ [.core (.plain i)]⟩ := by
  have hn := notStop_core_plain hi.1 hi.2.1 hb hr
  refine .intro (stops_notStop hn) fun y hy => ?_
  obtain ⟨V₁, V₂, y', rfl, hroot, rfl⟩ := lastRes_y hy hn.1
  obtain ⟨vs, args, c₀, rfl, hh, rfl⟩ := inert_root hi hd hroot
  simpa using h (V₁ ++ liftV vs) args c₀ (by simp [liftV]) hh

/-- **`block`.** -/
theorem tsafe_block {V : List FVal} {bt : BlockType} {body : List InstrFX} {t₁ t₂ : List Silmaril.Wasm.Validation.CValType}
    (hbt : f.module.blockType? bt = some (t₁, t₂))
    (h : ∀ V₁ vs, V = V₁ ++ vs → vs.length = t₁.length →
      TSafe P fx Q ⟨s, K, f, fvals V₁ ++ [.label t₂.length [] (fvals vs ++ body.map InstrFX.toAdmin)]⟩) :
    TSafe P fx Q ⟨s, K, f, fvals V ++ [.block bt body]⟩ := by
  have hn : NotStop (.block bt body) := ⟨rfl, id, by simp, by simp, by simp, by simp, by simp, by simp⟩
  refine .intro (stops_notStop hn) fun y hy => ?_
  obtain ⟨V₁, V₂, y', rfl, hroot, rfl⟩ := lastRes_y hy hn.1
  cases hroot with
  | block hbt' hm =>
    rw [hbt] at hbt'
    obtain ⟨rfl, rfl⟩ : t₁ = _ ∧ t₂ = _ := by simpa using hbt'
    exact h V₁ V₂ rfl hm

/-- **`cont.new`** of a function reference. -/
theorem tsafe_contNew {V : List FVal} {a : Nat} {fi : FuncInst H} {ct : TypeIdx}
    (hf : s.funcs[a]? = some fi)
    (h : TSafe P fx Q ⟨s, K ++ [some (newCont a fi)], f, fvals V ++ [.contRef K.length]⟩) :
    TSafe P fx Q ⟨s, K, f, fvals (V ++ [.val (.ref (.func a))]) ++ [.fx (.contNew ct)]⟩ := by
  have hn : NotStop (.fx (.contNew ct)) := ⟨rfl, id, by simp, by simp, by simp, by simp, by simp, by simp⟩
  refine .intro (stops_notStop hn) fun y hy => ?_
  obtain ⟨V₁, V₂, y', hV, hroot, rfl⟩ := lastRes_y hy hn.1
  cases hroot with
  | @contNew a' fi' _ hf' =>
    obtain ⟨rfl, ha⟩ := List.append_inj' hV rfl
    obtain rfl : a' = a := by simpa using ha.symm
    obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
    simpa [newCont] using h
  | contNewNull => exact absurd (List.append_inj' hV rfl).2 (by simp)

/-- **`resume`** of a continuation, for every payload split. -/
theorem tsafe_resume {V : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx} {hos : List OnClause}
    {hs' : List HClause} (hk : K[k]? = some (some C)) (hr : hos.mapM (resolve s f) = some hs')
    (h : ∀ V₁ vs, V = V₁ ++ vs →
      TSafe P fx Q ⟨s, K.set k none, f, fvals V₁ ++ [.handler hs' (C.plug (fvals vs))]⟩) :
    TSafe P fx Q ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.fx (.resume ct hos)]⟩ := by
  have hn : NotStop (.fx (.resume ct hos)) := ⟨rfl, id, by simp, by simp, by simp, by simp, by simp, by simp⟩
  refine .intro (stops_notStop hn) fun y hy => ?_
  obtain ⟨V₁, V₂, y', hV, hroot, rfl⟩ := lastRes_y hy hn.1
  cases hroot with
  | @resume vs k' C' _ _ hs'' hk' hr' =>
    have hV' : V ++ [.cont k] = (V₁ ++ vs) ++ [.cont k'] := by rw [hV]; simp
    obtain ⟨hV₁, hkk⟩ := List.append_inj' hV' rfl
    obtain rfl : k' = k := by simpa using hkk.symm
    obtain rfl : C' = C := by simpa [hk] using hk'.symm
    obtain rfl : hs'' = hs' := by simpa [hr] using hr'.symm
    simpa using h V₁ vs hV₁
  | @resumeNull vs _ _ =>
    have hV' : V ++ [.cont k] = (V₁ ++ vs) ++ [.val (.ref .null)] := by rw [hV]; simp
    exact absurd (List.append_inj' hV' rfl).2 (by simp)
  | @resumeUsed vs k' _ _ hk' =>
    have hV' : V ++ [.cont k] = (V₁ ++ vs) ++ [.cont k'] := by rw [hV]; simp
    obtain rfl : k' = k := by simpa using (List.append_inj' hV' rfl).2.symm
    simp [hk] at hk'

/-- An unhandled `suspend` at the top stops, for every split of the values below it. -/
theorem tsafe_suspend {V : List FVal} {x : TagIdx}
    (h : ∀ E vs, E.plug (suspCode vs x) = fvals V ++ [.fx (.suspend x)] → Unhandled s f E x →
      Q s K f (.susp E vs x)) :
    TSafe P fx Q ⟨s, K, f, fvals V ++ [.fx (.suspend x)]⟩ := by
  refine .intro (fun o ho => ?_) fun y hy => ?_
  · have hfoc := stops_focus rfl ho
    cases o with
    | susp E vs x' =>
      rcases hfoc with hx | hw
      · obtain rfl : x' = x := by simpa using hx.symm
        exact h E vs ho.1.symm ho.2
      · exact hw.elim
    | swtch E vs k ct x' => exact (hfoc.elim (by simp) id).elim
    | _ => simp_all [FocusOf]
  · obtain ⟨V₁, V₂, y', -, hroot, -⟩ := lastRes_y hy rfl
    cases hroot

theorem last_val_eq {V A : List FVal} {x : FVal} {B : List Val} {y : Val}
    (h : V ++ [x] = A ++ liftV (B ++ [y])) : x = .val y := by
  have h' : V ++ [x] = (A ++ liftV B) ++ [.val y] := by rw [h]; simp [liftV]
  exact List.singleton_inj.mp (List.append_inj' h' rfl).2

theorem notStop_callRef {c : Admin} (hc : c.IsCallRef) : NotStop (.core c) := by
  have hv : fval? (.core c) = none := by
    simp [fval?, Silmaril.Proofs.Wasm.Models.FXLower.IsCallRef.val?_none hc]
  refine ⟨hv, id, fun l h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, by simp, by simp⟩ <;>
    · cases h; simp [Admin.IsCallRef] at hc

theorem invoke_core_root {V V₁ : List FVal} {a : Nat} {fi : FuncInst H} {hh : H} {c : Admin}
    {W : List Val} {s' : Store H} {f' : Frame} {cs' : List Admin} (hc : c.IsCallRef)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (hV : V ++ [.val (.ref (.func a))] = V₁ ++ liftV W)
    (h : Step P noHost ⟨s, f, vals W ++ [c]⟩ ⟨s', f', cs'⟩) : False := by
  have hcv : c.val? = none := Silmaril.Proofs.Wasm.Models.FXLower.IsCallRef.val?_none hc
  obtain ⟨vs, args, c₀, rfl, hh', -⟩ := Silmaril.Wasm.SingleThreaded.hostFree_head_inv (rest := [])
    hcv (by rintro rfl; simp [Admin.IsCallRef] at hc) (by rintro rfl; simp [Admin.IsCallRef] at hc) h
  rcases Silmaril.Proofs.Wasm.Models.FXAsyncBack.head_callRef_inv hc hh' with rfl |
      ⟨vs', a', fi', code, rfl, hf', hcode'⟩
  · exact absurd (last_val_eq hV) (by simp)
  · have ha : a' = a := by
      have := last_val_eq (A := V₁) (B := vs ++ vs') (y := .ref (.func a')) (by rw [hV]; simp)
      simpa using this.symm
    rw [ha, hf] at hf'
    rw [← Option.some.inj hf', hcode] at hcode'
    cases hcode'

/-- **A call of an FX function** (`invoke`). -/
theorem tsafe_invoke {V : List FVal} {a : Nat} {fi : FuncInst H} {hh : H} {F : FuncFX} {c : Admin}
    (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (hfx : fx hh = some F)
    (h : ∀ V₁ vs, V = V₁ ++ liftV vs → vs.length = F.nparams →
      TSafe P fx Q ⟨s, K, f, fvals V₁ ++ [.frame F.nresults (Frame.forCall F.module vs F.locals)
        [.label F.nresults [] (F.body.map InstrFX.toAdmin)]]⟩) :
    TSafe P fx Q ⟨s, K, f, fvals (V ++ [.val (.ref (.func a))]) ++ [.core c]⟩ := by
  have hn := notStop_callRef hc
  refine .intro (stops_notStop hn) fun y hy => ?_
  obtain ⟨V₁, V₂, y', hV, hroot, rfl⟩ := lastRes_y hy hn.1
  cases hroot with
  | core h' => exact (invoke_core_root hc hf hcode hV h').elim
  | dropCont => simp [Admin.IsCallRef] at hc
  | trapSeq => simp [Admin.IsCallRef] at hc
  | throwSeq => simp [Admin.IsCallRef] at hc
  | @invoke _ vs a' fi' hh' F' _ hf' hcode' hfx' hn' =>
    have hV' : V ++ [.val (.ref (.func a))] = (V₁ ++ liftV vs) ++ [.val (.ref (.func a'))] := by
      rw [hV]; simp
    obtain ⟨hV₁, ha⟩ := List.append_inj' hV' rfl
    obtain rfl : a' = a := by simpa using ha.symm
    obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
    obtain rfl : hh' = hh := by rw [hcode] at hcode'; simpa using hcode'.symm
    obtain rfl : F' = F := Option.some.inj (hfx'.symm.trans hfx)
    simpa using h V₁ vs hV₁ hn'

theorem drop_core_root {V V₁ : List FVal} {k : Nat} {W : List Val} {s' : Store H} {f' : Frame}
    {cs' : List Admin} (hV : V ++ [.cont k] = V₁ ++ liftV W)
    (h : Step P noHost ⟨s, f, vals W ++ [.plain .drop]⟩ ⟨s', f', cs'⟩) : False := by
  obtain ⟨vs, args, c₀, rfl, hh, -⟩ :=
    Silmaril.Wasm.SingleThreaded.inert_head_inv (rest := []) rfl (by simp) rfl h
  rcases List.eq_nil_or_concat args with rfl | ⟨args', y, rfl⟩
  · rcases List.eq_nil_or_concat vs with rfl | ⟨vs', y, rfl⟩
    · exact Silmaril.Proofs.Wasm.Models.FXVRuns.not_head_drop hh
    · exact absurd (last_val_eq (A := V₁) (B := vs') (y := y) (by rw [hV]; simp)) (by simp)
  · exact absurd (last_val_eq (A := V₁) (B := vs ++ args') (y := y) (by rw [hV]; simp)) (by simp)

/-- **Dropping a continuation.** -/
theorem tsafe_dropCont {V : List FVal} {k : Nat} (h : TSafe P fx Q ⟨s, K, f, fvals V⟩) :
    TSafe P fx Q ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.core (.plain .drop)]⟩ := by
  have hn : NotStop (.core (.plain .drop)) := notStop_core_plain rfl (by simp) (by simp) (by simp)
  refine .intro (stops_notStop hn) fun y hy => ?_
  obtain ⟨V₁, V₂, y', hV, hroot, rfl⟩ := lastRes_y hy hn.1
  cases hroot with
  | core h' => exact (drop_core_root hV h').elim
  | dropCont =>
    obtain ⟨rfl, -⟩ := List.append_inj' hV rfl
    simpa using h
  | invoke hc => simp [Admin.IsCallRef] at hc

/-- **`resume_throw`**: the continuation resumes with an exception at its `suspend`, for every
split of the values below it into the exception's fields. -/
theorem tsafe_resumeThrow {V : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx} {x : TagIdx}
    {hos : List OnClause} {hs' : List HClause} {ta : Nat} {ti : TagInst}
    (hk : K[k]? = some (some C)) (ht : s.tag? f x = some (ta, ti))
    (hr : hos.mapM (resolve s f) = some hs')
    (h : ∀ V₁ vs, V = V₁ ++ liftV vs →
      TSafe P fx Q ⟨s.addExn ⟨ta, vs⟩, K.set k none, f,
        fvals V₁ ++ [.handler hs' (C.plug (cthrowing s.exns.length))]⟩) :
    TSafe P fx Q ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.fx (.resumeThrow ct x hos)]⟩ := by
  have hn : NotStop (.fx (.resumeThrow ct x hos)) :=
    ⟨rfl, id, by simp, by simp, by simp, by simp, by simp, by simp⟩
  refine .intro (stops_notStop hn) fun y hy => ?_
  obtain ⟨V₁, V₂, y', hV, hroot, rfl⟩ := lastRes_y hy hn.1
  cases hroot with
  | @resumeThrow vs k' C' _ _ _ hs'' ta' ti' hk' ht' hr' =>
    have hV' : V ++ [.cont k] = (V₁ ++ liftV vs) ++ [.cont k'] := by rw [hV]; simp
    obtain ⟨hV₁, hkk⟩ := List.append_inj' hV' rfl
    obtain rfl : k' = k := by simpa using hkk.symm
    obtain rfl : C' = C := by simpa [hk] using hk'.symm
    obtain rfl : hs'' = hs' := by simpa [hr] using hr'.symm
    obtain ⟨rfl, rfl⟩ : ta' = ta ∧ ti' = ti := by simpa [ht] using ht'.symm
    simpa using h V₁ vs hV₁
  | @resumeThrowNull vs _ _ _ =>
    have hV' : V ++ [.cont k] = (V₁ ++ liftV vs) ++ [.val (.ref .null)] := by rw [hV]; simp
    exact absurd (List.append_inj' hV' rfl).2 (by simp)

end Instr

end Silmaril.Proofs.Wasm.FX.Logic.EveryRun
