module

public import Silmaril.Proofs.Wasm.Models.FXVRuns.Fnv

/-!
# `StepFX'` is `StepFX` on code without continuations or FX instructions

`NoK code`: the code is built from Core instructions, labels with Core continuations, frames
and handler frames only: no continuation reference, no FX instruction, no FX block. On such
code, without FX functions:

* **`step_noK`**: every `StepFX'` step is a `StepFX` step, to code of the same kind (FX values
  in the rules are then Core values);
* **`behavioursFX'_noK`**: so the `StepFX'` behaviours are the `StepFX` behaviours.

This is what carries the `StepFX` analysis of a Core call under a handler frame
(`Silmaril.Proofs.Wasm.Models.FXLower.behaviours_underHW`) to `StepFX'`.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXVRuns

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H}

mutual

/-- An FX instruction without continuations or FX instructions. -/
def NoK : AdminFX → Prop
  | .core _ => True
  | .label _ k b => (∀ i ∈ k, ∃ c, i = InstrFX.core c) ∧ NoKs b
  | .frame _ _ b => NoKs b
  | .handler _ b => NoKs b
  | _ => False

/-- FX code without continuations or FX instructions. -/
def NoKs : List AdminFX → Prop
  | [] => True
  | a :: l => NoK a ∧ NoKs l

end

@[simp] theorem noKs_nil : NoKs [] ↔ True := by simp [NoKs]

@[simp] theorem noKs_cons (a : AdminFX) (l : List AdminFX) : NoKs (a :: l) ↔ NoK a ∧ NoKs l := by
  simp [NoKs]

@[simp] theorem noKs_append (A B : List AdminFX) : NoKs (A ++ B) ↔ NoKs A ∧ NoKs B := by
  induction A with
  | nil => simp
  | cons a A ih => simp [ih, and_assoc]

@[simp] theorem noK_core (a : Admin) : NoK (.core a) ↔ True := by simp [NoK]

@[simp] theorem noK_label (n : Nat) (k : List InstrFX) (b : List AdminFX) :
    NoK (.label n k b) ↔ (∀ i ∈ k, ∃ c, i = InstrFX.core c) ∧ NoKs b := by simp [NoK]

@[simp] theorem noK_frame (n : Nat) (f : Frame) (b : List AdminFX) :
    NoK (.frame n f b) ↔ NoKs b := by simp [NoK]

@[simp] theorem noK_handler (hs : List HClause) (b : List AdminFX) :
    NoK (.handler hs b) ↔ NoKs b := by simp [NoK]

@[simp] theorem noK_fx (i : FXInstr) : NoK (.fx i) ↔ False := by simp [NoK]
@[simp] theorem noK_contRef (k : Nat) : NoK (.contRef k) ↔ False := by simp [NoK]
@[simp] theorem noK_block (bt : BlockType) (b : List InstrFX) : NoK (.block bt b) ↔ False := by
  simp [NoK]
@[simp] theorem noK_loop (bt : BlockType) (b : List InstrFX) : NoK (.loop bt b) ↔ False := by
  simp [NoK]
@[simp] theorem noK_if (bt : BlockType) (b₁ b₂ : List InstrFX) :
    NoK (.if_ bt b₁ b₂) ↔ False := by simp [NoK]

theorem noKs_map_core (cs : List Admin) : NoKs (cs.map .core) := by
  induction cs with
  | nil => trivial
  | cons c cs ih => exact (noKs_cons _ _).2 ⟨trivial, ih⟩

theorem noKs_cvals (W : List Val) : NoKs (cvals W) := noKs_map_core _

theorem noKs_cthrowing (a : Nat) : NoKs (cthrowing a) := noKs_map_core _

/-- FX values without continuations are Core values. -/
theorem noKs_fvals {vs : List FVal} (h : NoKs (fvals vs)) : ∃ W, vs = liftV W := by
  induction vs with
  | nil => exact ⟨[], rfl⟩
  | cons v vs ih =>
    rw [fvals_cons, noKs_cons] at h
    obtain ⟨W, rfl⟩ := ih h.2
    cases v with
    | val w => exact ⟨w :: W, rfl⟩
    | cont k => exact absurd h.1 (by simp [FVal.toAdmin])

/-- Core continuation instructions give code without continuations. -/
theorem noKs_kmap {k : List InstrFX} (hk : ∀ i ∈ k, ∃ c, i = InstrFX.core c) :
    NoKs (k.map InstrFX.toAdmin) := by
  induction k with
  | nil => trivial
  | cons i k ih =>
    obtain ⟨c, rfl⟩ := hk i List.mem_cons_self
    exact (noKs_cons _ _).2 ⟨trivial, ih fun j hj => hk j (List.mem_cons_of_mem _ hj)⟩

/-- What fills a context is part of the plugged code. -/
theorem noKs_plug (E : CtxV) {c : List AdminFX} (h : NoKs (E.plug c)) : NoKs c := by
  induction E with
  | hole => exact h
  | seq vs E rest ih =>
    simp only [CtxV.plug, noKs_append] at h
    exact ih h.1.2
  | label n k E ih =>
    simp only [CtxV.plug, noKs_cons, noK_label, noKs_nil, and_true] at h
    exact ih h.2
  | frame n f E ih =>
    simp only [CtxV.plug, noKs_cons, noK_frame, noKs_nil, and_true] at h
    exact ih h
  | handler hs E ih =>
    simp only [CtxV.plug, noKs_cons, noK_handler, noKs_nil, and_true] at h
    exact ih h

theorem liftV_ne_or {W : List Val} {rest : List AdminFX} (h : liftV W ≠ [] ∨ rest ≠ []) :
    W ≠ [] ∨ rest ≠ [] :=
  h.imp_left fun h' hW => h' (by rw [hW]; rfl)

/-- The `ctxt-instrs` case of `step_noK`. -/
theorem step_noK_seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
    {vs : List FVal} {es es' rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ [])
    (hx : NoKs (fvals vs ++ es ++ rest))
    (ih : NoKs es → StepFX P host noFX ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩ ∧ NoKs es') :
    StepFX P host noFX ⟨s, K, f, fvals vs ++ es ++ rest⟩ ⟨s', K', f', fvals vs ++ es' ++ rest⟩ ∧
      NoKs (fvals vs ++ es' ++ rest) := by
  simp only [noKs_append] at hx
  obtain ⟨⟨hv, he⟩, hr⟩ := hx
  obtain ⟨W, rfl⟩ := noKs_fvals hv
  obtain ⟨h', he'⟩ := ih he
  rw [fvals_liftV']
  exact ⟨.seq h' (liftV_ne_or hne), by simp only [noKs_append]; exact ⟨⟨noKs_cvals W, he'⟩, hr⟩⟩

/-! ## The rules, one by one -/

section Arms

variable {s s' : Store H} {K K' : List (Option ContFX)} {f f' fi fi' : Frame} {n : Nat}
  {k : List InstrFX} {hs : List HClause} {es es' rest : List AdminFX} {vs vs' : List FVal}
  {l : LabelIdx}

theorem noKs_label_body {B : List AdminFX} (h : NoKs [.label n k B]) :
    (∀ i ∈ k, ∃ c, i = InstrFX.core c) ∧ NoKs B :=
  (noK_label _ _ _).1 ((noKs_cons _ _).1 h).1

theorem noKs_frame_body {B : List AdminFX} (h : NoKs [.frame n fi B]) : NoKs B :=
  (noK_frame _ _ _).1 ((noKs_cons _ _).1 h).1

theorem noKs_handler_body {B : List AdminFX} (h : NoKs [.handler hs B]) : NoKs B :=
  (noK_handler _ _).1 ((noKs_cons _ _).1 h).1

theorem noKs_pre1 {A C D : List AdminFX} (h : NoKs (A ++ C ++ D)) : NoKs A :=
  ((noKs_append _ _).1 ((noKs_append _ _).1 h).1).1

theorem noKs_pre2 {A B C D : List AdminFX} (h : NoKs (A ++ B ++ C ++ D)) : NoKs A ∧ NoKs B :=
  (noKs_append _ _).1 (noKs_pre1 h)

/-- The conclusion of `step_noK` for a step `x → y`. -/
abbrev NoKStep (P : Profile) (host : HostSemantics H) (x y : ConfigFX H) : Prop :=
  NoKs x.code → StepFX P host noFX x y ∧ NoKs y.code

theorem noK_ctxLabel (ih : NoKStep P host ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
    NoKStep P host ⟨s, K, f, [.label n k es]⟩ ⟨s', K', f', [.label n k es']⟩ := by
  intro hx
  have hx' : (∀ i ∈ k, ∃ c, i = InstrFX.core c) ∧ NoKs es := by simpa using hx
  have ih' := ih hx'.2
  exact ⟨.ctxLabel ih'.1, by simpa using ⟨hx'.1, ih'.2⟩⟩

theorem noK_ctxFrame (ih : NoKStep P host ⟨s, K, fi, es⟩ ⟨s', K', fi', es'⟩) :
    NoKStep P host ⟨s, K, f, [.frame n fi es]⟩ ⟨s', K', f, [.frame n fi' es']⟩ := by
  intro hx
  have ih' := ih (by simpa using hx)
  exact ⟨.ctxFrame ih'.1, by simpa using ih'.2⟩

theorem noK_ctxHandler (ih : NoKStep P host ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
    NoKStep P host ⟨s, K, f, [.handler hs es]⟩ ⟨s', K', f', [.handler hs es']⟩ := by
  intro hx
  have ih' := ih (by simpa using hx)
  exact ⟨.ctxHandler ih'.1, by simpa using ih'.2⟩

theorem noK_labelVals :
    NoKStep P host ⟨s, K, f, [.label n k (fvals vs)]⟩ ⟨s, K, f, fvals vs⟩ := by
  intro hx
  obtain ⟨W, hW⟩ := noKs_fvals (noKs_label_body hx).2
  rw [hW, fvals_liftV']
  exact ⟨.labelVals, noKs_cvals W⟩

theorem noK_brLabelZero (hl : l.toNat = 0) (hn : vs.length = n) :
    NoKStep P host
      ⟨s, K, f, [.label n k (fvals vs' ++ fvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
      ⟨s, K, f, fvals vs ++ k.map InstrFX.toAdmin⟩ := by
  intro hx
  have hb := noKs_label_body hx
  obtain ⟨W', hW'⟩ := noKs_fvals (noKs_pre2 hb.2).1
  obtain ⟨W, hW⟩ := noKs_fvals (noKs_pre2 hb.2).2
  rw [hW', hW, fvals_liftV', fvals_liftV']
  exact ⟨.brLabelZero hl (by simpa [hW, liftV] using hn),
    (noKs_append _ _).2 ⟨noKs_cvals W, noKs_kmap hb.1⟩⟩

theorem noK_brLabelSucc (hl : 0 < l.toNat) :
    NoKStep P host ⟨s, K, f, [.label n k (fvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
      ⟨s, K, f, fvals vs ++ [.core (.plain (.br (labelPred l)))]⟩ := by
  intro hx
  have hx' : NoKs (fvals vs) := noKs_pre1 (noKs_label_body hx).2
  obtain ⟨W, hW⟩ := noKs_fvals hx'
  rw [hW, fvals_liftV']
  exact ⟨.brLabelSucc hl, (noKs_append _ _).2 ⟨noKs_cvals W, by simp⟩⟩

theorem noK_brHandler :
    NoKStep P host ⟨s, K, f, [.handler hs (fvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
      ⟨s, K, f, fvals vs ++ [.core (.plain (.br l))]⟩ := by
  intro hx
  have hx' : NoKs (fvals vs) := noKs_pre1 (noKs_handler_body hx)
  obtain ⟨W, hW⟩ := noKs_fvals hx'
  rw [hW, fvals_liftV']
  exact ⟨.brHandler, (noKs_append _ _).2 ⟨noKs_cvals W, by simp⟩⟩

theorem noK_returnLabel :
    NoKStep P host ⟨s, K, f, [.label n k (fvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
      ⟨s, K, f, fvals vs ++ [.core (.plain .return_)]⟩ := by
  intro hx
  have hx' : NoKs (fvals vs) := noKs_pre1 (noKs_label_body hx).2
  obtain ⟨W, hW⟩ := noKs_fvals hx'
  rw [hW, fvals_liftV']
  exact ⟨.returnLabel, (noKs_append _ _).2 ⟨noKs_cvals W, by simp⟩⟩

theorem noK_returnHandler :
    NoKStep P host ⟨s, K, f, [.handler hs (fvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
      ⟨s, K, f, fvals vs ++ [.core (.plain .return_)]⟩ := by
  intro hx
  have hx' : NoKs (fvals vs) := noKs_pre1 (noKs_handler_body hx)
  obtain ⟨W, hW⟩ := noKs_fvals hx'
  rw [hW, fvals_liftV']
  exact ⟨.returnHandler, (noKs_append _ _).2 ⟨noKs_cvals W, by simp⟩⟩

theorem noK_frameVals (hn : vs.length = n) :
    NoKStep P host ⟨s, K, f, [.frame n fi (fvals vs)]⟩ ⟨s, K, f, fvals vs⟩ := by
  intro hx
  obtain ⟨W, hW⟩ := noKs_fvals (noKs_frame_body hx)
  rw [hW, fvals_liftV']
  exact ⟨.frameVals (by simpa [hW, liftV] using hn), noKs_cvals W⟩

theorem noK_returnFrame (hn : vs.length = n) :
    NoKStep P host
      ⟨s, K, f, [.frame n fi (fvals vs' ++ fvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
      ⟨s, K, f, fvals vs⟩ := by
  intro hx
  obtain ⟨W', hW'⟩ := noKs_fvals (noKs_pre2 (noKs_frame_body hx)).1
  obtain ⟨W, hW⟩ := noKs_fvals (noKs_pre2 (noKs_frame_body hx)).2
  rw [hW', hW, fvals_liftV', fvals_liftV']
  exact ⟨.returnFrame (by simpa [hW, liftV] using hn), noKs_cvals W⟩

theorem noK_handlerVals :
    NoKStep P host ⟨s, K, f, [.handler hs (fvals vs)]⟩ ⟨s, K, f, fvals vs⟩ := by
  intro hx
  obtain ⟨W, hW⟩ := noKs_fvals (noKs_handler_body hx)
  rw [hW, fvals_liftV']
  exact ⟨.handlerVals, noKs_cvals W⟩

theorem noK_trapSeq (hne : vs ≠ [] ∨ rest ≠ []) :
    NoKStep P host ⟨s, K, f, fvals vs ++ [.core .trap] ++ rest⟩ ⟨s, K, f, [.core .trap]⟩ := by
  intro hx
  obtain ⟨W, rfl⟩ := noKs_fvals (noKs_pre1 hx)
  rw [fvals_liftV']
  exact ⟨.trapSeq (liftV_ne_or hne), by simp⟩

theorem noK_throwSeq {a : Nat} (hne : vs ≠ [] ∨ rest ≠ []) :
    NoKStep P host ⟨s, K, f, fvals vs ++ cthrowing a ++ rest⟩ ⟨s, K, f, cthrowing a⟩ := by
  intro hx
  obtain ⟨W, rfl⟩ := noKs_fvals (noKs_pre1 hx)
  rw [fvals_liftV']
  exact ⟨.throwSeq (liftV_ne_or hne), noKs_cthrowing _⟩

/-- A handler around a `suspend` or `switch` site has an FX instruction. -/
theorem not_noK_site {E : CtxV} {pre : List AdminFX} {i : FXInstr}
    (hx : NoKs [.handler hs (E.plug (pre ++ [.fx i]))]) : False := by
  have h' : NoKs (pre ++ [.fx i]) := noKs_plug E (noKs_handler_body hx)
  simp at h'

theorem not_noK_switch {E : CtxV} {k : Nat} {i : FXInstr}
    (hx : NoKs [.handler hs (E.plug (fvals vs ++ [.contRef k, .fx i]))]) : False :=
  not_noK_site (hs := hs) (E := E) (pre := fvals vs ++ [.contRef k]) (i := i)
    (by rw [List.append_assoc]; exact hx)

end Arms

/-- **On code without continuations, `StepFX'` steps are `StepFX` steps** (no FX functions). -/
theorem step_noK {x y : ConfigFX H} (h : StepFX' P host noFX x y) : NoKStep P host x y := by
  induction h with
  | core h => exact fun _ => ⟨.core h, noKs_map_core _⟩
  | seq _ hne ih => exact fun hx => step_noK_seq hne hx ih
  | ctxLabel _ ih => exact noK_ctxLabel ih
  | ctxFrame _ ih => exact noK_ctxFrame ih
  | ctxHandler _ ih => exact noK_ctxHandler ih
  | labelVals => exact noK_labelVals
  | brLabelZero hl hn => exact noK_brLabelZero hl hn
  | brLabelSucc hl => exact noK_brLabelSucc hl
  | brHandler => exact noK_brHandler
  | returnLabel => exact noK_returnLabel
  | returnHandler => exact noK_returnHandler
  | frameVals hn => exact noK_frameVals hn
  | returnFrame hn => exact noK_returnFrame hn
  | handlerVals => exact noK_handlerVals
  | trapSeq hne => exact noK_trapSeq hne
  | trapLabel => exact fun _ => ⟨.trapLabel, by simp⟩
  | trapFrame => exact fun _ => ⟨.trapFrame, by simp⟩
  | trapHandler => exact fun _ => ⟨.trapHandler, by simp⟩
  | throwSeq hne => exact noK_throwSeq hne
  | throwLabel => exact fun _ => ⟨.throwLabel, noKs_cthrowing _⟩
  | throwFrame => exact fun _ => ⟨.throwFrame, noKs_cthrowing _⟩
  | throwHandler => exact fun _ => ⟨.throwHandler, noKs_cthrowing _⟩
  | invoke _ _ _ hfx => exact absurd hfx (by simp [noFX])
  | suspend => exact fun hx => (not_noK_site hx).elim
  | switch => exact fun hx => (not_noK_switch hx).elim
  | _ => exact fun hx => absurd hx (by simp [cvals])

/-- Runs from code without continuations are `StepFX` runs. -/
theorem steps_noK {x y : ConfigFX H} (h : StepsFX' P host noFX x y) (hx : NoKs x.code) :
    StepsFX P host noFX x y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head hs _ ih =>
    obtain ⟨hs', hy⟩ := step_noK hs hx
    exact .head hs' (ih hy)

/-- Infinite runs from code without continuations are `StepFX` infinite runs. -/
theorem infinite_noK {x : ConfigFX H} (h : Silmaril.InfiniteTrace (StepFX' P host noFX) x)
    (hx : NoKs x.code) : Silmaril.InfiniteTrace (StepFX P host noFX) x := by
  refine Silmaril.InfiniteTrace.coinduct
    (fun y => NoKs y.code ∧ Silmaril.InfiniteTrace (StepFX' P host noFX) y) ?_ ⟨hx, h⟩
  rintro y ⟨hy, hdiv⟩
  obtain ⟨z, hz, hdiv'⟩ := Silmaril.InfiniteTrace.unfold hdiv
  obtain ⟨hz', hzk⟩ := step_noK hz hy
  exact ⟨z, hz', hzk, hdiv'⟩

/-- **On code without continuations the two semantics have the same behaviours.** -/
theorem behavioursFX'_noK {x : ConfigFX H} (hx : NoKs x.code) :
    behavioursFX' P host noFX x = behavioursFX P host noFX x := by
  refine Set.Subset.antisymm ?_ (Silmaril.Wasm.Models.FXV.behavioursFX_incl x)
  rintro b (⟨d, r, hrun, hd, rfl⟩ | ⟨rfl, hdiv⟩)
  · exact Or.inl ⟨d, r, steps_noK hrun hx, hd, rfl⟩
  · exact Or.inr ⟨rfl, infinite_noK hdiv hx⟩

end Silmaril.Proofs.Wasm.Models.FXVRuns
