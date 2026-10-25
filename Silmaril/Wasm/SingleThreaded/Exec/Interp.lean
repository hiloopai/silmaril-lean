module

public import Silmaril.Wasm.SingleThreaded.Exec.Run
public import Silmaril.Wasm.SingleThreaded.Exec.Status
public import Silmaril.Wasm.SingleThreaded.Exec.Pure
public import Silmaril.Wasm.SingleThreaded.Exec.Vector
public import Silmaril.Wasm.SingleThreaded.Exec.VariableTable
public import Silmaril.Wasm.SingleThreaded.Exec.Reference
public import Silmaril.Wasm.SingleThreaded.Exec.Memory
public import Silmaril.Wasm.SingleThreaded.Exec.AggregateNew
public import Silmaril.Wasm.SingleThreaded.Exec.AggregateAccess
public import Silmaril.Wasm.SingleThreaded.Exec.Control
public import Silmaril.Wasm.SingleThreaded.Exec.Admin

@[expose] public section

/-! # The computable interpreter

`interpHead o` is the full head step: it dispatches on the family of the head
instruction to the per-family head-step functions (this is a separate execution-head development (not included in this package)'s
`head memoryStep? aggAccessStep? o`, written out here because a separate execution-head development (not included in this package)
and `Exec/Run.lean` both declare `Exec.HeadFn`/`Exec.HeadSound` and so cannot be
imported together). `stepI o := step? (interpHead o)` is the interpreter step.

* `stepI_sound`, `stepI_complete`: hypothesis-free apart from `StoreOk` and
  `DeepAll IHeadInv` (the cast-target side conditions).
* `interpHead_exact`: at a valid store, the head step returns every non-context
  head step exactly.
* `runI o := run? (interpHead o)`; `runI_steps`, `runI_stopped_no_step`,
  `runI_complete` under a configuration invariant `I` (`InterpInv`) that implies
  `StoreOk` and `DeepAll IHeadInv` and is preserved by reduction. `typedInv`
  instantiates it with Core typing (`ConfigOk`), given preservation of
  `IHeadInv` (`IHeadInvPres`).
* `statusI_eq`, `runCI_sound`: `Exec/Status.lean` instantiated with `stepI o`.
-/

namespace Silmaril.Wasm.SingleThreaded.Exec

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

/-! ## The head step and the interpreter step -/

/-- The full computable head step. -/
def interpHead (o : GrowOracle) : HeadFn H := fun s f vs e =>
  match famOf e with
  | .parametric => parametricStep? o s f vs e
  | .numeric => numericStep? o s f vs e
  | .vector => vectorStep? o s f vs e
  | .variable => variableStep? o s f vs e
  | .table => tableStep? o s f vs e
  | .memory => memoryStep? o s f vs e
  | .reference => referenceStep? o s f vs e
  | .aggregate => aggNewStep? o s f vs e <|> aggAccessStep? o s f vs e
  | .control => controlStep? refOk? o s f vs e <|> adminStep? o s f vs e

/-- The interpreter step. -/
def stepI (o : GrowOracle) : Config H → Option (Config H) := step? (interpHead o)

/-- The interpreter run loop. -/
def runI (o : GrowOracle) : Nat → Config H → Config H × Bool := run? (interpHead o)

/-- The side conditions of the head step: cast targets are valid closed types
(a separate execution-head development (not included in this package)'s `HeadInv`). -/
def IHeadInv (f : Frame) (e : Admin) : Prop :=
  (∀ rt, (e = .plain (.refTest rt) ∨ e = .plain (.refCast rt)) → TyOk {} (f.module.instRef rt)) ∧
  (∀ l rt₁ rt₂, (e = .plain (.brOnCast l rt₁ rt₂) ∨ e = .plain (.brOnCastFail l rt₁ rt₂)) →
    TyOk {} (f.module.instRef rt₂))

namespace Interp

theorem orElse_some {α : Type} {a b : Option α} {x : α} (h : (a <|> b) = some x) :
    a = some x ∨ b = some x := by
  cases a <;> simp_all [HOrElse.hOrElse, OrElse.orElse, Option.orElse]

theorem orElse_none {α : Type} {a b : Option α} (h : (a <|> b) = none) :
    a = none ∧ b = none := by
  cases a <;> simp_all [HOrElse.hOrElse, OrElse.orElse, Option.orElse]

theorem orElse_of_some {α : Type} {a b : Option α} {x : α} (h : a = some x) :
    (a <|> b) = some x := by
  subst h; rfl

theorem orElse_of_none {α : Type} {a b : Option α} (h : a = none) : (a <|> b) = b := by
  subst h; rfl

/-- An aggregate instruction is allocating or handled by `aggAccessStep?`. -/
theorem aggAccessInstr_of {e : Admin} (hf : famOf e = .aggregate) (hn : ¬ AggNewInstr e) :
    AggAccessInstr e := by
  cases e with
  | plain i => cases i <;> simp_all [famOf, AggNewInstr, AggAccessInstr]
  | _ => simp [famOf] at hf

theorem aggNewStep?_none {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val} {e : Admin}
    (hn : ¬ AggNewInstr e) : aggNewStep? o s f vs e = none := by
  cases e with
  | plain i => cases i <;> simp_all [aggNewStep?, AggNewInstr]
  | _ => rfl

end Interp

open Interp

section head
variable {o : GrowOracle} {s : Store H}

theorem interpHead_sound (hs : StoreOk s) :
    ∀ f vs e k c, IHeadInv f e → interpHead o s f vs e = some (k, c) →
      k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) e c := by
  intro f vs e k c hinv h
  unfold interpHead at h
  split at h
  · exact parametricStep?_sound h
  · exact numericStep?_sound h
  · exact vectorStep?_sound h
  · exact variableStep?_sound h
  · exact tableStep?_sound h
  · exact memoryStep?_sound h
  · exact referenceStep?_sound hs hinv.1 h
  · rcases orElse_some h with h | h
    · exact aggNewStep?_sound h
    · exact aggAccessStep?_sound h
  · rcases orElse_some h with h | h
    · exact controlStep?_sound (refOk?_iff hs) hinv.2 h
    · exact adminStep?_sound h

end head

/-! ## Exactness of the structured administrative head rules -/

namespace Adm

variable {s : Store H} {f : Frame} {P : Profile}

theorem fnv_blocked (vs : List Val) (c : Admin) (rest : List Admin) (hc : c.val? = none) :
    fnv (vals vs ++ c :: rest) = (vs, c :: rest) := by
  simp [fnv_cons_of_none hc]

/-- A body at which `labelAt` fires does not step. -/
theorem labelAt_noStep {n : Nat} {cont : List Instr} {vs : List Val} {c : Admin}
    {rest : List Admin} {c' d : Config H} (hsome : labelAt s f n cont vs c rest = some c')
    (hst : Step P noHost ⟨s, f, vals vs ++ c :: rest⟩ d) : False := by
  unfold labelAt at hsome
  split at hsome
  · exact not_step_blocked hst (fnv_blocked vs _ rest rfl) (.inl ⟨_, rfl⟩)
  · exact not_step_blocked hst (fnv_blocked vs _ rest rfl) (.inr (.inl rfl))
  · exact not_step_blocked hst (fnv_blocked vs _ rest rfl) (.inr (.inr trivial))
  · exact not_step_blocked hst (fnv_blocked vs _ rest rfl) (.inr (.inr trivial))
  · split at hsome
    · exact not_step_throwing hst
    · cases hsome
  · split at hsome
    · exact not_step_trap hst
    · cases hsome
  · cases hsome

theorem handlerAt_noStep {n : Nat} {cs : List Catch} {vs : List Val} {c : Admin}
    {rest : List Admin} {c' d : Config H} (hsome : handlerAt s f n cs vs c rest = some c')
    (hst : Step P noHost ⟨s, f, vals vs ++ c :: rest⟩ d) : False := by
  unfold handlerAt at hsome
  split at hsome
  · exact not_step_blocked hst (fnv_blocked vs _ rest rfl) (.inl ⟨_, rfl⟩)
  · exact not_step_blocked hst (fnv_blocked vs _ rest rfl) (.inr (.inl rfl))
  · exact not_step_blocked hst (fnv_blocked vs _ rest rfl) (.inr (.inr trivial))
  · exact not_step_blocked hst (fnv_blocked vs _ rest rfl) (.inr (.inr trivial))
  · split at hsome
    · exact not_step_throwing hst
    · cases hsome
  · split at hsome
    · exact not_step_trap hst
    · cases hsome
  · cases hsome

theorem frameAt_noStep {n : Nat} {fi : Frame} {vs : List Val} {c : Admin}
    {rest : List Admin} {c' d : Config H} (hsome : frameAt s f n fi vs c rest = some c')
    (hst : Step P noHost ⟨s, fi, vals vs ++ c :: rest⟩ d) : False := by
  unfold frameAt at hsome
  split at hsome
  · exact not_step_blocked hst (fnv_blocked vs _ rest rfl) (.inr (.inl rfl))
  · exact not_step_blocked hst (fnv_blocked vs _ rest rfl) (.inr (.inr trivial))
  · exact not_step_blocked hst (fnv_blocked vs _ rest rfl) (.inr (.inr trivial))
  · split at hsome
    · exact not_step_throwing hst
    · cases hsome
  · split at hsome
    · exact not_step_trap hst
    · cases hsome
  · cases hsome

theorem body_split (body : List Admin) {vs : List Val} {c : Admin} {rest : List Admin}
    (h : splitVals body = (vs, c :: rest)) : body = vals vs ++ c :: rest := by
  have := SingleThreaded.splitVals_spec body
  rw [h] at this; simpa using this

theorem labelStep_noStep {n : Nat} {cont : List Instr} {body : List Admin} {c' d : Config H}
    (hsome : labelStep s f n cont body = some c') (hst : Step P noHost ⟨s, f, body⟩ d) : False := by
  unfold labelStep at hsome
  split at hsome
  · rename_i vs hsp
    rw [body_vals hsp] at hst; exact not_step_vals hst
  · rename_i vs c rest hsp
    rw [body_split body hsp] at hst; exact labelAt_noStep hsome hst

theorem handlerStep_noStep {n : Nat} {cs : List Catch} {body : List Admin} {c' d : Config H}
    (hsome : handlerStep s f n cs body = some c') (hst : Step P noHost ⟨s, f, body⟩ d) : False := by
  unfold handlerStep at hsome
  split at hsome
  · rename_i vs hsp
    rw [body_vals hsp] at hst; exact not_step_vals hst
  · rename_i vs c rest hsp
    rw [body_split body hsp] at hst; exact handlerAt_noStep hsome hst

theorem frameStep_noStep {n : Nat} {fi : Frame} {body : List Admin} {c' d : Config H}
    (hsome : frameStep s f n fi body = some c') (hst : Step P noHost ⟨s, fi, body⟩ d) : False := by
  unfold frameStep at hsome
  split at hsome
  · rename_i vs hsp
    rw [body_vals hsp] at hst; exact not_step_vals hst
  · rename_i vs c rest hsp
    rw [body_split body hsp] at hst; exact frameAt_noStep hsome hst

set_option hygiene false in
macro "exact_fin" : tactic => `(tactic| first
  | exact hsome.symm
  | (obtain ⟨-, rfl⟩ := hsome; subst_vars; simp; done)
  | (obtain ⟨-, rfl⟩ := hsome; simp_all))

theorem labelStep_exact {n : Nat} {cont : List Instr} {body : List Admin} {args : List Val}
    {c c' : Config H} (h : Head P s f args (.label n cont body) c)
    (hsome : labelStep s f n cont body = some c') : c' = c := by
  cases h with
  | ctxtLabel h => exact (labelStep_noStep hsome h).elim
  | labelVals hb => subst hb; simp [labelStep, Det.splitVals_vals] at hsome; exact hsome.symm
  | brLabelZero hb hl hn =>
    subst hb; rw [br_eq, labelStep_cons _ rfl] at hsome
    simp [labelAt, hl] at hsome
    exact_fin
  | brLabelSucc hb hl =>
    subst hb; rw [br_eq', labelStep_cons _ rfl] at hsome
    simp [labelAt, Nat.pos_iff_ne_zero.mp hl] at hsome
    exact_fin
  | returnLabel hb =>
    subst hb; rw [br_eq', labelStep_cons _ rfl] at hsome; simp [labelAt] at hsome
    exact_fin
  | returnCallRefLabel hb hc =>
    subst hb; rw [br_eq', labelStep_cons _ (IsReturnCallRef.val_none hc)] at hsome
    rcases IsReturnCallRef.cases hc with ⟨x, rfl⟩ | ⟨d, rfl⟩ <;> simp [labelAt] at hsome
    all_goals exact_fin
  | throwRefLabel =>
    rw [throw_eq, labelStep_cons _ rfl] at hsome; simp [labelAt] at hsome
    exact_fin
  | trapLabel => rw [trap_eq, labelStep_cons _ rfl] at hsome; simp [labelAt] at hsome; exact_fin
  | _ => fam_kill

theorem handlerStep_exact {n : Nat} {cs : List Catch} {body : List Admin} {args : List Val}
    {c c' : Config H} (h : Head P s f args (.handler n cs body) c)
    (hsome : handlerStep s f n cs body = some c') : c' = c := by
  cases h with
  | ctxtHandler h => exact (handlerStep_noStep hsome h).elim
  | handlerVals hb => subst hb; simp [handlerStep, Det.splitVals_vals] at hsome; exact hsome.symm
  | brHandler hb =>
    subst hb; rw [br_eq', handlerStep_cons _ rfl] at hsome; simp [handlerAt] at hsome
    exact_fin
  | returnHandler hb =>
    subst hb; rw [br_eq', handlerStep_cons _ rfl] at hsome; simp [handlerAt] at hsome
    exact_fin
  | returnCallRefHandler hb hc =>
    subst hb; rw [br_eq', handlerStep_cons _ (IsReturnCallRef.val_none hc)] at hsome
    rcases IsReturnCallRef.cases hc with ⟨x, rfl⟩ | ⟨d, rfl⟩ <;> simp [handlerAt] at hsome
    all_goals exact_fin
  | throwRefHandlerEmpty =>
    rw [throw_eq, handlerStep_cons _ rfl, handlerAt_throw] at hsome
    simp [throwHandler] at hsome
    exact_fin
  | throwRefHandlerCatch =>
    rw [throw_eq, handlerStep_cons _ rfl, handlerAt_throw] at hsome
    simp_all [throwHandler, catchStep]
  | throwRefHandlerCatchRef =>
    rw [throw_eq, handlerStep_cons _ rfl, handlerAt_throw] at hsome
    simp_all [throwHandler, catchStep]
  | throwRefHandlerCatchAll =>
    rw [throw_eq, handlerStep_cons _ rfl, handlerAt_throw] at hsome
    simp_all [throwHandler, catchStep]
  | throwRefHandlerCatchAllRef =>
    rw [throw_eq, handlerStep_cons _ rfl, handlerAt_throw] at hsome
    simp_all [throwHandler, catchStep]
  | throwRefHandlerNext hnm =>
    rw [throw_eq, handlerStep_cons _ rfl, handlerAt_throw] at hsome
    rename_i cc cs a
    cases cc with
    | catch_ x l =>
      simp only [CatchMatches] at hnm
      simp only [throwHandler, catchStep] at hsome
      cases hx : s.exns[a]? with
      | none => simp [hx] at hsome; exact hsome.symm
      | some e =>
        cases ht : f.module.tags[x.toNat]? with
        | none => simp [hx, ht] at hsome; exact hsome.symm
        | some t =>
          have : e.tag ≠ t := fun h => hnm ⟨e, t, hx, ht, h⟩
          simp [hx, ht, this] at hsome; exact hsome.symm
    | catchRef x l =>
      simp only [CatchMatches] at hnm
      simp only [throwHandler, catchStep] at hsome
      cases hx : s.exns[a]? with
      | none => simp [hx] at hsome; exact hsome.symm
      | some e =>
        cases ht : f.module.tags[x.toNat]? with
        | none => simp [hx, ht] at hsome; exact hsome.symm
        | some t =>
          have : e.tag ≠ t := fun h => hnm ⟨e, t, hx, ht, h⟩
          simp [hx, ht, this] at hsome; exact hsome.symm
    | catchAll l => exact absurd trivial hnm
    | catchAllRef l => exact absurd trivial hnm
  | trapHandler =>
    rw [trap_eq, handlerStep_cons _ rfl] at hsome; simp [handlerAt] at hsome; exact_fin
  | _ => fam_kill

theorem frameStep_exact {n : Nat} {fi : Frame} {body : List Admin} {args : List Val}
    {c c' : Config H} (h : Head P s f args (.frame n fi body) c)
    (hsome : frameStep s f n fi body = some c') : c' = c := by
  cases h with
  | ctxtFrame h => exact (frameStep_noStep hsome h).elim
  | frameVals hb hn => subst hb; simp [frameStep, Det.splitVals_vals, hn] at hsome; exact hsome.symm
  | returnFrame hb hn =>
    subst hb; rw [br_eq, frameStep_cons _ rfl] at hsome
    simp [frameAt] at hsome
    exact_fin
  | returnCallRefFrameNull hb hc =>
    subst hb
    rw [show ∀ (vs : List Val) (c : Admin) (rest : List Admin), vals vs ++ [.ref .null, c] ++ rest =
        vals (vs ++ [.ref .null]) ++ c :: rest by intros; simp [Val.toAdmin],
      frameStep_cons _ (IsReturnCallRef.val_none hc), frameAt_rcr hc] at hsome
    simp [frameRCR] at hsome
    exact_fin
  | returnCallRefFrameAddr hb hc hf he hn =>
    subst hb
    rw [show ∀ (vs' vs : List Val) (a : Nat) (c : Admin) (rest : List Admin),
        vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest =
        vals (vs' ++ vs ++ [.ref (.func a)]) ++ c :: rest by intros; simp [Val.toAdmin],
      frameStep_cons _ (IsReturnCallRef.val_none hc), frameAt_rcr hc] at hsome
    simp [frameRCR, hf, Expand.iff.1 he] at hsome
    exact_fin
  | throwRefFrame =>
    rw [throw_eq, frameStep_cons _ rfl] at hsome; simp [frameAt] at hsome; exact_fin
  | trapFrame => rw [trap_eq, frameStep_cons _ rfl] at hsome; simp [frameAt] at hsome; exact_fin
  | _ => fam_kill

theorem adminStep?_exact {o : GrowOracle} {s : Store H} {f : Frame} {vs args : List Val}
    {e : Admin} {k : Nat} {c c' : Config H} (hsome : adminStep? o s f vs e = some (k, c'))
    (h : Head (profile o) s f args e c) : k = args.length ∧ c' = c := by
  cases e with
  | label n cont is =>
    simp only [adminStep?, Option.map_eq_some_iff, Prod.mk.injEq] at hsome
    obtain ⟨c'', hc'', rfl, rfl⟩ := hsome
    obtain rfl := Head.args_nil_label h
    exact ⟨rfl, labelStep_exact h hc''⟩
  | handler n cs is =>
    simp only [adminStep?, Option.map_eq_some_iff, Prod.mk.injEq] at hsome
    obtain ⟨c'', hc'', rfl, rfl⟩ := hsome
    obtain rfl := Head.args_nil_handler h
    exact ⟨rfl, handlerStep_exact h hc''⟩
  | frame n fi is =>
    simp only [adminStep?, Option.map_eq_some_iff, Prod.mk.injEq] at hsome
    obtain ⟨c'', hc'', rfl, rfl⟩ := hsome
    obtain rfl := Head.args_nil_frame h
    exact ⟨rfl, frameStep_exact h hc''⟩
  | _ => simp [adminStep?] at hsome

end Adm

/-! ## Soundness, completeness and exactness of the head step -/

section head
variable {o : GrowOracle} {s : Store H}

theorem controlStep?_nest {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val} {e : Admin}
    (hn : Adm.IsNest e) : controlStep? refOk? o s f vs e = none := by
  cases e <;> simp_all [Adm.IsNest, controlStep?, Admin.isCallRef]

/-- **Exactness** of the head step at a valid store (the per-store form of
`HeadExact`). -/
theorem interpHead_exact (hs : StoreOk s) :
    ∀ f vs args e c, IHeadInv f e → Head (profile o) s f args e c → (∃ q, vs = q ++ args) →
      interpHead o s f vs e = some (args.length, c) ∨
        (interpHead o s f vs e = none ∧ IsCtxtHead (profile o) s f e c) := by
  intro f vs args e c hinv h hq
  unfold interpHead
  split
  all_goals rename_i hf
  · exact .inl (parametricStep?_complete h hf hq)
  · exact .inl (numericStep?_complete h hf hq)
  · exact .inl (vectorStep?_complete h hf hq)
  · exact .inl (variableStep?_complete h hf hq)
  · exact .inl (tableStep?_complete h hf hq)
  · exact .inl (memoryStep?_complete h hf hq)
  · exact .inl (referenceStep?_complete hs hinv.1 h hf hq)
  · left
    by_cases hi : AggNewInstr e
    · exact orElse_of_some (aggNewStep?_complete h hi hq)
    · rw [orElse_of_none (aggNewStep?_none hi)]
      exact aggAccessStep?_complete h (aggAccessInstr_of hf hi) hq
  · by_cases hn : Adm.IsNest e
    · rw [orElse_of_none (controlStep?_nest hn)]
      cases ha : adminStep? o s f vs e with
      | none =>
        refine .inr ⟨rfl, ?_⟩
        rcases adminStep?_none ha h with h' | h' | h' | h'
        · exact .inl h'
        · exact .inr (.inl h')
        · exact .inr (.inr h')
        · exact absurd hn h'
      | some p =>
        obtain ⟨k, c'⟩ := p
        obtain ⟨rfl, rfl⟩ := Adm.adminStep?_exact ha h
        exact .inl rfl
    · left
      exact orElse_of_some (controlStep?_complete (refOk?_iff hs) hinv.2 h hf
        (by rintro n cont is rfl; exact hn trivial)
        (by rintro n cs is rfl; exact hn trivial)
        (by rintro n fi is rfl; exact hn trivial) hq)

theorem interpHead_complete (hs : StoreOk s) :
    ∀ f vs args e c, IHeadInv f e → Head (profile o) s f args e c → (∃ q, vs = q ++ args) →
      interpHead o s f vs e = none → IsCtxtHead (profile o) s f e c := by
  intro f vs args e c hi hH hq hn
  rcases interpHead_exact hs f vs args e c hi hH hq with h | ⟨-, h⟩
  · rw [h] at hn; cases hn
  · exact h

/-- **Soundness** of the interpreter step. -/
theorem stepI_sound {c c' : Config H} (hs : StoreOk c.store)
    (hi : DeepAll IHeadInv c.frame c.code) (h : stepI o c = some c') :
    Step (profile o) noHost c c' :=
  step?_sound (interpHead_sound hs) rfl hi h

/-- **Completeness** of the interpreter step. -/
theorem stepI_complete {c c' : Config H} (hs : StoreOk c.store)
    (hi : DeepAll IHeadInv c.frame c.code) (h : Step (profile o) noHost c c') :
    (stepI o c).isSome :=
  step?_complete (interpHead_complete hs) rfl hi h

end head

/-! ## The run loop under a store invariant -/

/-- A configuration invariant for the interpreter: it gives a valid store and the
cast side conditions, and is preserved by reduction. -/
structure InterpInv (o : GrowOracle) (I : Config H → Prop) : Prop where
  storeOk : ∀ c, I c → StoreOk c.store
  headInv : ∀ c, I c → DeepAll IHeadInv c.frame c.code
  pres : ∀ c c', I c → Step (profile o) noHost c c' → I c'

section run
variable {o : GrowOracle} {I : Config H → Prop}

theorem InterpInv.steps (hI : InterpInv o I) {c c' : Config H}
    (h : Steps (profile o) noHost c c') (hc : I c) : I c' := by
  induction h with
  | refl => exact hc
  | tail _ hst ih => exact hI.pres _ _ ih hst

/-- **Soundness** of the interpreter run loop. -/
theorem runI_steps (hI : InterpInv o I) :
    ∀ (n : Nat) (c : Config H), I c → Steps (profile o) noHost c (runI o n c).1
  | 0, c, _ => .refl
  | n + 1, c, hc => by
    show Steps _ _ c (run? (interpHead o) (n + 1) c).1
    cases hs : step? (interpHead o) c with
    | none => rw [run?_succ_none hs]
    | some d =>
      have h1 : Step (profile o) noHost c d := stepI_sound (hI.storeOk c hc) (hI.headInv c hc) hs
      rw [run?_succ_some hs]
      exact Relation.ReflTransGen.head h1 (runI_steps hI n d (hI.pres _ _ hc h1))

/-- A stopped result of the interpreter run loop has no core step. -/
theorem runI_stopped_no_step (hI : InterpInv o I) {n : Nat} {c : Config H} (hc : I c)
    (h : (runI o n c).2 = true) (c' : Config H) :
    ¬ Step (profile o) noHost (runI o n c).1 c' := by
  intro hst
  have hi' := hI.steps (runI_steps hI n c hc) hc
  have := stepI_complete (hI.storeOk _ hi') (hI.headInv _ hi') hst
  rw [stepI, show runI o n c = run? (interpHead o) n c from rfl,
    run?_stopped n c h] at this
  cases this

/-- Maximality of the driver, at a fixed store where the head step is exact. -/
theorem step?_maximal_at {head : HeadFn H} {Inv : Frame → Admin → Prop} {s : Store H}
    (hx : ∀ f vs args e c, Inv f e → Head (profile o) s f args e c → (∃ q, vs = q ++ args) →
      head s f vs e = some (args.length, c) ∨
        (head s f vs e = none ∧ IsCtxtHead (profile o) s f e c)) :
    ∀ (n : Nat) (c c₁ d : Config H), sizeOf c.code = n → c.store = s →
      DeepAll Inv c.frame c.code →
      Step (profile o) noHost c c₁ → step? head c = some d →
      Relation.ReflGen (Step (profile o) noHost) c₁ d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rintro ⟨s₀, f, code⟩ c₁ d hn hst hinv hstep hd
  simp only at hinv hn hst
  subst hst
  rcases Step.decomp hstep with hdec | hb
  · obtain ⟨vs₀, args, e, rest, c₀, hcode, hH, rfl⟩ := hdec
    simp only at hcode hH
    have hg := hH.good
    have hs : splitVals code = (vs₀ ++ args, e :: rest) := by
      rw [hcode, ← List.append_assoc, ← vals_append]; exact splitVals_vals_cons hg.val_none rest
    rw [step?_cons (c := ⟨s₀, f, code⟩) hs] at hd
    have hat : Drv.DeepAt Inv f e := by
      rw [hcode, ← List.append_assoc, ← vals_append] at hinv; exact Drv.deepAll_split hinv
    have htrap : Drv.isTrap e = false := by
      cases e <;> simp [Drv.isTrap]; exact hg.ne_trap rfl
    have hthrow : Drv.throwAddr? (vs₀ ++ args) e = none := by
      unfold Drv.throwAddr?
      split
      · rw [hg.throwRef rfl]; simp
      · rfl
    simp only [Drv.layer, htrap, hthrow] at hd
    rcases hx f (vs₀ ++ args) args e c₀ hat.inv hH ⟨vs₀, rfl⟩ with hsome | ⟨hnone, hctx⟩
    · rw [hsome] at hd
      simp only [Option.some.injEq] at hd
      subst hd
      have : (vs₀ ++ args).take ((vs₀ ++ args).length - args.length) = vs₀ := by
        simp
      simp only [this]
      exact .refl
    · rw [hnone] at hd
      simp only at hd
      rcases hctx with ⟨n', cont, is, s', f', is', rfl, rfl, hin⟩ |
        ⟨n', cs, is, s', f', is', rfl, rfl, hin⟩ | ⟨n', fi, is, s', fi', is', rfl, rfl, hin⟩
      · obtain rfl := Head.args_nil_label hH
        obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hd
        have hr := ih (sizeOf is)
          (by rw [← hn, hcode]; have := Drv.sizeOf_label_body (n := n') (cont := cont) (is := is)
              have := sizeOf_lt_code (vs := vs₀) (args := []) (e := .label n' cont is) (rest := rest)
              omega)
          ⟨s₀, f, is⟩ _ d' rfl rfl hat.2 hin hd'
        cases hr with
        | refl => simpa using (Relation.ReflGen.refl : Relation.ReflGen (Step (profile o) noHost) _ _)
        | single h =>
          have := lift_instrs vs₀ rest _ _ (lift_label n' cont _ _ h)
          exact .single (by simpa using this)
      · obtain rfl := Head.args_nil_handler hH
        obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hd
        have hr := ih (sizeOf is)
          (by rw [← hn, hcode]; have := Drv.sizeOf_handler_body (n := n') (cs := cs) (is := is)
              have := sizeOf_lt_code (vs := vs₀) (args := []) (e := .handler n' cs is) (rest := rest)
              omega)
          ⟨s₀, f, is⟩ _ d' rfl rfl hat.2 hin hd'
        cases hr with
        | refl => simpa using (Relation.ReflGen.refl : Relation.ReflGen (Step (profile o) noHost) _ _)
        | single h =>
          have := lift_instrs vs₀ rest _ _ (lift_handler n' cs _ _ h)
          exact .single (by simpa using this)
      · obtain rfl := Head.args_nil_frame hH
        obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hd
        have hr := ih (sizeOf is)
          (by rw [← hn, hcode]; have := Drv.sizeOf_frame_body (n := n') (fi := fi) (is := is)
              have := sizeOf_lt_code (vs := vs₀) (args := []) (e := .frame n' fi is) (rest := rest)
              omega)
          ⟨s₀, fi, is⟩ _ d' rfl rfl hat.2 hin hd'
        cases hr with
        | refl => simpa using (Relation.ReflGen.refl : Relation.ReflGen (Step (profile o) noHost) _ _)
        | single h =>
          have := lift_instrs vs₀ rest ⟨s', f, _⟩ ⟨d'.store, f, _⟩ (lift_frame n' f _ _ h)
          exact .single (by simpa using this)
  · obtain ⟨p, q, u, r, hqu, ⟨-, hcode, rfl⟩ | ⟨a, -, hcode, rfl⟩⟩ := fnv_bubble hb <;>
      simp only at hcode
    · have hs : splitVals code = (p ++ q, .trap :: (u ++ r)) := by
        rw [hcode]; exact splitVals_vals_cons rfl _
      rw [step?_cons (c := ⟨s₀, f, code⟩) hs] at hd
      simp only [Drv.layer, Drv.isTrap] at hd
      split at hd
      · cases hd
      · cases hd
        exact bubble_to (o := o) (.inl rfl)
    · have hs : splitVals code = (p ++ q ++ [.ref (.exn a)], .plain .throwRef :: (u ++ r)) := by
        rw [hcode]; exact splitVals_vals_cons rfl _
      rw [step?_cons (c := ⟨s₀, f, code⟩) hs] at hd
      simp only [Drv.layer, Drv.isTrap, Drv.throwAddr?, List.getLast?_append,
        List.getLast?_singleton, Option.some_or, List.dropLast_concat] at hd
      split at hd
      · cases hd
      · cases hd
        exact bubble_to (o := o) (.inr ⟨a, rfl⟩)

/-- Maximality of the interpreter step. -/
theorem stepI_maximal {c c₁ d : Config H} (hs : StoreOk c.store)
    (hi : DeepAll IHeadInv c.frame c.code) (h : Step (profile o) noHost c c₁)
    (hd : stepI o c = some d) : Relation.ReflGen (Step (profile o) noHost) c₁ d :=
  step?_maximal_at (interpHead_exact hs) _ c c₁ d rfl rfl hi h hd

theorem runI_complete_aux (hI : InterpInv o I) {c' : Config H}
    (hnf : ∀ x, ¬ Step (profile o) noHost c' x) :
    ∀ (n : Nat) (c : Config H), I c →
      Run.StepsN (Step (profile o) noHost) n c c' → runI o (n + 1) c = (c', true) := by
  intro n
  induction n with
  | zero =>
    intro c hc hN
    obtain rfl : c = c' := by cases hN; rfl
    show run? (interpHead o) 1 c = (c, true)
    cases hs : step? (interpHead o) c with
    | none => exact run?_succ_none hs
    | some d => exact absurd (stepI_sound (hI.storeOk c hc) (hI.headInv c hc) hs) (hnf d)
  | succ m ih =>
    intro c hc hN
    show run? (interpHead o) (m + 1 + 1) c = (c', true)
    cases hs : step? (interpHead o) c with
    | none =>
      rw [run?_succ_none hs]
      cases hN with
      | refl => rfl
      | step h _ =>
        have := stepI_complete (hI.storeOk c hc) (hI.headInv c hc) h
        rw [stepI, hs] at this; cases this
    | some d =>
      have hcd : Step (profile o) noHost c d := stepI_sound (hI.storeOk c hc) (hI.headInv c hc) hs
      rw [run?_succ_some hs]
      have hid := hI.pres _ _ hc hcd
      cases hN with
      | refl => exact absurd hcd (hnf _)
      | step h₁ hrest =>
        rcases stepI_maximal (hI.storeOk c hc) (hI.headInv c hc) h₁ hs with _ | h₁d
        · exact ih d hid hrest
        · exact ih d hid (Run.StepsN.diamond (fun _ _ _ => step_join) hnf hrest h₁d)

/-- **Completeness** of the interpreter run loop: if `c` reaches a configuration
`c'` with no core step, some fuel makes the loop stop exactly at `c'`. -/
theorem runI_complete (hI : InterpInv o I) {c c' : Config H} (hc : I c)
    (h : Steps (profile o) noHost c c') (hnf : ∀ x, ¬ Step (profile o) noHost c' x) :
    ∃ n, runI o n c = (c', true) := by
  obtain ⟨n, hn⟩ := Run.StepsN.of_rtg h
  exact ⟨n + 1, runI_complete_aux hI hnf n c hc hn⟩

end run

/-! ## The typed invariant -/

/-- Preservation of the cast side conditions by reduction of a typed
configuration (taken as a hypothesis). -/
def IHeadInvPres (o : GrowOracle) (ts : List CValType) : Prop :=
  ∀ c c' : Config H, ConfigOk c ts → DeepAll IHeadInv c.frame c.code →
    Step (profile o) noHost c c' → DeepAll IHeadInv c'.frame c'.code

/-- Core typing together with the cast side conditions is an interpreter
invariant, given `IHeadInvPres`. -/
theorem typedInv {o : GrowOracle} {ts : List CValType} (hp : IHeadInvPres (H := H) o ts) :
    InterpInv o (fun c : Config H => ConfigOk c ts ∧ DeepAll IHeadInv c.frame c.code) where
  storeOk _ h := ConfigOk.storeOk h.1
  headInv _ h := h.2
  pres c c' h hst :=
    ⟨(Step.preservation (P := profile o) divHost_ok h.1 (Step.of_noHost divHost hst)).1,
      hp c c' h.1 h.2 hst⟩

/-! ## Computable status -/

section status
variable {o : GrowOracle} {I : Config H → Prop}

/-- `statusC` with the interpreter step is the thread status. -/
theorem statusI_eq {s : Store H} {t : Thread} (hs : StoreOk (t.config s).store)
    (hi : DeepAll IHeadInv (t.config s).frame (t.config s).code) :
    statusC (stepI o) s t = status o s t :=
  statusC_eq o (fun _ h => stepI_sound hs hi h) (fun _ h => stepI_complete hs hi h)

theorem statusI_eq_of (hI : InterpInv o I) {s : Store H} {t : Thread} (hi : I (t.config s)) :
    statusC (stepI o) s t = status o s t :=
  statusI_eq (hI.storeOk _ hi) (hI.headInv _ hi)

/-- **Soundness** of the fuelled runner with the interpreter step: the result is
reachable by internal steps, satisfies the invariant, and a non-`running`
result is the true status. -/
theorem runCI_sound (hI : InterpInv o I) (fuel : Nat) (s : Store H) (t : Thread)
    (hi : I (t.config s)) {s' : Store H} {t' : Thread} {st : Status H}
    (h : runC (stepI o) fuel s t = (s', t', st)) :
    Relation.ReflTransGen (Internal o) (s, t) (s', t') ∧ I (t'.config s') ∧
      (st ≠ .running → st = status o s' t') := by
  induction fuel generalizing s t with
  | zero =>
    simp only [runC, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨.refl, hi, fun hne => absurd rfl hne⟩
  | succ n ih =>
    have fin : ∀ st₀, statusC (stepI o) s t = st₀ → (s, t, st₀) = (s', t', st) →
        Relation.ReflTransGen (Internal o) (s, t) (s', t') ∧ I (t'.config s') ∧
        (st ≠ .running → st = status o s' t') := by
      intro st₀ hs h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨.refl, hi, fun _ => ?_⟩
      rw [← hs]
      exact statusI_eq_of hI hi
    unfold runC at h
    cases hs : statusC (stepI o) s t with
    | running =>
      rw [hs] at h
      dsimp only at h
      cases hin : internalC (stepI o) (s, t) with
      | none =>
        rw [hin] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨.refl, hi, fun hne => absurd rfl hne⟩
      | some p =>
        obtain ⟨s₁, t₁⟩ := p
        rw [hin] at h
        have hsound : ∀ c', stepI o (t.config s) = some c' →
            Step (profile o) (fun _ _ _ _ => False) (t.config s) c' :=
          fun _ h => stepI_sound (hI.storeOk _ hi) (hI.headInv _ hi) h
        have hi₁ : I (t₁.config s₁) := by
          unfold internalC at hin
          obtain ⟨c', hc', heq⟩ := Option.map_eq_some_iff.mp hin
          cases heq
          exact hI.pres _ _ hi (hsound c' hc')
        obtain ⟨hr, hI', hst⟩ := ih s₁ t₁ hi₁ h
        exact ⟨.head (internalC_sound o hsound hin) hr, hI', hst⟩
    | returned r => rw [hs] at h; exact fin _ hs h
    | callout hc args => rw [hs] at h; exact fin _ hs h
    | stuck => rw [hs] at h; exact fin _ hs h

end status

end Silmaril.Wasm.SingleThreaded.Exec
