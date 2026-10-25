module

public import Silmaril.Wasm.SingleThreaded.Exec.Interp
public import Silmaril.Wasm.SingleThreaded.Exec.EndToEnd
public import Silmaril.Wasm.Execution.Core.Soundness.PresBrCast

@[expose] public section

/-! # The interpreter on typed configurations

Typed configurations satisfy `IHeadInv` deeply (port of a separate typed execution-head inversion development (not included in this package)
on top of `Exec/Interp.lean`), so `IHeadInvPres` holds and Core typing alone is an
interpreter invariant (`typedInv'`). Corollaries specialise the run loop, status
and end-to-end theorems to typed configurations with no side conditions.
-/

namespace Silmaril.Wasm.SingleThreaded.Exec

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

namespace IHeadInvTyped

/-- The part of `StateOk` the invariant needs: the context's types are the frame's
module types, and they are closed. -/
def TypesOk (f : Frame) (C : Context) : Prop :=
  C.types = f.module.types ∧ ∀ d ∈ C.types, TyOk {} d

theorem withLocals_types (C : Context) (xs : List Nat) (lts : List LocalType) :
    (C.withLocals xs lts).types = C.types := by
  induction xs generalizing C lts with
  | nil => cases lts <;> rfl
  | cons x xs ih =>
    cases lts with
    | nil => rfl
    | cons lt lts => simp only [Context.withLocals]; rw [ih]; rfl

theorem TypesOk.initLocals {f : Frame} {C : Context} (h : TypesOk f C) (xs : List Nat) :
    TypesOk f (C.initLocals xs) := by
  unfold TypesOk Context.initLocals; rw [withLocals_types]; exact h

theorem TypesOk.withLabel {f : Frame} {C : Context} (h : TypesOk f C) (ts : List CValType) :
    TypesOk f (C.withLabel ts) := h

theorem TypesOk.of_frameOk {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C) :
    TypesOk f C := ⟨h.types_eq, h.typesOkEmptyCast⟩

theorem TypesOk.of_stateOk {s : Store H} {f : Frame} {C : Context} (h : StateOk s f C) :
    TypesOk f C := of_frameOk h.2

theorem TypesOk.cast {f : Frame} {C : Context} (h : TypesOk f C) {rt : RefType}
    (hok : TyOk C.toTypeCtx (C.closeRef rt)) : TyOk {} (f.module.instRef rt) := by
  rw [← closeRef_eqCtl h.1]
  exact closeRef_okEmptyCast h.2 hok

theorem iHeadInv_plain {s : Store H} {f : Frame} {C : Context} {i : Instr} {it : InstrType}
    (hT : TypesOk f C) (h : AdminOk s C (.plain i) it) : IHeadInv f (.plain i) := by
  refine ⟨?_, ?_⟩
  · rintro rt (he | he) <;> cases he <;> cases h with
    | plain h =>
      cases h <;> (try (rename_i h; cases h))
      exact hT.cast ‹TyOk C.toTypeCtx (C.closeRef rt)›
  · rintro l rt₁ rt₂ (he | he) <;> cases he <;> cases h with
    | plain h =>
      cases h <;> (try (rename_i h; cases h))
      exact hT.cast ‹TyOk C.toTypeCtx (C.closeRef rt₂)›

theorem iHeadInv_nonplain {f : Frame} {e : Admin} (he : ∀ i, e ≠ .plain i) : IHeadInv f e := by
  refine ⟨?_, ?_⟩
  · rintro rt (h | h) <;> exact absurd h (he _)
  · rintro l rt₁ rt₂ (h | h) <;> exact absurd h (he _)

theorem deepAll_append' {Inv : Frame → Admin → Prop} {f : Frame} {l₁ l₂ : List Admin}
    (h₁ : DeepAll Inv f l₁) (h₂ : DeepAll Inv f l₂) : DeepAll Inv f (l₁ ++ l₂) :=
  Drv.deepAll_append.mpr ⟨h₁, h₂⟩

theorem main {s : Store H} :
    (∀ {C a it}, AdminOk s C a it → ∀ f, TypesOk f C → Drv.DeepAt IHeadInv f a) ∧
    (∀ {C code it}, AdminsOk s C code it → ∀ f, TypesOk f C → DeepAll IHeadInv f code) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine AdminOk.rec (motive_1 := fun C a _ _ => ∀ f, TypesOk f C → Drv.DeepAt IHeadInv f a)
      (motive_2 := fun C L _ _ => ∀ f, TypesOk f C → DeepAll IHeadInv f L)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    · intro C i it hi f hT; exact iHeadInv_plain hT (.plain (s := s) hi)
    · intro C d ps rs _ _ f _; exact iHeadInv_nonplain (by intro i h; cases h)
    · intro C d ps rs rs' t₃ t₄ _ _ _ _ _ f _; exact iHeadInv_nonplain (by intro i h; cases h)
    · intro C r rt _ f _; exact iHeadInv_nonplain (by intro i h; cases h)
    · intro C n cont body t' ts xs' xs _ _ _ _ ihb f hT
      simp only [Drv.DeepAt]
      exact ⟨iHeadInv_nonplain (by intro i h; cases h), ihb f (hT.withLabel _)⟩
    · intro C C' n fr body ts hf _ _ _ ih f _
      simp only [Drv.DeepAt]
      exact ⟨iHeadInv_nonplain (by intro i h; cases h), ih fr (TypesOk.of_frameOk hf : TypesOk fr C')⟩
    · intro C n cs body ts xs _ _ ih f hT
      simp only [Drv.DeepAt]
      exact ⟨iHeadInv_nonplain (by intro i h; cases h), ih f hT⟩
    · intro C t₁ t₂ xs _ f _; exact iHeadInv_nonplain (by intro i h; cases h)
    · intro C t₁ t₂ xs hok f hT; exact iHeadInv_plain hT (.throwRefInits (s := s) hok)
    · intro C f _; simp only [DeepAll]
    · intro C a it _ ih f hT; simp only [DeepAll]; exact ⟨ih f hT, trivial⟩
    · intro C as₁ as₂ t₁ t₂ t₃ xs₁ xs₂ _ _ _ ih₁ ih₂ f hT
      exact deepAll_append' (ih₁ f hT) (ih₂ f (hT.initLocals _))
    · intro C a as t₁ t₂ t₃ xs₁ xs₂ _ _ _ iha ihs f hT
      simp only [DeepAll]; exact ⟨iha f hT, ihs f (hT.initLocals _)⟩
    · intro C as it it' _ _ _ ih f hT; exact ih f hT
    · intro C as ts t₁ t₂ xs _ _ ih f hT; exact ih f hT
  · refine AdminsOk.rec (motive_1 := fun C a _ _ => ∀ f, TypesOk f C → Drv.DeepAt IHeadInv f a)
      (motive_2 := fun C L _ _ => ∀ f, TypesOk f C → DeepAll IHeadInv f L)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    · intro C i it hi f hT; exact iHeadInv_plain hT (.plain (s := s) hi)
    · intro C d ps rs _ _ f _; exact iHeadInv_nonplain (by intro i h; cases h)
    · intro C d ps rs rs' t₃ t₄ _ _ _ _ _ f _; exact iHeadInv_nonplain (by intro i h; cases h)
    · intro C r rt _ f _; exact iHeadInv_nonplain (by intro i h; cases h)
    · intro C n cont body t' ts xs' xs _ _ _ _ ihb f hT
      simp only [Drv.DeepAt]
      exact ⟨iHeadInv_nonplain (by intro i h; cases h), ihb f (hT.withLabel _)⟩
    · intro C C' n fr body ts hf _ _ _ ih f _
      simp only [Drv.DeepAt]
      exact ⟨iHeadInv_nonplain (by intro i h; cases h), ih fr (TypesOk.of_frameOk hf : TypesOk fr C')⟩
    · intro C n cs body ts xs _ _ ih f hT
      simp only [Drv.DeepAt]
      exact ⟨iHeadInv_nonplain (by intro i h; cases h), ih f hT⟩
    · intro C t₁ t₂ xs _ f _; exact iHeadInv_nonplain (by intro i h; cases h)
    · intro C t₁ t₂ xs hok f hT; exact iHeadInv_plain hT (.throwRefInits (s := s) hok)
    · intro C f _; simp only [DeepAll]
    · intro C a it _ ih f hT; simp only [DeepAll]; exact ⟨ih f hT, trivial⟩
    · intro C as₁ as₂ t₁ t₂ t₃ xs₁ xs₂ _ _ _ ih₁ ih₂ f hT
      exact deepAll_append' (ih₁ f hT) (ih₂ f (hT.initLocals _))
    · intro C a as t₁ t₂ t₃ xs₁ xs₂ _ _ _ iha ihs f hT
      simp only [DeepAll]; exact ⟨iha f hT, ihs f (hT.initLocals _)⟩
    · intro C as it it' _ _ _ ih f hT; exact ih f hT
    · intro C as ts t₁ t₂ xs _ _ ih f hT; exact ih f hT

end IHeadInvTyped

open IHeadInvTyped in
theorem AdminOk.deepAt_iHeadInv {s : Store H} {C : Context} {a : Admin} {it : InstrType}
    {f : Frame} (h : AdminOk s C a it) (hst : StateOk s f C) : Drv.DeepAt IHeadInv f a :=
  main.1 h f (TypesOk.of_stateOk hst)

open IHeadInvTyped in
theorem AdminsOk.deepAll_iHeadInv {s : Store H} {C : Context} {code : List Admin}
    {it : InstrType} {f : Frame} (h : AdminsOk s C code it) (hst : StateOk s f C) :
    DeepAll IHeadInv f code :=
  main.2 h f (TypesOk.of_stateOk hst)

/-- Typed configurations satisfy the cast side conditions deeply. -/
theorem ConfigOk.deepAll_iHeadInv {c : Config H} {ts} (h : ConfigOk c ts) :
    DeepAll IHeadInv c.frame c.code := by
  obtain ⟨C, hst, hc⟩ := h
  exact AdminsOk.deepAll_iHeadInv hc hst

/-- Preservation of the cast side conditions: discharged by typing. -/
theorem iHeadInvPres (o : GrowOracle) (ts : List CValType) : IHeadInvPres (H := H) o ts := by
  intro c c' h _ hst
  exact ConfigOk.deepAll_iHeadInv
    (Step.preservation (P := profile o) divHost_ok h (Step.of_noHost divHost hst)).1

/-- Core typing alone is an interpreter invariant. -/
theorem typedInv' {o : GrowOracle} {ts : List CValType} :
    InterpInv o (fun c : Config H => ConfigOk c ts) where
  storeOk _ h := ConfigOk.storeOk h
  headInv _ h := ConfigOk.deepAll_iHeadInv h
  pres _ _ h hst :=
    (Step.preservation (P := profile o) divHost_ok h (Step.of_noHost divHost hst)).1

section typed
variable {o : GrowOracle} {ts : List CValType}

theorem stepI_sound_typed {c c' : Config H} (hc : ConfigOk c ts) (h : stepI o c = some c') :
    Step (profile o) noHost c c' :=
  stepI_sound (ConfigOk.storeOk hc) (ConfigOk.deepAll_iHeadInv hc) h

theorem stepI_complete_typed {c c' : Config H} (hc : ConfigOk c ts)
    (h : Step (profile o) noHost c c') : (stepI o c).isSome :=
  stepI_complete (ConfigOk.storeOk hc) (ConfigOk.deepAll_iHeadInv hc) h

theorem runI_steps_typed (n : Nat) {c : Config H} (hc : ConfigOk c ts) :
    Steps (profile o) noHost c (runI o n c).1 :=
  runI_steps typedInv' n c hc

theorem runI_typed (n : Nat) {c : Config H} (hc : ConfigOk c ts) :
    ConfigOk (runI o n c).1 ts :=
  typedInv'.steps (runI_steps_typed n hc) hc

theorem runI_stopped_no_step_typed {n : Nat} {c : Config H} (hc : ConfigOk c ts)
    (h : (runI o n c).2 = true) (c' : Config H) :
    ¬ Step (profile o) noHost (runI o n c).1 c' :=
  runI_stopped_no_step typedInv' hc h c'

theorem runI_complete_typed {c c' : Config H} (hc : ConfigOk c ts)
    (h : Steps (profile o) noHost c c') (hnf : ∀ x, ¬ Step (profile o) noHost c' x) :
    ∃ n, runI o n c = (c', true) :=
  runI_complete typedInv' hc h hnf

theorem statusI_eq_typed {s : Store H} {t : Thread} (hi : ConfigOk (t.config s) ts) :
    statusC (stepI o) s t = status o s t :=
  statusI_eq_of typedInv' hi

theorem runCI_sound_typed (fuel : Nat) (s : Store H) (t : Thread)
    (hi : ConfigOk (t.config s) ts) {s' : Store H} {t' : Thread} {st : Status H}
    (h : runC (stepI o) fuel s t = (s', t', st)) :
    Relation.ReflTransGen (Internal o) (s, t) (s', t') ∧ ConfigOk (t'.config s') ts ∧
      (st ≠ .running → st = status o s' t') :=
  runCI_sound typedInv' fuel s t hi h

end typed

/-! ## End-to-end with the interpreter -/

namespace EndToEnd

theorem interpHead_soundAt (o : GrowOracle) :
    RunInv.HeadSoundAt (H := H) o StoreOk IHeadInv (interpHead o) :=
  fun _ hs => interpHead_sound hs

theorem interpHead_exactAt (o : GrowOracle) :
    RunInv.HeadExactAt (H := H) o StoreOk IHeadInv (interpHead o) :=
  fun _ hs => interpHead_exact hs

theorem configOk_iHeadInv :
    ∀ (c : Config H) ts, ConfigOk c ts → DeepAll IHeadInv c.frame c.code :=
  fun _ _ h => ConfigOk.deepAll_iHeadInv h

variable {o : GrowOracle}

/-- **Soundness** of instantiate-then-interpret. -/
theorem runModuleI?_sound
    {n : Nat} {s : Store H} {m : Module} {xas : List ExternAddr} (hs : StoreOk s)
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    {c' : Config H} {b : Bool} {r : Option Result}
    (h : runModule? (interpHead o) n s m xas = some (c', b, r)) :
    (∃ c₀, Instantiate (profile o) divHost s m xas c₀ ∧ Steps (profile o) divHost c₀ c') ∧
      ConfigOk c' [] ∧ (∀ res, r = some res → c'.code = res.toAdmin) :=
  runModule?_sound configOk_iHeadInv (interpHead_soundAt o) hs hvalid h

theorem runModuleI?_steps_noHost
    {n : Nat} {s : Store H} {m : Module} {xas : List ExternAddr} (hs : StoreOk s)
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    {c' : Config H} {b : Bool} {r : Option Result}
    (h : runModule? (interpHead o) n s m xas = some (c', b, r)) :
    ∃ c, instantiateInit? s m xas = some c ∧ Steps (profile o) noHost c c' :=
  runModule?_steps_noHost (o := o) configOk_iHeadInv (interpHead_soundAt o) hs hvalid h

/-- A stopped result is terminal or can only step through the host. -/
theorem runModuleI?_stopped
    {n : Nat} {s : Store H} {m : Module} {xas : List ExternAddr} (hs : StoreOk s)
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    {c' : Config H} {r : Option Result}
    (h : runModule? (interpHead o) n s m xas = some (c', true, r)) :
    (c'.Terminal ∨ ∃ c'', Step (profile o) divHost c' c'') ∧
      ∀ c'', ¬ Step (profile o) noHost c' c'' :=
  runModule?_stopped configOk_iHeadInv (interpHead_soundAt o) (interpHead_exactAt o) hs hvalid h

/-- **Completeness** of instantiate-then-interpret. -/
theorem runModuleI?_complete
    {s : Store H} {m : Module} {xas : List ExternAddr} (hs : StoreOk s)
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    {c c' : Config H} (hc : instantiateInit? s m xas = some c)
    (h : Steps (profile o) noHost c c') (hnf : ∀ x, ¬ Step (profile o) noHost c' x) :
    ∃ n, runModule? (interpHead o) n s m xas = some (c', true, c'.outcome?) :=
  runModule?_complete configOk_iHeadInv (interpHead_soundAt o) (interpHead_exactAt o) hs hvalid
    hc h hnf

end EndToEnd

end Silmaril.Wasm.SingleThreaded.Exec
