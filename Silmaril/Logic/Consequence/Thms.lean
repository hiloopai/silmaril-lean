module

public import Silmaril.Logic.Consequence.Defs

/-!
# Consequence systems: basic laws

**Order.** `le_iff`: `S ≤ T` is pointwise inclusion of judgements. `sound_iff`,
`complete_iff`, `sound_and_complete_iff_eq`: soundness and completeness against `T` together are
equality. The lattice operations are pointwise: `bot_apply`, `top_apply`, `sup_apply`,
`inf_apply`, `sdiff_apply`, `sSup_apply`, `sInf_apply` (the instances are Mathlib's; these are
the readable statements).

**Pullback.** `pullback_id`, `pullback_comp`: reindexing is functorial (contravariantly), and
`pullback_mono` it is monotone; it preserves `⊥`, `⊤`, `⊔`, `⊓` (`pullback_sup`, …).

**Witnesses.** `erase_apply`; `erase_mono_of`: a map of witnesses gives inclusion of erasures.

**Everything follows.** `universal_iff_eq_top`; `universal_iff_provesAll`;
`provesAll_of_isEmpty`, `not_contextConsistent_of_isEmpty`: with no conclusions every context is
trivially inconsistent, and with no contexts every system is universal. `ProvesAll.provesFalse`,
`ConsistentWrt.contextConsistent`: one direction always holds. `Explosive.provesFalse_iff`,
`Explosive.consistentWrt_iff`: bottom-relative and context (in)consistency agree under explosion;
`not_explosive_ex` shows the hypothesis is needed.

**Monotonicity.** `monoWrt_of_le`: monotonicity along a larger relation implies it along a smaller
one. `AxMono.mono`, `axMono_sup`, `axMono_inf`, `axMono_bot`, `axMono_top`.
-/

@[expose] public section

namespace Silmaril.Consequence

universe u v w u' v' u'' v''

namespace System

variable {Ax : Type u} {C : Type v} {Ax' : Type u'} {C' : Type v'} {Ax'' : Type u''}
  {C'' : Type v''} {S T : System Ax C}

/-! ## Order and lattice -/

theorem le_iff : S ≤ T ↔ ∀ a c, S a c → T a c := Iff.rfl

theorem sound_iff : S.Sound T ↔ ∀ a c, S a c → T a c := Iff.rfl

theorem complete_iff : S.Complete T ↔ ∀ a c, T a c → S a c := Iff.rfl

theorem sound_and_complete_iff_eq : S.Sound T ∧ S.Complete T ↔ S = T :=
  le_antisymm_iff.symm

theorem eq_iff : S = T ↔ ∀ a c, S a c ↔ T a c :=
  ⟨fun h _ _ => h ▸ Iff.rfl, fun h => funext₂ fun a c => propext (h a c)⟩

@[simp] theorem bot_apply (a : Ax) (c : C) : (⊥ : System Ax C) a c ↔ False := Iff.rfl
@[simp] theorem top_apply (a : Ax) (c : C) : (⊤ : System Ax C) a c ↔ True := Iff.rfl
@[simp] theorem sup_apply (a : Ax) (c : C) : (S ⊔ T) a c ↔ S a c ∨ T a c := Iff.rfl
@[simp] theorem inf_apply (a : Ax) (c : C) : (S ⊓ T) a c ↔ S a c ∧ T a c := Iff.rfl
@[simp] theorem sdiff_apply (a : Ax) (c : C) : (S \ T) a c ↔ S a c ∧ ¬ T a c := Iff.rfl
@[simp] theorem compl_apply (a : Ax) (c : C) : Sᶜ a c ↔ ¬ S a c := Iff.rfl

@[simp] theorem sSup_apply (F : Set (System Ax C)) (a : Ax) (c : C) :
    sSup F a c ↔ ∃ S ∈ F, S a c := by
  simp [_root_.sSup_apply, iSup_apply]

@[simp] theorem sInf_apply (F : Set (System Ax C)) (a : Ax) (c : C) :
    sInf F a c ↔ ∀ S ∈ F, S a c := by
  simp [_root_.sInf_apply, iInf_apply]

/-- The concrete lattice is the one Mathlib provides on `Ax → C → Prop`. -/
example : CompleteBooleanAlgebra (System Ax C) := inferInstance

/-! ## Pullback -/

@[simp] theorem pullback_apply (f : Ax' → Ax) (g : C' → C) (a : Ax') (c : C') :
    S.pullback f g a c ↔ S (f a) (g c) := Iff.rfl

theorem pullback_id : S.pullback id id = S := rfl

theorem pullback_comp (f : Ax' → Ax) (g : C' → C) (f' : Ax'' → Ax') (g' : C'' → C') :
    (S.pullback f g).pullback f' g' = S.pullback (f ∘ f') (g ∘ g') := rfl

theorem pullback_mono (f : Ax' → Ax) (g : C' → C) (h : S ≤ T) :
    S.pullback f g ≤ T.pullback f g := fun a c => h (f a) (g c)

theorem pullback_bot (f : Ax' → Ax) (g : C' → C) : (⊥ : System Ax C).pullback f g = ⊥ := rfl
theorem pullback_top (f : Ax' → Ax) (g : C' → C) : (⊤ : System Ax C).pullback f g = ⊤ := rfl
theorem pullback_sup (f : Ax' → Ax) (g : C' → C) :
    (S ⊔ T).pullback f g = S.pullback f g ⊔ T.pullback f g := rfl
theorem pullback_inf (f : Ax' → Ax) (g : C' → C) :
    (S ⊓ T).pullback f g = S.pullback f g ⊓ T.pullback f g := rfl
theorem pullback_sdiff (f : Ax' → Ax) (g : C' → C) :
    (S \ T).pullback f g = S.pullback f g \ T.pullback f g := rfl

/-! ## Everything follows -/

theorem universal_iff_eq_top : S.Universal ↔ S = ⊤ :=
  ⟨fun h => funext₂ fun a c => eq_true (h a c), fun h _ _ => h ▸ trivial⟩

theorem universal_iff_provesAll : S.Universal ↔ ∀ a, S.ProvesAll a := Iff.rfl

theorem contextConsistent_iff (a : Ax) : S.ContextConsistent a ↔ ∃ c, ¬ S a c :=
  not_forall

/-- With no conclusions, every context proves everything. -/
theorem provesAll_of_isEmpty [IsEmpty C] (a : Ax) : S.ProvesAll a := fun c => isEmptyElim c

/-- With no conclusions, no context is consistent, even in `⊥`. -/
theorem not_contextConsistent_of_isEmpty [IsEmpty C] (a : Ax) : ¬ S.ContextConsistent a :=
  not_not_intro (provesAll_of_isEmpty a)

/-- With no conclusions every system is universal, so `⊥ = ⊤`. -/
theorem universal_of_isEmpty [IsEmpty C] : S.Universal := fun a => provesAll_of_isEmpty a

/-- With no contexts every system is (vacuously) universal. -/
theorem universal_of_isEmpty_ax [IsEmpty Ax] : S.Universal := fun a => isEmptyElim a

theorem ProvesAll.provesFalse {a : Ax} (h : S.ProvesAll a) (ff : C) : S.ProvesFalse ff a := h ff

theorem ConsistentWrt.contextConsistent {ff : C} {a : Ax} (h : S.ConsistentWrt ff a) :
    S.ContextConsistent a := fun h' => h (h' ff)

theorem Explosive.provesFalse_iff {ff : C} (h : S.Explosive ff) (a : Ax) :
    S.ProvesFalse ff a ↔ S.ProvesAll a := ⟨h a, fun h' => h' ff⟩

theorem Explosive.consistentWrt_iff {ff : C} (h : S.Explosive ff) (a : Ax) :
    S.ConsistentWrt ff a ↔ S.ContextConsistent a := not_congr (h.provesFalse_iff a)

/-- If no context proves `ff`, `ff` is explosive vacuously. -/
theorem explosive_of_not_proves {ff : C} (h : ∀ a, ¬ S a ff) : S.Explosive ff :=
  fun a h' => absurd h' (h a)

/-- Bottom-relative inconsistency does not imply context inconsistency without explosion: in the
system on `Unit` and `Bool` proving exactly `false`, the context proves `ff := false` but not
`true`. -/
theorem not_explosive_ex :
    ∃ (S : System Unit Bool), S.ProvesFalse false () ∧ ¬ S.ProvesAll () :=
  ⟨fun _ c => c = false, rfl, fun h => Bool.noConfusion (h true)⟩

/-! ## Monotonicity in contexts -/

theorem monoWrt_of_le {r r' : Ax → Ax → Prop} (hr : ∀ a b, r a b → r' a b)
    (h : S.MonoWrt r') : S.MonoWrt r := fun a b hab => h (hr a b hab)

theorem axMono_iff [Preorder Ax] : S.AxMono ↔ ∀ ⦃a b : Ax⦄, a ≤ b → ∀ ⦃c⦄, S a c → S b c :=
  Iff.rfl

theorem AxMono.mono [Preorder Ax] (h : S.AxMono) {a b : Ax} (hab : a ≤ b) {c : C}
    (hs : S a c) : S b c := h hab hs

theorem axMono_bot [Preorder Ax] : (⊥ : System Ax C).AxMono := fun _ _ _ _ h => h
theorem axMono_top [Preorder Ax] : (⊤ : System Ax C).AxMono := fun _ _ _ _ _ => trivial

theorem axMono_sup [Preorder Ax] (hS : S.AxMono) (hT : T.AxMono) : (S ⊔ T).AxMono :=
  fun _ _ hab _ h => h.imp (fun h => hS hab h) (fun h => hT hab h)

theorem axMono_inf [Preorder Ax] (hS : S.AxMono) (hT : T.AxMono) : (S ⊓ T).AxMono :=
  fun _ _ hab _ h => ⟨hS hab h.1, hT hab h.2⟩

theorem axMono_pullback [Preorder Ax] [Preorder Ax'] {f : Ax' → Ax} (hf : Monotone f)
    (g : C' → C) (hS : S.AxMono) : (S.pullback f g).AxMono :=
  fun _ _ hab _ h => hS (hf hab) h

end System

namespace WSystem

variable {Ax : Type u} {C : Type v}

@[simp] theorem erase_apply (W : WSystem.{u, v, w} Ax C) (a : Ax) (c : C) :
    W.erase a c ↔ Nonempty (W a c) := Iff.rfl

/-- A family of witness maps gives inclusion of the erased systems. -/
theorem erase_mono_of {W V : WSystem.{u, v, w} Ax C} (f : ∀ a c, W a c → V a c) :
    W.erase ≤ V.erase := fun a c ⟨x⟩ => ⟨f a c x⟩

/-- A system as a witness system with at most one (proof-irrelevant) witness per judgement;
erasing gives the system back. -/
def ofSystem (S : System Ax C) : WSystem.{u, v, 0} Ax C := fun a c => PLift (S a c)

theorem erase_ofSystem (S : System Ax C) : (ofSystem S).erase = S :=
  funext₂ fun _ _ => propext ⟨fun ⟨h⟩ => h.down, fun h => ⟨⟨h⟩⟩⟩

end WSystem

end Silmaril.Consequence
