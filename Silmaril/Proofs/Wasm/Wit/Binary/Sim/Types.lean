module

public import Silmaril.Proofs.Wasm.Wit.Binary.Sim.Refs

/-!
# The WIT binary round trip: value types

`valType_sim`: the value type the encoder writes for a WIT type decodes back
to that type, in the decoder state reached by the declarations it wrote.
Anonymous types are shared through the `anon` table (`anon_sim`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary Enc

/-! ## Composing steps -/

theorem Sim.mono {e e' : Enc} {cst : CSt} {dst : Option DSt} {P Q : List Slot → Prop}
    (h : Sim e cst dst e' P) (hPQ : ∀ cur, P cur → Q cur) : Sim e cst dst e' Q := by
  obtain ⟨c, d, hI, hG, hp⟩ := h
  exact ⟨c, d, hI, hG, hPQ _ hp⟩

/-- Two steps in sequence; the first result must survive longer slot lists. -/
theorem Sim.seq {e e₁ e₂ : Enc} {cst : CSt} {dst : Option DSt} {P Q : List Slot → Prop}
    (h₁ : Sim e cst dst e₁ P) (hP : ∀ {a b}, P a → Ext a b → P b)
    (h₂ : ∀ {cst₁ dst₁}, Inv e₁ cst₁ dst₁ → Sim e₁ cst₁ dst₁ e₂ Q) :
    Sim e cst dst e₂ (fun cur => P cur ∧ Q cur) := by
  obtain ⟨c₁, d₁, hI₁, hG₁, hp⟩ := h₁
  obtain ⟨c₂, d₂, hI₂, hG₂, hq⟩ := h₂ hI₁
  exact ⟨c₂, d₂, hI₂, hG₁.trans hG₂, hP hp hG₂.cext, hq⟩

theorem decValTypes_ext {a b : List Slot} (hx : Ext a b) :
    ∀ {vs : List Silmaril.Wasm.Component.Binary.ValType} {ts : List Ty}, decValTypes a vs = .ok ts → decValTypes b vs = .ok ts
  | [], _, h => h
  | v :: vs, ts, h => by
    simp only [decValTypes] at h ⊢
    cases hv : decValType a v with
    | error e => rw [hv] at h; cases h
    | ok t =>
      rw [hv] at h
      cases hvs : decValTypes a vs with
      | error e => rw [hvs] at h; cases h
      | ok ts' => rw [decValType_ext hx hv, decValTypes_ext hx hvs]; rw [hvs] at h; exact h

/-! ## Anonymous types -/

/-- An anonymous type is looked up, or defined by `mk` and recorded. -/
theorem anon_sim {e e' : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst) {t : Ty}
    {mk : EncM DefValType} {v : Silmaril.Wasm.Component.Binary.ValType}
    (hmk : ∀ {d e₂}, mk.run e = .ok (d, e₂) → Sim e cst dst e₂ (fun cur => decDefVal cur d = .ok (.ty t)))
    (h : (anon t mk).run e = .ok (v, e')) : Sim e cst dst e' (fun cur => decValType cur v = .ok t) := by
  obtain ⟨m, e₁, h₁, h₂⟩ := run_bind_ok h
  rw [maps_run] at h₁; cases h₁
  cases hl : lookup t e.curMaps.anon with
  | some k =>
    rw [hl] at h₂; cases h₂
    exact ⟨cst, dst, hI, Grows.refl _ _ _, decValType_of_ty (hI.curOK.anon t k hl)⟩
  | none =>
    rw [hl] at h₂
    obtain ⟨d, e₂, h₃, h₄⟩ := run_bind_ok h₂
    obtain ⟨cst₂, dst₂, hI₂, hG₂, hd⟩ := hmk h₃
    obtain ⟨k, e₃, h₅, h₆⟩ := run_bind_ok h₄
    have P := defType_sim hI₂ (t := .val d) hd h₅
    obtain ⟨cst₃, dst₃, hI₃, hG₃, hc⟩ := P.sim
    have hk : (curSlots cst₃ dst₃)[k]? = some (.ty t) := by rw [hc, P.idx]; simp
    obtain ⟨u, e₄, h₇, h₈⟩ := run_bind_ok h₆
    rw [insertAnon_run] at h₇; cases h₇
    obtain ⟨rfl, rfl⟩ := run_pure_ok h₈
    exact ⟨cst₃, dst₃, insertAnon_sim hI₃ hk, hG₂.trans (hG₃.trans (Grows.withMaps _ _ _ _)),
      decValType_of_ty hk⟩

/-! ## Definitions of one constructor -/

/-- `f <$> x` where `x` simulates `P`. -/
theorem map_sim {α : Type} {e e' : Enc} {cst : CSt} {dst : Option DSt} {x : EncM α}
    {f : α → DefValType} {d : DefValType} {P : α → List Slot → Prop} (h : (f <$> x).run e = .ok (d, e'))
    (hx : ∀ {a e₂}, x.run e = .ok (a, e₂) → Sim e cst dst e₂ (P a)) :
    ∃ a, d = f a ∧ Sim e cst dst e' (P a) := by
  obtain ⟨a, ha, rfl⟩ := run_map_ok h
  exact ⟨a, rfl, hx ha⟩

/-- Two components then `pure`. -/
theorem pair_sim {α β : Type} {e e' : Enc} {cst : CSt} {dst : Option DSt} {x : EncM α} {y : EncM β}
    {f : α → β → DefValType} {d : DefValType} {P : α → List Slot → Prop} {Q : β → List Slot → Prop}
    (h : (do let a ← x; let b ← y; pure (f a b)).run e = .ok (d, e'))
    (hx : ∀ {a e₂}, x.run e = .ok (a, e₂) → Sim e cst dst e₂ (P a))
    (hy : ∀ {e₁ cst₁ dst₁ b e₂}, Inv e₁ cst₁ dst₁ → y.run e₁ = .ok (b, e₂) → Sim e₁ cst₁ dst₁ e₂ (Q b))
    (hP : ∀ {a u w}, P a u → Ext u w → P a w) :
    ∃ a b, d = f a b ∧ Sim e cst dst e' (fun cur => P a cur ∧ Q b cur) := by
  obtain ⟨a, e₁, h₁, h₂⟩ := run_bind_ok h
  obtain ⟨b, e₂, h₃, h₄⟩ := run_bind_ok h₂
  obtain ⟨rfl, rfl⟩ := run_pure_ok h₄
  exact ⟨a, b, rfl, Sim.seq (hx h₁) hP (fun hI₁ => hy hI₁ h₃)⟩

/-! ## Value types -/

mutual
/-- **Value types round-trip**: the value type written for `t` decodes to `t`. -/
theorem valType_sim : ∀ (t : Ty) {e e' : Enc} {cst : CSt} {dst : Option DSt} {v : Silmaril.Wasm.Component.Binary.ValType},
    Inv e cst dst → (valType t).run e = .ok (v, e') →
    Sim e cst dst e' (fun cur => decValType cur v = .ok t)
  | .prim p, _, _, cst, dst, _, hI, h => by
    obtain ⟨rfl, rfl⟩ := run_pure_ok (a := Silmaril.Wasm.Component.Binary.ValType.prim p) h
    exact ⟨cst, dst, hI, Grows.refl _ _ _, rfl⟩
  | .ref r, _, _, _, _, _, hI, h => by
    obtain ⟨k, hk, rfl⟩ := run_map_ok (f := Silmaril.Wasm.Component.Binary.ValType.idx) h
    exact (refIdx_sim hI hk).mono fun _ hc => decValType_of_named hc
  | .list t, _, _, _, _, _, hI, h => anon_sim hI (fun hd => by
      obtain ⟨a, rfl, hs⟩ := map_sim (P := fun a cur => decValType cur a = .ok t) hd (valType_sim t hI)
      exact hs.mono fun cur hc => by simp only [decDefVal, hc]; rfl) h
  | .fixedList t n, _, _, _, _, _, hI, h => anon_sim hI (fun hd => by
      obtain ⟨a, rfl, hs⟩ := map_sim (P := fun a cur => decValType cur a = .ok t) hd (valType_sim t hI)
      exact hs.mono fun cur hc => by simp only [decDefVal, hc]; rfl) h
  | .option t, _, _, _, _, _, hI, h => anon_sim hI (fun hd => by
      obtain ⟨a, rfl, hs⟩ := map_sim (P := fun a cur => decValType cur a = .ok t) hd (valType_sim t hI)
      exact hs.mono fun cur hc => by simp only [decDefVal, hc]; rfl) h
  | .map k v, _, _, _, _, _, hI, h => anon_sim hI (fun hd => by
      obtain ⟨a, b, rfl, hs⟩ := pair_sim (P := fun a cur => decValType cur a = .ok k)
        (Q := fun b cur => decValType cur b = .ok v) hd (valType_sim k hI) (fun hI₁ => valType_sim v hI₁)
        (fun hp hx => decValType_ext hx hp)
      exact hs.mono fun cur hc => by simp only [decDefVal, hc.1, hc.2]; rfl) h
  | .result o e, _, _, _, _, _, hI, h => anon_sim hI (fun hd => by
      obtain ⟨a, b, rfl, hs⟩ := pair_sim (P := fun a cur => decOpt cur a = .ok o)
        (Q := fun b cur => decOpt cur b = .ok e) hd (optValType_sim o hI) (fun hI₁ => optValType_sim e hI₁)
        (fun hp hx => decOpt_ext hx hp)
      exact hs.mono fun cur hc => by simp only [decDefVal, hc.1, hc.2]; rfl) h
  | .tuple ts, _, _, _, _, _, hI, h => anon_sim hI (fun hd => by
      obtain ⟨a, rfl, hs⟩ := map_sim (P := fun a cur => decValTypes cur a = .ok ts) hd (valTypes_sim ts hI)
      exact hs.mono fun cur hc => by simp only [decDefVal, hc]; rfl) h
  | .own r, _, _, _, _, _, hI, h => anon_sim hI (fun hd => by
      obtain ⟨a, rfl, hs⟩ := map_sim (P := fun a cur => cur[a]? = some (.named r)) hd (refIdx_sim hI)
      exact hs.mono fun cur hc => by simp only [decDefVal, decRef_of_get hc]; rfl) h
  | .borrow r, _, _, _, _, _, hI, h => anon_sim hI (fun hd => by
      obtain ⟨a, rfl, hs⟩ := map_sim (P := fun a cur => cur[a]? = some (.named r)) hd (refIdx_sim hI)
      exact hs.mono fun cur hc => by simp only [decDefVal, decRef_of_get hc]; rfl) h
  | .future t, _, _, _, _, _, hI, h => anon_sim hI (fun hd => by
      obtain ⟨a, rfl, hs⟩ := map_sim (P := fun a cur => decOpt cur a = .ok t) hd (optValType_sim t hI)
      exact hs.mono fun cur hc => by simp only [decDefVal, hc]; rfl) h
  | .stream t, _, _, _, _, _, hI, h => anon_sim hI (fun hd => by
      obtain ⟨a, rfl, hs⟩ := map_sim (P := fun a cur => decOpt cur a = .ok t) hd (optValType_sim t hI)
      exact hs.mono fun cur hc => by simp only [decDefVal, hc]; rfl) h

theorem optValType_sim : ∀ (o : Option Ty) {e e' : Enc} {cst : CSt} {dst : Option DSt}
    {v : Option Silmaril.Wasm.Component.Binary.ValType}, Inv e cst dst → (optValType o).run e = .ok (v, e') →
    Sim e cst dst e' (fun cur => decOpt cur v = .ok o)
  | none, _, _, cst, dst, _, hI, h => by
    obtain ⟨rfl, rfl⟩ := run_pure_ok (a := (none : Option Silmaril.Wasm.Component.Binary.ValType)) h
    exact ⟨cst, dst, hI, Grows.refl _ _ _, rfl⟩
  | some t, _, _, _, _, _, hI, h => by
    obtain ⟨a, ha, rfl⟩ := run_map_ok (f := some) h
    exact (valType_sim t hI ha).mono fun cur hc => by simp only [decOpt, hc]; rfl

theorem valTypes_sim : ∀ (ts : List Ty) {e e' : Enc} {cst : CSt} {dst : Option DSt}
    {vs : List Silmaril.Wasm.Component.Binary.ValType}, Inv e cst dst → (valTypes ts).run e = .ok (vs, e') →
    Sim e cst dst e' (fun cur => decValTypes cur vs = .ok ts)
  | [], _, _, cst, dst, _, hI, h => by
    obtain ⟨rfl, rfl⟩ := run_pure_ok (a := ([] : List Silmaril.Wasm.Component.Binary.ValType)) h
    exact ⟨cst, dst, hI, Grows.refl _ _ _, rfl⟩
  | t :: ts, _, _, _, _, _, hI, h => by
    obtain ⟨a, e₁, h₁, h₂⟩ := run_bind_ok h
    obtain ⟨b, e₂, h₃, h₄⟩ := run_bind_ok h₂
    obtain ⟨rfl, rfl⟩ := run_pure_ok h₄
    exact (Sim.seq (valType_sim t hI h₁) (fun hp hx => decValType_ext hx hp)
      (fun hI₁ => valTypes_sim ts hI₁ h₃)).mono fun cur hc => by
        simp only [decValTypes, hc.1, hc.2]; rfl
end

end Silmaril.Wasm.Wit.Binary
