module

public import Silmaril.Proofs.Wasm.Wit.Binary.Sim.Types

/-!
# The WIT binary round trip: named types and function types

The definition the encoder writes for a named type is *claimed* by the
export (or world import) naming it, and the decoder reads the type back
without its docs (`typeDefIdx_sim`, `typeDef_sim_inner`, `typeDef_sim_world`);
function types decode to the function's signature (`funcType_sim`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary Enc

/-! ## Lists of components -/

theorem decFields_ext {a b : List Slot} (hx : Ext a b) :
    ∀ {fs : List (String × ValType)} {ls : List (Labeled Ty)}, decFields a fs = .ok ls → decFields b fs = .ok ls
  | [], _, h => h
  | (n, v) :: fs, ls, h => by
    simp only [decFields] at h ⊢
    cases hv : decValType a v with
    | error e => rw [hv] at h; cases h
    | ok t =>
      rw [hv] at h
      cases hvs : decFields a fs with
      | error e => rw [hvs] at h; cases h
      | ok ts' => rw [decValType_ext hx hv, decFields_ext hx hvs]; rw [hvs] at h; exact h

theorem decCases_ext {a b : List Slot} (hx : Ext a b) :
    ∀ {cs : List (String × Option ValType)} {ls : List (Labeled (Option Ty))},
      decCases a cs = .ok ls → decCases b cs = .ok ls
  | [], _, h => h
  | (n, v) :: cs, ls, h => by
    simp only [decCases] at h ⊢
    cases hv : decOpt a v with
    | error e => rw [hv] at h; cases h
    | ok t =>
      rw [hv] at h
      cases hvs : decCases a cs with
      | error e => rw [hvs] at h; cases h
      | ok ts' => rw [decOpt_ext hx hv, decCases_ext hx hvs]; rw [hvs] at h; exact h

theorem decParams_ext {a b : List Slot} (hx : Ext a b) :
    ∀ {ps : List (String × ValType)} {ls : List (String × Ty)}, decParams a ps = .ok ls → decParams b ps = .ok ls
  | [], _, h => h
  | (n, v) :: ps, ls, h => by
    simp only [decParams] at h ⊢
    cases hv : decValType a v with
    | error e => rw [hv] at h; cases h
    | ok t =>
      rw [hv] at h
      cases hvs : decParams a ps with
      | error e => rw [hvs] at h; cases h
      | ok ts' => rw [decValType_ext hx hv, decParams_ext hx hvs]; rw [hvs] at h; exact h

/-- Two steps whose results are combined by `pure`. -/
theorem cons_sim {α β γ : Type} {e e' : Enc} {cst : CSt} {dst : Option DSt} {x : EncM α}
    {y : EncM (List β)} {f : α → List β → γ} {r : γ} {P : α → List Slot → Prop} {Q : List β → List Slot → Prop}
    (h : (do let a ← x; let b ← y; pure (f a b)).run e = .ok (r, e'))
    (hx : ∀ {a e₂}, x.run e = .ok (a, e₂) → Sim e cst dst e₂ (P a))
    (hy : ∀ {e₁ cst₁ dst₁ b e₂}, Inv e₁ cst₁ dst₁ → y.run e₁ = .ok (b, e₂) → Sim e₁ cst₁ dst₁ e₂ (Q b))
    (hP : ∀ {a u w}, P a u → Ext u w → P a w) :
    ∃ a b, r = f a b ∧ Sim e cst dst e' (fun cur => P a cur ∧ Q b cur) := by
  obtain ⟨a, e₁, h₁, h₂⟩ := run_bind_ok h
  obtain ⟨b, e₂, h₃, h₄⟩ := run_bind_ok h₂
  obtain ⟨rfl, rfl⟩ := run_pure_ok h₄
  exact ⟨a, b, rfl, Sim.seq (hx h₁) hP (fun hI₁ => hy hI₁ h₃)⟩

theorem fields_sim : ∀ (fs : List (Labeled Ty)) {e e' : Enc} {cst : CSt} {dst : Option DSt}
    {vs : List (String × ValType)}, Inv e cst dst → (fields fs).run e = .ok (vs, e') →
    Sim e cst dst e' (fun cur => decFields cur vs = .ok (fs.map Labeled.strip))
  | [], _, _, cst, dst, _, hI, h => by
    obtain ⟨rfl, rfl⟩ := run_pure_ok (a := ([] : List (String × ValType))) h
    exact ⟨cst, dst, hI, Grows.refl _ _ _, rfl⟩
  | f :: fs, _, _, _, _, _, hI, h => by
    obtain ⟨a, b, rfl, hs⟩ := cons_sim (P := fun a cur => decValType cur a = .ok f.ty)
      (Q := fun b cur => decFields cur b = .ok (fs.map Labeled.strip)) h (valType_sim f.ty hI)
      (fun hI₁ => fields_sim fs hI₁) (fun hp hx => decValType_ext hx hp)
    exact hs.mono fun cur hc => by simp only [decFields, hc.1, hc.2]; rfl

theorem cases_sim : ∀ (cs : List (Labeled (Option Ty))) {e e' : Enc} {cst : CSt} {dst : Option DSt}
    {vs : List (String × Option ValType)}, Inv e cst dst → (cases cs).run e = .ok (vs, e') →
    Sim e cst dst e' (fun cur => decCases cur vs = .ok (cs.map Labeled.strip))
  | [], _, _, cst, dst, _, hI, h => by
    obtain ⟨rfl, rfl⟩ := run_pure_ok (a := ([] : List (String × Option ValType))) h
    exact ⟨cst, dst, hI, Grows.refl _ _ _, rfl⟩
  | c :: cs, _, _, _, _, _, hI, h => by
    obtain ⟨a, b, rfl, hs⟩ := cons_sim (P := fun a cur => decOpt cur a = .ok c.ty)
      (Q := fun b cur => decCases cur b = .ok (cs.map Labeled.strip)) h (optValType_sim c.ty hI)
      (fun hI₁ => cases_sim cs hI₁) (fun hp hx => decOpt_ext hx hp)
    exact hs.mono fun cur hc => by simp only [decCases, hc.1, hc.2]; rfl

theorem params_sim : ∀ (ps : List (String × Ty)) {e e' : Enc} {cst : CSt} {dst : Option DSt}
    {vs : List (String × ValType)}, Inv e cst dst → (params ps).run e = .ok (vs, e') →
    Sim e cst dst e' (fun cur => decParams cur vs = .ok ps)
  | [], _, _, cst, dst, _, hI, h => by
    obtain ⟨rfl, rfl⟩ := run_pure_ok (a := ([] : List (String × ValType))) h
    exact ⟨cst, dst, hI, Grows.refl _ _ _, rfl⟩
  | p :: ps, _, _, _, _, _, hI, h => by
    obtain ⟨a, b, rfl, hs⟩ := cons_sim (P := fun a cur => decValType cur a = .ok p.2)
      (Q := fun b cur => decParams cur b = .ok ps) h (valType_sim p.2 hI)
      (fun hI₁ => params_sim ps hI₁) (fun hp hx => decValType_ext hx hp)
    exact hs.mono fun cur hc => by simp only [decParams, hc.1, hc.2]; rfl

/-! ## Fresh definitions -/

/-- The definition of a structural type decodes to that type. -/
theorem structural_sim {e e' : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst) :
    ∀ (t : Ty) {d : DefValType}, (structural t).run e = .ok (d, e') →
      Sim e cst dst e' (fun cur => decDefVal cur d = .ok (.ty t))
  | .prim p, _, h => by
    obtain ⟨rfl, rfl⟩ := run_pure_ok (a := DefValType.prim p) h
    exact ⟨cst, dst, hI, Grows.refl _ _ _, rfl⟩
  | .ref _, _, h => absurd h run_fail
  | .list t, _, h => by
    obtain ⟨a, rfl, hs⟩ := map_sim (P := fun a cur => decValType cur a = .ok t) h (valType_sim t hI)
    exact hs.mono fun cur hc => by simp only [decDefVal, hc]; rfl
  | .fixedList t n, _, h => by
    obtain ⟨a, rfl, hs⟩ := map_sim (P := fun a cur => decValType cur a = .ok t) h (valType_sim t hI)
    exact hs.mono fun cur hc => by simp only [decDefVal, hc]; rfl
  | .option t, _, h => by
    obtain ⟨a, rfl, hs⟩ := map_sim (P := fun a cur => decValType cur a = .ok t) h (valType_sim t hI)
    exact hs.mono fun cur hc => by simp only [decDefVal, hc]; rfl
  | .map k v, _, h => by
    obtain ⟨a, b, rfl, hs⟩ := pair_sim (P := fun a cur => decValType cur a = .ok k)
      (Q := fun b cur => decValType cur b = .ok v) h (valType_sim k hI) (fun hI₁ => valType_sim v hI₁)
      (fun hp hx => decValType_ext hx hp)
    exact hs.mono fun cur hc => by simp only [decDefVal, hc.1, hc.2]; rfl
  | .result o r, _, h => by
    obtain ⟨a, b, rfl, hs⟩ := pair_sim (P := fun a cur => decOpt cur a = .ok o)
      (Q := fun b cur => decOpt cur b = .ok r) h (optValType_sim o hI) (fun hI₁ => optValType_sim r hI₁)
      (fun hp hx => decOpt_ext hx hp)
    exact hs.mono fun cur hc => by simp only [decDefVal, hc.1, hc.2]; rfl
  | .tuple ts, _, h => by
    obtain ⟨a, rfl, hs⟩ := map_sim (P := fun a cur => decValTypes cur a = .ok ts) h (valTypes_sim ts hI)
    exact hs.mono fun cur hc => by simp only [decDefVal, hc]; rfl
  | .own r, _, h => by
    obtain ⟨a, rfl, hs⟩ := map_sim (P := fun a cur => cur[a]? = some (.named r)) h (refIdx_sim hI)
    exact hs.mono fun cur hc => by simp only [decDefVal, decRef_of_get hc]; rfl
  | .borrow r, _, h => by
    obtain ⟨a, rfl, hs⟩ := map_sim (P := fun a cur => cur[a]? = some (.named r)) h (refIdx_sim hI)
    exact hs.mono fun cur hc => by simp only [decDefVal, decRef_of_get hc]; rfl
  | .future t, _, h => by
    obtain ⟨a, rfl, hs⟩ := map_sim (P := fun a cur => decOpt cur a = .ok t) h (optValType_sim t hI)
    exact hs.mono fun cur hc => by simp only [decDefVal, hc]; rfl
  | .stream t, _, h => by
    obtain ⟨a, rfl, hs⟩ := map_sim (P := fun a cur => decOpt cur a = .ok t) h (optValType_sim t hI)
    exact hs.mono fun cur hc => by simp only [decDefVal, hc]; rfl

/-- The slot `c` can be claimed as the definition of a type of kind `k`. -/
def ClaimOK (m : Maps) (cur : List Slot) (c : Nat) (k : TyDefKind) : Prop :=
  ∃ sl, claim cur c = .ok (k, sl) ∧ sl.length = cur.length ∧ SlotsOK m sl

/-- A slot appended after tables were made can be claimed: no entry points
to it. -/
theorem SlotsOK.set_fresh {m : Maps} {cur : List Slot} (h : SlotsOK m cur) (s s' : Slot) :
    SlotsOK m ((cur ++ [s]).set cur.length s') := by
  have hx : SlotsOK m (cur ++ [s]) := h.ext (Ext.append _ _)
  have fresh : ∀ {α : Type} [DecidableEq α] {tbl : List (α × Nat)} {den : α → Slot},
      TableOK tbl cur den → ∀ x, lookup x tbl ≠ some cur.length :=
    fun ht x hx' => Nat.lt_irrefl _ (ht.lt hx')
  exact ⟨hx.named.set (fresh h.named) s', hx.anon.set (fresh h.anon) s', hx.funcs.set (fresh h.funcs) s'⟩

/-- A fresh definition decoded as `sl` is claimed as `k`. -/
theorem claim_fresh {m : Maps} {cur : List Slot} (h : SlotsOK m cur) {sl : Slot} {k : TyDefKind}
    (hk : sl = .def k ∨ ∃ t, sl = .ty t ∧ k = .type t) : ClaimOK m (cur ++ [sl]) cur.length k := by
  refine ⟨(cur ++ [sl]).set cur.length .used, ?_, by simp, h.set_fresh sl .used⟩
  have hget : slotAt (cur ++ [sl]) cur.length = .ok sl := slotAt_of_get (by simp)
  rcases hk with rfl | ⟨t, rfl, rfl⟩ <;> simp only [claim, hget] <;> rfl

/-- After a fresh definition: it is claimable. -/
theorem fresh_claim {e e' : Enc} {cst : CSt} {dst : Option DSt} {sl : Slot} {c : Nat} {k : TyDefKind}
    (P : Pushed e e' cst dst sl c) (hI : Inv e cst dst) (hk : sl = .def k ∨ ∃ t, sl = .ty t ∧ k = .type t) :
    Sim e cst dst e' (fun cur => ClaimOK e'.curMaps cur c k) := by
  obtain ⟨cst', dst', hI', hG, hc⟩ := P.sim
  refine ⟨cst', dst', hI', hG, ?_⟩
  rw [hc, P.idx, P.maps]
  exact claim_fresh hI.curOK hk

theorem label_strip (c : Labeled Unit) : label c.name = c.strip := rfl

theorem names_label (cs : List (Labeled Unit)) : (cs.map (·.name)).map label = cs.map Labeled.strip := by
  simp only [List.map_map]; rfl

/-- The definition of a named type of kind `k`, claimable as `k` without docs. -/
theorem typeDefIdx_sim {e e' : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst) :
    ∀ (k : TyDefKind) {c : Nat}, (typeDefIdx k).run e = .ok (c, e') →
      Sim e cst dst e' (fun cur => ClaimOK e'.curMaps cur c k.strip)
  | .record fs, _, h => by
    obtain ⟨vs, e₁, h₁, h₂⟩ := run_bind_ok h
    obtain ⟨cst₁, dst₁, hI₁, hG₁, hd⟩ := fields_sim fs hI h₁
    have hd' : DefSlot (curSlots cst₁ dst₁) (.val (.record vs)) (.def (.record (fs.map Labeled.strip))) := by
      simp only [DefSlot, decDefVal, hd]; rfl
    obtain ⟨c₂, d₂, hI₂, hG₂, hp⟩ := fresh_claim (defType_sim hI₁ hd' h₂) hI₁ (.inl rfl)
    exact ⟨c₂, d₂, hI₂, hG₁.trans hG₂, hp⟩
  | .variant cs, _, h => by
    obtain ⟨vs, e₁, h₁, h₂⟩ := run_bind_ok h
    obtain ⟨cst₁, dst₁, hI₁, hG₁, hd⟩ := cases_sim cs hI h₁
    have hd' : DefSlot (curSlots cst₁ dst₁) (.val (.variant vs)) (.def (.variant (cs.map Labeled.strip))) := by
      simp only [DefSlot, decDefVal, hd]; rfl
    obtain ⟨c₂, d₂, hI₂, hG₂, hp⟩ := fresh_claim (defType_sim hI₁ hd' h₂) hI₁ (.inl rfl)
    exact ⟨c₂, d₂, hI₂, hG₁.trans hG₂, hp⟩
  | .enum cs, _, h => by
    have hd' : DefSlot (curSlots cst dst) (.val (.enum (cs.map (·.name)))) (.def (.enum (cs.map Labeled.strip))) := by
      simp only [DefSlot, decDefVal, names_label]; rfl
    exact fresh_claim (defType_sim hI hd' h) hI (.inl rfl)
  | .flags fs, _, h => by
    have hd' : DefSlot (curSlots cst dst) (.val (.flags (fs.map (·.name)))) (.def (.flags (fs.map Labeled.strip))) := by
      simp only [DefSlot, decDefVal, names_label]; rfl
    exact fresh_claim (defType_sim hI hd' h) hI (.inl rfl)
  | .resource, _, h => absurd h run_fail
  | .type (.ref r), _, h => by
    obtain ⟨cst₁, dst₁, hI₁, hG₁, hk⟩ := refIdx_sim hI h
    refine ⟨cst₁, dst₁, hI₁, hG₁, curSlots cst₁ dst₁, ?_, rfl, hI₁.curOK⟩
    simp only [claim, slotAt_of_get hk]; rfl
  | .type (.prim p), _, h => typeDefIdx_struct hI (.prim p) h
  | .type (.list t), _, h => typeDefIdx_struct hI (.list t) h
  | .type (.fixedList t n), _, h => typeDefIdx_struct hI (.fixedList t n) h
  | .type (.map k v), _, h => typeDefIdx_struct hI (.map k v) h
  | .type (.option t), _, h => typeDefIdx_struct hI (.option t) h
  | .type (.result o r), _, h => typeDefIdx_struct hI (.result o r) h
  | .type (.tuple ts), _, h => typeDefIdx_struct hI (.tuple ts) h
  | .type (.own r), _, h => typeDefIdx_struct hI (.own r) h
  | .type (.borrow r), _, h => typeDefIdx_struct hI (.borrow r) h
  | .type (.future t), _, h => typeDefIdx_struct hI (.future t) h
  | .type (.stream t), _, h => typeDefIdx_struct hI (.stream t) h
where
  typeDefIdx_struct {e e' : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst) (t : Ty) {c : Nat}
      (h : (do let d ← structural t; defType (.val d)).run e = .ok (c, e')) :
      Sim e cst dst e' (fun cur => ClaimOK e'.curMaps cur c (TyDefKind.type t).strip) := by
    obtain ⟨d, e₁, h₁, h₂⟩ := run_bind_ok h
    obtain ⟨cst₁, dst₁, hI₁, hG₁, hd⟩ := structural_sim hI t h₁
    obtain ⟨c₂, d₂, hI₂, hG₂, hp⟩ := fresh_claim (defType_sim hI₁ (t := .val d) hd h₂) hI₁ (.inr ⟨t, rfl, rfl⟩)
    exact ⟨c₂, d₂, hI₂, hG₁.trans hG₂, hp⟩

end Silmaril.Wasm.Wit.Binary
