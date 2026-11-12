module

public import Silmaril.Proofs.Wasm.Wit.Binary.Sim.Prim

/-!
# The WIT binary round trip: table entries and type references

Recording a table entry for an index whose slot denotes the key keeps the
invariant (`insertNamed_sim`, `insertAnon_sim`); a type reference, local or
aliased out of an imported interface, gets an index whose slot names it
(`refIdx_sim`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary Enc

/-! ## Table entries -/

theorem insertNamed_run (r : TyRef) (k : Nat) (e : Enc) :
    (insertNamed r k).run e = .ok ((), e.withMaps { e.curMaps with named := (r, k) :: e.curMaps.named }) :=
  rfl

theorem insertAnon_run (t : Ty) (k : Nat) (e : Enc) :
    (insertAnon t k).run e = .ok ((), e.withMaps { e.curMaps with anon := (t, k) :: e.curMaps.anon }) :=
  rfl

theorem withMaps_outerTypes (e : Enc) (m : Maps) : (e.withMaps m).outerTypes = e.outerTypes := by
  unfold Enc.withMaps; cases e.inner <;> rfl

theorem withMaps_inner_isSome (e : Enc) (m : Maps) : (e.withMaps m).inner.isSome = e.inner.isSome := by
  unfold Enc.withMaps; cases e.inner <;> rfl

/-- Recording that `r` is named by `k`. -/
theorem insertNamed_sim {e : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst) {r : TyRef}
    {k : Nat} (hk : (curSlots cst dst)[k]? = some (.named r)) :
    Inv (e.withMaps { e.curMaps with named := (r, k) :: e.curMaps.named }) cst dst :=
  hI.withMaps ⟨hI.curOK.named.cons hk, hI.curOK.anon, hI.curOK.funcs⟩

/-- Recording that the anonymous type `t` is defined at `k`. -/
theorem insertAnon_sim {e : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst) {t : Ty}
    {k : Nat} (hk : (curSlots cst dst)[k]? = some (.ty t)) :
    Inv (e.withMaps { e.curMaps with anon := (t, k) :: e.curMaps.anon }) cst dst :=
  hI.withMaps ⟨hI.curOK.named, hI.curOK.anon.cons hk, hI.curOK.funcs⟩

/-! ## Aliases of foreign types -/

/-- The new outer slots after an outer alias, as the decoder reads them. -/
theorem outerAlias_dec {e : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst) {i : IfaceName}
    {inst : Nat} (hi : lookup i e.instOf = some inst) (n : String) :
    compStep cst (.inst (.alias ⟨.type, .export inst n⟩)) =
      .ok { cst with slots := cst.slots ++ [.named ⟨.iface i, n⟩] } := by
  simp only [compStep, hI.inst i inst hi]; rfl

theorem InnerOK.outer_ext {inner : Option (Space InstanceDecl)} {o o' : List Slot} {dst : Option DSt}
    (h : InnerOK inner o dst) (hx : Ext o o') : InnerOK inner o' dst := by
  match inner, dst, h with
  | none, none, _ => trivial
  | some _, some _, h => exact ⟨instSteps_outer_ext hx h.1, h.2.1, h.2.2⟩

theorem curSlots_outer_ext {cst cst' : CSt} (hx : Ext cst.slots cst'.slots) :
    ∀ dst : Option DSt, Ext (curSlots cst dst) (curSlots cst' dst)
  | none => hx
  | some _ => Ext.refl _

/-- A new outer alias: the outer slots grow by the aliased type. -/
theorem outerAlias_new {e : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst) {i : IfaceName}
    {inst : Nat} (hi : lookup i e.instOf = some inst) (n : String) :
    let e' : Enc := { e with outer := { e.outer with decls := e.outer.decls ++ [ComponentDecl.inst (.alias ⟨.type, .export inst n⟩)], count := e.outer.count + 1 }, outerTypes := ((i, n), e.outer.count) :: e.outerTypes }
    let cst' : CSt := { cst with slots := cst.slots ++ [.named ⟨.iface i, n⟩] }
    Inv e' cst' dst ∧ Grows e e' cst cst' dst dst := by
  intro e' cst'
  have hx : Ext cst.slots cst'.slots := Ext.append _ _
  have hk : cst'.slots[e.outer.count]? = some (.named ⟨.iface i, n⟩) := by
    simp [cst', ← hI.olen]
  refine ⟨⟨compSteps_snoc hI.outer (outerAlias_dec hI hi n), by simp [cst', hI.olen, e'],
    hI.ook.ext hx, (hI.otypes.ext hx).cons hk, hI.ilen, hI.inst, hI.inner.outer_ext hx⟩,
    ⟨hx, curSlots_outer_ext hx dst, rfl, rfl, rfl, OutSame.refl _, rfl, rfl, rfl⟩⟩

/-- The outer alias of a foreign type: an outer slot naming it. -/
theorem outerAliasSt_sim {e e' : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst)
    {i : IfaceName} {n : String} {k : Nat} (h : outerAliasSt i n e = .ok (k, e')) :
    e'.inner = e.inner ∧ e'.curMaps = e.curMaps ∧
    ∃ cst', Inv e' cst' dst ∧ Grows e e' cst cst' dst dst ∧ cst'.slots[k]? = some (.named ⟨.iface i, n⟩) := by
  unfold outerAliasSt at h
  cases hi : lookup i e.instOf with
  | none => rw [hi] at h; cases h
  | some inst =>
    rw [hi] at h
    cases ho : lookup (i, n) e.outerTypes with
    | some k₀ =>
      rw [ho] at h; cases h
      exact ⟨rfl, rfl, cst, hI, Grows.refl _ _ _, hI.otypes (i, n) k ho⟩
    | none =>
      rw [ho] at h; cases h
      obtain ⟨hI', hG⟩ := outerAlias_new hI hi n
      exact ⟨rfl, rfl, _, hI', hG, by simp [← hI.olen]⟩

/-- The alias step inside an instance type. -/
theorem innerAlias_some {e : Enc} {cst : CSt} {d : DSt} {s : Space InstanceDecl} (hs : e.inner = some s)
    (hI : Inv e cst (some d)) {k : Nat} {r : TyRef} (hk : cst.slots[k]? = some (.named r)) :
    (innerAliasSt k e).2.curMaps = e.curMaps ∧ (innerAliasSt k e).2.outerTypes = e.outerTypes ∧
    Sim e cst (some d) (innerAliasSt k e).2 (fun cur => cur[(innerAliasSt k e).1]? = some (.named r)) := by
  have hi : InnerOK (some s) cst.slots (some d) := hs ▸ hI.inner
  have hstep : instStep cst.slots d (.alias ⟨.type, .outer 1 k⟩) =
      .ok { d with slots := d.slots ++ [.named r] } := by simp only [instStep, hk]; rfl
  have hget : (d.slots ++ [Slot.named r])[s.count]? = some (.named r) := by simp [← hi.2.1]
  unfold innerAliasSt
  rw [hs]
  exact ⟨by simp [Enc.curMaps, hs], rfl, cst, some { d with slots := d.slots ++ [.named r] },
    ⟨hI.outer, hI.olen, hI.ook, hI.otypes, hI.ilen, hI.inst,
      instSteps_snoc hi.1 hstep, by simp [hi.2.1], hi.2.2.ext (Ext.append _ _)⟩,
    ⟨Ext.refl _, Ext.append _ _, rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩, hget⟩

/-- Inside an instance type, an alias of the outer slot `k`. -/
theorem innerAliasSt_sim {e : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst) {k : Nat}
    {r : TyRef} (hk : cst.slots[k]? = some (.named r)) :
    (innerAliasSt k e).2.curMaps = e.curMaps ∧ (innerAliasSt k e).2.outerTypes = e.outerTypes ∧
    Sim e cst dst (innerAliasSt k e).2 (fun cur => cur[(innerAliasSt k e).1]? = some (.named r)) := by
  have hi := hI.inner
  cases hs : e.inner with
  | none =>
    rw [hs] at hi
    cases dst with
    | none => unfold innerAliasSt; rw [hs]; exact ⟨rfl, rfl, cst, none, hI, Grows.refl _ _ _, hk⟩
    | some d => exact absurd hi id
  | some s =>
    rw [hs] at hi
    cases dst with
    | none => exact absurd hi id
    | some d => exact innerAlias_some hs hI hk

/-- `import_type`: an index of the current space naming the foreign type. -/
theorem importType_sim {e e' : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst)
    {i : IfaceName} {n : String} {k : Nat} (h : (importType i n).run e = .ok (k, e')) :
    e'.curMaps = e.curMaps ∧ Sim e cst dst e' (fun cur => cur[k]? = some (.named ⟨.iface i, n⟩)) := by
  obtain ⟨k₁, e₁, h₁, h₂⟩ := run_bind_ok h
  obtain ⟨hin, hm, cst₁, hI₁, hG₁, hk₁⟩ := outerAliasSt_sim hI h₁
  have h₂' : innerAliasSt k₁ e₁ = (k, e') := Except.ok.inj h₂
  obtain ⟨hm₂, -, cst₂, dst₂, hI₂, hG₂, hk₂⟩ := innerAliasSt_sim hI₁ hk₁
  rw [h₂'] at hm₂ hI₂ hG₂ hk₂
  exact ⟨hm₂.trans hm, cst₂, dst₂, hI₂, hG₁.trans hG₂, hk₂⟩

/-- A foreign reference not yet aliased: alias it and record it. -/
theorem refIdx_foreign {e e' : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst) {i : IfaceName}
    {r : TyRef} (ho : r.owner = .iface i) {k : Nat}
    (h : (do let k ← importType i r.name; insertNamed r k; pure k).run e = .ok (k, e')) :
    Sim e cst dst e' (fun cur => cur[k]? = some (.named r)) := by
  obtain ⟨k₁, e₂, h₃, h₄⟩ := run_bind_ok h
  obtain ⟨-, cst₂, dst₂, hI₂, hG₂, hk₂⟩ := importType_sim hI h₃
  have hr : (⟨.iface i, r.name⟩ : TyRef) = r := by cases r; simp_all
  have hk : (curSlots cst₂ dst₂)[k₁]? = some (.named r) := hr ▸ hk₂
  obtain ⟨u, e₃, h₅, h₆⟩ := run_bind_ok h₄
  rw [insertNamed_run] at h₅; cases h₅
  obtain ⟨rfl, rfl⟩ := run_pure_ok h₆
  exact ⟨cst₂, dst₂, insertNamed_sim hI₂ hk, hG₂.trans (Grows.withMaps _ _ _ _), hk⟩

/-- **A type reference** gets an index whose slot names it, recorded in the
named table. -/
theorem refIdx_sim {e e' : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst)
    {r : TyRef} {k : Nat} (h : (refIdx r).run e = .ok (k, e')) :
    Sim e cst dst e' (fun cur => cur[k]? = some (.named r)) := by
  obtain ⟨m, e₁, h₁, h₂⟩ := run_bind_ok h
  rw [maps_run] at h₁; cases h₁
  cases hl : lookup r e.curMaps.named with
  | some k₀ =>
    rw [hl] at h₂; cases h₂
    exact ⟨cst, dst, hI, Grows.refl _ _ _, hI.curOK.named r k hl⟩
  | none =>
    rw [hl] at h₂
    cases ho : r.owner with
    | «local» => rw [ho] at h₂; exact absurd h₂ run_fail
    | iface i => rw [ho] at h₂; exact refIdx_foreign hI ho h₂

theorem decRef_of_get {cur : List Slot} {k : Nat} {r : TyRef} (h : cur[k]? = some (.named r)) :
    decRef cur k = .ok r := by
  simp only [decRef, slotAt_of_get h]; rfl

theorem decValType_of_named {cur : List Slot} {k : Nat} {r : TyRef} (h : cur[k]? = some (.named r)) :
    decValType cur (.idx k) = .ok (.ref r) := by
  simp only [decValType, slotAt_of_get h]; rfl

theorem decValType_of_ty {cur : List Slot} {k : Nat} {t : Ty} (h : cur[k]? = some (.ty t)) :
    decValType cur (.idx k) = .ok t := by
  simp only [decValType, slotAt_of_get h]; rfl

end Silmaril.Wasm.Wit.Binary
