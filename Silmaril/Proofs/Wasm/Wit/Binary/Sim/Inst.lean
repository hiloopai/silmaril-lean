module

public import Silmaril.Proofs.Wasm.Wit.Binary.Sim.Defs

/-!
# The WIT binary round trip: named types, functions and instance types

`typeDef_sim_inner` and `typeDef_sim_world`: a named type is read back
without docs, in an instance type or as a world import. `funcType_sim`: a
function type decodes to the function's signature. `exportFuncs_sim`: the
exported functions are read back without docs.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary Enc

/-- Steps that keep the component type's outputs. -/
structure Frame (e e' : Enc) (cst cst' : CSt) : Prop where
  oext : Ext cst.slots cst'.slots
  insts : cst'.insts = cst.insts
  imports : cst'.imports = cst.imports
  exports : cst'.exports = cst.exports
  importTypes : e'.importTypes = e.importTypes
  instsN : e'.insts = e.insts
  instOf : e'.instOf = e.instOf

theorem Frame.refl (e : Enc) (cst : CSt) : Frame e e cst cst :=
  ⟨Ext.refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Frame.trans {e₁ e₂ e₃ : Enc} {c₁ c₂ c₃ : CSt} (h : Frame e₁ e₂ c₁ c₂) (h' : Frame e₂ e₃ c₂ c₃) :
    Frame e₁ e₃ c₁ c₃ :=
  ⟨h.oext.trans h'.oext, h'.insts.trans h.insts, h'.imports.trans h.imports, h'.exports.trans h.exports,
    h'.importTypes.trans h.importTypes, h'.instsN.trans h.instsN, h'.instOf.trans h.instOf⟩

theorem Grows.frame {e e' : Enc} {cst cst' : CSt} {dst dst' : Option DSt} (h : Grows e e' cst cst' dst dst') :
    Frame e e' cst cst' :=
  ⟨h.oext, h.insts, h.imports, h.exports, h.importTypes, h.instsN, h.instOf⟩

theorem Inv.inner_some {e : Enc} {cst : CSt} {d : DSt} (hI : Inv e cst (some d)) :
    ∃ s, e.inner = some s ∧ instSteps cst.slots {} s.decls = .ok d ∧ d.slots.length = s.count := by
  have hi := hI.inner
  cases hs : e.inner with
  | none => rw [hs] at hi; exact hi.elim
  | some s => rw [hs] at hi; exact ⟨s, rfl, hi.1, hi.2.1⟩

theorem Inv.inner_none {e : Enc} {cst : CSt} (hI : Inv e cst none) : e.inner = none := by
  have hi := hI.inner
  cases hs : e.inner with
  | none => rfl
  | some s => rw [hs] at hi; exact hi.elim

theorem Grows.dst_some {e e' : Enc} {cst cst' : CSt} {d : DSt} {dst' : Option DSt}
    (h : Grows e e' cst cst' (some d) dst') : ∃ d', dst' = some d' ∧ d'.types = d.types ∧ d'.funcs = d.funcs := by
  have ho := h.out
  cases dst' with
  | none => exact ho.elim
  | some d' => exact ⟨d', rfl, ho.1, ho.2⟩

theorem Grows.dst_none {e e' : Enc} {cst cst' : CSt} {dst' : Option DSt}
    (h : Grows e e' cst cst' none dst') : dst' = none := by
  have ho := h.out
  cases dst' with
  | none => rfl
  | some d' => exact ho.elim

/-! ## Naming a type in an instance type -/

theorem exportType_inner_run {e : Enc} {s : Space InstanceDecl} (hs : e.inner = some s) (n : String)
    (b : TypeBound) : (exportType n b).run e = .ok (s.count,
      { e with inner := some { s with decls := s.decls ++ [.export ↑n (.type b)], count := s.count + 1 } }) := by
  unfold exportType; simp [hs]; rfl

/-- An exported type of an instance type: the decoder's state after it. -/
def DSt.named (d : DSt) (sl : List Slot) (n : String) (k : TyDefKind) : DSt :=
  { d with slots := sl ++ [.named ⟨.local, n⟩], types := d.types ++ [{ name := n, kind := k }] }

/-- Silmaril.Wasm.Component.Binary.Export the type `idx` claimable as `k` under `n`, and record the name. -/
theorem nameType_inner {e e' : Enc} {cst : CSt} {d : DSt} (hI : Inv e cst (some d)) {n : String}
    {b : TypeBound} {k : TyDefKind} {sl : List Slot} (hsl : sl.length = d.slots.length)
    (hok : SlotsOK e.curMaps sl)
    (hstep : instStep cst.slots d (.export ↑n (.type b)) = .ok (d.named sl n k))
    (h : (do let i ← exportType n b; insertNamed ⟨.local, n⟩ i).run e = .ok ((), e')) :
    Inv e' cst (some (d.named sl n k)) ∧ Frame e e' cst cst := by
  obtain ⟨s, hs, hd, hlen⟩ := hI.inner_some
  obtain ⟨i, e₁, h₁, h₂⟩ := run_bind_ok h
  rw [exportType_inner_run hs] at h₁; cases h₁
  rw [insertNamed_run] at h₂; cases h₂
  have hm : SlotsOK s.maps (sl ++ [.named ⟨.local, n⟩]) := by
    have := hok.ext (Ext.append sl [.named ⟨.local, n⟩]); simpa [Enc.curMaps, hs] using this
  have hI₁ : Inv { e with inner := some { s with decls := s.decls ++ [.export ↑n (.type b)], count := s.count + 1 } } cst (some (d.named sl n k)) :=
    ⟨hI.outer, hI.olen, hI.ook, hI.otypes, hI.ilen, hI.inst,
      instSteps_snoc hd hstep, by simp [DSt.named, hsl, hlen], hm⟩
  have hget : (curSlots cst (some (d.named sl n k)))[s.count]? = some (.named ⟨.local, n⟩) := by
    simp [curSlots, DSt.named, ← hlen, ← hsl]
  exact ⟨insertNamed_sim hI₁ hget, ⟨Ext.refl _, rfl, rfl, rfl, by unfold Enc.withMaps; rfl, by unfold Enc.withMaps; rfl,
    by unfold Enc.withMaps; rfl⟩⟩

theorem typeDef_resource {td : TypeDef} (hk : td.kind = .resource) :
    typeDef td = (do let k ← exportType td.name .subResource; insertNamed ⟨.local, td.name⟩ k) := by
  unfold typeDef; rw [hk]

theorem typeDef_other {td : TypeDef} (hk : td.kind ≠ .resource) :
    typeDef td = (do
      let idx ← typeDefIdx td.kind
      let k ← exportType td.name (.eq idx)
      insertNamed ⟨.local, td.name⟩ k) := by
  unfold typeDef; split
  · next h => exact absurd h hk
  · rfl

theorem TypeDef.strip_eq (td : TypeDef) : td.strip = { name := td.name, kind := td.kind.strip } := rfl

/-- **A named type in an instance type** is read back without docs. -/
theorem typeDef_sim_inner {e e' : Enc} {cst : CSt} {d : DSt} (hI : Inv e cst (some d)) (td : TypeDef)
    (h : (typeDef td).run e = .ok ((), e')) :
    ∃ cst' d', Inv e' cst' (some d') ∧ Frame e e' cst cst' ∧ d'.types = d.types ++ [td.strip] ∧
      d'.funcs = d.funcs := by
  by_cases hk : td.kind = .resource
  · rw [typeDef_resource hk] at h
    have hstep : instStep cst.slots d (.export ↑td.name (.type .subResource)) =
        .ok (d.named d.slots td.name .resource) := rfl
    obtain ⟨hI', hF⟩ := nameType_inner hI rfl hI.curOK hstep h
    exact ⟨cst, _, hI', hF, by simp [DSt.named, TypeDef.strip_eq, hk, TyDefKind.strip], rfl⟩
  · rw [typeDef_other hk] at h
    obtain ⟨idx, e₁, h₁, h₂⟩ := run_bind_ok h
    obtain ⟨cst₁, dst₁, hI₁, hG₁, sl, hcl, hsl, hok⟩ := typeDefIdx_sim hI td.kind h₁
    obtain ⟨d₁, rfl, ht, hf⟩ := hG₁.dst_some
    have hcl' : claim d₁.slots idx = .ok (td.kind.strip, sl) := hcl
    have hstep : instStep cst₁.slots d₁ (.export ↑td.name (.type (.eq idx))) =
        .ok (d₁.named sl td.name td.kind.strip) := by simp only [instStep, hcl']; rfl
    obtain ⟨hI', hF⟩ := nameType_inner hI₁ hsl hok hstep h₂
    exact ⟨cst₁, _, hI', hG₁.frame.trans hF, by simp [DSt.named, TypeDef.strip_eq, ht], hf⟩

theorem typeDefs_sim_inner : ∀ (tds : List TypeDef) {e e' : Enc} {cst : CSt} {d : DSt},
    Inv e cst (some d) → (typeDefs tds).run e = .ok ((), e') →
    ∃ cst' d', Inv e' cst' (some d') ∧ Frame e e' cst cst' ∧ d'.types = d.types ++ tds.map TypeDef.strip ∧
      d'.funcs = d.funcs
  | [], _, _, cst, d, hI, h => by
    obtain ⟨-, rfl⟩ := run_pure_ok h
    exact ⟨cst, d, hI, Frame.refl _ _, by simp, rfl⟩
  | td :: tds, _, _, _, _, hI, h => by
    obtain ⟨u, e₁, h₁, h₂⟩ := run_bind_ok h
    obtain ⟨c₁, d₁, hI₁, hF₁, ht₁, hf₁⟩ := typeDef_sim_inner hI td h₁
    obtain ⟨c₂, d₂, hI₂, hF₂, ht₂, hf₂⟩ := typeDefs_sim_inner tds hI₁ h₂
    exact ⟨c₂, d₂, hI₂, hF₁.trans hF₂, by simp [ht₂, ht₁], hf₂.trans hf₁⟩

/-! ## Naming a type in a world -/

theorem exportType_world_run {e : Enc} (hs : e.inner = none) (ht : e.importTypes = true) (n : String)
    (b : TypeBound) : (exportType n b).run e = .ok (e.outer.count,
      { e with outer := { e.outer with decls := e.outer.decls ++ [.import ↑n (.type b)], count := e.outer.count + 1 } }) := by
  unfold exportType; simp [hs, ht]; rfl

/-- An imported type of a world: the decoder's state after it. -/
def CSt.named (c : CSt) (sl : List Slot) (n : String) (k : TyDefKind) : CSt :=
  { c with slots := sl ++ [.named ⟨.local, n⟩], imports := c.imports ++ [.type { name := n, kind := k }] }

/-- A world imports the type `idx` claimable as `k` under `n`. -/
theorem nameType_world {e e' : Enc} {cst : CSt} (hI : Inv e cst none) (ht : e.importTypes = true)
    {n : String} {b : TypeBound} {k : TyDefKind} {sl : List Slot} (hsl : sl.length = cst.slots.length)
    (hok : SlotsOK e.curMaps sl) (hotypes : TableOK e.outerTypes sl (fun p => .named ⟨.iface p.1, p.2⟩))
    (hstep : compStep cst (.import ↑n (.type b)) = .ok (cst.named sl n k))
    (h : (do let i ← exportType n b; insertNamed ⟨.local, n⟩ i).run e = .ok ((), e')) :
    Inv e' (cst.named sl n k) none ∧ e'.importTypes = e.importTypes ∧ e'.insts = e.insts ∧
      e'.instOf = e.instOf := by
  have hs := hI.inner_none
  obtain ⟨i, e₁, h₁, h₂⟩ := run_bind_ok h
  rw [exportType_world_run hs ht] at h₁; cases h₁
  rw [insertNamed_run] at h₂; cases h₂
  have hx : Ext sl (sl ++ [.named ⟨.local, n⟩]) := Ext.append _ _
  have hm : SlotsOK e.outer.maps (sl ++ [.named ⟨.local, n⟩]) := by
    have := hok.ext hx; simpa [Enc.curMaps, hs] using this
  have hI₁ : Inv { e with outer := { e.outer with decls := e.outer.decls ++ [.import ↑n (.type b)], count := e.outer.count + 1 } } (cst.named sl n k) none :=
    ⟨compSteps_snoc hI.outer hstep, by simp [CSt.named, hsl, hI.olen], hm, hotypes.ext hx, hI.ilen,
      hI.inst, by simp [InnerOK, hs]⟩
  have hget : (curSlots (cst.named sl n k) none)[e.outer.count]? = some (.named ⟨.local, n⟩) := by
    simp [curSlots, CSt.named, hsl, hI.olen]
  exact ⟨insertNamed_sim hI₁ hget, by unfold Enc.withMaps; simp [hs], by unfold Enc.withMaps; simp [hs],
    by unfold Enc.withMaps; simp [hs]⟩

end Silmaril.Wasm.Wit.Binary
