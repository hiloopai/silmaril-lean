module

public import Silmaril.Proofs.Wasm.Wit.Binary.Sim.Base

/-!
# The WIT binary round trip: basic encoder steps

Each basic step of the encoder (defining a type, recording a table entry,
aliasing a foreign type) keeps the invariant `Inv`, and the decoder's slot
for its result is what the step was asked for.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary Enc

/-! ## Tables -/

theorem maps_run (e : Enc) : (maps).run e = .ok (e.curMaps, e) := rfl

/-- The state with the current tables replaced. -/
def Enc.withMaps (e : Enc) (m : Maps) : Enc :=
  match e.inner with
  | some s => { e with inner := some { s with maps := m } }
  | none => { e with outer := { e.outer with maps := m } }

theorem setMaps_run (e : Enc) (m : Maps) : (setMaps m).run e = .ok ((), e.withMaps m) := rfl

theorem withMaps_curMaps (e : Enc) (m : Maps) : (e.withMaps m).curMaps = m := by
  unfold Enc.withMaps Enc.curMaps; cases e.inner <;> rfl

/-- Replacing the current tables by tables that agree with the current slots
keeps the invariant. -/
theorem Inv.withMaps {e : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst) {m : Maps}
    (hm : SlotsOK m (curSlots cst dst)) : Inv (e.withMaps m) cst dst := by
  unfold Enc.withMaps
  have hi := hI.inner
  cases hs : e.inner with
  | none =>
    rw [hs] at hi
    cases dst with
    | none => exact ⟨hI.outer, hI.olen, hm, hI.otypes, hI.ilen, hI.inst, by simp [InnerOK]⟩
    | some d => exact absurd hi id
  | some s =>
    rw [hs] at hi
    cases dst with
    | none => exact absurd hi id
    | some d => exact ⟨hI.outer, hI.olen, hI.ook, hI.otypes, hI.ilen, hI.inst, ⟨hi.1, hi.2.1, hm⟩⟩

theorem Grows.withMaps (e : Enc) (m : Maps) (cst : CSt) (dst : Option DSt) :
    Grows e (e.withMaps m) cst cst dst dst := by
  refine ⟨Ext.refl _, Ext.refl _, rfl, rfl, rfl, OutSame.refl _, ?_, ?_, ?_⟩ <;>
    (unfold Enc.withMaps; cases e.inner <;> rfl)

/-- The current tables agree with the current slots. -/
theorem Inv.curOK {e : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst) :
    SlotsOK e.curMaps (curSlots cst dst) := by
  have hi := hI.inner
  unfold Enc.curMaps
  cases hs : e.inner with
  | none =>
    rw [hs] at hi
    cases dst with
    | none => exact hI.ook
    | some d => exact absurd hi id
  | some s =>
    rw [hs] at hi
    cases dst with
    | none => exact absurd hi id
    | some d => exact hi.2.2

theorem Inv.curLen {e : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst) :
    (curSlots cst dst).length = (match e.inner with | some s => s.count | none => e.outer.count) := by
  have hi := hI.inner
  cases hs : e.inner with
  | none =>
    rw [hs] at hi
    cases dst with
    | none => exact hI.olen
    | some d => exact absurd hi id
  | some s =>
    rw [hs] at hi
    cases dst with
    | none => exact absurd hi id
    | some d => exact hi.2.1

/-! ## Defining a type -/

/-- What the decoder makes of a type definition in the current space. -/
def DefSlot (cur : List Slot) : DefType → Slot → Prop
  | .val d, sl => decDefVal cur d = .ok sl
  | .func f, sl => ∃ g, decFuncType cur f = .ok g ∧ sl = .func g
  | _, _ => False

theorem instStep_def {o : List Slot} {d : DSt} {t : DefType} {sl : Slot} (hd : DefSlot d.slots t sl) :
    instStep o d (.type t) = .ok { d with slots := d.slots ++ [sl] } := by
  cases t with
  | val dv => simp only [DefSlot] at hd; simp only [instStep, hd]; rfl
  | func f =>
    obtain ⟨g, hg, rfl⟩ := hd
    simp only [instStep, hg]; rfl
  | component _ => exact hd.elim
  | «instance» _ => exact hd.elim
  | resource _ _ => exact hd.elim

theorem compStep_def {c : CSt} {t : DefType} {sl : Slot} (hd : DefSlot c.slots t sl) :
    compStep c (.inst (.type t)) = .ok { c with slots := c.slots ++ [sl] } := by
  cases t with
  | val dv => simp only [DefSlot] at hd; simp only [compStep, hd]; rfl
  | func f =>
    obtain ⟨g, hg, rfl⟩ := hd
    simp only [compStep, hg]; rfl
  | component _ => exact hd.elim
  | «instance» _ => exact hd.elim
  | resource _ _ => exact hd.elim

theorem defType_inner {e : Enc} {s : Space InstanceDecl} (hs : e.inner = some s) (t : DefType) :
    (defType t).run e = .ok (s.count,
      { e with inner := some { s with decls := s.decls ++ [.type t], count := s.count + 1 } }) := by
  unfold defType; simp [hs]; rfl

theorem defType_outer {e : Enc} (hs : e.inner = none) (t : DefType) :
    (defType t).run e = .ok (e.outer.count,
      { e with outer := { e.outer with decls := e.outer.decls ++ [.inst (.type t)],
                                       count := e.outer.count + 1 } }) := by
  unfold defType; simp [hs]; rfl

/-- The result of a step that appends one slot to the current space. -/
structure Pushed (e e' : Enc) (cst : CSt) (dst : Option DSt) (sl : Slot) (k : Nat) : Prop where
  idx : k = (curSlots cst dst).length
  maps : e'.curMaps = e.curMaps
  otypes : e'.outerTypes = e.outerTypes
  sim : Sim e cst dst e' (· = curSlots cst dst ++ [sl])

theorem defType_sim_inner {e e' : Enc} {cst : CSt} {d : DSt} {s : Space InstanceDecl}
    (hs : e.inner = some s) (hI : Inv e cst (some d)) {t : DefType} {k : Nat} {sl : Slot}
    (hd : DefSlot d.slots t sl) (h : (defType t).run e = .ok (k, e')) : Pushed e e' cst (some d) sl k := by
  rw [defType_inner hs] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
  have hi : InnerOK e.inner cst.slots (some d) := hI.inner
  rw [hs] at hi
  have hlen : d.slots.length = s.count := hi.2.1
  refine ⟨hlen.symm, by simp [Enc.curMaps, hs], rfl, cst, some { d with slots := d.slots ++ [sl] }, ?_, ?_, rfl⟩
  · exact ⟨hI.outer, hI.olen, hI.ook, hI.otypes, hI.ilen, hI.inst,
      instSteps_snoc hi.1 (instStep_def hd), by simp [hlen], hi.2.2.ext (Ext.append _ _)⟩
  · exact ⟨Ext.refl _, Ext.append _ _, rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩

theorem defType_sim_outer {e e' : Enc} {cst : CSt} (hs : e.inner = none) (hI : Inv e cst none)
    {t : DefType} {k : Nat} {sl : Slot} (hd : DefSlot cst.slots t sl)
    (h : (defType t).run e = .ok (k, e')) : Pushed e e' cst none sl k := by
  rw [defType_outer hs] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
  have hc : compSteps {} (e.outer.decls ++ [.inst (.type t)]) = .ok { cst with slots := cst.slots ++ [sl] } :=
    compSteps_snoc hI.outer (compStep_def hd)
  refine ⟨hI.olen.symm, by simp [Enc.curMaps, hs], rfl, { cst with slots := cst.slots ++ [sl] }, none, ?_, ?_, rfl⟩
  · exact ⟨hc, by simp [hI.olen], hI.ook.ext (Ext.append _ _), hI.otypes.ext (Ext.append _ _), hI.ilen,
      hI.inst, by simp [hs, InnerOK]⟩
  · exact ⟨Ext.append _ _, Ext.append _ _, rfl, rfl, rfl, trivial, rfl, rfl, rfl⟩

/-- **Defining a type** appends the decoder's slot for it. -/
theorem defType_sim {e e' : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst)
    {t : DefType} {k : Nat} {sl : Slot} (hd : DefSlot (curSlots cst dst) t sl)
    (h : (defType t).run e = .ok (k, e')) : Pushed e e' cst dst sl k := by
  have hi := hI.inner
  cases hs : e.inner with
  | none =>
    rw [hs] at hi
    cases dst with
    | none => exact defType_sim_outer hs hI hd h
    | some d => exact absurd hi id
  | some s =>
    rw [hs] at hi
    cases dst with
    | none => exact absurd hi id
    | some d => exact defType_sim_inner hs hI hd h

end Silmaril.Wasm.Wit.Binary
