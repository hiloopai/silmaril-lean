module

public import Silmaril.Wasm.Wit.Binary.Normal.Defs

/-!
# The WIT binary round trip: the simulation invariant

The decoder, run on the declarations the encoder has written so far, agrees
with the encoder's tables (`Inv`): every type index an encoder table maps a
key to is a slot of the decoder denoting that key (`SlotsOK`). This file has
the invariant, the decoders' stability under longer slot lists (`Ext`), and
the encoder's basic steps.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary Enc

/-! ## Running the encoder -/

theorem run_bind_ok {α β : Type} {x : EncM α} {f : α → EncM β} {e : Enc} {b : β} {e₂ : Enc}
    (h : (x >>= f).run e = .ok (b, e₂)) :
    ∃ a e₁, x.run e = .ok (a, e₁) ∧ (f a).run e₁ = .ok (b, e₂) := by
  simp only [StateT.run_bind] at h
  cases hx : x.run e with
  | error err => rw [hx] at h; cases h
  | ok p => obtain ⟨a, e₁⟩ := p; rw [hx] at h; exact ⟨a, e₁, rfl, h⟩

theorem run_pure_ok {α : Type} {a b : α} {e e' : Enc} (h : (pure a : EncM α).run e = .ok (b, e')) :
    b = a ∧ e' = e := by
  cases h; exact ⟨rfl, rfl⟩

theorem run_map_ok {α β : Type} {x : EncM α} {f : α → β} {e : Enc} {b : β} {e' : Enc}
    (h : (f <$> x).run e = .ok (b, e')) : ∃ a, x.run e = .ok (a, e') ∧ b = f a := by
  simp only [StateT.run_map] at h
  cases hx : x.run e with
  | error err => rw [hx] at h; cases h
  | ok p => obtain ⟨a, e₁⟩ := p; rw [hx] at h; cases h; exact ⟨a, rfl, rfl⟩

theorem run_fail {α : Type} {m : String} {e : Enc} {r : α × Enc} :
    (Enc.fail m : EncM α).run e ≠ .ok r := by
  intro h; cases h

/-! ## Slot lists -/

/-- `b` extends `a`. -/
def Ext (a b : List Slot) : Prop := ∃ xs, b = a ++ xs

theorem Ext.refl (a : List Slot) : Ext a a := ⟨[], by simp⟩

theorem Ext.trans {a b c : List Slot} (h₁ : Ext a b) (h₂ : Ext b c) : Ext a c := by
  obtain ⟨xs, rfl⟩ := h₁; obtain ⟨ys, rfl⟩ := h₂; exact ⟨xs ++ ys, by simp⟩

theorem Ext.append (a xs : List Slot) : Ext a (a ++ xs) := ⟨xs, rfl⟩

theorem Ext.get {a b : List Slot} (h : Ext a b) {k : Nat} {s : Slot} (hk : a[k]? = some s) :
    b[k]? = some s := by
  obtain ⟨xs, rfl⟩ := h
  have hl : k < a.length := (List.getElem?_eq_some_iff.mp hk).1
  rw [List.getElem?_append_left hl]; exact hk

theorem slotAt_ok {a : List Slot} {k : Nat} {s : Slot} : slotAt a k = .ok s ↔ a[k]? = some s := by
  unfold slotAt
  cases hk : a[k]? with
  | none => simp [throw, throwThe, MonadExceptOf.throw]
  | some t => exact ⟨fun h => by cases h; rfl, fun h => by cases h; rfl⟩

theorem slotAt_of_get {a : List Slot} {k : Nat} {s : Slot} (h : a[k]? = some s) : slotAt a k = .ok s :=
  slotAt_ok.mpr h

/-- A decoder that succeeds on `a` succeeds the same way on an extension:
it only reads the slots it succeeded on. -/
theorem slotAt_ext {a b : List Slot} (hx : Ext a b) {k : Nat} {r : Slot} (h : slotAt a k = .ok r) :
    slotAt b k = .ok r :=
  slotAt_of_get (hx.get (slotAt_ok.mp h))

theorem decRef_ext {a b : List Slot} (hx : Ext a b) {k : Nat} {r : TyRef} (h : decRef a k = .ok r) :
    decRef b k = .ok r := by
  unfold decRef at h ⊢
  cases hk : slotAt a k with
  | error e => rw [hk] at h; cases h
  | ok s => rw [slotAt_ext hx hk]; rw [hk] at h; exact h

theorem decValType_ext {a b : List Slot} (hx : Ext a b) {v : ValType} {t : Ty}
    (h : decValType a v = .ok t) : decValType b v = .ok t := by
  cases v with
  | prim p => exact h
  | idx k =>
    simp only [decValType] at h ⊢
    cases hk : slotAt a k with
    | error e => rw [hk] at h; cases h
    | ok s => rw [slotAt_ext hx hk]; rw [hk] at h; exact h

theorem decOpt_ext {a b : List Slot} (hx : Ext a b) {v : Option ValType} {t : Option Ty}
    (h : decOpt a v = .ok t) : decOpt b v = .ok t := by
  cases v with
  | none => exact h
  | some v =>
    simp only [decOpt] at h ⊢
    cases hv : decValType a v with
    | error e => rw [hv] at h; cases h
    | ok s => rw [decValType_ext hx hv]; rw [hv] at h; exact h

/-! ## Tables -/

/-- A table maps a key only to an existing slot denoting it. -/
def TableOK {α : Type} [DecidableEq α] (tbl : List (α × Nat)) (slots : List Slot)
    (den : α → Slot) : Prop :=
  ∀ x k, lookup x tbl = some k → slots[k]? = some (den x)

/-- The tables of an index space agree with the decoder's slots. -/
structure SlotsOK (m : Maps) (slots : List Slot) : Prop where
  named : TableOK m.named slots .named
  anon : TableOK m.anon slots .ty
  funcs : TableOK m.funcs slots .func

theorem TableOK.ext {α : Type} [DecidableEq α] {tbl : List (α × Nat)} {a b : List Slot}
    {den : α → Slot} (h : TableOK tbl a den) (hx : Ext a b) : TableOK tbl b den :=
  fun x k hk => hx.get (h x k hk)

theorem TableOK.cons {α : Type} [DecidableEq α] {tbl : List (α × Nat)} {a : List Slot}
    {den : α → Slot} (h : TableOK tbl a den) {x : α} {k : Nat} (hk : a[k]? = some (den x)) :
    TableOK ((x, k) :: tbl) a den := by
  intro y j hj
  by_cases e : x = y
  · subst e
    have hkj : k = j := by simpa [lookup] using hj
    exact hkj ▸ hk
  · have hy : lookup y tbl = some j := by simpa [lookup, e] using hj
    exact h y j hy

theorem TableOK.lt {α : Type} [DecidableEq α] {tbl : List (α × Nat)} {a : List Slot}
    {den : α → Slot} (h : TableOK tbl a den) {x : α} {k : Nat} (hk : lookup x tbl = some k) :
    k < a.length :=
  (List.getElem?_eq_some_iff.mp (h x k hk)).1

theorem SlotsOK.ext {m : Maps} {a b : List Slot} (h : SlotsOK m a) (hx : Ext a b) : SlotsOK m b :=
  ⟨h.named.ext hx, h.anon.ext hx, h.funcs.ext hx⟩

/-- Setting a slot no table maps to keeps the tables right. -/
theorem TableOK.set {α : Type} [DecidableEq α] {tbl : List (α × Nat)} {a : List Slot}
    {den : α → Slot} (h : TableOK tbl a den) {c : Nat} (hc : ∀ x, lookup x tbl ≠ some c) (s : Slot) :
    TableOK tbl (a.set c s) den := by
  intro x k hk
  have hne : c ≠ k := fun e => hc x (e ▸ hk)
  rw [List.getElem?_set_ne hne]; exact h x k hk

end Silmaril.Wasm.Wit.Binary

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary Enc

/-! ## Decoder runs -/

theorem instSteps_append (o : List Slot) (s : DSt) (a b : List InstanceDecl) :
    instSteps o s (a ++ b) = (instSteps o s a >>= fun s' => instSteps o s' b) := by
  induction a generalizing s with
  | nil => rfl
  | cons x a ih =>
    simp only [List.cons_append, instSteps]
    cases instStep o s x with
    | error e => rfl
    | ok s₁ => exact ih s₁

theorem compSteps_append (s : CSt) (a b : List ComponentDecl) :
    compSteps s (a ++ b) = (compSteps s a >>= fun s' => compSteps s' b) := by
  induction a generalizing s with
  | nil => rfl
  | cons x a ih =>
    simp only [List.cons_append, compSteps]
    cases compStep s x with
    | error e => rfl
    | ok s₁ => exact ih s₁

theorem instSteps_snoc {o : List Slot} {s s' s'' : DSt} {a : List InstanceDecl} {x : InstanceDecl}
    (h : instSteps o s a = .ok s') (hx : instStep o s' x = .ok s'') :
    instSteps o s (a ++ [x]) = .ok s'' := by
  rw [instSteps_append, h]
  show (instStep o s' x >>= fun s => instSteps o s []) = _
  rw [hx]; rfl

theorem compSteps_snoc {s s' s'' : CSt} {a : List ComponentDecl} {x : ComponentDecl}
    (h : compSteps s a = .ok s') (hx : compStep s' x = .ok s'') :
    compSteps s (a ++ [x]) = .ok s'' := by
  rw [compSteps_append, h]
  show (compStep s' x >>= fun s => compSteps s []) = _
  rw [hx]; rfl

/-- Instance types read outer slots only where they succeeded. -/
theorem instStep_outer_ext {o o' : List Slot} (hx : Ext o o') {s r : DSt} {x : InstanceDecl}
    (h : instStep o s x = .ok r) : instStep o' s x = .ok r := by
  unfold instStep at h ⊢
  split at h
  all_goals first
    | exact h
    | (rename_i j
       cases hj : o[j]? with
       | none => rw [hj] at h; cases h
       | some sl => rw [hx.get hj]; rw [hj] at h; exact h)

theorem instSteps_outer_ext {o o' : List Slot} (hx : Ext o o') :
    ∀ {s r : DSt} {ds : List InstanceDecl}, instSteps o s ds = .ok r → instSteps o' s ds = .ok r
  | _, _, [], h => h
  | s, r, x :: ds, h => by
    simp only [instSteps] at h ⊢
    cases hs : instStep o s x with
    | error e => rw [hs] at h; cases h
    | ok s₁ =>
      rw [instStep_outer_ext hx hs]; rw [hs] at h
      exact instSteps_outer_ext hx h

/-! ## The invariant -/

/-- The tables of the current index space. -/
def Enc.curMaps (e : Enc) : Maps := match e.inner with | some s => s.maps | none => e.outer.maps

def curSlots (cst : CSt) : Option DSt → List Slot
  | some d => d.slots
  | none => cst.slots

/-- The instance type being written decodes to `dst`. -/
def InnerOK : Option (Space InstanceDecl) → List Slot → Option DSt → Prop
  | none, _, none => True
  | some s, o, some d => instSteps o {} s.decls = .ok d ∧ d.slots.length = s.count ∧ SlotsOK s.maps d.slots
  | _, _, _ => False

/-- The simulation invariant: the decoder read the component type (`cst`)
and the instance type (`dst`) written so far, in agreement with the
encoder's tables. -/
structure Inv (e : Enc) (cst : CSt) (dst : Option DSt) : Prop where
  outer : compSteps {} e.outer.decls = .ok cst
  olen : cst.slots.length = e.outer.count
  ook : SlotsOK e.outer.maps cst.slots
  otypes : TableOK e.outerTypes cst.slots (fun p => .named ⟨.iface p.1, p.2⟩)
  ilen : cst.insts.length = e.insts
  inst : ∀ i k, lookup i e.instOf = some k → cst.insts[k]? = some (some i)
  inner : InnerOK e.inner cst.slots dst

/-- The outputs of an instance type are the same. -/
def OutSame : Option DSt → Option DSt → Prop
  | none, none => True
  | some d, some d' => d'.types = d.types ∧ d'.funcs = d.funcs
  | _, _ => False

/-- A step that only defines types: slots grow, nothing else changes. -/
structure Grows (e e' : Enc) (cst cst' : CSt) (dst dst' : Option DSt) : Prop where
  oext : Ext cst.slots cst'.slots
  cext : Ext (curSlots cst dst) (curSlots cst' dst')
  insts : cst'.insts = cst.insts
  imports : cst'.imports = cst.imports
  exports : cst'.exports = cst.exports
  out : OutSame dst dst'
  importTypes : e'.importTypes = e.importTypes
  instsN : e'.insts = e.insts
  instOf : e'.instOf = e.instOf

theorem OutSame.refl : ∀ d : Option DSt, OutSame d d
  | none => trivial
  | some _ => ⟨rfl, rfl⟩

theorem OutSame.trans : ∀ {a b c : Option DSt}, OutSame a b → OutSame b c → OutSame a c
  | none, none, none, _, _ => trivial
  | some _, some _, some _, ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨h3.trans h1, h4.trans h2⟩

theorem Grows.refl (e : Enc) (cst : CSt) (dst : Option DSt) : Grows e e cst cst dst dst :=
  ⟨Ext.refl _, Ext.refl _, rfl, rfl, rfl, OutSame.refl _, rfl, rfl, rfl⟩

theorem Grows.trans {e₁ e₂ e₃ : Enc} {c₁ c₂ c₃ : CSt} {d₁ d₂ d₃ : Option DSt}
    (h : Grows e₁ e₂ c₁ c₂ d₁ d₂) (h' : Grows e₂ e₃ c₂ c₃ d₂ d₃) : Grows e₁ e₃ c₁ c₃ d₁ d₃ :=
  ⟨h.oext.trans h'.oext, h.cext.trans h'.cext, h'.insts.trans h.insts, h'.imports.trans h.imports,
    h'.exports.trans h.exports, h.out.trans h'.out, h'.importTypes.trans h.importTypes,
    h'.instsN.trans h.instsN, h'.instOf.trans h.instOf⟩

/-- The result of a step that only defines types. -/
def Sim (e : Enc) (cst : CSt) (dst : Option DSt) (e' : Enc) (P : List Slot → Prop) : Prop :=
  ∃ cst' dst', Inv e' cst' dst' ∧ Grows e e' cst cst' dst dst' ∧ P (curSlots cst' dst')

end Silmaril.Wasm.Wit.Binary
