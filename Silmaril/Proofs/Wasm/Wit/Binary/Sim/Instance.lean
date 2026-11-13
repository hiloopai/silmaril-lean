module

public import Silmaril.Proofs.Wasm.Wit.Binary.Sim.Func

/-!
# The WIT binary round trip: instance types as items

An interface body written as an instance type and then imported or exported
by a component type is read back: in normal form (`encodeInstance`), or as
its types only (`encodeTypesOnly`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary Enc

/-- The declaration importing (`imp`) or exporting the instance of type `k`. -/
def instDecl (imp : Bool) (n : String) (k : Nat) : ComponentDecl :=
  if imp then .import ↑n (.instance k) else .inst (.export ↑n (.instance k))

/-- The decoder's state after an instance item. -/
def CSt.addInst (c : CSt) (b : Interface) (key : IfaceName ⊕ String) (imp : Bool) : CSt :=
  { c with slots := c.slots ++ [.inst b], insts := c.insts ++ [key.getLeft?],
           imports := if imp then c.imports ++ [.iface key b] else c.imports,
           exports := if imp then c.exports else c.exports ++ [.iface key b] }

theorem SlotsOK.empty (sl : List Slot) : SlotsOK {} sl :=
  ⟨fun _ _ h => (by simp [lookup] at h), fun _ _ h => (by simp [lookup] at h),
    fun _ _ h => (by simp [lookup] at h)⟩

theorem push_sim {e e' : Enc} {cst : CSt} (hI : Inv e cst none) (h : (push).run e = .ok ((), e')) :
    Inv e' cst (some {}) ∧ Frame e e' cst cst := by
  cases h
  exact ⟨⟨hI.outer, hI.olen, hI.ook, hI.otypes, hI.ilen, hI.inst, ⟨rfl, rfl, SlotsOK.empty _⟩⟩,
    ⟨Ext.refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem pop_run {e : Enc} {s : Space InstanceDecl} (hs : e.inner = some s) (i : Option IfaceName) :
    (pop i).run e = .ok (e.outer.count, { e with inner := none, outer := { e.outer with decls := e.outer.decls ++ [.inst (.type (.instance s.decls))], count := e.outer.count + 1 }, insts := e.insts + 1, instOf := match i with | some i => (i, e.insts) :: e.instOf | none => e.instOf }) := by
  unfold pop; simp [hs]; rfl

theorem decInstance_of {o : List Slot} {ds : List InstanceDecl} {d : DSt} (h : instSteps o {} ds = .ok d) :
    decInstance o ds = .ok { types := d.types, funcs := d.funcs } := by
  simp only [decInstance, h]; rfl

/-- The decoder reads an instance item. -/
theorem compStep_inst {c : CSt} {b : Interface} {key : IfaceName ⊕ String} {n : String}
    (hkey : nameKey n = .ok key) (imp : Bool) :
    compStep { c with slots := c.slots ++ [.inst b] } (instDecl imp n c.slots.length) =
      .ok (c.addInst b key imp) := by
  have hget : slotAt (c.slots ++ [.inst b]) c.slots.length = .ok (.inst b) := slotAt_of_get (by simp)
  cases imp <;> simp only [instDecl, ↓reduceIte, Bool.false_eq_true, compStep, instanceItem, hget, hkey,
    bind, Except.bind, pure, Except.pure] <;> rfl

theorem inst_lookup {e : Enc} {cst : CSt} {dst : Option DSt} (hI : Inv e cst dst) (key : IfaceName ⊕ String) (i : IfaceName)
    (k : Nat) (hk : lookup i (match key.getLeft? with | some j => (j, e.insts) :: e.instOf | none => e.instOf) = some k) :
    (cst.insts ++ [key.getLeft?])[k]? = some (some i) := by
  have old : ∀ k, lookup i e.instOf = some k → (cst.insts ++ [key.getLeft?])[k]? = some (some i) := by
    intro k hk
    have h1 := hI.inst i k hk
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h1).1]; exact h1
  cases key with
  | inr n => exact old k hk
  | inl j =>
    by_cases hji : j = i
    · have hkk : e.insts = k := by simpa [lookup, hji] using hk
      rw [← hkk, ← hI.ilen, ← hji]; simp
    · exact old k (by simpa [lookup, hji] using hk)

/-- **Closing an instance type and importing or exporting it**: the decoder
reads the body it decoded so far as an instance item. -/
theorem popEmit_sim {e e₁ e₂ : Enc} {cst : CSt} {d : DSt} (hI : Inv e cst (some d))
    {key : IfaceName ⊕ String} {n : String} (hkey : nameKey n = .ok key) (imp : Bool) {k : Nat}
    (h₁ : (pop key.getLeft?).run e = .ok (k, e₁)) (h₂ : (emit (instDecl imp n k)).run e₁ = .ok ((), e₂)) :
    Inv e₂ (cst.addInst { types := d.types, funcs := d.funcs } key imp) none ∧
      e₂.importTypes = e.importTypes := by
  obtain ⟨s, hs, hd, -⟩ := hI.inner_some
  rw [pop_run hs] at h₁; cases h₁
  cases h₂
  have hc₁ : compStep cst (.inst (.type (.instance s.decls))) =
      .ok { cst with slots := cst.slots ++ [.inst { types := d.types, funcs := d.funcs }] } := by
    simp only [compStep, decInstance_of hd]; rfl
  have hc₂ := compStep_inst (c := cst) (b := { types := d.types, funcs := d.funcs }) hkey imp
  rw [hI.olen] at hc₂
  have hx : Ext cst.slots (cst.slots ++ [.inst { types := d.types, funcs := d.funcs }]) := Ext.append _ _
  refine ⟨⟨compSteps_snoc (compSteps_snoc hI.outer hc₁) hc₂, by simp [CSt.addInst, hI.olen],
    hI.ook.ext hx, hI.otypes.ext hx, by simp [CSt.addInst, hI.ilen], inst_lookup hI key,
    by simp [InnerOK]⟩, rfl⟩

theorem mem_sortFuncs {types : List TypeDef} {fs : List Func} {f : Func} (h : f ∈ sortFuncs types fs) :
    f ∈ fs := by
  unfold sortFuncs at h
  obtain ⟨_, -, hf⟩ := List.mem_flatMap.mp h
  exact (List.mem_filter.mp hf).1

/-- The component type's outputs are those of `cst` (after aliases). -/
structure SameOut (cst cst' : CSt) : Prop where
  insts : cst'.insts = cst.insts
  imports : cst'.imports = cst.imports
  exports : cst'.exports = cst.exports

/-- **An interface body as an instance item**, read back in normal form. -/
theorem encodeInstance_item {e e' : Enc} {cst : CSt} (hI : Inv e cst none) {body : Interface}
    (hv : ∀ f ∈ body.funcs, f.Valid) {key : IfaceName ⊕ String} {n : String} (hkey : nameKey n = .ok key)
    (imp : Bool) (h : (do let k ← encodeInstance key.getLeft? body; emit (instDecl imp n k)).run e = .ok ((), e')) :
    ∃ cst₁, SameOut cst cst₁ ∧ Inv e' (cst₁.addInst body.normalize key imp) none ∧
      e'.importTypes = e.importTypes := by
  obtain ⟨k, e₁, h₁, h₂⟩ := run_bind_ok h
  obtain ⟨u₁, e₂, hp, h₃⟩ := run_bind_ok h₁
  obtain ⟨hI₂, hF₂⟩ := push_sim hI hp
  obtain ⟨u₂, e₃, ht, h₄⟩ := run_bind_ok h₃
  obtain ⟨c₃, d₃, hI₃, hF₃, ht₃, hf₃⟩ := typeDefs_sim_inner body.types hI₂ ht
  obtain ⟨u₃, e₄, hx, h₅⟩ := run_bind_ok h₄
  obtain ⟨c₄, d₄, hI₄, hF₄, ht₄, hf₄⟩ :=
    exportFuncs_sim _ (fun f hf => hv f (mem_sortFuncs hf)) hI₃ hx
  obtain ⟨hI', hT⟩ := popEmit_sim hI₄ hkey imp h₅ h₂
  have hF := hF₂.trans (hF₃.trans hF₄)
  have hb : ({ types := d₄.types, funcs := d₄.funcs } : Interface) = body.normalize := by
    simp [Interface.normalize, ht₄, ht₃, hf₄, hf₃]
  rw [hb] at hI'
  exact ⟨c₄, ⟨hF.insts, hF.imports, hF.exports⟩, hI', hT.trans hF.importTypes⟩

/-- The types of an interface body, as an instance type. -/
def Interface.typesOnly (b : Interface) : Interface := { types := b.types.map TypeDef.strip }

/-- **The types of an interface as an instance item.** -/
theorem encodeTypesOnly_item {e e' : Enc} {cst : CSt} (hI : Inv e cst none) {body : Interface}
    {i : IfaceName} (hkey : nameKey i.id = .ok (.inl i)) (imp : Bool)
    (h : (do let k ← encodeTypesOnly i body; emit (instDecl imp i.id k)).run e = .ok ((), e')) :
    ∃ cst₁, SameOut cst cst₁ ∧ Inv e' (cst₁.addInst body.typesOnly (.inl i) imp) none ∧
      e'.importTypes = e.importTypes := by
  obtain ⟨k, e₁, h₁, h₂⟩ := run_bind_ok h
  obtain ⟨u₁, e₂, hp, h₃⟩ := run_bind_ok h₁
  obtain ⟨hI₂, hF₂⟩ := push_sim hI hp
  obtain ⟨u₂, e₃, ht, h₄⟩ := run_bind_ok h₃
  obtain ⟨c₃, d₃, hI₃, hF₃, ht₃, hf₃⟩ := typeDefs_sim_inner body.types hI₂ ht
  obtain ⟨hI', hT⟩ := popEmit_sim (key := .inl i) hI₃ hkey imp h₄ h₂
  have hF := hF₂.trans hF₃
  have hb : ({ types := d₃.types, funcs := d₃.funcs } : Interface) = body.typesOnly := by
    simp [Interface.typesOnly, ht₃, hf₃]
  rw [hb] at hI'
  exact ⟨c₃, ⟨hF.insts, hF.imports, hF.exports⟩, hI', hT.trans hF.importTypes⟩

end Silmaril.Wasm.Wit.Binary
