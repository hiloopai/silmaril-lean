module

public import Silmaril.Proofs.Wasm.Wit.Binary.Sim.Inst
public import Silmaril.Proofs.Wasm.Wit.Binary.Names

/-!
# The WIT binary round trip: world types, functions and instance items

`typeDef_sim_world` (a world's type import), `funcType_sim` (a function type
decodes to the function's signature), `exportFuncs_sim` (exported functions
are read back without docs) and `instItem_sim` (an interface imported or
exported as an instance type is read back in normal form).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary Enc

/-! ## World types -/

/-- Claiming keeps a table whose entries name types. -/
theorem TableOK.claim_named {α : Type} [DecidableEq α] {tbl : List (α × Nat)} {cur sl : List Slot}
    {f : α → TyRef} (h : TableOK tbl cur (fun x => .named (f x))) {c : Nat} {k : TyDefKind}
    (hc : claim cur c = .ok (k, sl)) : TableOK tbl sl (fun x => .named (f x)) := by
  unfold claim at hc
  cases hs : slotAt cur c with
  | error err => rw [hs] at hc; cases hc
  | ok s =>
    rw [hs] at hc
    have hget : cur[c]? = some s := slotAt_ok.mp hs
    have notc : ∀ (s' : Slot), (∀ r, s ≠ .named r) → ∀ x, lookup x tbl ≠ some c := by
      intro _ hn x hx; exact hn _ (Option.some.inj (hget.symm.trans (h x c hx)))
    cases s with
    | «def» kind => cases hc; exact h.set (notc (.used) (fun r e => by cases e)) .used
    | ty t => cases hc; exact h.set (notc (.used) (fun r e => by cases e)) .used
    | named r => cases hc; exact h
    | func _ => cases hc
    | inst _ => cases hc
    | used => cases hc

/-- The outputs of a world type import. -/
def WorldTypeOK (e e' : Enc) (cst cst' : CSt) (td : TypeDef) : Prop :=
  cst'.insts = cst.insts ∧ cst'.imports = cst.imports ++ [.type td.strip] ∧ cst'.exports = cst.exports ∧
    e'.importTypes = e.importTypes ∧ e'.insts = e.insts ∧ e'.instOf = e.instOf

/-- A resource imported by a world. -/
theorem resource_sim_world {e e' : Enc} {cst : CSt} (hI : Inv e cst none) (ht : e.importTypes = true)
    {td : TypeDef} (hk : td.kind = .resource) (h : (typeDef td).run e = .ok ((), e')) :
    ∃ cst', Inv e' cst' none ∧ WorldTypeOK e e' cst cst' td := by
  rw [typeDef_resource hk] at h
  have hstep : compStep cst (.import ↑td.name (.type .subResource)) =
      .ok (cst.named cst.slots td.name .resource) := rfl
  obtain ⟨hI', h1, h2, h3⟩ := nameType_world hI ht rfl hI.curOK hI.otypes hstep h
  exact ⟨_, hI', rfl, by simp [CSt.named, TypeDef.strip_eq, hk, TyDefKind.strip], rfl, h1, h2, h3⟩

/-- **A named type in a world** is imported and read back without docs. -/
theorem typeDef_sim_world {e e' : Enc} {cst : CSt} (hI : Inv e cst none) (ht : e.importTypes = true)
    (td : TypeDef) (h : (typeDef td).run e = .ok ((), e')) :
    ∃ cst', Inv e' cst' none ∧ WorldTypeOK e e' cst cst' td := by
  by_cases hk : td.kind = .resource
  · exact resource_sim_world hI ht hk h
  · rw [typeDef_other hk] at h
    obtain ⟨idx, e₁, h₁, h₂⟩ := run_bind_ok h
    obtain ⟨cst₁, dst₁, hI₁, hG₁, sl, hcl, hsl, hok⟩ := typeDefIdx_sim hI td.kind h₁
    have hd₁ : dst₁ = none := hG₁.dst_none
    rw [hd₁] at hI₁ hcl hsl
    have hcl' : claim cst₁.slots idx = .ok (td.kind.strip, sl) := hcl
    have hstep : compStep cst₁ (.import ↑td.name (.type (.eq idx))) =
        .ok (cst₁.named sl td.name td.kind.strip) := by simp only [compStep, hcl']; rfl
    obtain ⟨hI', h1, h2, h3⟩ := nameType_world hI₁ (hG₁.importTypes.trans ht) hsl hok
      (hI₁.otypes.claim_named hcl') hstep h₂
    exact ⟨_, hI', hG₁.insts, by simp [CSt.named, TypeDef.strip_eq, hG₁.imports], hG₁.exports,
      h1.trans hG₁.importTypes, h2.trans hG₁.instsN, h3.trans hG₁.instOf⟩

end Silmaril.Wasm.Wit.Binary
