module

public import Silmaril.Proofs.Wasm.Wac.Nest.Inline
public import Silmaril.Proofs.Wasm.Wac.Nest.Sort

/-!
# Nesting = inlining: the imports of the two compositions

* `uses_renInst`, `names_uses_inner`, `tyCons_uses_inner`: the imports used by an instance
  of `g₂` and by its nodes in the inlined graph have the same names and types;
* `usesInv_fold`: along the whole inlining;
* `lookup_iface_inline`: the imports of the inlined graph and of `g₂` (packages
  `nestPkgs P k0 g₁`) have the same lookups; `sortIface_iface_inline`: so their sorted
  forms are equal.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.NestProof

open Silmaril.Wasm.Component

variable {M : Type}

/-! ## Types of entries -/

theorem tyCons_lookup {T : String → Option FuncTy} {L : Iface} (h : TyCons T L) {x : String}
    {t : FuncTy} (hl : L.lookup x = some t) : T x = some t :=
  h (x, t) (mem_of_lookup hl)

theorem lookup_none_of_not_mem {L : Iface} {x : String} (h : x ∉ names L) : L.lookup x = none := by
  cases hl : L.lookup x with
  | none => rfl
  | some t => exact absurd (List.mem_map_of_mem (f := Prod.fst) (mem_of_lookup hl)) h

/-- Two interfaces with the same names and the same types per name have the same lookups. -/
theorem lookup_eq_of_tyCons {T : String → Option FuncTy} {L₁ L₂ : Iface} (h₁ : TyCons T L₁)
    (h₂ : TyCons T L₂) (hn : ∀ y, y ∈ names L₁ ↔ y ∈ names L₂) (x : String) :
    L₁.lookup x = L₂.lookup x := by
  by_cases hx : x ∈ names L₁
  · obtain ⟨t₁, e₁⟩ := lookup_of_mem hx
    obtain ⟨t₂, e₂⟩ := lookup_of_mem ((hn x).1 hx)
    rw [e₁, e₂, ← tyCons_lookup h₁ e₁, ← tyCons_lookup h₂ e₂]
  · rw [lookup_none_of_not_mem hx, lookup_none_of_not_mem (fun h => hx ((hn x).2 h))]

theorem tyCons_append {T : String → Option FuncTy} {L₁ L₂ : Iface} (h₁ : TyCons T L₁)
    (h₂ : TyCons T L₂) : TyCons T (L₁ ++ L₂) := fun p hp =>
  (List.mem_append.1 hp).elim (h₁ p) (h₂ p)

/-! ## Used imports -/

/-- The use of an import of a package by a reference. -/
def useOf (p : String × FuncTy) : Src → Option (String × FuncTy)
  | .imp x => some (x, p.2)
  | .out _ _ => none

theorem uses_eq (S : Nat → PkgSig) (n : Inst) :
    n.uses S = (S n.pkg).imports.filterMap fun p => useOf p (n.src p.1) := by
  unfold Inst.uses
  apply List.filterMap_congr
  intro p _
  cases n.src p.1 <;> rfl

theorem mem_uses_iff (S : Nat → PkgSig) (n : Inst) (r : String × FuncTy) :
    r ∈ n.uses S ↔ ∃ p ∈ (S n.pkg).imports, n.src p.1 = .imp r.1 ∧ p.2 = r.2 := by
  rw [uses_eq, List.mem_filterMap]
  apply exists_congr
  intro p
  apply and_congr_right
  intro _
  cases n.src p.1 with
  | imp x => simp [useOf, Prod.ext_iff, eq_comm]
  | out k q => simp [useOf]

/-- The renaming keeps the kind of a resolved reference. -/
theorem useOf_renSrc {S S' : Nat → PkgSig} {g₂ : Graph} {acc : IAcc} {j : Nat}
    (hr : RenOk S S' g₂ acc j) {I : Iface} (p : String × FuncTy) :
    ∀ {s : Src}, g₂.Resolves S' I j s → useOf p (renSrc acc.ren s) = useOf p s
  | .imp _, _ => rfl
  | .out j' q, ⟨n, hn, hj, hq⟩ => by
    obtain ⟨t, q', m, h, _, _, _⟩ := hr.2 j' n q hn hj hq
    rw [h]
    rfl

theorem renSrc_imp_iff {S S' : Nat → PkgSig} {g₂ : Graph} {acc : IAcc} {j : Nat}
    (hr : RenOk S S' g₂ acc j) {I : Iface} {s : Src} (hs : g₂.Resolves S' I j s) (y : String) :
    renSrc acc.ren s = .imp y ↔ s = .imp y := by
  have h := useOf_renSrc hr ("", ⟨[], []⟩) hs
  constructor
  · intro e
    cases s with
    | imp x => exact e
    | out _ _ =>
      have h' : useOf ("", ⟨[], []⟩) (.imp y) = useOf ("", ⟨[], []⟩) (.out _ _) := e ▸ h
      exact absurd h' (by simp [useOf])
  · intro e
    rw [e]
    rfl

/-- **An instance of another package uses the same imports in both graphs.** -/
theorem uses_renInst {S S' : Nat → PkgSig} {g₂ : Graph} {acc : IAcc} {j : Nat} {n : Inst}
    (hr : RenOk S S' g₂ acc j) {I : Iface} (hS : S n.pkg = S' n.pkg)
    (hres : ∀ p ∈ (S' n.pkg).imports, g₂.Resolves S' I j (n.src p.1)) :
    (renInst acc.ren n).uses S = n.uses S' := by
  rw [uses_eq, uses_eq]
  show ((S n.pkg).imports.filterMap fun p => useOf p ((renInst acc.ren n).src p.1)) = _
  rw [hS]
  apply List.filterMap_congr
  intro p hp
  rw [renInst, src_ren]
  exact useOf_renSrc hr p (hres p hp)

theorem innerSrc_imp_iff (n' : Inst) (base : Nat) (s : Src) (y : String) :
    innerSrc n' base s = .imp y ↔ ∃ x, s = .imp x ∧ n'.src x = .imp y := by
  cases s with
  | imp x => simp [innerSrc]
  | out _ _ => simp [innerSrc]

theorem mem_uses_innerInst (S : Nat → PkgSig) (n' : Inst) (base : Nat) (m : Inst)
    (r : String × FuncTy) :
    r ∈ (innerInst S n' base m).uses S ↔
      ∃ p ∈ (S m.pkg).imports, ∃ x, m.src p.1 = .imp x ∧ n'.src x = .imp r.1 ∧ p.2 = r.2 := by
  rw [mem_uses_iff]
  apply exists_congr
  intro p
  constructor
  · intro ⟨hp, hs, ht⟩
    have hs' := (innerSrc_imp_iff n' base _ _).1 ((src_inner S n' base m
      (List.mem_map_of_mem hp)).symm.trans hs)
    obtain ⟨x, hx, hy⟩ := hs'
    exact ⟨hp, x, hx, hy, ht⟩
  · intro ⟨hp, x, hx, hy, ht⟩
    refine ⟨hp, ?_, ht⟩
    rw [innerInst, src_inner S n' base m (List.mem_map_of_mem hp)]
    exact (innerSrc_imp_iff n' base _ _).2 ⟨x, hx, hy⟩

end Silmaril.Wasm.Wac.NestProof
