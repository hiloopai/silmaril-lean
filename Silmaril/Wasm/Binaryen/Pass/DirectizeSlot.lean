module

public import Silmaril.Wasm.Binaryen.ElemInit
public import Silmaril.Wasm.Binaryen.Pass.Directize

@[expose] public section

/-! # Directize: the slot it reads is the slot instantiation writes

`Directize.slot?` (`Pass/Directize.lean`) folds `Directize.step` over the element segments
of the syntax; `ElemInit.initElemList?_slot` gives the contents of a slot after the
element segments have run as the fold of `ElemInit.segSlot` over the same segments.
`slot_of_slot?` relates the two: when Directize finds function `fn` in slot `k` of
table `t`, the slot of the table's address holds `ref.func` of the address of `fn`,
given that the table index `t` is the only one that resolves to that address and that
every `ref.func g` entry of a segment's element instance is `ref.func (A g)`.
-/

namespace Silmaril.Wasm.Binaryen

namespace Directize

open Execution.Core ElemInit

theorem foldl_step_none (t k : Nat) :
    ∀ L : List Elem, L.foldl (step t k) none = none
  | [] => rfl
  | el :: L => by simpa [step] using foldl_step_none t k L

/-- One segment keeps the correspondence. -/
theorem step_segSlot {mi : ModuleInst} {R : Nat → List Ref} {ta t k : Nat} {A : Nat → Nat}
    (hT : ∀ y : TableIdx, mi.tables[y.toNat]? = some ta ↔ y.toNat = t) {p : Nat × Elem}
    (hR : ∀ (j : Nat) (g : FuncIdx), p.2.init[j]? = some [Instr.refFunc g] →
      (R p.1)[j]? = some (Ref.func (A g.toNat)))
    {accD : Option (Option Nat)} {accC : Option Ref}
    (h : ∀ fn, accD = some (some fn) → accC = some (Ref.func (A fn))) :
    ∀ fn, step t k accD p.2 = some (some fn) → segSlot mi R ta k accC p = some (Ref.func (A fn)) := by
  intro fn hs
  rcases accD with _ | v
  · simp [step] at hs
  have hR' : ∀ (j : Nat), (p.2.init[j]?.bind entryFunc) = some fn →
      (R p.1)[j]? = some (Ref.func (A fn)) := by
    intro j hj
    cases he : p.2.init[j]? with
    | none => simp [he] at hj
    | some e =>
      simp only [he, Option.bind_some] at hj
      unfold entryFunc at hj
      split at hj
      · rename_i g
        simp only [Option.some.injEq] at hj
        subst hj
        exact hR _ g he
      · cases hj
  unfold segSlot
  cases hmode : p.2.mode with
  | passive =>
    simp only [step, hmode] at hs
    exact h fn hs
  | declarative =>
    simp only [step, hmode] at hs
    exact h fn hs
  | active tbl off =>
    simp only [step, hmode] at hs
    by_cases hne : tbl.toNat = t
    · have ht : mi.tables[tbl.toNat]? = some ta := (hT tbl).mpr hne
      simp only [hne, bne_self_eq_false, Bool.false_eq_true, ite_false] at hs
      split at hs
      · rename_i o
        simp only [ht, true_and]
        split at hs
        · rename_i hcov
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcov
          simp only [hcov, and_self, ite_true]
          simp only [Option.some.injEq] at hs
          exact hR' _ hs
        · rename_i hcov
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcov
          simp only [hcov, ite_false]
          exact h fn hs
      · cases hs
    · have ht : ¬ mi.tables[tbl.toNat]? = some ta := fun e => hne ((hT tbl).mp e)
      have hb : (tbl.toNat != t) = true := by simpa using hne
      simp only [hb, ite_true] at hs
      split
      · rename_i y o hm'
        cases hm'
        simp only [ht, false_and, ite_false]
        exact h fn hs
      · exact h fn hs

/-- **The fold of Directize is a fold of the slot contents.** -/
theorem foldl_step_segSlot {mi : ModuleInst} {R : Nat → List Ref} {ta t k : Nat} {A : Nat → Nat}
    (hT : ∀ y : TableIdx, mi.tables[y.toNat]? = some ta ↔ y.toNat = t) :
    ∀ (L : List (Nat × Elem)) (accD : Option (Option Nat)) (accC : Option Ref),
      (∀ p ∈ L, ∀ (j : Nat) (g : FuncIdx), p.2.init[j]? = some [Instr.refFunc g] →
        (R p.1)[j]? = some (Ref.func (A g.toNat))) →
      (∀ fn, accD = some (some fn) → accC = some (Ref.func (A fn))) →
      ∀ fn, (L.map Prod.snd).foldl (step t k) accD = some (some fn) →
        L.foldl (segSlot mi R ta k) accC = some (Ref.func (A fn))
  | [], _, _, _, h, fn, hf => h fn hf
  | p :: L, accD, accC, hR, h, fn, hf => by
    simp only [List.map_cons, List.foldl_cons] at hf ⊢
    exact foldl_step_segSlot hT L _ _ (fun q hq => hR q (List.mem_cons_of_mem _ hq))
      (step_segSlot hT (hR p (by simp)) h) fn hf

/-- **The slot Directize reads holds the function it finds**, after the element segments
`(List.range n).zip m.base.elems` (with `m.base.elems.length ≤ n`) have run. -/
theorem slot_of_slot? {m : BModule} {t k fn : Nat} (h : slot? m t k = some fn)
    {mi : ModuleInst} {R : Nat → List Ref} {ta n : Nat} {A : Nat → Nat}
    (hT : ∀ y : TableIdx, mi.tables[y.toNat]? = some ta ↔ y.toNat = t)
    (hn : m.base.elems.length ≤ n)
    (hR : ∀ p ∈ (List.range n).zip m.base.elems, ∀ (j : Nat) (g : FuncIdx),
      p.2.init[j]? = some [Instr.refFunc g] → (R p.1)[j]? = some (Ref.func (A g.toNat)))
    (acc : Option Ref) :
    ((List.range n).zip m.base.elems).foldl (segSlot mi R ta k) acc = some (Ref.func (A fn)) := by
  unfold slot? at h
  split at h
  · split at h
    · rename_i f' hf
      simp only [Option.some.injEq] at h
      subst h
      refine foldl_step_segSlot hT _ (some none) acc hR (by simp) f' ?_
      rw [List.map_snd_zip (by simpa using hn)]
      exact hf
    · cases h
  · cases h

end Directize

end Silmaril.Wasm.Binaryen
