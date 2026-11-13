module

public import Silmaril.Wasm.LimeCompile.PassiveEquiv.Defs

/-!
# The passive-data store relation: basic facts

* where the source functions and the helpers are in a related target store (`SRel.funcs_lt`,
  `SRel.helper`), and that `extFI` keeps types (`extFI_type`);
* the target instance exports what the source instance exports (`exportFunc?_mi'`);
* related stores accept the same invocations of exported functions (`SRel.invokeOk_iff`), and the
  invocation configurations differ only in the store (`invoke_eq`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.PassiveEquiv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen (exportFunc?)
open Silmaril.Wasm.LimeCompile.PassiveData Silmaril.Wasm.LimeCompile.PassiveEquiv

variable {H : Type}

theorem extFI_type (K : Ctx) (fi : FuncInst H) : (K.extFI fi).type = fi.type := rfl

theorem getElem?_take_drop {α : Type} (l : List α) (k : Nat) (g : α → α) (a : Nat) :
    (l.take k ++ (l.drop k).map g)[a]? = if a < k then l[a]? else (l[a]?).map g := by
  by_cases hl : a < l.length
  · by_cases ha : a < k
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt ha, ite_eq_left ha]
    · have hk : (l.take k).length = k := by simp; omega
      rw [ite_eq_right ha, List.getElem?_append_right (by omega), List.getElem?_map,
        List.getElem?_drop, hk, Nat.add_sub_cancel' (by omega)]
  · have hn : (l.take k ++ (l.drop k).map g).length ≤ a := by simp; omega
    rw [List.getElem?_eq_none hn, List.getElem?_eq_none (by omega)]
    split <;> rfl

theorem length_take_drop {α : Type} (l : List α) (k : Nat) (g : α → α) :
    (l.take k ++ (l.drop k).map g).length = l.length := by
  simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem helperInsts_length (K : Ctx) : (K.helperInsts (H := H)).length = K.m.data.length := by
  simp [Ctx.helperInsts]

theorem helperInsts_getElem? (K : Ctx) (y : Nat) :
    (K.helperInsts (H := H))[y]? = (K.m.data[y]?).map (K.helperInst y) := by
  unfold Ctx.helperInsts
  rw [List.getElem?_map, List.zip_eq_zipWith, List.getElem?_zipWith]
  by_cases hy : y < K.m.data.length
  · simp [List.getElem?_range hy, List.getElem?_eq_getElem hy]
  · rw [List.getElem?_eq_none (by simpa using hy), List.getElem?_eq_none (by omega)]
    rfl

namespace SRel

variable {K : Ctx} {s t : Store H}

theorem funcs_lt (h : SRel K s t) {a : Nat} (ha : a < K.N) :
    t.funcs[a]? = if a < K.N₀ then s.funcs[a]? else (s.funcs[a]?).map K.extFI := by
  have ha' : a < (s.funcs.take K.N₀ ++ (s.funcs.drop K.N₀).map K.extFI).length := by
    rw [length_take_drop, h.nfuncs]
    exact ha
  rw [h.funcs, List.getElem?_append_left ha', getElem?_take_drop]

theorem helper (h : SRel K s t) (y : Nat) :
    t.funcs[K.N + y]? = (K.m.data[y]?).map (K.helperInst y) := by
  have hl : (s.funcs.take K.N₀ ++ (s.funcs.drop K.N₀).map K.extFI).length = K.N := by
    rw [length_take_drop, h.nfuncs]
  rw [h.funcs, List.getElem?_append_right (by omega), hl, Nat.add_sub_cancel_left,
    helperInsts_getElem?]

theorem type_lt (h : SRel K s t) {a : Nat} (ha : a < K.N) :
    (t.funcs[a]?).map FuncInst.type = (s.funcs[a]?).map FuncInst.type := by
  rw [SRel.funcs_lt h ha]
  split
  · rfl
  · rw [Option.map_map]
    rfl

/-- Values of numeric type are typed in every store. -/
theorem valOk_num {s t : Store H} {v : Val} {nt : NumType} (hv : ValOk s v (.num nt)) :
    ValOk t v (.num nt) := by
  cases hv with
  | num v => exact .num v

theorem forall₂_valOk_num {s t : Store H} :
    ∀ {vs : List Val} {ps : List CValType}, (∀ p ∈ ps, ∃ nt, p = .num nt) →
      List.Forall₂ (ValOk s) vs ps → List.Forall₂ (ValOk t) vs ps
  | _, _, _, .nil => .nil
  | _, _, hp, .cons hv hs => by
    obtain ⟨nt, rfl⟩ := hp _ (List.mem_cons_self ..)
    exact .cons (valOk_num hv) (forall₂_valOk_num (fun q hq => hp q (List.mem_cons_of_mem _ hq)) hs)

/-- **Related stores accept the same invocations of exported functions.** -/
theorem invokeOk_iff (h : SRel K s t) {x : String} {a : Nat} (hx : exportFunc? K.mi x = some a)
    (vs : List Val) : InvokeOk s a vs ↔ InvokeOk t a vs := by
  obtain ⟨ha, hnum⟩ := h.exportsNum x a hx
  have hty := SRel.type_lt h ha
  have hlt : a < s.funcs.length := by rw [h.nfuncs]; exact ha
  obtain ⟨fi, hf⟩ : ∃ fi, s.funcs[a]? = some fi := ⟨_, List.getElem?_eq_getElem hlt⟩
  obtain ⟨gi, hg, hgt⟩ : ∃ gi, t.funcs[a]? = some gi ∧ gi.type = fi.type := by
    rw [hf] at hty
    cases hgx : t.funcs[a]? with
    | none => rw [hgx] at hty; cases hty
    | some gi => rw [hgx] at hty; exact ⟨gi, rfl, Option.some.inj hty⟩
  constructor
  · rintro ⟨fi', ps, rs, hf', he, hv⟩
    rw [hf] at hf'
    cases hf'
    exact ⟨gi, ps, rs, hg, by rw [hgt]; exact he, forall₂_valOk_num (hnum fi hf ps rs he) hv⟩
  · rintro ⟨gi', ps, rs, hg', he, hv⟩
    rw [hg] at hg'
    cases hg'
    rw [hgt] at he
    exact ⟨fi, ps, rs, hf, he, forall₂_valOk_num (hnum fi hf ps rs he) hv⟩

/-- The invocation configurations of an exported function differ only in the store. -/
theorem invoke_eq (h : SRel K s t) {x : String} {a : Nat} (hx : exportFunc? K.mi x = some a)
    (vs : List Val) : invoke t a vs = { invoke s a vs with store := t } := by
  have hty := SRel.type_lt h (h.exportsNum x a hx).1
  simp only [invoke, hty]

end SRel

/-- The target instance exports what the source instance exports. -/
theorem exportFunc?_mi' (K : Ctx) (x : String) : exportFunc? K.mi' x = exportFunc? K.mi x := rfl

end Silmaril.Proofs.Wasm.LimeCompile.PassiveEquiv
