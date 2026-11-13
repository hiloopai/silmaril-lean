module

public import Silmaril.Compiler.Target.RenameCorrect.Defs
public import Silmaril.Compiler.Target.QSortPerm.Defs
public import Std.Data.HashMap.Lemmas
public import Std.Data.HashSet.Lemmas
public import Std.Data.TreeMap.Lemmas
public import Init.Data.Range.Lemmas

/-! # `renumberσ` can merge two parameters of a function without its entry block

`infos` places the register parameters of a function at the write position of its entry
header. When the entry label names no block, a parameter that occurs in the blocks keeps
its interval there, and a parameter that occurs nowhere gets a point interval after the
last block. The two intervals are disjoint, so `assign` may give both the same number.
`LiveCert.params` asks for distinct numbers in every function, whatever its entry, so no
liveness sets certify such a numbering, and `Targets.renumber_certified` is false.

`cex` is one function `fun (r0, r1) => ret r0` with entry label `1` and a single block
`0`, for one register home (`k = 1`): liveness converges, `r0` gets the interval `[0, 2]`
and weight `1`, `r1` the interval `[4, 4]` and weight `0`, and `assign` gives both the
number `0`, in either order of the two (`qsort` is only known to permute).
-/

@[expose] public section

namespace Silmaril.Compile.Target.RegAlloc

open Silmaril.Machine Silmaril.Machine.Lir

/-- A function whose entry label names no block, with two register parameters. -/
def cexFunc : Func Nat where
  params := [.reg 0, .reg 1]
  entry := 1
  blocks := [⟨[], .ret [.reg 0]⟩]

def cex : Prog Nat := ⟨[cexFunc]⟩

private theorem ofList_nil : ofList [] = #[] := by
  simp [ofList, Array.qsort_of_size_le_one]

private theorem ofList_single (x : Nat) : ofList [x] = #[x] := by
  simp [ofList, Array.qsort_of_size_le_one]

private theorem cex_genKill : genKill ⟨[], .ret [.reg 0]⟩ = (#[0], #[]) := by
  simp [genKill, termUses, locRegs, ofList_nil, ofList_single, Std.HashSet.toList_empty]

private theorem cex_liveness :
    liveness cexFunc.blocks.toArray (cexFunc.blocks.toArray.size + 2) = some (#[#[0]], #[#[]]) := by
  have : (#[⟨[], .ret [.reg 0]⟩] : Array (Block Nat)).map genKill = #[(#[0], #[])] := by
    simp [cex_genKill]
  show liveness #[⟨[], .ret [.reg 0]⟩] 3 = _
  unfold liveness
  rw [this]
  simp [union, diff, termSuccs, Std.Legacy.Range.size, List.range'_succ]

private abbrev cexInfos : Std.HashMap Nat Info :=
  (((∅ : Std.HashMap Nat Info).insert 0 ⟨0, 0, 0⟩).insert 0 ⟨0, 2, 1⟩).insert 1 ⟨4, 4, 0⟩

private theorem cex_infos : infos cexFunc cexFunc.blocks.toArray #[#[0]] #[#[]] = cexInfos := by
  simp [infos, cexFunc, loopDepth, termSuccs, termUses, locRegs, Info.extend,
    Std.Legacy.Range.size]

private theorem cexInfos_toList :
    cexInfos.toList.Perm [(1, ⟨4, 4, 0⟩), (0, ⟨0, 2, 1⟩)] := by
  have h₁ : ((∅ : Std.HashMap Nat Info).insert 0 ⟨0, 0, 0⟩).toList.Perm [(0, ⟨0, 0, 0⟩)] :=
    Std.HashMap.toList_insert_perm.trans (by simp)
  have h₂ : (((∅ : Std.HashMap Nat Info).insert 0 ⟨0, 0, 0⟩).insert 0 ⟨0, 2, 1⟩).toList.Perm
      [(0, ⟨0, 2, 1⟩)] :=
    Std.HashMap.toList_insert_perm.trans (List.Perm.cons _ ((h₁.filter _).trans (by simp)))
  exact Std.HashMap.toList_insert_perm.trans (List.Perm.cons _ ((h₂.filter _).trans (by simp)))

private theorem perm_pair {α : Type _} {l : List α} {a b : α} (h : l.Perm [a, b]) :
    l = [a, b] ∨ l = [b, a] := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
  · simpa using h.length_eq
  · simpa using h.length_eq
  · have hx : x ∈ [a, b] := h.subset (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · left; have := (List.perm_cons x).mp h; simp_all
    · right; have := (List.perm_cons x).mp (h.trans (List.Perm.swap x a [])); simp_all
  · simpa using h.length_eq

private theorem cex_assign :
    (assign 1 cexInfos).getD 0 0 = 0 ∧ (assign 1 cexInfos).getD 1 1 = 0 := by
  unfold assign
  generalize hq : cexInfos.toArray.qsort (fun (v, a) (w, b) =>
    a.weight > b.weight || (a.weight == b.weight &&
      (a.start < b.start || (a.start == b.start && v < w)))) = order
  have hp : order.toList.Perm [(1, ⟨4, 4, 0⟩), (0, ⟨0, 2, 1⟩)] := by
    rw [← hq]
    refine (Array.perm_iff_toList_perm.mp (Array.qsort_perm _ _ _ _)).trans ?_
    simpa [Std.HashMap.toArray_toList] using cexInfos_toList
  have t₁ : (∅ : Std.TreeMap Nat Nat).getEntryLE? 4 = none := by decide +kernel
  have t₂ : (∅ : Std.TreeMap Nat Nat).getEntryLE? 2 = none := by decide +kernel
  have t₃ : ((∅ : Std.TreeMap Nat Nat).insert 4 4).getEntryLE? 2 = none := by decide +kernel
  have t₄ : ((∅ : Std.TreeMap Nat Nat).insert 0 2).getEntryLE? 4 = some (0, 2) := by
    decide +kernel
  rcases order with ⟨l⟩
  rcases perm_pair hp with rfl | rfl <;>
    simp [meets, Std.HashMap.getD_insert, t₁, t₂, t₃, t₄]

/-- `renumberσ 1 cex` sends both parameters of `cex` to `0`. -/
theorem cex_merges : renumberσ 1 cex 0 0 = 0 ∧ renumberσ 1 cex 0 1 = 0 := by
  have : renumberσ 1 cex 0 = fun v => (assign 1 cexInfos).getD v v := by
    simp only [renumberσ, cex, List.getElem?_cons_zero, Option.map_some, Option.getD_some, funcσ]
    rw [cex_liveness]
    simp only [cex_infos]
  rw [this]
  exact cex_assign

/-- No liveness sets certify `renumberσ 1 cex`. -/
theorem not_liveCert_cex (live : Point → Set Nat) : ¬ LiveCert cex (renumberσ 1 cex) live :=
  fun h => absurd (h.params 0 cexFunc rfl 0 (by simp [cexFunc, locRegs]) 1
    (by simp [cexFunc, locRegs]) (cex_merges.1.trans cex_merges.2.symm)) (by decide)

/-- `∀ k p, ∃ live, LiveCert p (renumberσ k p) live` (`Targets.renumber_certified`) is
false. -/
theorem not_renumber_certified :
    ¬ ∀ (k : Nat) (p : Prog Nat), ∃ live, LiveCert p (renumberσ k p) live :=
  fun h => (h 1 cex).elim not_liveCert_cex

end Silmaril.Compile.Target.RegAlloc
