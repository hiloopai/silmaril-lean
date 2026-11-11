module

public import Silmaril.WasmSpec.InsertionSort.Defs
public import Silmaril.Proofs.WasmSpec.InsertionSort.Lists
public import Silmaril.Wasm.Logic.Words.Thms
public import Silmaril.Wasm.Game.Signature.Defs

/-!
# `insertion_sort`: the proof by tactics

Method `tactic`: symbolic execution with the rules and tactics of `Silmaril.Wasm.Logic.Words`
(`wrun`, `t_brIf`, `t_while`), two loop invariants and the list lemmas of `Lists`:

* outer loop (`OInv`, variant `n + 1 - i`): memory `0` holds some `B'` that agrees with the
  input `B` outside the segment, whose words are a permutation of the input's, with a sorted
  prefix of length `i`;
* inner loop (`IInv`, variant `j`), for the array `ys` at the start of the outer iteration and
  `key = ys[i]`: the words are `hole ys i j` (`ys[j..i)` shifted one place up) and every
  shifted element is above `key`.

Every-run total correctness at every profile and for every host relation.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.InsertionSort

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem func_body : sortFunc.body = body := rfl

theorem forCall_eq (mi : ModuleInst) (p n : BitVec 32) :
    Frame.forCall mi [.i32 p, .i32 n] sortFunc.locals = fr mi [p, n, 0, 0, 0] := rfl

/-! ## Invariants -/

/-- **The outer invariant**: memory `0` holds `B'` (equal to `B` outside the segment, a
permutation of its words, with a sorted prefix of length `i`); locals `p, n, i, j, key`. -/
def OInv (s₀ : Store H) (mi : ModuleInst) (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (p n : BitVec 32) (s : Store H) (f : Frame) : Prop :=
  ∃ (B' : ByteArray) (i j k : BitVec 32), s = s₀.setMem ma ⟨mt, B'⟩ ∧ f = fr mi [p, n, i, j, k] ∧
    1 ≤ i.toNat ∧ i.toNat ≤ n.toNat + 1 ∧ SameOutside B B' p.toNat (4 * n.toNat) ∧
    (words B' p.toNat n.toNat).Perm (words B p.toNat n.toNat) ∧
    SortedS ((words B' p.toNat n.toNat).take i.toNat)

/-- The outer variant `n + 1 - i`. -/
def OV (n : BitVec 32) (_ : Store H) (f : Frame) : Nat := n.toNat + 1 - loc f 2

/-- The facts of the inner invariant: the hole is at `j ≤ i`, `B'` agrees with `B` outside the
segment, its words are `hole ys i j`, and the shifted elements are above `key = ys[i]`. -/
def IFacts (B B' : ByteArray) (p n : BitVec 32) (ys : List (BitVec 32)) (i j : BitVec 32) :
    Prop :=
  j.toNat ≤ i.toNat ∧ SameOutside B B' p.toNat (4 * n.toNat) ∧
    words B' p.toNat n.toNat = hole ys i.toNat j.toNat ∧
    ∀ x ∈ (ys.take i.toNat).drop j.toNat, (ys.getD i.toNat 0).toInt < x.toInt

/-- **The inner invariant**, for the array `ys` at the start of outer iteration `i`. -/
def IInv (s₀ : Store H) (mi : ModuleInst) (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (p n : BitVec 32) (ys : List (BitVec 32)) (i : BitVec 32) (s : Store H) (f : Frame) : Prop :=
  ∃ (B' : ByteArray) (j : BitVec 32), s = s₀.setMem ma ⟨mt, B'⟩ ∧
    f = fr mi [p, n, i, j, ys.getD i.toNat 0] ∧ IFacts B B' p n ys i j

/-- The inner variant `j`. -/
def IV (_ : Store H) (f : Frame) : Nat := loc f 3

/-- The context of an outer iteration: `ys` (the array at its start) is a permutation of the
input with a sorted prefix of length `i`, and `1 ≤ i < n`. -/
def OCtx (B : ByteArray) (p n : BitVec 32) (ys : List (BitVec 32)) (i : BitVec 32) : Prop :=
  ys.length = n.toNat ∧ ys.Perm (words B p.toNat n.toNat) ∧ SortedS (ys.take i.toNat) ∧
    1 ≤ i.toNat ∧ i.toNat < n.toNat

theorem OV_fr {n p i j k : BitVec 32} {mi : ModuleInst} {s : Store H} :
    OV n s (fr mi [p, n, i, j, k]) = n.toNat + 1 - i.toNat := by
  simp only [OV, loc_fr (L := [p, n, i, j, k]) (k := 2) (by simp), List.getD_cons_succ,
    List.getD_cons_zero]

theorem IV_fr {n p i j k : BitVec 32} {mi : ModuleInst} {s : Store H} :
    IV s (fr mi [p, n, i, j, k]) = j.toNat := by
  simp only [IV, loc_fr (L := [p, n, i, j, k]) (k := 3) (by simp), List.getD_cons_succ,
    List.getD_cons_zero]

/-! ## Placing the key -/

/-- The memory after placing `key` at the hole meets the outer invariant for `i + 1`. -/
theorem place_facts {B B' : ByteArray} {p n i j : BitVec 32} {ys : List (BitVec 32)}
    (hb : p.toNat + 4 * n.toNat ≤ B.size) (hw : p.toNat + 4 * n.toNat < 2 ^ 32)
    (hc : OCtx B p n ys i) (hf : IFacts B B' p n ys i j)
    (hle : j.toNat = 0 ∨ (ys.getD (j.toNat - 1) 0).toInt ≤ (ys.getD i.toNat 0).toInt) :
    SameOutside B (wr B' (p + j * 4#32).toNat (ys.getD i.toNat 0)) p.toNat (4 * n.toNat) ∧
      (words (wr B' (p + j * 4#32).toNat (ys.getD i.toNat 0)) p.toNat n.toNat).Perm
        (words B p.toNat n.toNat) ∧
      SortedS ((words (wr B' (p + j * 4#32).toNat (ys.getD i.toNat 0)) p.toNat n.toNat).take
        (i + 1#32).toNat) := by
  obtain ⟨hlen, hperm, hs, h1, hi⟩ := hc
  obtain ⟨hj, hso, hws, hgt⟩ := hf
  have hiY : i.toNat < ys.length := by omega
  have hkey : ys.getD i.toNat 0 = ys[i.toNat] := getD_of_lt _ hiY
  have hb' : p.toNat + 4 * n.toNat ≤ B'.size := by rw [hso.1]; exact hb
  have hw' : words (wr B' (p + j * 4#32).toNat (ys.getD i.toNat 0)) p.toNat n.toNat =
      (hole ys i.toNat j.toNat).set j.toNat ys[i.toNat] := by
    rw [words_wr_addr _ (by omega) hw hb', hws, hkey]
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
  have hgt' : ∀ x ∈ (ys.take i.toNat).drop j.toNat, ys[i.toNat].toInt < x.toInt := hkey ▸ hgt
  have hle' : j.toNat = 0 ∨ (ys[j.toNat - 1]).toInt ≤ ys[i.toNat].toInt := by
    rcases hle with h0 | h
    · exact .inl h0
    · exact .inr (by rwa [getD_of_lt _ (by omega), hkey] at h)
  refine ⟨hso.trans (sameOutside_wr_addr _ (by omega) hw hb'), ?_, ?_⟩
  · rw [hw']
    exact (hole_place_perm hj hiY).trans hperm
  · rw [hw', hi1]
    exact hole_place_sorted hj hiY hs hgt' hle'

/-- **Placing the key** (the code after the inner loop): `a[j] := key`, `i := i + 1`, repeat
the outer loop with its invariant and a smaller variant. -/
theorem place_key {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B B' : ByteArray} {p n i j : BitVec 32} {ys : List (BitVec 32)}
    (hm₀ : MemAt s₀ mi ma mt B) (hb : p.toNat + 4 * n.toNat ≤ B.size)
    (hw : p.toNat + 4 * n.toNat < 2 ^ 32) {Q : Post H}
    (hc : OCtx B p n ys i) (hf : IFacts B B' p n ys i j)
    (hle : j.toNat = 0 ∨ (ys.getD (j.toNat - 1) 0).toInt ≤ (ys.getD i.toNat 0).toInt) :
    TWP P host (s₀.setMem ma ⟨mt, B'⟩) (fr mi [p, n, i, j, ys.getD i.toNat 0])
      (vals [] ++ expression placeKey)
      (whilePostT P host (OInv s₀ mi ma mt B p n) (OV n) (n.toNat + 1 - i.toNat) [] Q) := by
  have hm : MemAt (s₀.setMem ma ⟨mt, B'⟩) mi ma mt B' := hm₀.setMem B'
  have hsz : B'.size = B.size := hf.2.1.1
  have hjn : j.toNat < n.toNat := by have := hc.2.2.2.2; have := hf.1; omega
  obtain ⟨hso', hperm', hs'⟩ := place_facts hb hw hc hf hle
  have hv : OV n s₀ (fr mi [p, n, i + 1#32, j, ys.getD i.toNat 0]) < n.toNat + 1 - i.toNat := by
    rw [OV_fr]
    have := hc.2.2.2.2
    bv_omega
  simp only [placeKey]
  wbegin
  wrun
  rw [setMem_setMem]
  exact t_br (whilePostT_cont ⟨_, i + 1#32, j, _, rfl, rfl, by bv_omega, by bv_omega, hso', hperm',
    hs'⟩ hv)

/-! ## The inner loop -/

/-- The facts after one shift `a[j] := a[j - 1]`, `j := j - 1`. -/
theorem shift_facts {B B' : ByteArray} {p n i j : BitVec 32} {ys : List (BitVec 32)}
    (hb : p.toNat + 4 * n.toNat ≤ B.size) (hw : p.toNat + 4 * n.toNat < 2 ^ 32)
    (hc : OCtx B p n ys i) (hf : IFacts B B' p n ys i j) (hj0 : j.toNat ≠ 0)
    (hlt : (ys.getD i.toNat 0).toInt < (ys.getD (j.toNat - 1) 0).toInt) :
    IFacts B (wr B' (p + j * 4#32).toNat (ys.getD (j.toNat - 1) 0)) p n ys i (j - 1#32) := by
  obtain ⟨hlen, -, -, -, hi⟩ := hc
  obtain ⟨hj, hso, hws, hgt⟩ := hf
  have hiY : i.toNat < ys.length := by omega
  have hj1 : (j - 1#32).toNat = j.toNat - 1 := by bv_omega
  have hb' : p.toNat + 4 * n.toNat ≤ B'.size := by rw [hso.1]; exact hb
  have hpred : ys.getD (j.toNat - 1) 0 = ys[j.toNat - 1] := getD_of_lt _ (by omega)
  have hdrop : (ys.take i.toNat).drop (j.toNat - 1) =
      ys[j.toNat - 1] :: (ys.take i.toNat).drop j.toNat := by
    rw [List.drop_eq_getElem_cons (by simp; omega), List.getElem_take]
    congr 2
    omega
  refine ⟨by omega, hso.trans (sameOutside_wr_addr _ (by omega) hw hb'), ?_, ?_⟩
  · rw [words_wr_addr _ (by omega) hw hb', hws, hj1, hpred]
    exact hole_shift (by omega) hj hiY
  · rw [hj1, hdrop]
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx'
    · rw [← hpred]
      exact hlt
    · exact hgt x hx'

/-- The word below the hole is `ys[j - 1]`. -/
theorem load_pred {B B' : ByteArray} {p n i j : BitVec 32} {ys : List (BitVec 32)}
    (hw : p.toNat + 4 * n.toNat < 2 ^ 32) (hc : OCtx B p n ys i) (hf : IFacts B B' p n ys i j)
    (hj0 : j.toNat ≠ 0) : wd B' (p + (j - 1#32) * 4#32).toNat = ys.getD (j.toNat - 1) 0 := by
  obtain ⟨hlen, -, -, -, hi⟩ := hc
  obtain ⟨hj, -, hws, -⟩ := hf
  have hiY : i.toNat < ys.length := by omega
  rw [wd_addr_pred (by omega) (by omega) hw, hws,
    getD_of_lt _ (by rw [length_hole hj hiY]; omega), getElem_hole_pred (by omega) hj hiY]
  exact (getD_of_lt _ (by omega)).symm

/-- **One shift** of the inner loop, from `a[j] := a[j - 1]` on. -/
theorem inner_shift {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B B' : ByteArray} {p n i j : BitVec 32} {ys : List (BitVec 32)}
    (hm₀ : MemAt s₀ mi ma mt B) (hb : p.toNat + 4 * n.toNat ≤ B.size)
    (hw : p.toNat + 4 * n.toNat < 2 ^ 32) {rest : List Admin} {Q : Post H}
    (hc : OCtx B p n ys i) (hf : IFacts B B' p n ys i j) (hj0 : j.toNat ≠ 0)
    (hlt : (ys.getD i.toNat 0).toInt < (ys.getD (j.toNat - 1) 0).toInt) :
    TWP P host (s₀.setMem ma ⟨mt, B'⟩) (fr mi [p, n, i, j, ys.getD i.toNat 0])
      (vals ([] : List Val).reverse ++ expression innerShift)
      (whilePostT P host (IInv s₀ mi ma mt B p n ys i) IV j.toNat rest Q) := by
  have hf' := shift_facts hb hw hc hf hj0 hlt
  have hld := load_pred hw hc hf hj0
  obtain ⟨hj, hso, hws, -⟩ := hf
  have hm : MemAt (s₀.setMem ma ⟨mt, B'⟩) mi ma mt B' := hm₀.setMem B'
  have hsz : B'.size = B.size := hso.1
  have hiY : i.toNat < ys.length := by have := hc.1; have := hc.2.2.2.2; omega
  have hjn : j.toNat < n.toNat := by have := hc.2.2.2.2; omega
  have hv : IV s₀ (fr mi [p, n, i, j - 1#32, ys.getD i.toNat 0]) < j.toNat := by
    rw [IV_fr]
    bv_omega
  simp only [innerShift]
  wbegin
  wrun
  rw [hld, setMem_setMem]
  exact t_br (whilePostT_cont ⟨_, j - 1#32, rfl, rfl, hf'⟩ hv)

/-- The inner loop with `j ≠ 0`: compare `a[j - 1]` with `key`. -/
theorem inner_cmp {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B B' : ByteArray} {p n i j : BitVec 32} {ys : List (BitVec 32)}
    (hm₀ : MemAt s₀ mi ma mt B) (hb : p.toNat + 4 * n.toNat ≤ B.size)
    (hw : p.toNat + 4 * n.toNat < 2 ^ 32) {rest : List Admin} {Q : Post H}
    (hc : OCtx B p n ys i)
    (hplace : ∀ B' j, IFacts B B' p n ys i j →
      (j.toNat = 0 ∨ (ys.getD (j.toNat - 1) 0).toInt ≤ (ys.getD i.toNat 0).toInt) →
      TWP P host (s₀.setMem ma ⟨mt, B'⟩) (fr mi [p, n, i, j, ys.getD i.toNat 0])
        (vals [] ++ rest) Q)
    (hf : IFacts B B' p n ys i j) (hj0 : j.toNat ≠ 0) :
    TWP P host (s₀.setMem ma ⟨mt, B'⟩) (fr mi [p, n, i, j, ys.getD i.toNat 0])
      (vals ([] : List Val).reverse ++ expression (innerCmp ++ innerShift))
      (whilePostT P host (IInv s₀ mi ma mt B p n ys i) IV j.toNat rest Q) := by
  have hm : MemAt (s₀.setMem ma ⟨mt, B'⟩) mi ma mt B' := hm₀.setMem B'
  have hld : wd B' (p + (j - 1#32) * 4#32).toNat = ys.getD (j.toNat - 1) 0 :=
    load_pred hw hc hf hj0
  have hsz : B'.size = B.size := hf.2.1.1
  have hjn : j.toNat < n.toNat := by have := hc.2.2.2.2; have := hf.1; omega
  simp only [innerCmp, List.cons_append, List.nil_append, expression, List.map_cons]
  wrun
  rw [hld]
  refine t_brIf (fun hc1 => ?_) (fun hc1 => ?_)
  · have hle : (ys.getD (j.toNat - 1) 0).toInt ≤ (ys.getD i.toNat 0).toInt := by
      simpa using hc1
    exact whilePostT_exit (hplace B' j hf (.inr hle))
  · have hlt : (ys.getD i.toNat 0).toInt < (ys.getD (j.toNat - 1) 0).toInt := by
      simpa using hc1
    exact inner_shift hm₀ hb hw hc hf hj0 hlt

/-- **One iteration of the inner loop**: leave to `rest` when `j = 0` or `a[j - 1] ≤ key`
(`hplace`), else shift. -/
theorem inner_body {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B : ByteArray} {p n i : BitVec 32} {ys : List (BitVec 32)}
    (hm₀ : MemAt s₀ mi ma mt B) (hb : p.toNat + 4 * n.toNat ≤ B.size)
    (hw : p.toNat + 4 * n.toNat < 2 ^ 32) {rest : List Admin} {Q : Post H}
    (hc : OCtx B p n ys i)
    (hplace : ∀ B' j, IFacts B B' p n ys i j →
      (j.toNat = 0 ∨ (ys.getD (j.toNat - 1) 0).toInt ≤ (ys.getD i.toNat 0).toInt) →
      TWP P host (s₀.setMem ma ⟨mt, B'⟩) (fr mi [p, n, i, j, ys.getD i.toNat 0])
        (vals [] ++ rest) Q)
    {s : Store H} {f : Frame} (hI : IInv s₀ mi ma mt B p n ys i s f) :
    TWP P host s f (vals [] ++ expression innerBody)
      (whilePostT P host (IInv s₀ mi ma mt B p n ys i) IV (IV s f) rest Q) := by
  obtain ⟨B', j, rfl, rfl, hf⟩ := hI
  rw [IV_fr]
  simp only [innerBody, innerTest, List.cons_append, List.nil_append]
  wbegin
  wrun
  refine t_brIf (fun hc0 => ?_) (fun hc0 => ?_)
  · have hj0 : j.toNat = 0 := by simp at hc0; simp [hc0]
    exact whilePostT_exit (hplace B' j hf (.inl hj0))
  · have hj0 : j.toNat ≠ 0 := by simp at hc0; bv_omega
    exact inner_cmp hm₀ hb hw hc hplace hf hj0

/-! ## The outer loop and the function -/

/-- **One iteration of the outer loop**: leave when `i ≥ n` (the array is sorted), else load
`key = a[i]`, run the inner loop from `j = i`, and place the key. -/
theorem outer_body {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B : ByteArray} {p n : BitVec 32}
    (hm₀ : MemAt s₀ mi ma mt B) (hb : p.toNat + 4 * n.toNat ≤ B.size)
    (hw : p.toNat + 4 * n.toNat < 2 ^ 32) {Q : Post H}
    (hfin : ∀ B', Sorts B B' p.toNat n.toNat → ∀ F, Q (s₀.setMem ma ⟨mt, B'⟩) F (.normal []))
    {s : Store H} {f : Frame} (hI : OInv s₀ mi ma mt B p n s f) :
    TWP P host s f (vals [] ++ expression outerBody)
      (whilePostT P host (OInv s₀ mi ma mt B p n) (OV n) (OV n s f) [] Q) := by
  obtain ⟨B', i, j, k, rfl, rfl, h1, h2, hso, hperm, hs⟩ := hI
  rw [OV_fr]
  have hm : MemAt (s₀.setMem ma ⟨mt, B'⟩) mi ma mt B' := hm₀.setMem B'
  have hsz : B'.size = B.size := hso.1
  simp only [outerBody, List.cons_append, List.nil_append]
  wbegin
  wrun
  refine t_brIf (fun hc => ?_) (fun hc => ?_)
  · have hge : n.toNat ≤ i.toNat := by simpa using hc
    have hsorted : SortedS (words B' p.toNat n.toNat) := sortedS_of_take hs (by simpa using hge)
    exact whilePostT_exit (w_end (m := .total) (rs := []) (hfin B' ⟨hso, hsorted, hperm⟩ _))
  · have hlt : i.toNat < n.toNat := by simpa using hc
    have hctx : OCtx B p n (words B' p.toNat n.toNat) i := ⟨by simp, hperm, hs, h1, hlt⟩
    wrun
    rw [wd_addr hlt hw]
    exact t_while (Inv := IInv s₀ mi ma mt B p n (words B' p.toNat n.toNat) i) (V := IV)
      ⟨B', i, rfl, rfl, le_refl _, hso, (hole_self _ _).symm, by simp⟩
      (fun _ _ hI => inner_body hm₀ hb hw hctx
        (fun _ _ hf hle => place_key hm₀ hb hw hctx hf hle) hI)

/-- The body from the entry of the function. -/
theorem body_twp {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B : ByteArray} {p n : BitVec 32}
    (hm₀ : MemAt s₀ mi ma mt B) (hb : p.toNat + 4 * n.toNat ≤ B.size)
    (hw : p.toNat + 4 * n.toNat < 2 ^ 32) {Q : Post H}
    (hfin : ∀ B', Sorts B B' p.toNat n.toNat → ∀ F, Q (s₀.setMem ma ⟨mt, B'⟩) F (.normal [])) :
    TWP P host s₀ (fr mi [p, n, 0, 0, 0]) (vals [] ++ expression body) Q := by
  simp only [body]
  wbegin
  wrun
  exact t_while (Inv := OInv s₀ mi ma mt B p n) (V := OV n)
    ⟨B, 1#32, 0#32, 0#32, hm₀.setMem_self.symm, rfl, by simp, by simp,
      SameOutside.refl _ _ _, List.Perm.refl _, by simpa using sortedS_take_one _⟩
    (fun _ _ hI => outer_body hm₀ hb hw hfin hI)

/-- **`insertion_sort` meets its specification** (total correctness), at every profile and for
every host relation, for any function instance whose code is `sortFunc` and whose type has two
parameters and no results. -/
theorem sort_valid {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm sortFunc) (he : Expand fi.type (.func ps rs))
    (hps : ps.length = 2) (hrs : rs.length = 0) :
    TFSpecAt P host a (sortSpec a fi) := by
  refine TFSpecAt.of_body (fun _ _ h => h.1) hcode he ?_ ?_
  · rintro s args ⟨-, p, n, ma, mt, B, rfl, -⟩
    simp [hps]
  · rintro s args ⟨-, p, n, ma, mt, B, rfl, hm, hb, hw⟩ f vs₀
    have hfin : ∀ B', Sorts B B' p.toNat n.toNat → ∀ F, bodyPostT P host rs.length f vs₀
        (callPost f vs₀ ((sortSpec a fi).post s [.i32 p, .i32 n])) (s.setMem ma ⟨mt, B'⟩) F
        (.normal []) := fun B' hS F =>
      bodyPostT_normal (by simp [hrs]) fun p' n' ma' mt' B'' hargs hm' => by
        simp only [List.cons.injEq, and_true] at hargs
        obtain rfl := i32_inj hargs.1
        obtain rfl := i32_inj hargs.2
        obtain ⟨rfl, rfl, rfl⟩ := hm'.unique hm
        exact ⟨rfl, B', rfl, hS⟩
    have h := body_twp (P := P) (host := host) hm hb hw hfin
    rw [forCall_eq, func_body]
    simpa [TWP] using h

/-- The instantiated store holds `insertion_sort` as its only function, of type
`[i32, i32] → []`. -/
theorem store₀_funcs : ∃ fi : FuncInst Nat, store₀.funcs = [fi] ∧
    fi.code = .wasm sortFunc ∧
    Silmaril.Wasm.Game.FnType.ofDefType? fi.type = some ⟨[.num (.int .i32), .num (.int .i32)], []⟩ := by
  have hlen : store₀.funcs.length = 1 := rfl
  obtain ⟨fi, hf⟩ := List.length_eq_one_iff.mp hlen
  have hc : store₀.funcs.map FuncInst.code = [.wasm sortFunc] := rfl
  have ht : store₀.funcs.map (fun fi => Silmaril.Wasm.Game.FnType.ofDefType? fi.type) =
      [some ⟨[.num (.int .i32), .num (.int .i32)], []⟩] := by
    decide +kernel
  rw [hf] at hc ht
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hc ht
  exact ⟨fi, hf, hc, ht⟩

/-- **`Spec`, by tactics.** -/
theorem spec_tactic : Spec := fun P host _ _ _ _ hcode he hps hrs =>
  sort_valid (P := P) (host := host) hcode he hps hrs

/-- **`SpecStore`, by tactics**: the instantiated `insertion_sort` meets its specification. -/
theorem specStore_tactic : SpecStore := by
  obtain ⟨fi, hf, hc, ht⟩ := store₀_funcs
  refine ⟨fi, by rw [hf]; rfl, fun P host => ?_⟩
  exact sort_valid hc (Silmaril.Wasm.Game.FnType.expand_of_ofDefType? ht) rfl rfl

end Silmaril.WasmSpec.InsertionSort
