module

public import Silmaril.WasmSpec.MergeSort.Defs
public import Silmaril.Proofs.WasmSpec.MergeSort.Lists
public import Silmaril.Wasm.Logic.Words.Thms

/-!
# `merge`: the proof by tactics

Symbolic execution with the rules of `Silmaril.Wasm.Logic.Words`, two loop invariants and the
list lemmas of `Lists`:

* the merge loop (`MInv`, variant `n - k`): only the buffer has changed; its prefix
  `T = take k (words B' t n)` is sorted, a permutation of `take i L ++ take (j - m) R` and
  below everything still to merge (`L`, `R` the two halves);
* the copy loop (`CInv`, variant `n - k`): the buffer holds the merged list `W`, and the
  array is `take k W ++ drop k (L ++ R)`.

Every-run total correctness, every profile and host relation. A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.MergeSort

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Core (Outcome)

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem mergeFunc_body : mergeFunc.body = mergeCode := rfl

theorem mergeFunc_forCall (mi : ModuleInst) (p m n t : BitVec 32) :
    Frame.forCall mi [.i32 p, .i32 m, .i32 n, .i32 t] mergeFunc.locals =
      fr mi [p, m, n, t, 0, 0, 0, 0] := rfl

theorem loc_fr8 {mi : ModuleInst} {a b c d e g h k : BitVec 32} {i : Nat} (hi : i < 8) :
    loc (fr mi [a, b, c, d, e, g, h, k]) i = ([a, b, c, d, e, g, h, k].getD i 0).toNat :=
  loc_fr (by simpa using hi)

/-- The array and the buffer fit in `B`, are disjoint and do not wrap (`Layout` without the
store). -/
def Bounds (B : ByteArray) (p n t : BitVec 32) : Prop :=
  p.toNat + 4 * n.toNat ≤ B.size ∧ t.toNat + 4 * n.toNat ≤ B.size ∧
    p.toNat + 4 * n.toNat < 2 ^ 32 ∧ t.toNat + 4 * n.toNat < 2 ^ 32 ∧
    (p.toNat + 4 * n.toNat ≤ t.toNat ∨ t.toNat + 4 * n.toNat ≤ p.toNat)

theorem Bounds.of_size {B B' : ByteArray} {p n t : BitVec 32} (h : Bounds B p n t)
    (hs : B'.size = B.size) : Bounds B' p n t := by
  unfold Bounds at *
  omega

/-! ## The copy loop -/

/-- **The copy-loop invariant**, for the merged list `W`. -/
def CInv (s₀ : Store H) (mi : ModuleInst) (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (p m n t : BitVec 32) (W : List (BitVec 32)) (s : Store H) (f : Frame) : Prop :=
  ∃ (B' : ByteArray) (i j k l : BitVec 32), s = s₀.setMem ma ⟨mt, B'⟩ ∧
    f = fr mi [p, m, n, t, i, j, k, l] ∧ k.toNat ≤ n.toNat ∧
    SameOutside2 B B' p.toNat (4 * n.toNat) t.toNat (4 * n.toNat) ∧ words B' t.toNat n.toNat = W ∧
    words B' p.toNat n.toNat = W.take k.toNat ++ (words B p.toNat n.toNat).drop k.toNat

/-- The variant of both loops: `n - k`. -/
def KV (n : BitVec 32) (_ : Store H) (f : Frame) : Nat := n.toNat - loc f 6

theorem KV_fr {mi : ModuleInst} {p m n t i j k l : BitVec 32} {s : Store H} :
    KV n s (fr mi [p, m, n, t, i, j, k, l]) = n.toNat - k.toNat := by
  simp only [KV, loc_fr8 (by decide : 6 < 8), List.getD_cons_succ, List.getD_cons_zero]

/-- The memory after one copy step. -/
theorem copy_facts {B B' : ByteArray} {p n t k : BitVec 32} {W : List (BitVec 32)}
    (hl : Bounds B p n t) (hk : k.toNat < n.toNat) (hW : W.length = n.toNat)
    (hso : SameOutside2 B B' p.toNat (4 * n.toNat) t.toNat (4 * n.toNat))
    (hwt : words B' t.toNat n.toNat = W)
    (hwp : words B' p.toNat n.toNat = W.take k.toNat ++ (words B p.toNat n.toNat).drop k.toNat) :
    SameOutside2 B (wr B' (p + k * 4#32).toNat (W.getD k.toNat 0)) p.toNat (4 * n.toNat) t.toNat
        (4 * n.toNat) ∧
      words (wr B' (p + k * 4#32).toNat (W.getD k.toNat 0)) t.toNat n.toNat = W ∧
      words (wr B' (p + k * 4#32).toNat (W.getD k.toNat 0)) p.toNat n.toNat =
        W.take (k + 1#32).toNat ++ (words B p.toNat n.toNat).drop (k + 1#32).toNat := by
  have hl' : Bounds B' p n t := hl.of_size hso.1
  obtain ⟨hbp, hbt, hwp', hwt', hd⟩ := hl'
  have ha : (p + k * 4#32).toNat = p.toNat + 4 * k.toNat := addr_toNat hk hwp'
  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
  refine ⟨hso.trans ((sameOutside_wr_addr _ hk hwp' hbp).two _ _), ?_, ?_⟩
  · rw [words_wr_out _ (by omega) (by omega), hwt]
  · rw [words_wr_addr _ hk hwp' hbp, hwp, hk1]
    exact copy_set (by omega) (by simp [hW])

/-- One copy step `a[k] := t[k]`, `k := k + 1`, for `k < n`. -/
theorem copy_step {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B B' : ByteArray}
    {p m n t i j k l : BitVec 32} {W : List (BitVec 32)} (hm₀ : MemAt s₀ mi ma mt B)
    (hl : Bounds B p n t) (hW : W.length = n.toNat) {Q : Silmaril.Wasm.Logic.Core.Post H}
    (hso : SameOutside2 B B' p.toNat (4 * n.toNat) t.toNat (4 * n.toNat))
    (hwt : words B' t.toNat n.toNat = W)
    (hwp : words B' p.toNat n.toNat = W.take k.toNat ++ (words B p.toNat n.toNat).drop k.toNat)
    (hlt : k.toNat < n.toNat) :
    TWP P host (s₀.setMem ma ⟨mt, B'⟩) (fr mi [p, m, n, t, i, j, k, l])
      (vals ([] : List Val).reverse ++ expression (copyBody.drop 4))
      (whilePostT P host (CInv s₀ mi ma mt B p m n t W) (KV n) (n.toNat - k.toNat) [] Q) := by
  have hm : MemAt (s₀.setMem ma ⟨mt, B'⟩) mi ma mt B' := hm₀.setMem B'
  have hl' : Bounds B' p n t := hl.of_size hso.1
  obtain ⟨hso', hwt', hwp'⟩ := copy_facts hl hlt hW hso hwt hwp
  have hld : wd B' (t + k * 4#32).toNat = W.getD k.toNat 0 := by
    rw [wd_addr hlt hl'.2.2.2.1, hwt]
  have hv : KV n s₀ (fr mi [p, m, n, t, i, j, k + 1#32, l]) < n.toNat - k.toNat := by
    rw [KV_fr]
    bv_omega
  obtain ⟨hb₁, hb₂, hb₃, hb₄, -⟩ := hl'
  simp only [copyBody, List.drop]
  wbegin
  wrun
  rw [hld, setMem_setMem]
  exact t_br (whilePostT_cont ⟨_, i, j, k + 1#32, l, rfl, rfl, by bv_omega, hso', hwt', hwp'⟩ hv)

/-- **One iteration of the copy loop.** -/
theorem copy_body {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {p m n t : BitVec 32} {W : List (BitVec 32)} (hm₀ : MemAt s₀ mi ma mt B)
    (hl : Bounds B p n t) (hW : W.length = n.toNat) {Q : Silmaril.Wasm.Logic.Core.Post H}
    (hfin : ∀ B', SameOutside2 B B' p.toNat (4 * n.toNat) t.toNat (4 * n.toNat) →
      words B' p.toNat n.toNat = W → ∀ F, Q (s₀.setMem ma ⟨mt, B'⟩) F (.normal []))
    {s : Store H} {f : Frame} (hI : CInv s₀ mi ma mt B p m n t W s f) :
    TWP P host s f (vals [] ++ expression copyBody)
      (whilePostT P host (CInv s₀ mi ma mt B p m n t W) (KV n) (KV n s f) [] Q) := by
  obtain ⟨B', i, j, k, l, rfl, rfl, hkn, hso, hwt, hwp⟩ := hI
  rw [KV_fr]
  simp only [copyBody]
  wbegin
  wrun
  refine t_brIf (fun hc => ?_) (fun hc => ?_)
  · have hge : n.toNat ≤ k.toNat := by simpa using hc
    have hdone : words B' p.toNat n.toNat = W := by
      rw [hwp, List.take_of_length_le (by omega), List.drop_of_length_le (by simp; omega),
        List.append_nil]
    exact whilePostT_exit (w_end (m := .total) (rs := []) (hfin B' hso hdone _))
  · have hlt : k.toNat < n.toNat := by simpa using hc
    exact copy_step hm₀ hl hW hso hwt hwp hlt

/-- **The copy loop**, from the end of the merge loop: the buffer holds `W`, the array is
unchanged. -/
theorem copy_twp {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B B' : ByteArray}
    {p m n t i j k l : BitVec 32} {W : List (BitVec 32)} (hm₀ : MemAt s₀ mi ma mt B)
    (hl : Bounds B p n t) (hW : W.length = n.toNat) {Q : Silmaril.Wasm.Logic.Core.Post H}
    (hfin : ∀ B', SameOutside2 B B' p.toNat (4 * n.toNat) t.toNat (4 * n.toNat) →
      words B' p.toNat n.toNat = W → ∀ F, Q (s₀.setMem ma ⟨mt, B'⟩) F (.normal []))
    (hso : SameOutside B B' t.toNat (4 * n.toNat)) (hwt : words B' t.toNat n.toNat = W) :
    TWP P host (s₀.setMem ma ⟨mt, B'⟩) (fr mi [p, m, n, t, i, j, k, l])
      (vals [] ++ expression copyCode) Q := by
  have hwp : words B' p.toNat n.toNat = words B p.toNat n.toNat :=
    hso.words_eq (by have := hl.2.2.2.2; omega)
  simp only [copyCode]
  wbegin
  wrun
  exact t_while (Inv := CInv s₀ mi ma mt B p m n t W) (V := KV n)
    ⟨B', i, j, 0#32, l, rfl, rfl, by simp, hso.two' _ _, hwt, by simpa using hwp⟩
    (fun _ _ hI => copy_body hm₀ hl hW hfin hI)

/-! ## The merge loop -/

/-- The left half `a[0..m)`. -/
def half₁ (B : ByteArray) (p m : BitVec 32) : List (BitVec 32) := words B p.toNat m.toNat

/-- The right half `a[m..n)`. -/
def half₂ (B : ByteArray) (p m n : BitVec 32) : List (BitVec 32) :=
  words B (p.toNat + 4 * m.toNat) (n.toNat - m.toNat)

/-- The merged prefix: the first `k` words of the buffer. -/
def merged (B' : ByteArray) (n t k : BitVec 32) : List (BitVec 32) :=
  (words B' t.toNat n.toNat).take k.toNat

/-- The facts of the merge-loop invariant. -/
def MFacts (B B' : ByteArray) (p m n t i j k : BitVec 32) : Prop :=
  i.toNat ≤ m.toNat ∧ m.toNat ≤ j.toNat ∧ j.toNat ≤ n.toNat ∧
    k.toNat = i.toNat + (j.toNat - m.toNat) ∧ SameOutside B B' t.toNat (4 * n.toNat) ∧
    SortedS (merged B' n t k) ∧
    (merged B' n t k).Perm ((half₁ B p m).take i.toNat ++ (half₂ B p m n).take (j.toNat - m.toNat)) ∧
    Cross (merged B' n t k) ((half₁ B p m).drop i.toNat ++ (half₂ B p m n).drop (j.toNat - m.toNat))

/-- **The merge-loop invariant.** -/
def MInv (s₀ : Store H) (mi : ModuleInst) (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (p m n t : BitVec 32) (s : Store H) (f : Frame) : Prop :=
  ∃ (B' : ByteArray) (i j k l : BitVec 32), s = s₀.setMem ma ⟨mt, B'⟩ ∧
    f = fr mi [p, m, n, t, i, j, k, l] ∧ MFacts B B' p m n t i j k

/-- The array's words, while only the buffer has changed, read at `i < m` and at `m ≤ j < n`. -/
theorem read_halves {B B' : ByteArray} {p m n t : BitVec 32} (hl : Bounds B p n t)
    (hmn : m.toNat ≤ n.toNat) (hso : SameOutside B B' t.toNat (4 * n.toNat)) :
    (∀ i : BitVec 32, i.toNat < m.toNat →
      wd B' (p + i * 4#32).toNat = (half₁ B p m).getD i.toNat 0) ∧
    (∀ j : BitVec 32, m.toNat ≤ j.toNat → j.toNat < n.toNat →
      wd B' (p + j * 4#32).toNat = (half₂ B p m n).getD (j.toNat - m.toNat) 0) := by
  have hwp : words B' p.toNat n.toNat = half₁ B p m ++ half₂ B p m n := by
    rw [hso.words_eq (by have := hl.2.2.2.2; omega), half₁, half₂, ← words_append]
    congr 1
    omega
  have hlen : (half₁ B p m).length = m.toNat := by simp [half₁]
  refine ⟨fun i hi => ?_, fun j hj hjn => ?_⟩
  · rw [wd_addr (by omega) hl.2.2.1, hwp, getD_append_left (by omega)]
  · rw [wd_addr hjn hl.2.2.1, hwp, getD_append_right (by omega), hlen]

/-- Writing `v` at `t[k]` appends it to the merged prefix. -/
theorem merged_wr {B' : ByteArray} {n t k : BitVec 32} (v : BitVec 32) (hk : k.toNat < n.toNat)
    (hw : t.toNat + 4 * n.toNat < 2 ^ 32) (hb : t.toNat + 4 * n.toNat ≤ B'.size) :
    merged (wr B' (t + k * 4#32).toNat v) n t (k + 1#32) = merged B' n t k ++ [v] := by
  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
  rw [merged, merged, words_wr_addr v hk hw hb, hk1, take_set_succ v (by simpa using hk)]

/-- The facts after taking the left element. -/
theorem left_facts {B B' : ByteArray} {p m n t i j k : BitVec 32} (hl : Bounds B p n t)
    (hL : SortedS (half₁ B p m)) (hR : SortedS (half₂ B p m n))
    (hf : MFacts B B' p m n t i j k) (hk : k.toNat < n.toNat) (hi : i.toNat < m.toNat)
    (hle : n.toNat ≤ j.toNat ∨
      ((half₁ B p m).getD i.toNat 0).toInt ≤ ((half₂ B p m n).getD (j.toNat - m.toNat) 0).toInt) :
    MFacts B (wr B' (t + k * 4#32).toNat ((half₁ B p m).getD i.toNat 0)) p m n t (i + 1#32) j
      (k + 1#32) := by
  obtain ⟨hi₁, hj₁, hj₂, hk', hso, hT, hp, hc⟩ := hf
  obtain ⟨-, hbt, -, hwt, -⟩ := hl.of_size hso.1
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
  have hle' : (half₂ B p m n).length ≤ j.toNat - m.toNat ∨
      ((half₁ B p m).getD i.toNat 0).toInt ≤ ((half₂ B p m n).getD (j.toNat - m.toNat) 0).toInt := by
    rcases hle with h | h
    · exact .inl (by simp [half₂]; omega)
    · exact .inr h
  obtain ⟨h₁, h₂, h₃⟩ := merge_left hL hR hT hc hp (by simp [half₁]; omega) hle'
  have hmw := merged_wr (B' := B') ((half₁ B p m).getD i.toNat 0) hk hwt hbt
  refine ⟨by omega, hj₁, hj₂, by omega, hso.trans (sameOutside_wr_addr _ hk hwt hbt), ?_, ?_, ?_⟩
  · rw [hmw]
    exact h₁
  · rw [hmw, hi1]
    exact h₂
  · rw [hmw, hi1]
    exact h₃

/-- The facts after taking the right element. -/
theorem right_facts {B B' : ByteArray} {p m n t i j k : BitVec 32} (hl : Bounds B p n t)
    (hL : SortedS (half₁ B p m)) (hR : SortedS (half₂ B p m n))
    (hf : MFacts B B' p m n t i j k) (hk : k.toNat < n.toNat) (hj : j.toNat < n.toNat)
    (hlt : m.toNat ≤ i.toNat ∨
      ((half₂ B p m n).getD (j.toNat - m.toNat) 0).toInt < ((half₁ B p m).getD i.toNat 0).toInt) :
    MFacts B (wr B' (t + k * 4#32).toNat ((half₂ B p m n).getD (j.toNat - m.toNat) 0)) p m n t i
      (j + 1#32) (k + 1#32) := by
  obtain ⟨hi₁, hj₁, hj₂, hk', hso, hT, hp, hc⟩ := hf
  obtain ⟨-, hbt, -, hwt, -⟩ := hl.of_size hso.1
  have hj1 : (j + 1#32).toNat - m.toNat = j.toNat - m.toNat + 1 := by bv_omega
  have hlt' : (half₁ B p m).length ≤ i.toNat ∨
      ((half₂ B p m n).getD (j.toNat - m.toNat) 0).toInt < ((half₁ B p m).getD i.toNat 0).toInt := by
    rcases hlt with h | h
    · exact .inl (by simp [half₁]; omega)
    · exact .inr h
  obtain ⟨h₁, h₂, h₃⟩ := merge_right hL hR hT hc hp (by simp [half₂]; omega) hlt'
  have hmw := merged_wr (B' := B') ((half₂ B p m n).getD (j.toNat - m.toNat) 0) hk hwt hbt
  refine ⟨hi₁, by bv_omega, by bv_omega, by bv_omega,
    hso.trans (sameOutside_wr_addr _ hk hwt hbt), ?_, ?_, ?_⟩
  · rw [hmw]
    exact h₁
  · rw [hmw, hj1]
    exact h₂
  · rw [hmw, hj1]
    exact h₃

/-- The flag `l` chosen by `chooseCode`: nonzero takes the left element, zero the right one. -/
def Flag (B : ByteArray) (p m n i j l : BitVec 32) : Prop :=
  (l ≠ 0 → i.toNat < m.toNat ∧ (n.toNat ≤ j.toNat ∨
    ((half₁ B p m).getD i.toNat 0).toInt ≤ ((half₂ B p m n).getD (j.toNat - m.toNat) 0).toInt)) ∧
  (l = 0 → j.toNat < n.toNat ∧ (m.toNat ≤ i.toNat ∨
    ((half₂ B p m n).getD (j.toNat - m.toNat) 0).toInt < ((half₁ B p m).getD i.toNat 0).toInt))

/-- The code after an arm of `takeCode`. -/
abbrev nextCode : List Instr := [lget 6, c32 1, iadd, lset 6, br 0]

/-- **Taking the left element** (the `then` arm of `takeCode`). -/
theorem take_left {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B B' : ByteArray}
    {p m n t i j k l : BitVec 32} (hm₀ : MemAt s₀ mi ma mt B) (hl : Bounds B p n t)
    (hmn : m.toNat ≤ n.toNat) (hL : SortedS (half₁ B p m)) (hR : SortedS (half₂ B p m n))
    {rest : List Admin} {Q : Silmaril.Wasm.Logic.Core.Post H}
    (hf : MFacts B B' p m n t i j k) (hk : k.toNat < n.toNat) (hi : i.toNat < m.toNat)
    (hle : n.toNat ≤ j.toNat ∨
      ((half₁ B p m).getD i.toNat 0).toInt ≤ ((half₂ B p m n).getD (j.toNat - m.toNat) 0).toInt) :
    TWP P host (s₀.setMem ma ⟨mt, B'⟩) (fr mi [p, m, n, t, i, j, k, l])
      (vals [] ++ expression takeLeft)
      (armPostT P host [] (expression nextCode)
        (whilePostT P host (MInv s₀ mi ma mt B p m n t) (KV n) (n.toNat - k.toNat) rest Q)) := by
  have hm : MemAt (s₀.setMem ma ⟨mt, B'⟩) mi ma mt B' := hm₀.setMem B'
  have hld := (read_halves hl hmn hf.2.2.2.2.1).1 i hi
  have hf' := left_facts hl hL hR hf hk hi hle
  have hv : KV n s₀ (fr mi [p, m, n, t, i + 1#32, j, k + 1#32, l]) < n.toNat - k.toNat := by
    rw [KV_fr]
    bv_omega
  obtain ⟨hb₁, hb₂, hb₃, hb₄, -⟩ := hl.of_size hf.2.2.2.2.1.1
  simp only [takeLeft]
  wbegin
  wrun
  rw [hld, setMem_setMem]
  refine t_armEnd ?_
  wrun
  exact t_br (whilePostT_cont ⟨_, i + 1#32, j, k + 1#32, l, rfl, rfl, hf'⟩ hv)

/-- **Taking the right element** (the `else` arm of `takeCode`). -/
theorem take_right {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B B' : ByteArray} {p m n t i j k l : BitVec 32} (hm₀ : MemAt s₀ mi ma mt B)
    (hl : Bounds B p n t) (hmn : m.toNat ≤ n.toNat) (hL : SortedS (half₁ B p m))
    (hR : SortedS (half₂ B p m n)) {rest : List Admin} {Q : Silmaril.Wasm.Logic.Core.Post H}
    (hf : MFacts B B' p m n t i j k) (hk : k.toNat < n.toNat) (hj : j.toNat < n.toNat)
    (hlt : m.toNat ≤ i.toNat ∨
      ((half₂ B p m n).getD (j.toNat - m.toNat) 0).toInt < ((half₁ B p m).getD i.toNat 0).toInt) :
    TWP P host (s₀.setMem ma ⟨mt, B'⟩) (fr mi [p, m, n, t, i, j, k, l])
      (vals [] ++ expression takeRight)
      (armPostT P host [] (expression nextCode)
        (whilePostT P host (MInv s₀ mi ma mt B p m n t) (KV n) (n.toNat - k.toNat) rest Q)) := by
  have hm : MemAt (s₀.setMem ma ⟨mt, B'⟩) mi ma mt B' := hm₀.setMem B'
  have hld := (read_halves hl hmn hf.2.2.2.2.1).2 j hf.2.1 hj
  have hf' := right_facts hl hL hR hf hk hj hlt
  have hv : KV n s₀ (fr mi [p, m, n, t, i, j + 1#32, k + 1#32, l]) < n.toNat - k.toNat := by
    rw [KV_fr]
    bv_omega
  obtain ⟨hb₁, hb₂, hb₃, hb₄, -⟩ := hl.of_size hf.2.2.2.2.1.1
  simp only [takeRight]
  wbegin
  wrun
  rw [hld, setMem_setMem]
  refine t_armEnd ?_
  wrun
  exact t_br (whilePostT_cont ⟨_, i, j + 1#32, k + 1#32, l, rfl, rfl, hf'⟩ hv)

/-- **`takeCode`**: take the side the flag chose, `k := k + 1`, repeat. -/
theorem take_twp {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B B' : ByteArray}
    {p m n t i j k l : BitVec 32} (hm₀ : MemAt s₀ mi ma mt B) (hl : Bounds B p n t)
    (hmn : m.toNat ≤ n.toNat) (hL : SortedS (half₁ B p m)) (hR : SortedS (half₂ B p m n))
    {rest : List Admin} {Q : Silmaril.Wasm.Logic.Core.Post H}
    (hf : MFacts B B' p m n t i j k) (hk : k.toNat < n.toNat) (hfl : Flag B p m n i j l) :
    TWP P host (s₀.setMem ma ⟨mt, B'⟩) (fr mi [p, m, n, t, i, j, k, l])
      (vals [] ++ expression takeCode)
      (whilePostT P host (MInv s₀ mi ma mt B p m n t) (KV n) (n.toNat - k.toNat) rest Q) := by
  simp only [takeCode]
  wbegin
  wrun
  refine t_if (fun hc => ?_) (fun hc => ?_)
  · obtain ⟨hi, hle⟩ := hfl.1 hc
    exact take_left hm₀ hl hmn hL hR hf hk hi hle
  · obtain ⟨hj, hlt⟩ := hfl.2 hc
    exact take_right hm₀ hl hmn hL hR hf hk hj hlt

/-- The comparison arm of `chooseCode` (`i < m`, `j < n`): `l := (a[i] ≤ a[j])`. -/
theorem choose_cmp {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B B' : ByteArray} {p m n t i j k l : BitVec 32} (hm₀ : MemAt s₀ mi ma mt B)
    (hl : Bounds B p n t) (hmn : m.toNat ≤ n.toNat) {Q : Silmaril.Wasm.Logic.Core.Post H}
    (hso : SameOutside B B' t.toNat (4 * n.toNat)) (hj₁ : m.toNat ≤ j.toNat)
    (hjn : j.toNat < n.toNat) (hi : i.toNat < m.toNat)
    (hcont : ∀ l', Flag B p m n i j l' → TWP P host (s₀.setMem ma ⟨mt, B'⟩)
      (fr mi [p, m, n, t, i, j, k, l']) (vals [] ++ expression takeCode) Q) :
    TWP P host (s₀.setMem ma ⟨mt, B'⟩) (fr mi [p, m, n, t, i, j, k, l])
      (vals [] ++ expression cmpCode)
      (armPostT P host [] [] (armPostT P host [] (expression takeCode) Q)) := by
  have hm : MemAt (s₀.setMem ma ⟨mt, B'⟩) mi ma mt B' := hm₀.setMem B'
  obtain ⟨hb₁, hb₂, hb₃, hb₄, -⟩ := hl.of_size hso.1
  obtain ⟨hr₁, hr₂⟩ := read_halves hl hmn hso
  simp only [cmpCode]
  wbegin
  wrun
  rw [hr₁ i hi, hr₂ j hj₁ hjn]
  refine t_armEnd (t_armEnd (hcont _ ⟨fun h => ⟨hi, .inr ?_⟩, fun h => ⟨hjn, .inr ?_⟩⟩))
  · simpa using h
  · simpa using h

/-- **`chooseCode`**: set the flag `l`, then continue with `takeCode` (`hk`). -/
theorem choose_twp {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B B' : ByteArray} {p m n t i j k l : BitVec 32} (hm₀ : MemAt s₀ mi ma mt B)
    (hl : Bounds B p n t) (hmn : m.toNat ≤ n.toNat) {Q : Silmaril.Wasm.Logic.Core.Post H}
    (hf : MFacts B B' p m n t i j k) (hk : k.toNat < n.toNat)
    (hcont : ∀ l', Flag B p m n i j l' → TWP P host (s₀.setMem ma ⟨mt, B'⟩)
      (fr mi [p, m, n, t, i, j, k, l']) (vals [] ++ expression takeCode) Q) :
    TWP P host (s₀.setMem ma ⟨mt, B'⟩) (fr mi [p, m, n, t, i, j, k, l])
      (vals ([] : List Val).reverse ++ expression (chooseCode ++ takeCode)) Q := by
  have hm : MemAt (s₀.setMem ma ⟨mt, B'⟩) mi ma mt B' := hm₀.setMem B'
  obtain ⟨hi₁, hj₁, hj₂, hk', hso, -⟩ := hf
  obtain ⟨hb₁, hb₂, hb₃, hb₄, -⟩ := hl.of_size hso.1
  simp only [chooseCode, List.cons_append, List.nil_append, expression, List.map_cons]
  wrun
  refine t_if (fun hc => ?_) (fun hc => ?_)
  · have hnj : n.toNat ≤ j.toNat := by simpa using hc
    wbegin
    wrun
    exact t_armEnd (hcont 1#32 ⟨fun _ => ⟨by omega, .inl hnj⟩, fun h => absurd h (by decide)⟩)
  · have hjn : j.toNat < n.toNat := by simpa using hc
    wbegin; wrun
    refine t_if (fun hc' => ?_) (fun hc' => ?_)
    · have hmi : m.toNat ≤ i.toNat := by simpa using hc'
      wbegin; wrun
      exact t_armEnd (t_armEnd (hcont 0#32 ⟨fun h => absurd rfl h, fun _ => ⟨hjn, .inl hmi⟩⟩))
    · exact choose_cmp hm₀ hl hmn hso hj₁ hjn (by simpa using hc') hcont

/-- At the end of the merge loop the buffer holds a sorted permutation of the array. -/
theorem merge_done {B B' : ByteArray} {p m n t i j k : BitVec 32} (hmn : m.toNat ≤ n.toNat)
    (hf : MFacts B B' p m n t i j k) (hk : n.toNat ≤ k.toNat) :
    SortedS (words B' t.toNat n.toNat) ∧
      (words B' t.toNat n.toNat).Perm (words B p.toNat n.toNat) := by
  obtain ⟨hi₁, hj₁, hj₂, hk', -, hT, hp, -⟩ := hf
  have hm : merged B' n t k = words B' t.toNat n.toNat :=
    List.take_of_length_le (by simp; omega)
  have hsplit : words B p.toNat n.toNat = half₁ B p m ++ half₂ B p m n := by
    rw [half₁, half₂, ← words_append]
    congr 1
    omega
  have hL : (half₁ B p m).take i.toNat = half₁ B p m :=
    List.take_of_length_le (by simp [half₁]; omega)
  have hR : (half₂ B p m n).take (j.toNat - m.toNat) = half₂ B p m n :=
    List.take_of_length_le (by simp [half₂]; omega)
  rw [hm, hL, hR, ← hsplit] at hp
  exact ⟨hm ▸ hT, hp⟩

/-- **One iteration of the merge loop.** -/
theorem merge_body {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {p m n t : BitVec 32} (hm₀ : MemAt s₀ mi ma mt B) (hl : Bounds B p n t)
    (hmn : m.toNat ≤ n.toNat) (hL : SortedS (half₁ B p m)) (hR : SortedS (half₂ B p m n))
    {Q : Silmaril.Wasm.Logic.Core.Post H}
    (hfin : ∀ B', Sorts B B' p.toNat n.toNat t.toNat → ∀ F, Q (s₀.setMem ma ⟨mt, B'⟩) F (.normal []))
    {s : Store H} {f : Frame} (hI : MInv s₀ mi ma mt B p m n t s f) :
    TWP P host s f (vals [] ++ expression mergeBody)
      (whilePostT P host (MInv s₀ mi ma mt B p m n t) (KV n) (KV n s f) (expression copyCode) Q) := by
  obtain ⟨B', i, j, k, l, rfl, rfl, hf⟩ := hI
  rw [KV_fr]
  simp only [mergeBody, List.cons_append, List.nil_append]
  wbegin
  wrun
  refine t_brIf (fun hc => ?_) (fun hc => ?_)
  · have hge : n.toNat ≤ k.toNat := by simpa using hc
    obtain ⟨hWs, hWp⟩ := merge_done hmn hf hge
    have hfin' : ∀ B'', SameOutside2 B B'' p.toNat (4 * n.toNat) t.toNat (4 * n.toNat) →
        words B'' p.toNat n.toNat = words B' t.toNat n.toNat →
        ∀ F, Q (s₀.setMem ma ⟨mt, B''⟩) F (.normal []) := fun B'' h₂ hw F =>
      hfin B'' ⟨h₂, hw ▸ hWs, hw ▸ hWp⟩ F
    exact whilePostT_exit (copy_twp hm₀ hl (by simp) hfin' hf.2.2.2.2.1 rfl)
  · have hlt : k.toNat < n.toNat := by simpa using hc
    exact choose_twp hm₀ hl hmn hf hlt (fun _ hfl => take_twp hm₀ hl hmn hL hR hf hlt hfl)

/-- The body of `merge` from the entry of the function. -/
theorem merge_twp {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {p m n t : BitVec 32} (hm₀ : MemAt s₀ mi ma mt B) (hl : Bounds B p n t)
    (hmn : m.toNat ≤ n.toNat) (hL : SortedS (half₁ B p m)) (hR : SortedS (half₂ B p m n))
    {Q : Silmaril.Wasm.Logic.Core.Post H}
    (hfin : ∀ B', Sorts B B' p.toNat n.toNat t.toNat → ∀ F, Q (s₀.setMem ma ⟨mt, B'⟩) F (.normal [])) :
    TWP P host s₀ (fr mi [p, m, n, t, 0, 0, 0, 0]) (vals [] ++ expression mergeCode) Q := by
  have hf₀ : MFacts B B p m n t 0#32 m 0#32 := ⟨by simp, le_refl _, hmn, by simp,
    SameOutside.refl _ _ _, by simp [merged], by simp [merged], by simp [merged, Cross]⟩
  simp only [mergeCode, List.cons_append, List.nil_append]
  wbegin
  wrun
  exact t_while (Inv := MInv s₀ mi ma mt B p m n t) (V := KV n)
    ⟨B, 0#32, m, 0#32, 0#32, hm₀.setMem_self.symm, rfl, hf₀⟩
    (fun _ _ hI => merge_body hm₀ hl hmn hL hR hfin hI)

/-- The postcondition for `merge`'s arguments. -/
theorem post_merge {fi : FuncInst H} {s : Store H} {p m n t : BitVec 32} {ma : Nat}
    {mt : MemoryType} {B B' : ByteArray} (hm : MemAt s fi.module ma mt B)
    (hS : Sorts B B' p.toNat n.toNat t.toNat) :
    Post fi s [.i32 p, .i32 m, .i32 n, .i32 t] (s.setMem ma ⟨mt, B'⟩) (.normal []) := by
  intro p' m' n' t' ma' mt' B'' hargs hm'
  obtain ⟨rfl, rfl, rfl⟩ := hm'.unique hm
  rcases hargs with h | ⟨h, -⟩
  · simp only [List.cons.injEq, and_true] at h
    obtain rfl := i32_inj h.1
    obtain rfl := i32_inj h.2.1
    obtain rfl := i32_inj h.2.2.1
    obtain rfl := i32_inj h.2.2.2
    exact ⟨rfl, B', rfl, hS⟩
  · simp at h

/-- **`merge` meets its specification** (total correctness), at every profile and for every
host relation. -/
theorem merge_valid {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm mergeFunc) (he : Expand fi.type (.func ps rs))
    (hps : ps.length = 4) (hrs : rs.length = 0) :
    TFSpecAt P host a (mergeSpec a fi) := by
  refine TFSpecAt.of_body (fun _ _ h => h.1) hcode he ?_ ?_
  · rintro s args ⟨-, p, m, n, t, ma, mt, B, rfl, -⟩
    simp [hps]
  · rintro s args ⟨-, p, m, n, t, ma, mt, B, rfl, ⟨hm, hl⟩, hmn, hL, hR⟩ f vs₀
    have hfin : ∀ B', Sorts B B' p.toNat n.toNat t.toNat → ∀ F, bodyPostT P host rs.length f vs₀
        (callPost f vs₀ ((mergeSpec a fi).post s [.i32 p, .i32 m, .i32 n, .i32 t]))
        (s.setMem ma ⟨mt, B'⟩) F (.normal []) := fun B' hS F =>
      bodyPostT_normal (by simp [hrs]) (post_merge hm hS)
    have h := merge_twp (P := P) (host := host) hm hl hmn hL hR hfin
    rw [mergeFunc_forCall, mergeFunc_body]
    simpa [TWP] using h

/-- **`MergeSpec`, by tactics.** -/
theorem mergeSpec_tactic : MergeSpec := fun P host _ _ _ _ hcode he hps hrs =>
  merge_valid (P := P) (host := host) hcode he hps hrs

end Silmaril.WasmSpec.MergeSort
