module

public import Silmaril.Proofs.WasmSpec.MergeSort.Merge
public import Silmaril.Wasm.Game.Signature.Defs

/-!
# `merge_sort`: the proof by tactics

`merge` is proved in `Silmaril.Proofs.WasmSpec.MergeSort.Merge` (`merge_valid`). `merge_sort` is
proved by induction on a bound `N` of its length argument (`sort_below`: the specification
restricted to `n < N`, `FSpec.below`), each recursive call having a smaller length; the calls
use the total call rule over the `i32` view (`Silmaril.Wasm.Logic.Words.t_call`), and the three
`Sorts` facts of the calls compose (`sorts_compose`). Every-run total correctness at every
profile and for every host relation.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.MergeSort

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Core (Outcome)

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem sortFunc_body : sortFunc.body = sortCode := rfl

theorem sortFunc_forCall (mi : ModuleInst) (p n t : BitVec 32) :
    Frame.forCall mi [.i32 p, .i32 n, .i32 t] sortFunc.locals = fr mi [p, n, t, 0] := rfl

/-- A list of at most one word is sorted. -/
theorem sortedS_of_length_le_one {l : List (BitVec 32)} (h : l.length ≤ 1) : SortedS l := by
  match l, h with
  | [], _ => exact sortedS_nil
  | [x], _ => exact sortedS_single x

/-- **The three calls compose**: sorting the halves and merging sorts the segment. -/
theorem sorts_compose {B B₁ B₂ B₃ : ByteArray} {p m n t : Nat} (hmn : m ≤ n)
    (hd : p + 4 * n ≤ t ∨ t + 4 * n ≤ p) (h₁ : Sorts B B₁ p m t)
    (h₂ : Sorts B₁ B₂ (p + 4 * m) (n - m) t) (h₃ : Sorts B₂ B₃ p n t) : Sorts B B₃ p n t := by
  obtain ⟨hs₁, -, hp₁⟩ := h₁
  obtain ⟨hs₂, -, hp₂⟩ := h₂
  obtain ⟨hs₃, hsort, hp₃⟩ := h₃
  have hn : n = m + (n - m) := by omega
  have hw₂ : words B₂ p m = words B₁ p m := hs₂.words_eq (by omega) (by omega)
  have hw₁ : words B₁ (p + 4 * m) (n - m) = words B (p + 4 * m) (n - m) :=
    hs₁.words_eq (by omega) (by omega)
  have hsplit : ∀ C : ByteArray, words C p n = words C p m ++ words C (p + 4 * m) (n - m) :=
    fun C => by rw [← words_append, ← hn]
  have hperm : (words B₂ p n).Perm (words B p n) := by
    rw [hsplit B₂, hsplit B, hw₂]
    exact List.Perm.append hp₁ (hp₂.trans (by rw [hw₁]))
  refine ⟨?_, hsort, hp₃.trans hperm⟩
  exact ((hs₁.mono (le_refl _) (by omega) (le_refl _) (by omega)).trans
    (hs₂.mono (by omega) (by omega) (le_refl _) (by omega))).trans hs₃

/-- The length argument of `merge_sort`: the measure of the recursion. -/
def lenOf : List Val → Nat
  | [_, .num ⟨.int .i32, n⟩, _] => n.toNat
  | _ => 0

theorem lenOf_eq (p n t : BitVec 32) : lenOf [.i32 p, .i32 n, .i32 t] = n.toNat := rfl

/-- The specification of `merge_sort` for lengths below `N`. -/
abbrev sortBelow (a : Nat) (fi : FuncInst H) (aM : Nat) (fiM : FuncInst H) (N : Nat) : FSpec H :=
  (sortSpec a fi aM fiM).below (fun _ => lenOf) N

/-- The context of the calls: the instances, the specifications they use, the memory and
the layout, `n ≥ 2` and `n ≤ N`. -/
structure CallCtx (P : Profile) (host : HostSemantics H) (s₀ : Store H) (a aM : Nat)
    (fi fiM : FuncInst H) (N ma : Nat) (mt : MemoryType) (B : ByteArray) (p n t : BitVec 32) :
    Prop where
  hS : TFSpecAt P host a (sortBelow a fi aM fiM N)
  hM : TFSpecAt P host aM (mergeSpec aM fiM)
  link : Linked a fi aM fiM
  hf : s₀.funcs[a]? = some fi
  hfM : s₀.funcs[aM]? = some fiM
  mem : MemAt s₀ fi.module ma mt B
  bounds : Bounds B p n t
  two : 2 ≤ n.toNat
  le : n.toNat ≤ N

/-- After the second recursive call: merge the sorted halves. -/
theorem after_second {s₀ : Store H} {a aM : Nat} {fi fiM : FuncInst H} {N ma : Nat}
    {mt : MemoryType} {B B₁ B₂ : ByteArray} {p n t m : BitVec 32}
    (hc : CallCtx P host s₀ a aM fi fiM N ma mt B p n t) (hm2 : m.toNat = n.toNat / 2)
    (h₁ : Sorts B B₁ p.toNat m.toNat t.toNat)
    (h₂ : Sorts B₁ B₂ (p.toNat + 4 * m.toNat) (n.toNat - m.toNat) t.toNat)
    {Q : Silmaril.Wasm.Logic.Core.Post H}
    (hfin : ∀ B', Sorts B B' p.toNat n.toNat t.toNat → ∀ F,
      Q (s₀.setMem ma ⟨mt, B'⟩) F (.normal [])) :
    TWP P host (s₀.setMem ma ⟨mt, B₂⟩) (fr fi.module [p, n, t, m])
      (vals ([] : List Val).reverse ++ expression [lget 0, lget 3, lget 1, lget 2, call 0])
      (armPostT P host [] [] Q) := by
  obtain ⟨hb₁, hb₂, hb₃, hb₄, hd⟩ := hc.bounds
  have hsz : B₂.size = B.size := h₂.1.1.trans h₁.1.1
  have hmn : m.toNat ≤ n.toNat := by omega
  have hm : MemAt (s₀.setMem ma ⟨mt, B₂⟩) fiM.module ma mt B₂ := by
    rw [hc.link.2.2.2.1]
    exact hc.mem.setMem B₂
  have hL : SortedS (words B₂ p.toNat m.toNat) := by
    rw [h₂.1.words_eq (by omega) (by omega)]
    exact h₁.2.1
  have hpre : (mergeSpec aM fiM).pre (s₀.setMem ma ⟨mt, B₂⟩) [.i32 p, .i32 m, .i32 n, .i32 t] :=
    ⟨hc.hfM, p, m, n, t, ma, mt, B₂, rfl, ⟨hm, by omega, by omega, hb₃, hb₄, hd⟩, hmn, hL, h₂.2.1⟩
  wbegin
  wrun
  refine t_call (rs := []) (args := [.i32 p, .i32 m, .i32 n, .i32 t]) (S := mergeSpec aM fiM)
    (by simpa [Idx.toNat] using hc.link.1) hc.hfM hc.hM hpre fun s₃ o hp => ?_
  obtain ⟨ho, B₃, rfl, h₃⟩ := hp p m n t ma mt B₂ (.inl rfl) hm
  have hS : Sorts B B₃ p.toNat n.toNat t.toNat := sorts_compose hmn hd h₁ h₂ h₃
  rw [setMem_setMem]
  exact ⟨ho, t_armEnd (rs := []) (w_end (m := .total) (rs := []) (hfin B₃ hS _))⟩

/-- After the first recursive call: sort the right half, then merge. -/
theorem after_first {s₀ : Store H} {a aM : Nat} {fi fiM : FuncInst H} {N ma : Nat}
    {mt : MemoryType} {B B₁ : ByteArray} {p n t m : BitVec 32}
    (hc : CallCtx P host s₀ a aM fi fiM N ma mt B p n t) (hm2 : m.toNat = n.toNat / 2)
    (h₁ : Sorts B B₁ p.toNat m.toNat t.toNat) {Q : Silmaril.Wasm.Logic.Core.Post H}
    (hfin : ∀ B', Sorts B B' p.toNat n.toNat t.toNat → ∀ F,
      Q (s₀.setMem ma ⟨mt, B'⟩) F (.normal [])) :
    TWP P host (s₀.setMem ma ⟨mt, B₁⟩) (fr fi.module [p, n, t, m])
      (vals ([] : List Val).reverse ++ expression [lget 0, lget 3, c32 4, imul, iadd, lget 1,
        lget 3, isub, lget 2, call 1, lget 0, lget 3, lget 1, lget 2, call 0])
      (armPostT P host [] [] Q) := by
  obtain ⟨hb₁, hb₂, hb₃, hb₄, hd⟩ := hc.bounds
  have h2 := hc.two
  have hsz : B₁.size = B.size := h₁.1.1
  have ha : (p + m * 4#32).toNat = p.toNat + 4 * m.toNat := addr_toNat (n := n.toNat) (by omega) hb₃
  have hnm : (n - m).toNat = n.toNat - m.toNat := by bv_omega
  have hm : MemAt (s₀.setMem ma ⟨mt, B₁⟩) fi.module ma mt B₁ := hc.mem.setMem B₁
  have hpre : (sortBelow a fi aM fiM N).pre (s₀.setMem ma ⟨mt, B₁⟩)
      [.i32 (p + m * 4#32), .i32 (n - m), .i32 t] :=
    ⟨⟨hc.hf, hc.hfM, p + m * 4#32, n - m, t, ma, mt, B₁, rfl,
      ⟨hm, by omega, by omega, by omega, by omega, by omega⟩⟩,
      by show lenOf _ < N; rw [lenOf_eq]; have := hc.le; omega⟩
  wbegin
  wrun
  refine t_call (rs := []) (args := [.i32 (p + m * 4#32), .i32 (n - m), .i32 t])
    (S := sortBelow a fi aM fiM N) (by simpa [Idx.toNat] using hc.link.2.1) hc.hf hc.hS hpre
    fun s₂ o hp => ?_
  obtain ⟨ho, B₂, rfl, h₂⟩ := hp (p + m * 4#32) 0 (n - m) t ma mt B₁ (.inr ⟨rfl, rfl⟩) hm
  rw [ha, hnm] at h₂
  rw [setMem_setMem]
  exact ⟨ho, after_second hc hm2 h₁ h₂ hfin⟩

/-- The recursive calls and the merge, for `n ≥ 2`. -/
theorem sort_calls {s₀ : Store H} {a aM : Nat} {fi fiM : FuncInst H} {N ma : Nat}
    {mt : MemoryType} {B : ByteArray} {p n t : BitVec 32}
    (hc : CallCtx P host s₀ a aM fi fiM N ma mt B p n t) {Q : Silmaril.Wasm.Logic.Core.Post H}
    (hfin : ∀ B', Sorts B B' p.toNat n.toNat t.toNat → ∀ F,
      Q (s₀.setMem ma ⟨mt, B'⟩) F (.normal [])) :
    TWP P host s₀ (fr fi.module [p, n, t, 0]) (vals ([] : List Val).reverse ++ expression callsCode)
      (armPostT P host [] [] Q) := by
  obtain ⟨hb₁, hb₂, hb₃, hb₄, hd⟩ := hc.bounds
  have h2 := hc.two
  have hm2 : (n >>> ((1#32).toNat % 32)).toNat = n.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hmn : (n >>> ((1#32).toNat % 32)).toNat < n.toNat := by omega
  have hpre : (sortBelow a fi aM fiM N).pre s₀
      [.i32 p, .i32 (n >>> ((1#32).toNat % 32)), .i32 t] :=
    ⟨⟨hc.hf, hc.hfM, p, _, t, ma, mt, B, rfl, ⟨hc.mem, by omega, by omega, by omega, by omega,
      by omega⟩⟩, by show lenOf _ < N; rw [lenOf_eq]; have := hc.le; omega⟩
  simp only [callsCode]
  wbegin
  wrun
  refine t_call (rs := []) (args := [.i32 p, .i32 (n >>> ((1#32).toNat % 32)), .i32 t])
    (S := sortBelow a fi aM fiM N) (by simpa [Idx.toNat] using hc.link.2.1) hc.hf hc.hS hpre
    fun s₁ o hp => ?_
  obtain ⟨ho, B₁, rfl, h₁⟩ := hp p 0 _ t ma mt B (.inr ⟨rfl, rfl⟩) hc.mem
  exact ⟨ho, after_first hc hm2 h₁ hfin⟩

/-- **The body of `merge_sort`**: return at once when `n < 2`, else the calls. -/
theorem sort_body {s₀ : Store H} {a aM : Nat} {fi fiM : FuncInst H} {N ma : Nat}
    {mt : MemoryType} {B : ByteArray} {p n t : BitVec 32}
    (hS : TFSpecAt P host a (sortBelow a fi aM fiM N)) (hM : TFSpecAt P host aM (mergeSpec aM fiM))
    (hlink : Linked a fi aM fiM) (hf : s₀.funcs[a]? = some fi) (hfM : s₀.funcs[aM]? = some fiM)
    (hm₀ : MemAt s₀ fi.module ma mt B) (hl : Bounds B p n t) (hN : n.toNat ≤ N)
    {Q : Silmaril.Wasm.Logic.Core.Post H}
    (hfin : ∀ B', Sorts B B' p.toNat n.toNat t.toNat → ∀ F,
      Q (s₀.setMem ma ⟨mt, B'⟩) F (.normal [])) :
    TWP P host s₀ (fr fi.module [p, n, t, 0]) (vals [] ++ expression sortCode) Q := by
  simp only [sortCode]
  wbegin
  refine t_block ?_
  wbegin
  wrun
  refine t_brIf (fun hc => ?_) (fun hc => ?_)
  · have h1 : n.toNat < 2 := by simpa using hc
    have hS₀ : Sorts B B p.toNat n.toNat t.toNat :=
      ⟨SameOutside2.refl _ _ _ _ _, sortedS_of_length_le_one (by simp; omega), List.Perm.refl _⟩
    have hq := hfin B hS₀ (fr fi.module [p, n, t, 0])
    rw [hm₀.setMem_self] at hq
    exact armPostT_exit (w_end (m := .total) (rs := []) hq)
  · have h2 : 2 ≤ n.toNat := by simpa using hc
    exact sort_calls ⟨hS, hM, hlink, hf, hfM, hm₀, hl, h2, hN⟩ hfin

/-- The postcondition for `merge_sort`'s arguments. -/
theorem post_sort {fi : FuncInst H} {s : Store H} {p n t : BitVec 32} {ma : Nat}
    {mt : MemoryType} {B B' : ByteArray} (hm : MemAt s fi.module ma mt B)
    (hS : Sorts B B' p.toNat n.toNat t.toNat) :
    Post fi s [.i32 p, .i32 n, .i32 t] (s.setMem ma ⟨mt, B'⟩) (.normal []) := by
  intro p' m' n' t' ma' mt' B'' hargs hm'
  obtain ⟨rfl, rfl, rfl⟩ := hm'.unique hm
  rcases hargs with h | ⟨h, -⟩
  · simp at h
  · simp only [List.cons.injEq, and_true] at h
    obtain rfl := i32_inj h.1
    obtain rfl := i32_inj h.2.1
    obtain rfl := i32_inj h.2.2
    exact ⟨rfl, B', rfl, hS⟩

/-- **`merge_sort` for lengths below `N`**, by induction on `N`. -/
theorem sort_below {a aM : Nat} {fi fiM : FuncInst H} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm sortFunc) (he : Expand fi.type (.func ps rs)) (hps : ps.length = 3)
    (hrs : rs.length = 0) (hlink : Linked a fi aM fiM)
    (hM : TFSpecAt P host aM (mergeSpec aM fiM)) :
    ∀ N, TFSpecAt P host a (sortBelow a fi aM fiM N)
  | 0 => fun _ _ hpre => absurd hpre.2 (Nat.not_lt_zero _)
  | N + 1 => by
    refine TFSpecAt.of_body (fun _ _ h => h.1.1) hcode he ?_ ?_
    · rintro s args ⟨⟨-, -, p, n, t, ma, mt, B, rfl, -⟩, -⟩
      simp [hps]
    · rintro s args ⟨⟨hf, hfM, p, n, t, ma, mt, B, rfl, hm, hl⟩, hlt⟩ f vs₀
      have hN : n.toNat ≤ N := by
        have h' : lenOf [.i32 p, .i32 n, .i32 t] < N + 1 := hlt
        rw [lenOf_eq] at h'
        omega
      have hfin : ∀ B', Sorts B B' p.toNat n.toNat t.toNat → ∀ F, bodyPostT P host rs.length f vs₀
          (callPost f vs₀ ((sortBelow a fi aM fiM (N + 1)).post s [.i32 p, .i32 n, .i32 t]))
          (s.setMem ma ⟨mt, B'⟩) F (.normal []) := fun B' hS F =>
        bodyPostT_normal (by simp [hrs]) (post_sort hm hS)
      have h := sort_body (sort_below hcode he hps hrs hlink hM N) hM hlink hf hfM hm hl hN hfin
      rw [sortFunc_forCall, sortFunc_body]
      simpa [TWP] using h

/-- **`merge_sort` meets its specification** (total correctness), at every profile and for
every host relation. -/
theorem sort_valid {a aM : Nat} {fi fiM : FuncInst H} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm sortFunc) (he : Expand fi.type (.func ps rs)) (hps : ps.length = 3)
    (hrs : rs.length = 0) (hlink : Linked a fi aM fiM) :
    TFSpecAt P host a (sortSpec a fi aM fiM) := by
  obtain ⟨-, -, hcM, -, psM, rsM, heM, hpsM, hrsM⟩ := id hlink
  have hM : TFSpecAt P host aM (mergeSpec aM fiM) := merge_valid hcM heM hpsM hrsM
  exact fun s args hpre =>
    sort_below hcode he hps hrs hlink hM (lenOf args + 1) s args ⟨hpre, Nat.lt_succ_self _⟩

/-- **`Spec`, by tactics.** -/
theorem spec_tactic : Spec := fun P host _ _ _ _ _ _ hcode he hps hrs hlink =>
  sort_valid (P := P) (host := host) hcode he hps hrs hlink

/-- The instantiated store holds `merge` and `merge_sort` (addresses `0` and `1`) of one module
instance whose function indices are those addresses. -/
theorem store₀_funcs : ∃ fiM fi : FuncInst Nat, store₀.funcs = [fiM, fi] ∧
    fiM.code = .wasm mergeFunc ∧ fi.code = .wasm sortFunc ∧
    Silmaril.Wasm.Game.FnType.ofDefType? fiM.type =
      some ⟨[.num (.int .i32), .num (.int .i32), .num (.int .i32), .num (.int .i32)], []⟩ ∧
    Silmaril.Wasm.Game.FnType.ofDefType? fi.type =
      some ⟨[.num (.int .i32), .num (.int .i32), .num (.int .i32)], []⟩ ∧
    fiM.module = fi.module ∧ fi.module.funcs = [0, 1] := by
  have hlen : store₀.funcs.length = 2 := rfl
  obtain ⟨fiM, fi, hf⟩ := List.length_eq_two.mp hlen
  have hc : store₀.funcs.map FuncInst.code = [.wasm mergeFunc, .wasm sortFunc] := rfl
  have ht : store₀.funcs.map (fun fi => Silmaril.Wasm.Game.FnType.ofDefType? fi.type) =
      [some ⟨[.num (.int .i32), .num (.int .i32), .num (.int .i32), .num (.int .i32)], []⟩,
       some ⟨[.num (.int .i32), .num (.int .i32), .num (.int .i32)], []⟩] := by
    decide +kernel
  have hmod : (store₀.funcs.map FuncInst.module).Pairwise (· = ·) := by decide +kernel
  have hfs : store₀.funcs.map (fun fi => fi.module.funcs) = [[0, 1], [0, 1]] := by decide +kernel
  rw [hf] at hc ht hmod hfs
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, List.pairwise_cons,
    List.mem_singleton, forall_eq] at hc ht hmod hfs
  exact ⟨fiM, fi, hf, hc.1, hc.2, ht.1, ht.2, hmod.1, hfs.2⟩

/-- **`SpecStore`, by tactics**: the instantiated `merge_sort` meets its specification. -/
theorem specStore_tactic : SpecStore := by
  obtain ⟨fiM, fi, hf, hcM, hc, htM, ht, hmod, hfs⟩ := store₀_funcs
  refine ⟨fiM, fi, hf, fun P host => ?_⟩
  have hlink : Linked 1 fi 0 fiM := ⟨by simp [hfs], by simp [hfs], hcM, hmod, _, _,
    Silmaril.Wasm.Game.FnType.expand_of_ofDefType? htM, rfl, rfl⟩
  exact sort_valid hc (Silmaril.Wasm.Game.FnType.expand_of_ofDefType? ht) rfl rfl hlink

end Silmaril.WasmSpec.MergeSort
