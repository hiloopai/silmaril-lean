module

public import Silmaril.Wasm.FX.Asyncify.Tool.Thms
public import Silmaril.Wasm.FX.Asyncify.Tool.Spill.Defs

/-!
# Spilling: what the spill code does to locals and operands

Target locals are `ls ++ ex`: the source's locals, then the temporaries `ex`. `setsCode_tv`
stores operands in a block of temporaries (`ovw`), `getsCode_tv` reloads them; `spillPre_run`
and `spillPost_run` are the code around a call site.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-- `ex` with `vs` written from index `a`. -/
def ovw (ex : List W) (a : Nat) (vs : List W) : List W := ex.take a ++ vs ++ ex.drop (a + vs.length)

theorem ovw_length {ex : List W} {a : Nat} {vs : List W} (h : a + vs.length ≤ ex.length) :
    (ovw ex a vs).length = ex.length := by
  simp only [ovw, List.length_append, List.length_take, List.length_drop]; omega

theorem tv_length (B a k : Nat) : (tv B a k).length = k := by simp [tv]

theorem tv_succ (B a k : Nat) : tv B a (k + 1) = tv B a k ++ [lidx (B + a + k)] := by
  simp [tv, List.range_succ]

theorem tv_lt {B a k : Nat} {ls ex : List W} (hl : ls.length = B) (hk : a + k ≤ ex.length)
    (hB : B + ex.length < 2 ^ 32) : ∀ x ∈ tv B a k, x.value.val < (ls ++ ex).length := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  have hj' : j < k := List.mem_range.1 hj
  rw [lidx_val (by omega), List.length_append, hl]; omega

theorem lv_tv {B a k : Nat} {ls ex : List W} (hl : ls.length = B) (hk : a + k ≤ ex.length)
    (hB : B + ex.length < 2 ^ 32) : (tv B a k).map (lv (ls ++ ex)) = (ex.drop a).take k := by
  apply List.ext_getElem (by simp [tv]; omega)
  intro j h1 h2
  have hj : j < k := by simpa [tv] using h1
  simp only [tv, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop, lv]
  rw [lidx_val (by omega), List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), hl, show B + a + j - B = a + j by omega,
    List.getElem?_eq_getElem (by omega)]
  rfl

theorem getsCode_tv {B a k : Nat} {ls ex ops gs : List W} {mem : Nat → W} (hl : ls.length = B)
    (hk : a + k ≤ ex.length) (hB : B + ex.length < 2 ^ 32) :
    runSeg (getsCode (tv B a k)) ⟨ls ++ ex, ops, gs, mem⟩ =
      some ⟨ls ++ ex, ((ex.drop a).take k).reverse ++ ops, gs, mem⟩ := by
  rw [getsCode_seg (tv_lt hl hk hB), lv_tv hl hk hB]

theorem ovw_set {ex : List W} {a k : Nat} {vs : List W} {w : W} (hk : vs.length = k)
    (h : a + k < ex.length) : ovw (ex.set (a + k) w) a vs = ovw ex a (vs ++ [w]) := by
  have h1 : (ex.set (a + k) w).take a = ex.take a := List.take_set_of_le (by omega)
  have h2 : (ex.set (a + k) w).drop (a + k) = w :: ex.drop (a + k + 1) := by
    rw [List.drop_set, ite_eq_right (by omega), Nat.sub_self,
      List.drop_eq_getElem_cons (show a + k < ex.length by omega), List.set_cons_zero]
  simp only [ovw, hk, h1, h2, List.length_append, List.length_singleton, List.append_assoc,
    List.cons_append, List.nil_append, Nat.add_assoc]

theorem setsCode_snoc (rs : List LocalIdx) (r : LocalIdx) :
    setsCode (rs ++ [r]) = .localSet r :: setsCode rs := by simp [setsCode]

/-- Storing the top `w.length` operands in temporaries `a, …` (the deepest at `a`). -/
theorem setsCode_tv {B a : Nat} {ls gs : List W} {mem : Nat → W} (hl : ls.length = B) :
    ∀ (w ex ops : List W), a + w.length ≤ ex.length → B + ex.length < 2 ^ 32 →
      runSeg (setsCode (tv B a w.length)) ⟨ls ++ ex, w ++ ops, gs, mem⟩ =
        some ⟨ls ++ ovw ex a w.reverse, ops, gs, mem⟩
  | [], ex, ops, _, _ => by simp [tv, setsCode, runSeg, ovw]
  | w0 :: w, ex, ops, hk, hB => by
    have hk' : a + w.length < ex.length := by simp at hk; omega
    have hidx : (lidx (B + a + w.length)).value.val = B + a + w.length := lidx_val (by omega)
    have hset : (ls ++ ex).set (B + a + w.length) w0 = ls ++ ex.set (a + w.length) w0 := by
      rw [List.set_append_right _ _ (by omega), hl, show B + a + w.length - B = a + w.length by omega]
    have h1 : segStep (.localSet (lidx (B + a + w.length))) ⟨ls ++ ex, w0 :: (w ++ ops), gs, mem⟩ =
        some ⟨ls ++ ex.set (a + w.length) w0, w ++ ops, gs, mem⟩ := by
      simp only [segStep, ctlOf, segCore, pexec, hidx, List.length_append, hl,
        show B + a + w.length < B + ex.length by omega, ↓reduceIte, hset]
    have hlen : (ex.set (a + w.length) w0).length = ex.length := List.length_set
    have ih := setsCode_tv (a := a) (gs := gs) (mem := mem) hl w (ex.set (a + w.length) w0) ops
      (by omega) (by omega)
    rw [List.length_cons, tv_succ, setsCode_snoc, List.cons_append, runSeg, h1, Option.bind_some,
      ih, ovw_set (List.length_reverse) hk', List.reverse_cons]

theorem ovw_zero {ex vs : List W} : ovw ex 0 vs = vs ++ ex.drop vs.length := by simp [ovw]

/-- Before a call: the `d` operands go to temporaries `0 … d-1`, the `n` arguments come back. -/
theorem spillPre_run {B : Nat} {s : Site} {ls ex w ops gs : List W} {mem : Nat → W}
    (hl : ls.length = B) (hw : w.length = s.d) (hn : s.n ≤ s.d) (hd : s.d ≤ ex.length)
    (hB : B + ex.length < 2 ^ 32) :
    runSeg (spillPre B s) ⟨ls ++ ex, w ++ ops, gs, mem⟩ =
      some ⟨ls ++ (w.reverse ++ ex.drop s.d), w.take s.n ++ ops, gs, mem⟩ := by
  have hset := setsCode_tv (a := 0) (gs := gs) (mem := mem) hl w ex ops (by omega) hB
  have hex1 : ovw ex 0 w.reverse = w.reverse ++ ex.drop s.d := by
    rw [ovw_zero, List.length_reverse, hw]
  have hlen1 : (w.reverse ++ ex.drop s.d).length = ex.length := by simp; omega
  have hget := getsCode_tv (a := s.d - s.n) (k := s.n) (ops := ops) (gs := gs) (mem := mem) hl
    (ex := w.reverse ++ ex.drop s.d) (by omega) (by omega)
  have hargs : (((w.reverse ++ ex.drop s.d).drop (s.d - s.n)).take s.n).reverse = w.take s.n := by
    rw [List.drop_append_of_le_length (by simp; omega), List.take_append_of_le_length
      (by simp; omega), List.drop_reverse, hw, show s.d - (s.d - s.n) = s.n by omega,
      List.take_of_length_le (by simp), List.reverse_reverse]
  unfold spillPre
  rw [runSeg_append, ← hw, hset, hw, Option.bind_some, hex1, hget, hargs]

theorem ovw_take {ex vs : List W} {a k : Nat} (hk : k ≤ a) (ha : a ≤ ex.length) :
    (ovw ex a vs).take k = ex.take k := by
  simp only [ovw, List.append_assoc]
  rw [List.take_append_of_le_length (by simp; omega), List.take_take, Nat.min_eq_left hk]

theorem ovw_drop_take {ex vs : List W} {a : Nat} (ha : a ≤ ex.length) :
    ((ovw ex a vs).drop a).take vs.length = vs := by
  simp only [ovw, List.append_assoc]
  rw [List.drop_append_of_le_length (by simp; omega), List.drop_eq_nil_of_le (by simp),
    List.nil_append, List.take_left' rfl]

/-- After a call: the `m` results go to temporaries `D …`, the live operands come back, then the
results. -/
theorem spillPost_run {B D : Nat} {s : Site} {ls ex vs ops gs : List W} {mem : Nat → W}
    (hl : ls.length = B) (hv : vs.length = s.m) (hL : s.d - s.n ≤ D) (hD : D + s.m ≤ ex.length)
    (hB : B + ex.length < 2 ^ 32) :
    runSeg (spillPost B D s) ⟨ls ++ ex, vs ++ ops, gs, mem⟩ =
      some ⟨ls ++ ovw ex D vs.reverse, vs ++ ((ex.take (s.d - s.n)).reverse ++ ops), gs, mem⟩ := by
  have hset := setsCode_tv (a := D) (gs := gs) (mem := mem) hl vs ex ops (by omega) hB
  have hlen2 : (ovw ex D vs.reverse).length = ex.length := ovw_length (by simp; omega)
  have hg1 := getsCode_tv (a := 0) (k := s.d - s.n) (ops := ops) (gs := gs) (mem := mem) hl
    (ex := ovw ex D vs.reverse) (by omega) (by omega)
  have hg2 := getsCode_tv (a := D) (k := s.m) (gs := gs) (mem := mem) hl
    (ops := ((ovw ex D vs.reverse).drop 0 |>.take (s.d - s.n)).reverse ++ ops)
    (ex := ovw ex D vs.reverse) (by omega) (by omega)
  have hlive : ((ovw ex D vs.reverse).drop 0).take (s.d - s.n) = ex.take (s.d - s.n) := by
    rw [List.drop_zero, ovw_take hL (by omega)]
  have hres : ((ovw ex D vs.reverse).drop D).take s.m = vs.reverse := by
    have := ovw_drop_take (ex := ex) (vs := vs.reverse) (a := D) (by omega)
    rwa [List.length_reverse, hv] at this
  unfold spillPost
  rw [runSeg_append, runSeg_append, ← hv, hset, hv, Option.bind_some, hg1, Option.bind_some, hg2,
    hres, hlive, List.reverse_reverse]

end Silmaril.Wasm.FX.Asyncify.Tool
