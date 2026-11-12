module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Basic

/-!
# The generated code fragments as segments: memory words, saves, restores, guards
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-! ## Arithmetic -/

theorem toNat_ofNat32 {a : Nat} (h : a < 2 ^ 32) : (BitVec.ofNat 32 a).toNat = a := by
  simp [BitVec.toNat_ofNat]; omega

theorem fin64 {a : Nat} (h : a < 2 ^ 64) : (Fin.ofNat (2 ^ 64) a).val = a := by
  simp [Fin.ofNat]; omega

theorem ofNat32_ne {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : a ≠ b) :
    BitVec.ofNat 32 a ≠ BitVec.ofNat 32 b := by
  intro he
  have := congrArg BitVec.toNat he
  rw [toNat_ofNat32 ha, toNat_ofNat32 hb] at this
  exact h this

theorem lidx_val {i : Nat} (h : i < 2 ^ 32) : (lidx i).value.val = i := by
  simp [lidx, Fin.ofNat]; omega

theorem marg_off {o : Nat} (h : o < 2 ^ 64) : (marg o).offset.val = o := fin64 h

/-! ## Memory words -/

theorem writeWords_lt {mem : Nat → W} {a x : Nat} : ∀ {ws : List W}, x < a →
    writeWords mem a ws x = mem x
  | [], _ => rfl
  | w :: ws, h => by
    simp only [writeWords]
    rw [writeWords_lt (by omega)]
    simp [upd]; omega

theorem writeWords_ge {a x : Nat} : ∀ {mem : Nat → W} {ws : List W}, a + 4 * ws.length ≤ x →
    writeWords mem a ws x = mem x
  | _, [], _ => rfl
  | mem, w :: ws, h => by
    simp only [writeWords, List.length_cons] at h ⊢
    rw [writeWords_ge (by omega)]
    simp [upd]; omega

theorem writeWords_at {a : Nat} : ∀ {mem : Nat → W} {ws : List W} {j : Nat} (h : j < ws.length),
    writeWords mem a ws (a + 4 * j) = ws[j]
  | _, [], _, h => by simp at h
  | mem, w :: ws, 0, _ => by
    simp only [writeWords, Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero]
    rw [writeWords_lt (by omega)]
    simp [upd]
  | mem, w :: ws, j + 1, h => by
    simp only [writeWords, List.getElem_cons_succ]
    have := writeWords_at (a := a + 4) (mem := upd mem a w) (ws := ws) (j := j)
      (by simp at h; omega)
    rw [show a + 4 * (j + 1) = a + 4 + 4 * j by omega]
    exact this

theorem writeWords_append {a : Nat} : ∀ {mem : Nat → W} {ws vs : List W},
    writeWords mem a (ws ++ vs) = writeWords (writeWords mem a ws) (a + 4 * ws.length) vs
  | _, [], _ => by simp [writeWords]
  | mem, w :: ws, vs => by
    simp only [List.cons_append, writeWords, List.length_cons]
    rw [writeWords_append (a := a + 4)]
    congr 1
    omega

/-! ## Segments -/

theorem runSeg_append : ∀ (a b : List Instr) (s : LS),
    runSeg (a ++ b) s = (runSeg a s).bind (runSeg b)
  | [], b, s => by simp [runSeg]
  | i :: a, b, s => by
    simp only [List.cons_append, runSeg]
    cases segStep i s with
    | none => rfl
    | some s1 => simp only [Option.bind_some]; exact runSeg_append a b s1

/-- `n` words of `mem` from byte address `a`. -/
def readWords (mem : Nat → W) (a : Nat) (n : Nat) : List W :=
  (List.range n).map fun j => mem (a + 4 * j)

theorem readWords_writeWords {mem : Nat → W} {a : Nat} {ws : List W} :
    readWords (writeWords mem a ws) a ws.length = ws := by
  apply List.ext_getElem (by simp [readWords])
  intro j h1 h2
  simp only [readWords, List.getElem_map, List.getElem_range]
  exact writeWords_at h2

theorem saveLocals_seg {ls ops gs : List W} {sp : W} (hsp : gs[1]? = some sp) :
    ∀ {i n : Nat} {mem : Nat → W}, i + n ≤ ls.length → 4 * (i + n) < 2 ^ 32 →
    runSeg (saveLocals i n) ⟨ls, ops, gs, mem⟩ =
      some ⟨ls, ops, gs, writeWords mem (sp.toNat + 4 * i) ((ls.drop i).take n)⟩
  | i, 0, mem, _, _ => by simp [saveLocals, runSeg, writeWords]
  | i, n + 1, mem, h1, h2 => by
    simp only [saveLocals, runSeg_append]
    have hi : i < ls.length := by omega
    have h3 : 4 * (i + 1 + n) < 2 ^ 32 := by omega
    have h4 : i + 1 + n ≤ ls.length := by omega
    have hseg : runSeg [gSp, .localGet (lidx i), st (4 * i)] ⟨ls, ops, gs, mem⟩ =
        some ⟨ls, ops, gs, upd mem (sp.toNat + 4 * i) ls[i]⟩ := by
      simp [runSeg, segStep, ctlOf, segCore, gSp, st, pexec, hsp, lidx_val (show i < 2 ^ 32 by omega),
        marg_off (show 4 * i < 2 ^ 64 by omega), hi]
    rw [hseg, Option.bind_some, saveLocals_seg hsp (i := i + 1) (n := n) (mem := upd mem (sp.toNat + 4 * i) ls[i]) h4 h3]
    have hd : (ls.drop i).take (n + 1) = ls[i] :: (ls.drop (i + 1)).take n := by
      rw [List.drop_eq_getElem_cons hi]; rfl
    rw [hd, writeWords, show sp.toNat + 4 * i + 4 = sp.toNat + 4 * (i + 1) by omega]

theorem readWords_succ (mem : Nat → W) (a n : Nat) :
    readWords mem a (n + 1) = mem a :: readWords mem (a + 4) n := by
  simp only [readWords, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.mul_zero,
    Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp]
  congr 1; omega

theorem take_set_succ {v : W} : ∀ {l : List W} {i : Nat}, i < l.length →
    (l.set i v).take (i + 1) = l.take i ++ [v]
  | [], _, h => by simp at h
  | x :: xs, 0, _ => by simp
  | x :: xs, i + 1, h => by
    simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append]
    rw [take_set_succ (by simp at h; omega)]

theorem loadLocals_seg {ops gs : List W} {sp : W} {mem : Nat → W} (hsp : gs[1]? = some sp) :
    ∀ {i n : Nat} {ls : List W}, i + n = ls.length → 4 * (i + n) < 2 ^ 32 →
    runSeg (loadLocals i n) ⟨ls, ops, gs, mem⟩ =
      some ⟨ls.take i ++ readWords mem (sp.toNat + 4 * i) n, ops, gs, mem⟩
  | i, 0, ls, h1, _ => by simp [loadLocals, runSeg, readWords, ← h1]
  | i, n + 1, ls, h1, h2 => by
    simp only [loadLocals, runSeg_append]
    have hi : i < ls.length := by omega
    have h3 : 4 * (i + 1 + n) < 2 ^ 32 := by omega
    have h4 : i + 1 + n = (ls.set i (mem (sp.toNat + 4 * i))).length := by
      rw [List.length_set]; omega
    have hseg : runSeg [gSp, ld (4 * i), .localSet (lidx i)] ⟨ls, ops, gs, mem⟩ =
        some ⟨ls.set i (mem (sp.toNat + 4 * i)), ops, gs, mem⟩ := by
      simp [runSeg, segStep, ctlOf, segCore, gSp, ld, pexec, hsp, lidx_val (show i < 2 ^ 32 by omega),
        marg_off (show 4 * i < 2 ^ 64 by omega), hi]
    rw [hseg, Option.bind_some, loadLocals_seg hsp (i := i + 1) (n := n) (ls := ls.set i (mem (sp.toNat + 4 * i))) h4 h3]
    rw [take_set_succ hi, readWords_succ, List.append_assoc, List.singleton_append,
      show sp.toNat + 4 * i + 4 = sp.toNat + 4 * (i + 1) by omega]

theorem pushAns_seg {ls gs : List W} {mem : Nat → W} :
    ∀ {j m : Nat} {ops : List W}, 4 * (j + m) < 2 ^ 32 →
    runSeg (pushAns j m) ⟨ls, ops, gs, mem⟩ =
      some ⟨ls, (readWords mem (4 * j) m).reverse ++ ops, gs, mem⟩
  | j, 0, ops, _ => by simp [pushAns, runSeg, readWords]
  | j, m + 1, ops, h => by
    simp only [pushAns, runSeg_append]
    have hseg : runSeg [c32 0, ld (4 * j)] ⟨ls, ops, gs, mem⟩ =
        some ⟨ls, mem (4 * j) :: ops, gs, mem⟩ := by
      simp [runSeg, segStep, ctlOf, segCore, c32, ld, pexec,
        marg_off (show 4 * j < 2 ^ 64 by omega)]
    rw [hseg, Option.bind_some, pushAns_seg (j := j + 1) (m := m) (ops := mem (4 * j) :: ops) (by omega)]
    rw [readWords_succ, List.reverse_cons, List.append_assoc, List.singleton_append,
      show 4 * j + 4 = 4 * (j + 1) by omega]

/-- The value of local `a` (zero when out of range). -/
def lv (ls : List W) (a : LocalIdx) : W := ls.getD a.value.val 0

theorem reqArgs_seg {ls ops gs : List W} :
    ∀ {j : Nat} {as : List LocalIdx} {mem : Nat → W}, 4 * (j + as.length) < 2 ^ 32 →
    (∀ a ∈ as, a.value.val < ls.length) →
    runSeg (reqArgs j as) ⟨ls, ops, gs, mem⟩ =
      some ⟨ls, ops, gs, writeWords mem (4 * j) (as.map (lv ls))⟩
  | j, [], mem, _, _ => by simp [reqArgs, runSeg, writeWords]
  | j, a :: as, mem, h, ha => by
    simp only [reqArgs, runSeg_append]
    have hal : a.value.val < ls.length := ha a (by simp)
    have hseg : runSeg [c32 0, .localGet a, st (4 * j)] ⟨ls, ops, gs, mem⟩ =
        some ⟨ls, ops, gs, upd mem (4 * j) (lv ls a)⟩ := by
      simp [runSeg, segStep, ctlOf, segCore, c32, st, pexec, hal, lv,
        marg_off (show 4 * j < 2 ^ 64 by simp at h; omega)]
    rw [hseg, Option.bind_some, reqArgs_seg (ls := ls) (ops := ops) (gs := gs) (j := j + 1) (as := as)
      (mem := upd mem (4 * j) (lv ls a)) (by simp at h ⊢; omega)
      (fun b hb => ha b (by simp [hb]))]
    simp only [List.map_cons, writeWords]
    rw [show 4 * j + 4 = 4 * (j + 1) by omega]

theorem dummies_seg {ls ops gs : List W} {mem : Nat → W} (n : Nat) :
    runSeg (dummies n) ⟨ls, ops, gs, mem⟩ = some ⟨ls, List.replicate n 0 ++ ops, gs, mem⟩ := by
  induction n generalizing ops with
  | zero => simp [dummies, runSeg]
  | succ n ih =>
    simp only [dummies, List.replicate_succ, runSeg]
    have : segStep (c32 0) ⟨ls, ops, gs, mem⟩ = some ⟨ls, 0 :: ops, gs, mem⟩ := by
      simp [segStep, ctlOf, segCore, c32, pexec]
    rw [this, Option.bind_some]
    have := ih (ops := 0 :: ops)
    simp only [dummies] at this
    rw [this]
    rw [← List.singleton_append, ← List.append_assoc, ← List.replicate_succ', List.replicate_succ,
      List.cons_append]

theorem getsCode_seg {ls gs : List W} {mem : Nat → W} :
    ∀ {as : List LocalIdx} {ops : List W}, (∀ a ∈ as, a.value.val < ls.length) →
    runSeg (getsCode as) ⟨ls, ops, gs, mem⟩ =
      some ⟨ls, (as.map (lv ls)).reverse ++ ops, gs, mem⟩
  | [], ops, _ => by simp [getsCode, runSeg]
  | a :: as, ops, ha => by
    have hal : a.value.val < ls.length := ha a (by simp)
    simp only [getsCode, List.map_cons, runSeg]
    have : segStep (.localGet a) ⟨ls, ops, gs, mem⟩ = some ⟨ls, lv ls a :: ops, gs, mem⟩ := by
      simp [segStep, ctlOf, segCore, pexec, hal, lv]
    rw [this, Option.bind_some]
    have := getsCode_seg (ls := ls) (gs := gs) (mem := mem) (as := as) (ops := lv ls a :: ops) (fun b hb => ha b (by simp [hb]))
    simp only [getsCode] at this
    rw [this]
    simp

end Silmaril.Wasm.FX.Asyncify.Tool
