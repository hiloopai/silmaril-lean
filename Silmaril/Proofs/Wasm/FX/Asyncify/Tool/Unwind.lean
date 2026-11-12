module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Call

/-!
# Unwinding: every waiting frame saves its record and returns

New proofs (moved from `Silmaril/Raw/Wasm/FX/Asyncify/Tool/Unwind.lean` and restyled: one waiting
frame is `unwind_wait`, the chain is an induction over it).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-- The record saved for a frame waiting on statement `k`: its first `F - 1` locals, then `k`. -/
def recOf (F k : Nat) (tl : List W) : List W := tl.take (F - 1) ++ [BitVec.ofNat 32 k]

/-- The records of waiting frames. -/
def recs (F : Nat) : List Nat → List Frame → List (List W)
  | k :: ks, w :: ws => recOf F k w.locals :: recs F ks ws
  | _, _ => []

/-- Write records of `F` words at `a, a + 4F, …`. -/
def writeRecs (F : Nat) (mem : Nat → W) (a : Nat) : List (List W) → Nat → W
  | [] => mem
  | r :: rs => writeRecs F (writeWords mem a r) (a + 4 * F) rs

theorem recOf_length {F k : Nat} {tl : List W} (h : tl.length = F) (hF : 1 ≤ F) :
    (recOf F k tl).length = F := by
  simp [recOf, h]; omega

/-- The index of a call statement fits in 31 bits. -/
theorem FnOk.pre_lt {P : Prog} {fn : FnSrc} (hok : FnOk P fn) {pre rest : List Stmt} {s : Stmt}
    (hst : fn.stmts = pre ++ s :: rest) : pre.length < 2 ^ 31 := by
  have hlen : fn.stmts.length = pre.length + (rest.length + 1) := by rw [hst]; simp
  have := hok.nstmts
  omega

theorem saveCode_seg {F k a : Nat} {tl ops : List W} {g0 : W} {mem : Nat → W}
    (hl : tl.length = F) (hF : 1 ≤ F) (ha : a + 4 * F < 2 ^ 32) (_hk : k < 2 ^ 32) :
    runSeg (saveCode F k) ⟨tl, ops, [g0, BitVec.ofNat 32 a], mem⟩ =
      some ⟨tl, ops, [g0, BitVec.ofNat 32 (a + 4 * F)], writeWords mem a (recOf F k tl)⟩ := by
  have hsp : ([g0, BitVec.ofNat 32 a] : List W)[1]? = some (BitVec.ofNat 32 a) := rfl
  have hta : (BitVec.ofNat 32 a).toNat = a := toNat_ofNat32 (by omega)
  unfold saveCode
  rw [runSeg_append, saveLocals_seg hsp (by omega) (by omega), Option.bind_some, hta]
  simp only [Nat.mul_zero, Nat.add_zero, List.drop_zero]
  have hseg : runSeg [gSp, c32 k, st (4 * (F - 1)), gSp, c32 (4 * F), addI, sSp]
      ⟨tl, ops, [g0, BitVec.ofNat 32 a], writeWords mem a (tl.take (F - 1))⟩ =
      some ⟨tl, ops, [g0, BitVec.ofNat 32 (a + 4 * F)],
        upd (writeWords mem a (tl.take (F - 1))) (a + 4 * (F - 1)) (BitVec.ofNat 32 k)⟩ := by
    have hadd : BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * F) = BitVec.ofNat 32 (a + 4 * F) :=
      BitVec.ofNat_add_ofNat _ _
    simp [runSeg, segStep, ctlOf, segCore, gSp, sSp, c32, st, addI, pexec, Numerics.intBinOp,
      hta, marg_off (show 4 * (F - 1) < 2 ^ 64 by omega)]
    rw [← hadd]; rfl
  rw [hseg]
  congr 2
  rw [recOf, writeWords_append, List.length_take, hl, Nat.min_eq_left (by omega)]
  rfl

theorem addr_le (a F n : Nat) : a + 4 * F ≤ a + 4 * F * (n + 1) := by
  rw [Nat.mul_add, Nat.mul_one]; omega

theorem addr_step (a F n : Nat) : a + 4 * F + 4 * F * n = a + 4 * F * (n + 1) := by
  rw [Nat.mul_add, Nat.mul_one]; omega

theorem seg_chk_unwind (ls ops : List W) (sp : W) (m : Nat → W) :
    runSeg [gState, c32 1, eqI] ⟨ls, ops, [1, sp], m⟩ = some ⟨ls, 1 :: ops, [1, sp], m⟩ := rfl

theorem ret_cons {c : Cfg} {vs : List W} {w : Frame} {ws : List Frame} :
    ret c vs (w :: ws) = .next { c with frames := { w with ops := vs ++ w.ops } :: ws } := rfl

theorem step_return {E : Env} {c : Cfg} {fr : Frame} {rest : List Frame} {K : List Instr}
    (hf : c.frames = fr :: rest) (hcode : fr.code = .return_ :: K) :
    step E c = ret c (fr.ops.take fr.nres) rest := by
  simp [step, hf, hcode, exec, ctlOf]

/-- One waiting frame unwinds: the frame above returns into its call-site check, which saves the
frame's record at `a` and reaches the frame's own `return`. -/
theorem unwind_wait {P : Prog} (hP : P.WF) {fid : Nat} {fn : FnSrc} {sl tl : List W}
    {pre rest : List Stmt} {f : FuncIdx} {as rs : List LocalIdx} (hfn : P.fnAt fid = some fn)
    (hloc : LocR P fn sl tl) (hst : fn.stmts = pre ++ Stmt.call f as rs :: rest)
    {fr : Frame} {K : List Instr} {ts : List Frame} {mem : Nat → W} {a : Nat}
    (hcode : fr.code = .return_ :: K) (ha : a + 4 * P.frameWords < 2 ^ 32) :
    Steps (asyncifyProg P)
      (1 + ((3 + 1) + (saveCode P.frameWords pre.length ++ dummies fn.nres).length))
      ⟨fr :: ⟨fid, tl, [], chk P.frameWords pre.length fn.nres ++ setsCode rs ++
          trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: ts,
        [1, BitVec.ofNat 32 a], mem⟩
      ⟨⟨fid, tl, List.replicate fn.nres 0 ++ (fr.ops.take fr.nres ++ []),
          .return_ :: (setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail),
          fn.nres⟩ :: ts,
        [1, BitVec.ofNat 32 (a + 4 * P.frameWords)],
        writeWords mem a (recOf P.frameWords pre.length tl)⟩ := by
  have hok : FnOk P fn := Prog.fnOk hP hfn
  have htl : tl.length = P.frameWords := hloc.len hok.nloc
  have hk : pre.length < 2 ^ 32 := by have := hok.pre_lt hst; omega
  have hF : 1 ≤ P.frameWords := by have := hok.nloc; omega
  let K' := setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail
  let ops := fr.ops.take fr.nres ++ []
  let save := saveCode P.frameWords pre.length ++ dummies fn.nres
  have e1 : step (asyncifyProg P) ⟨fr :: ⟨fid, tl, [], chk P.frameWords pre.length fn.nres ++
      setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: ts,
      [1, BitVec.ofNat 32 a], mem⟩ = .next ⟨⟨fid, tl, ops, chk P.frameWords pre.length fn.nres ++
        setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: ts,
        [1, BitVec.ofNat 32 a], mem⟩ := by
    rw [step_return rfl hcode, ret_cons]
  have m2 : Steps (asyncifyProg P) (3 + 1)
      ⟨⟨fid, tl, ops, chk P.frameWords pre.length fn.nres ++ setsCode rs ++
        trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail, fn.nres⟩ :: ts, [1, BitVec.ofNat 32 a], mem⟩
      ⟨⟨fid, tl, ops, save ++ .return_ :: K', fn.nres⟩ :: ts, [1, BitVec.ofNat 32 a], mem⟩ := by
    have e2 := steps_guard (E := asyncifyProg P) (fr := ⟨fid, tl, ops, [], fn.nres⟩) (rest := ts)
      (t := save ++ [.return_]) (K := K') (seg_chk_unwind tl ops (BitVec.ofNat 32 a) mem)
    simpa [chk, ifThen, save, K', List.append_assoc] using e2
  have m3 : Steps (asyncifyProg P) save.length
      ⟨⟨fid, tl, ops, save ++ .return_ :: K', fn.nres⟩ :: ts, [1, BitVec.ofNat 32 a], mem⟩
      ⟨⟨fid, tl, List.replicate fn.nres 0 ++ ops, .return_ :: K', fn.nres⟩ :: ts,
        [1, BitVec.ofNat 32 (a + 4 * P.frameWords)],
        writeWords mem a (recOf P.frameWords pre.length tl)⟩ := by
    have e3 := steps_seg (E := asyncifyProg P) (fr := ⟨fid, tl, ops, [], fn.nres⟩) (rest := ts)
      (code := .return_ :: K') (g := [1, BitVec.ofNat 32 a]) (m := mem)
      (show runSeg save _ = _ by
        rw [runSeg_append, saveCode_seg (a := a) htl hF ha hk, Option.bind_some, dummies_seg])
    simpa using e3
  exact (Steps.one e1).trans (m2.trans m3)

/-- Unwinding a chain of waiting frames from a frame about to `return`: the records are written
at `a, a + 4F, …` and the export returns with `state = 1`. -/
theorem unwind {P : Prog} (hP : P.WF) {above e : Nat} {ks : List Nat} {sw tw : List Frame}
    (hch : Chain P above e ks sw tw) :
    ∀ (fr : Frame) (K : List Instr) (mem : Nat → W) (a : Nat), fr.code = .return_ :: K →
      fr.nres ≤ fr.ops.length → a + 4 * P.frameWords * tw.length < 2 ^ 32 →
      ∃ n c vs, Steps (asyncifyProg P) n ⟨fr :: tw, [1, BitVec.ofNat 32 a], mem⟩ c ∧
        step (asyncifyProg P) c = .done vs ⟨[], [1, BitVec.ofNat 32 (a + 4 * P.frameWords * tw.length)],
          writeRecs P.frameWords mem a (recs P.frameWords ks tw)⟩ := by
  induction hch with
  | nil e =>
    intro fr K mem a hcode _ _
    refine ⟨0, _, fr.ops.take fr.nres, .refl _, ?_⟩
    rw [step_return rfl hcode]
    simp [ret, recs, writeRecs]
  | @cons _ _ _ _ _ _ _ ts hw _ ih =>
    intro fr K mem a hcode _ hb
    cases hw with
    | @mk fid fn sl tl pre rest f as rs hfn hloc hst _ =>
      have hb' : a + 4 * P.frameWords + 4 * P.frameWords * ts.length < 2 ^ 32 := by
        rw [addr_step]; simpa using hb
      have hw1 := unwind_wait hP hfn hloc hst (ts := ts) (mem := mem) (a := a) hcode (by omega)
      obtain ⟨n, c, vs, hs, hd⟩ := ih ⟨fid, tl, List.replicate fn.nres 0 ++ (fr.ops.take fr.nres ++ []),
        .return_ :: (setsCode rs ++ trS (P.ctx fn) (pre.length + 1) rest ++ fn.tail), fn.nres⟩ _ _
        (a + 4 * P.frameWords) rfl (by simp) hb'
      refine ⟨_, c, vs, hw1.trans hs, ?_⟩
      rw [hd, List.length_cons, ← addr_step]
      rfl

end Silmaril.Wasm.FX.Asyncify.Tool
