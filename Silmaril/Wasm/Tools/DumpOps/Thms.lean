module

public import Silmaril.Wasm.Tools.DumpOps.Defs

/-!
# `wasm-tools dump`: the logging decoder is silmaril-lean's decoder

`dSeq_erase`: dropping the operator log of `dSeq` gives `Decode.readSeq`, and `dInstr_erase`:
dropping it from `dInstr` gives `Decode.readInstr`; `dExpr_erase`: likewise for `readExpr`.
So on every input the instructions (and the end position, and every error) of dump's
instruction walker are those of the certified decoder.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.DumpOps

open Silmaril Silmaril.Wasm Silmaril.Wasm.Binary.Core.Decode

theorem map_decodeError {α β : Type} (f : α → β) (msg : String) :
    f <$> (decodeError msg : DecodeM α) = decodeError msg := by
  apply StateT.ext; intro c
  simp [decodeError, StateT.run_map, StateT.run_bind, StateT.run_get]
  rfl

/-- Reading the position and ignoring it changes nothing. -/
theorem map_fst_curPos {α β : Type} (f : Nat → DecodeM (α × β)) (g : DecodeM α)
    (h : ∀ p, Prod.fst <$> f p = g) : Prod.fst <$> (curPos >>= f) = g := by
  apply StateT.ext; intro c
  have := congrArg (fun m => StateT.run m c) (h c.pos)
  simpa [curPos, StateT.run_bind, StateT.run_get, StateT.run_map] using this

/-- The `if` of a decoded terminator, after the log is dropped. -/
theorem map_fst_ite {α β : Type} (c : Bool) (a : α) (e : β) (msg : String) :
    Prod.fst <$> (if c = true then (pure (a, e) : DecodeM (α × β)) else decodeError msg) =
      (if c = true then pure a else decodeError msg) := by
  cases c <;> simp [map_decodeError]

/-- The `if` arm after its `then` branch, with the log dropped. -/
theorem if_tail (n : Nat) (bt : BlockType) (p : Nat) (thn : List Instr) (t : UInt8)
    (es : List Ev) :
    Prod.fst <$> (if (t == 0x0B) = true then
        (pure (.if_ bt thn [], ⟨blockText "if" bt, p⟩ :: es) : DecodeM (Instr × List Ev))
      else do
        let ((els, t'), es') ← dSeq n
        if (t' == 0x0B) = true then pure (.if_ bt thn els, ⟨blockText "if" bt, p⟩ :: (es ++ es'))
        else decodeError "second `else` in `if`") =
    (if (t == 0x0B) = true then pure (.if_ bt thn [])
      else do
        let (els, t') ← Prod.fst <$> dSeq n
        if (t' == 0x0B) = true then pure (.if_ bt thn els) else decodeError "second `else` in `if`") := by
  by_cases ht : (t == 0x0B) = true
  · simp [ht]
  · simp only [ht, Bool.false_eq_true, ite_false]
    rw [map_bind, bind_map_left]; refine bind_congr fun y => ?_
    obtain ⟨⟨els, t'⟩, es'⟩ := y
    exact map_fst_ite _ _ _ _

/-- One step of the induction for `dInstr`. -/
theorem instr_step (n : Nat) (ihS : Prod.fst <$> dSeq n = readSeq n) (op : Nat) :
    Prod.fst <$> dInstr (n + 1) op = readInstr (n + 1) op := by
  simp only [dInstr, readInstr, ← ihS]
  split
  · rw [map_bind]; refine bind_congr fun bt => map_fst_curPos _ _ fun p => ?_
    rw [map_bind, bind_map_left]; refine bind_congr fun ⟨⟨body, t⟩, es⟩ => ?_
    exact map_fst_ite _ _ _ _
  · rw [map_bind]; refine bind_congr fun bt => map_fst_curPos _ _ fun p => ?_
    rw [map_bind, bind_map_left]; refine bind_congr fun ⟨⟨body, t⟩, es⟩ => ?_
    exact map_fst_ite _ _ _ _
  · rw [map_bind]; refine bind_congr fun bt => map_fst_curPos _ _ fun p => ?_
    rw [map_bind, bind_map_left]; refine bind_congr fun ⟨⟨thn, t⟩, es⟩ => ?_
    exact if_tail n bt p thn t es
  · rw [map_bind]; refine bind_congr fun bt => ?_
    rw [map_bind]; refine bind_congr fun cs => map_fst_curPos _ _ fun p => ?_
    rw [map_bind, bind_map_left]; refine bind_congr fun ⟨⟨body, t⟩, es⟩ => ?_
    exact map_fst_ite _ _ _ _
  · split
    all_goals first
      | (simp_all; done)
      | (rw [map_bind]; conv => rhs; rw [← bind_pure (readPlain _)]
         exact bind_congr fun i => map_fst_curPos _ _ fun p => by simp)

/-- One step of the induction for `dSeq`. -/
theorem seq_step (n : Nat) (ihI : ∀ op, Prod.fst <$> dInstr n op = readInstr n op)
    (ihS : Prod.fst <$> dSeq n = readSeq n) :
    Prod.fst <$> dSeq (n + 1) = readSeq (n + 1) := by
  simp only [dSeq, readSeq]
  rw [map_bind]; refine bind_congr fun b => ?_
  split
  · exact map_fst_curPos _ _ fun p => by simp
  · rw [map_bind, ← ihI, bind_map_left]; refine bind_congr fun ⟨i, es⟩ => ?_
    rw [map_bind, ← ihS, bind_map_left]; refine bind_congr fun ⟨⟨rest, t⟩, es'⟩ => ?_
    simp

theorem erase (fuel : Nat) :
    (∀ op, Prod.fst <$> dInstr fuel op = readInstr fuel op) ∧
    (Prod.fst <$> dSeq fuel = readSeq fuel) := by
  induction fuel with
  | zero => exact ⟨fun op => by simp [dInstr, readInstr, map_decodeError],
      by simp [dSeq, readSeq, map_decodeError]⟩
  | succ n ih => exact ⟨instr_step n ih.2, seq_step n ih.1 ih.2⟩

theorem dInstr_erase (fuel op : Nat) : Prod.fst <$> dInstr fuel op = readInstr fuel op :=
  (erase fuel).1 op

theorem dSeq_erase (fuel : Nat) : Prod.fst <$> dSeq fuel = readSeq fuel :=
  (erase fuel).2

theorem dExpr_erase : Prod.fst <$> dExpr = readExpr := by
  simp only [dExpr, readExpr]
  rw [map_bind]; refine bind_congr fun r => ?_
  rw [map_bind, ← dSeq_erase, bind_map_left]; refine bind_congr fun x => ?_
  obtain ⟨⟨is, t⟩, es⟩ := x
  exact map_fst_ite _ _ _ _

end Silmaril.Wasm.Tools.DumpOps
