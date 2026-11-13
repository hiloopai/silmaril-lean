module

public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Mem
public import Silmaril.Wasm.JcoTool.KCoreCore.Thms

/-!
# Expressions of the fragment on Core 3.0

`cev_eval`: the checked value is `E.eval`. `expr_run`: under `Rel`, an expression whose checked
value is `v` runs, as the instructions `KCoreEmit.eCode e`, from any operand stack and under
any code after it, to the stack with `i32 v` pushed (`v < 2 ^ 32`), leaving store and frame
unchanged. The operators are `KCoreCore.bin_core` (the fragment's operators on Core `i32`s).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (E Bin BI M32)
open Silmaril.Wasm.JcoTool.KDrop (DSt)
open Silmaril.Wasm.JcoTool.KCoreEmit (ix eCode binInstr c32)
open Silmaril.Wasm.FX.Asyncify.Tool (W stackA pexec gidx)

variable {H : Type} {Pf : Profile} {hb : BI → H} {ma : Nat}

theorem binInstr_core (o : Bin) : binInstr o = o.core := by cases o <;> rfl

theorem binop_ok {op : IntBinOp} {x y r : W}
    (h : pexec (.intBinOp .i32 op) [] [y, x] = some ([], [r])) :
    Numerics.intBinOp .i32 op x y = .ok r := by
  simp only [pexec] at h
  cases hc : Numerics.intBinOp .i32 op x y with
  | error e => rw [hc] at h; cases h
  | ok z => rw [hc] at h; cases h; rfl

theorem relop_val {op : IntRelOp} {x y r : W}
    (h : pexec (.intRelOp .i32 op) [] [y, x] = some ([], [r])) : Numerics.intRelOp .i32 op x y = r := by
  simp [pexec] at h
  exact h

theorem relop_step {op : IntRelOp} {x y r : W}
    (h : pexec (.intRelOp .i32 op) [] [y, x] = some ([], [r])) :
    NumericStep Pf [(Val.i32 x).toAdmin, (Val.i32 y).toAdmin, .plain (.intRelOp .i32 op)]
      [(Val.i32 r).toAdmin] := by
  have e := relop_val h
  subst e
  exact .intRelOp

/-- **The fragment's binary operators as Core numeric steps** (nonzero divisors). -/
theorem bin_step (o : Bin) {a b : Nat} (ha : a < M32) (hb' : b < M32)
    (hd : (o = .divu ∨ o = .remu) → b ≠ 0) :
    NumericStep Pf [(Val.i32 (w a)).toAdmin, (Val.i32 (w b)).toAdmin, .plain (binInstr o)]
      [(Val.i32 (w (o.eval a b))).toAdmin] := by
  have h := Silmaril.Wasm.JcoTool.KCoreCore.bin_core o ha hb' hd [] []
  cases o
  · exact .intBinOp (binop_ok h)
  · exact .intBinOp (binop_ok h)
  · exact relop_step h
  · exact relop_step h
  · exact relop_step h
  · exact relop_step h
  · exact .intBinOp (binop_ok h)
  · exact .intBinOp (binop_ok h)
  · exact .intBinOp (binop_ok h)

theorem eqz_step {a : Nat} (ha : a < M32) :
    NumericStep Pf [(Val.i32 (w a)).toAdmin, .plain (.intTestOp .i32 .eqz)]
      [(Val.i32 (w (if a = 0 then 1 else 0))).toAdmin] := by
  have e : Numerics.intTestOp .i32 .eqz (w a) = w (if a = 0 then 1 else 0) := by
    show Numerics.bool32 (w a == 0) = _
    by_cases h : a = 0
    · subst h; rfl
    · have hne : (w a == 0) = false := by
        rw [beq_eq_false_iff_ne]
        intro h'
        have := congrArg BitVec.toNat h'
        rw [w_toNat ha] at this
        exact h this
      rw [hne]
      simp only [h, ↓reduceIte]
      rfl
  rw [← e]
  exact .intTestOp

/-! ## Checked values -/

theorem cev_bin {nl : Nat} {s : DSt} {o : Bin} {a b : E} {v : Nat}
    (h : cev nl s (.bin o a b) = some v) :
    ∃ x y, cev nl s a = some x ∧ cev nl s b = some y ∧ ¬ ((o = .divu ∨ o = .remu) ∧ y = 0) ∧
      v = o.eval x y := by
  simp only [cev] at h
  cases ha : cev nl s a with
  | none => rw [ha] at h; cases h
  | some x =>
    cases hb : cev nl s b with
    | none => rw [ha, hb] at h; cases h
    | some y =>
      rw [ha, hb] at h
      simp only [bind, Option.bind] at h
      split at h
      · cases h
      · rename_i hc
        exact ⟨x, y, rfl, rfl, hc, (Option.some.inj h).symm⟩

theorem cev_ld8 {nl : Nat} {s : DSt} {a : E} {v : Nat} (h : cev nl s (.ld8 a) = some v) :
    ∃ x, cev nl s a = some x ∧ x < MSZ ∧ v = s.m x := by
  simp only [cev] at h
  cases ha : cev nl s a with
  | none => rw [ha] at h; cases h
  | some x =>
    rw [ha] at h
    simp only [bind, Option.bind] at h
    split at h
    · exact ⟨x, rfl, by assumption, (Option.some.inj h).symm⟩
    · cases h

/-- **The checked value is `E.eval`.** -/
theorem cev_eval {nl : Nat} {s : DSt} : ∀ (e : E) {v : Nat}, cev nl s e = some v → v = e.eval s.down
  | .c n, v, h => by simp only [cev, Option.some.injEq] at h; rw [← h]; rfl
  | .l i, v, h => by
    simp only [cev] at h
    split at h
    · rw [← Option.some.inj h]; rfl
    · cases h
  | .g i, v, h => by
    simp only [cev] at h
    split at h
    · rw [← Option.some.inj h]; rfl
    · cases h
  | .bin o a b, v, h => by
    obtain ⟨x, y, hx, hy, -, rfl⟩ := cev_bin h
    rw [cev_eval a hx, cev_eval b hy]
    rfl
  | .eqz a, v, h => by
    simp only [cev] at h
    cases ha : cev nl s a with
    | none => rw [ha] at h; cases h
    | some x =>
      rw [ha] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [← h, cev_eval a ha]
      rfl
  | .ld8 a, v, h => by
    obtain ⟨x, hx, -, rfl⟩ := cev_ld8 h
    rw [cev_eval a hx]
    rfl

/-! ## The run of an expression -/

theorem _root_.Silmaril.Wasm.JcoTool.KCoreRun.Rel.memR {nl : Nat} {cs : Store H} {F : Frame} {s : DSt} (h : Rel hb nl ma cs F s) :
    MemR cs F ma s.m :=
  h.mem

theorem c32_eq (n : Nat) : c32 n = .intConst .i32 (w (n % M32)) := by
  have e : BitVec.ofNat 32 n = w (n % M32) := by
    apply BitVec.eq_of_toNat_eq
    simp [w, M32]
  simp only [c32, e]

theorem ix_toNat {k : IndexKind} {i : Nat} (hi : i < M32) : (ix (k := k) i).toNat = i :=
  Nat.mod_eq_of_lt hi

theorem bin_lt (o : Bin) {a : Nat} (b : Nat) (ha : a < M32) : o.eval a b < M32 := by
  have hM : 0 < M32 := by decide
  cases o with
  | add => exact Nat.mod_lt _ hM
  | sub => exact Nat.mod_lt _ hM
  | eq => simp only [Bin.eval]; split <;> decide
  | ne => simp only [Bin.eval]; split <;> decide
  | ltu => simp only [Bin.eval]; split <;> decide
  | geu => simp only [Bin.eval]; split <;> decide
  | divu => exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
  | remu => exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha
  | shl => exact Nat.mod_lt _ hM

/-- The run of compiled code pushing `v`, from any stack and under any code. -/
def ERuns (Pf : Profile) (hb : BI → H) (ma : Nat) (q : HQ) (cs : Store H) (F : Frame)
    (code : List Instr) (v : Nat) : Prop :=
  ∀ (ops : List W) (rest : List Admin),
    HSteps Pf hb ma (q, ⟨cs, F, stackA ops ++ (code.map Admin.plain ++ rest)⟩)
      (q, ⟨cs, F, stackA (w v :: ops) ++ rest⟩)

theorem eruns_snoc {q : HQ} {cs : Store H} {F : Frame} {code : List Instr} {x : Nat} {i : Instr}
    {v : Nat} (hc : ERuns Pf hb ma q cs F code x)
    (hi : ∀ (ops : List W) (rest : List Admin),
      HSteps Pf hb ma (q, ⟨cs, F, stackA (w x :: ops) ++ .plain i :: rest⟩)
        (q, ⟨cs, F, stackA (w v :: ops) ++ rest⟩)) :
    ERuns Pf hb ma q cs F (code ++ [i]) v := by
  intro ops rest
  have e : (code ++ [i]).map Admin.plain ++ rest = code.map Admin.plain ++ (.plain i :: rest) := by
    simp
  rw [e]
  exact (hc ops _).trans (hi ops rest)

/-- **A compiled expression runs to its checked value** under `Rel`. -/
theorem expr_run {nl : Nat} {q : HQ} {cs : Store H} {F : Frame} {s : DSt}
    (h : Rel hb nl ma cs F s) :
    ∀ (e : E) {v : Nat}, cev nl s e = some v → v < M32 ∧ ERuns Pf hb ma q cs F (eCode e) v
  | .c n, v, hv => by
    simp only [cev, Option.some.injEq] at hv
    subst hv
    refine ⟨Nat.mod_lt _ (by decide), fun ops rest => ?_⟩
    show HSteps Pf hb ma (q, ⟨cs, F, stackA ops ++ (Admin.plain (c32 n) :: rest)⟩) _
    rw [c32_eq, const_val]
  | .l i, v, hv => by
    simp only [cev] at hv
    split at hv
    · rename_i hi
      cases hv
      obtain ⟨hl, hlt⟩ := h.loc i hi
      refine ⟨hlt, fun ops rest => ?_⟩
      have hx : F.local? (ix i) = some (some (Val.i32 (w (s.l i)))) := by
        simp only [Frame.local?, ix_toNat (Nat.lt_of_lt_of_le hi h.nl32), hl]
      exact r_lget hx ops rest
    · cases hv
  | .g i, v, hv => by
    simp only [cev] at hv
    split at hv
    · rename_i hi
      cases hv
      refine ⟨h.glt i hi, fun ops rest => ?_⟩
      have hlen : i < (gsOf s.g).length := by simp [gsOf, hi]
      obtain ⟨a, gi, hga, hgv, -⟩ := h.glob.2.1 i hlen
      have hgi : (gsOf s.g)[i] = w (s.g i) := by simp [gsOf]
      rw [hgi] at hgv
      exact r_gget hga hgv ops rest
    · cases hv
  | .bin o a b, v, hv => by
    obtain ⟨x, y, hx, hy, hd, rfl⟩ := cev_bin hv
    obtain ⟨hxl, rx⟩ := expr_run h a hx
    obtain ⟨hyl, ry⟩ := expr_run h b hy
    refine ⟨bin_lt o y hxl, ?_⟩
    have hd' : (o = .divu ∨ o = .remu) → y ≠ 0 := fun ho hy0 => hd ⟨ho, hy0⟩
    intro ops rest
    have e : (eCode a ++ eCode b ++ [binInstr o]).map Admin.plain ++ rest =
        (eCode a).map Admin.plain ++ ((eCode b).map Admin.plain ++ (.plain (binInstr o) :: rest)) := by
      simp
    show HSteps Pf hb ma (q, ⟨cs, F, stackA ops ++ ((eCode a ++ eCode b ++ [binInstr o]).map Admin.plain ++ rest)⟩) _
    rw [e]
    exact (rx ops _).trans ((ry (w x :: ops) _).trans (r_binop ops rest (bin_step o hxl hyl hd')))
  | .eqz a, v, hv => by
    simp only [cev] at hv
    cases ha : cev nl s a with
    | none => rw [ha] at hv; cases hv
    | some x =>
      rw [ha] at hv
      simp only [Option.map_some, Option.some.injEq] at hv
      subst hv
      obtain ⟨hxl, rx⟩ := expr_run h a ha
      refine ⟨by split <;> decide, ?_⟩
      exact eruns_snoc rx fun ops rest => r_unop ops rest (eqz_step hxl)
  | .ld8 a, v, hv => by
    obtain ⟨x, hx, hxm, rfl⟩ := cev_ld8 hv
    obtain ⟨hxl, rx⟩ := expr_run h a hx
    refine ⟨Nat.lt_of_lt_of_le (h.memR.byte_lt hxm) (by decide), ?_⟩
    exact eruns_snoc rx fun ops rest => memR_load h.memR rfl hxm ops rest

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun
