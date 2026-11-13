module

public import Silmaril.Wasm.JcoTool.KCoreCore.Defs
public import Silmaril.Wasm.FX.Asyncify.Tool.Core.Thms

/-!
# KCore expressions on Core 3.0: proofs

`eval_lt`: under `E.Fits` an expression's value is below `2 ^ 32`. `bin_pexec`, `eqz_pexec`:
each operator, on the `i32`s of values below `2 ^ 32`, is the `i32` of `Bin.eval` (division and
remainder by a nonzero divisor). `code_core`: the Core run of the compiled expression, by
induction, from `pure_core` and `global_get_core` of `Silmaril.Wasm.FX.Asyncify.Tool.Core`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreCore

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCore (E Bin St M32)
open Silmaril.Wasm.JcoTool.KCoreCore
open Silmaril.Wasm.FX.Asyncify.Tool (W gidx pexec stackA localsF GlobalsAre pure_core global_get_core)

/-- The `i32` of a number. -/
abbrev w (n : Nat) : W := BitVec.ofNat 32 n

theorem M32_eq : M32 = 2 ^ 32 := rfl

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
  | remu =>
    show a % b < M32
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha
  | shl => exact Nat.mod_lt _ hM

/-- The value of an expression that fits is an `i32`. -/
theorem eval_lt {s : St} {ls gs : List W} : ∀ {e : E}, e.Fits s ls gs → e.eval s < M32
  | .c n, _ => Nat.mod_lt _ (by decide)
  | .l _, h => h.2.2
  | .g _, h => h.2.2
  | .bin o _ _, h => bin_lt o _ (eval_lt h.1)
  | .eqz _, _ => by simp only [E.eval]; split <;> decide
  | .ld8 _, h => h.elim

theorem w_toNat {a : Nat} (ha : a < M32) : (w a).toNat = a := by
  simp only [w, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt ha

theorem w_inj {a b : Nat} (ha : a < M32) (hb : b < M32) : w a = w b ↔ a = b := by
  constructor
  · intro h
    rw [← w_toNat ha, ← w_toNat hb, h]
  · intro h
    rw [h]

theorem bool32_w (c : Prop) [Decidable c] :
    Numerics.bool32 (decide c) = w (if c then 1 else 0) := by
  by_cases hc : c <;> simp [hc, Numerics.bool32, w]

theorem add_w (a b : Nat) : w a + w b = w ((a + b) % M32) := by
  apply BitVec.eq_of_toNat_eq
  simp [w, BitVec.toNat_add, M32_eq]

theorem sub_w {a b : Nat} (ha : a < M32) (hb : b < M32) :
    w a - w b = w ((a + (M32 - b % M32)) % M32) := by
  apply BitVec.eq_of_toNat_eq
  have e : (w a - w b).toNat = (2 ^ 32 - b + a) % 2 ^ 32 := by
    rw [BitVec.toNat_sub, w_toNat ha, w_toNat hb]
  rw [e, w_toNat (Nat.mod_lt _ (by decide)), Nat.mod_eq_of_lt hb, Nat.add_comm, M32_eq]

theorem div_w {a b : Nat} (ha : a < M32) (hb : b < M32) : w a / w b = w (a / b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, w_toNat ha, w_toNat hb,
    w_toNat (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem rem_w {a b : Nat} (ha : a < M32) (hb : b < M32) : w a % w b = w (a % b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, w_toNat ha, w_toNat hb,
    w_toNat (Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha)]

theorem shl_w {a b : Nat} (ha : a < M32) (hb : b < M32) :
    w a <<< ((w b).toNat % 32) = w ((a * 2 ^ (b % 32)) % M32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, w_toNat ha, w_toNat hb, w_toNat (Nat.mod_lt _ (by decide)),
    Nat.shiftLeft_eq, M32_eq]

theorem pexec_bin_ok {op : IntBinOp} {x y r : W} (h : Numerics.intBinOp .i32 op x y = .ok r)
    (ls ops : List W) : pexec (.intBinOp .i32 op) ls (y :: x :: ops) = some (ls, r :: ops) := by
  simp only [pexec, h]

theorem pexec_rel (op : IntRelOp) (x y : W) (ls ops : List W) :
    pexec (.intRelOp .i32 op) ls (y :: x :: ops) = some (ls, Numerics.intRelOp .i32 op x y :: ops) :=
  rfl

theorem bool32_true : Numerics.bool32 true = w 1 := rfl

theorem bool32_false : Numerics.bool32 false = w 0 := rfl

theorem rel_core (o : Bin) {a b : Nat} (ha : a < M32) (hb : b < M32)
    (hr : o = .eq ∨ o = .ne ∨ o = .ltu ∨ o = .geu) (ls ops : List W) :
    pexec o.core ls (w b :: w a :: ops) = some (ls, w (o.eval a b) :: ops) := by
  have hab : (w a = w b) ↔ a = b := w_inj ha hb
  rcases hr with rfl | rfl | rfl | rfl
  · rw [Bin.core, pexec_rel]
    show some (ls, Numerics.bool32 (w a == w b) :: ops) = _
    by_cases h : a = b
    · have e : (w a == w b) = true := beq_iff_eq.mpr (hab.mpr h)
      rw [e, bool32_true, Bin.eval, ite_eq_left h]
    · have e : (w a == w b) = false := beq_eq_false_iff_ne.mpr fun h' => h (hab.mp h')
      rw [e, bool32_false, Bin.eval, ite_eq_right h]
  · rw [Bin.core, pexec_rel]
    show some (ls, Numerics.bool32 (w a != w b) :: ops) = _
    by_cases h : a = b
    · have e : (w a != w b) = false := by rw [bne_eq_false_iff_eq]; exact hab.mpr h
      rw [e, bool32_false, Bin.eval, ite_eq_left h]
    · have e : (w a != w b) = true := by rw [bne_iff_ne]; exact fun h' => h (hab.mp h')
      rw [e, bool32_true, Bin.eval, ite_eq_right h]
  · rw [Bin.core, pexec_rel]
    show some (ls, Numerics.bool32 (decide ((w a).toNat < (w b).toNat)) :: ops) = _
    rw [w_toNat ha, w_toNat hb, bool32_w]
    rfl
  · rw [Bin.core, pexec_rel]
    show some (ls, Numerics.bool32 (decide ((w a).toNat ≥ (w b).toNat)) :: ops) = _
    rw [w_toNat ha, w_toNat hb, bool32_w]
    rfl

/-- **An operator on Core `i32`s is `Bin.eval`.** -/
theorem bin_pexec (o : Bin) {a b : Nat} (ha : a < M32) (hb : b < M32)
    (hd : (o = .divu ∨ o = .remu) → b ≠ 0) (ls ops : List W) :
    pexec o.core ls (w b :: w a :: ops) = some (ls, w (o.eval a b) :: ops) := by
  have hwb : w b ≠ 0 ↔ b ≠ 0 := by
    have h0 : (0 : W) = w 0 := rfl
    rw [h0, Ne, Ne, w_inj hb (by decide)]
  cases o with
  | add =>
    have h : Numerics.intBinOp .i32 .add (w a) (w b) = .ok (w ((a + b) % M32)) := by
      show Except.ok (w a + w b) = _
      rw [add_w]
      rfl
    exact pexec_bin_ok h ls ops
  | sub =>
    have h : Numerics.intBinOp .i32 .sub (w a) (w b) = .ok (w ((a + (M32 - b % M32)) % M32)) := by
      show Except.ok (w a - w b) = _
      rw [sub_w ha hb]
      rfl
    exact pexec_bin_ok h ls ops
  | eq => exact rel_core .eq ha hb (.inl rfl) ls ops
  | ne => exact rel_core .ne ha hb (.inr (.inl rfl)) ls ops
  | ltu => exact rel_core .ltu ha hb (.inr (.inr (.inl rfl))) ls ops
  | geu => exact rel_core .geu ha hb (.inr (.inr (.inr rfl))) ls ops
  | divu =>
    show pexec Bin.divu.core ls (w b :: w a :: ops) = some (ls, w (Bin.divu.eval a b) :: ops)
    have hw0 : w b ≠ 0 := hwb.mpr (hd (.inl rfl))
    have h : Numerics.intBinOp .i32 (.div .unsigned) (w a) (w b) = .ok (w (a / b)) := by
      have hw0' : (w b : Numerics.IntValue .i32) ≠ 0 := hw0
      simp only [Numerics.intBinOp]
      split
      · exact absurd ‹_› hw0'
      show Except.ok (w a / w b) = _
      rw [div_w ha hb]
      rfl
    exact pexec_bin_ok h ls ops
  | remu =>
    show pexec Bin.remu.core ls (w b :: w a :: ops) = some (ls, w (Bin.remu.eval a b) :: ops)
    have hw0 : w b ≠ 0 := hwb.mpr (hd (.inr rfl))
    have h : Numerics.intBinOp .i32 (.rem .unsigned) (w a) (w b) = .ok (w (a % b)) := by
      have hw0' : (w b : Numerics.IntValue .i32) ≠ 0 := hw0
      simp only [Numerics.intBinOp]
      split
      · exact absurd ‹_› hw0'
      show Except.ok (w a % w b) = _
      rw [rem_w ha hb]
      rfl
    exact pexec_bin_ok h ls ops
  | shl =>
    have h : Numerics.intBinOp .i32 .shl (w a) (w b) = .ok (w ((a * 2 ^ (b % 32)) % M32)) := by
      show Except.ok (w a <<< ((w b).toNat % 32)) = _
      rw [shl_w ha hb]
      rfl
    exact pexec_bin_ok h ls ops

theorem eqz_pexec {a : Nat} (ha : a < M32) (ls ops : List W) :
    pexec (.intTestOp .i32 .eqz) ls (w a :: ops) = some (ls, w (if a = 0 then 1 else 0) :: ops) := by
  have h0 : (w a = 0) ↔ a = 0 := by
    have h0 : (0 : W) = w 0 := rfl
    rw [h0, w_inj ha (by decide)]
  show some (ls, Numerics.bool32 (w a == 0) :: ops) = _
  by_cases h : a = 0
  · rw [beq_iff_eq.mpr (h0.mpr h), bool32_true, ite_eq_left h]
  · rw [beq_eq_false_iff_ne.mpr fun h' => h (h0.mp h'), bool32_false, ite_eq_right h]

theorem const_pexec (n : Nat) (ls ops : List W) :
    pexec (.intConst .i32 (BitVec.ofNat 32 n)) ls ops = some (ls, w (n % M32) :: ops) := by
  have e : BitVec.ofNat 32 n = w (n % M32) := by
    apply BitVec.eq_of_toNat_eq
    simp [w, M32_eq]
  simp only [pexec, e]

theorem lget_pexec {i : Nat} (hi : i < 2 ^ 32) {ls : List W} {v : W} (h : ls[i]? = some v)
    (ops : List W) : pexec (.localGet (lidx i)) ls ops = some (ls, v :: ops) := by
  have hv : (lidx i).value.val = i := Nat.mod_eq_of_lt hi
  simp [pexec, hv, h]

theorem gidx_val {i : Nat} (hi : i < 2 ^ 32) : (gidx i).value.val = i := Nat.mod_eq_of_lt hi

variable {H : Type}

theorem bin_code {o : Bin} {a b : E} {code : List Instr}
    (h : (E.bin o a b).code? = some code) :
    ∃ ca cb, a.code? = some ca ∧ b.code? = some cb ∧ code = ca ++ cb ++ [o.core] := by
  cases ha : a.code? with
  | none => simp [E.code?, ha] at h
  | some ca =>
    cases hb : b.code? with
    | none => simp [E.code?, ha, hb] at h
    | some cb =>
      have hc : code = ca ++ cb ++ [o.core] := by
        simp only [E.code?, ha, hb, bind, Option.bind, pure, Option.some.injEq] at h
        exact h.symm
      exact ⟨ca, cb, rfl, rfl, hc⟩

theorem eqz_code {a : E} {code : List Instr} (h : (E.eqz a).code? = some code) :
    ∃ ca, a.code? = some ca ∧ code = ca ++ [Instr.intTestOp .i32 .eqz] := by
  cases ha : a.code? with
  | none => simp [E.code?, ha] at h
  | some ca =>
    have hc : code = ca ++ [Instr.intTestOp .i32 .eqz] := by
      simp only [E.code?, ha, Option.map_some, Option.some.injEq] at h
      exact h.symm
    exact ⟨ca, rfl, hc⟩

/-- The Core run of a compiled expression, in the form `stack ++ (code ++ rest)`. -/
def Runs (Pf : Profile) (host : HostSemantics H) (cs : Store H)
    (f : Silmaril.Wasm.Execution.Core.Frame) (ls : List W) (code : List Instr) (v : W) : Prop :=
  ∀ (ops : List W) (rest : List Admin),
    Steps Pf host ⟨cs, localsF f ls, stackA ops ++ (code.map Admin.plain ++ rest)⟩
      ⟨cs, localsF f ls, stackA (v :: ops) ++ rest⟩

theorem runs_one {Pf : Profile} {host : HostSemantics H} {cs : Store H}
    {f : Silmaril.Wasm.Execution.Core.Frame} {ls : List W} {i : Instr} {v : W}
    (h : ∀ ops, pexec i ls ops = some (ls, v :: ops)) : Runs Pf host cs f ls [i] v := by
  intro ops rest
  exact pure_core Pf host cs f (h ops) rest

/-- The run of a binary expression: the operands, then the operator. -/
theorem runs_bin {Pf : Profile} {host : HostSemantics H} {cs : Store H}
    {f : Silmaril.Wasm.Execution.Core.Frame} {ls : List W} {o : Bin} {ca cb : List Instr} {a b : Nat}
    (hra : Runs Pf host cs f ls ca (w a)) (hrb : Runs Pf host cs f ls cb (w b)) (ha : a < M32)
    (hb : b < M32) (hd : (o = .divu ∨ o = .remu) → b ≠ 0) :
    Runs Pf host cs f ls (ca ++ cb ++ [o.core]) (w (o.eval a b)) := by
  intro ops rest
  have e₀ : stackA ops ++ ((ca ++ cb ++ [o.core]).map Admin.plain ++ rest) =
      stackA ops ++ (ca.map Admin.plain ++ (cb.map Admin.plain ++ (Admin.plain o.core :: rest))) := by
    simp only [List.map_append, List.append_assoc, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append]
  rw [e₀]
  refine (hra ops _).trans ((hrb (w a :: ops) _).trans ?_)
  exact pure_core Pf host cs f (bin_pexec o ha hb hd ls ops) rest

/-- **The Core run of a compiled expression** pushes its value. -/
theorem code_runs (Pf : Profile) (host : HostSemantics H) (cs : Store H)
    (f : Silmaril.Wasm.Execution.Core.Frame) {s : St} {ls gs : List W} (hg : GlobalsAre cs f gs) :
    ∀ (e : E) {code : List Instr}, e.code? = some code → e.Fits s ls gs →
      Runs Pf host cs f ls code (w (e.eval s))
  | .c n, _, hc, _ => by
      cases hc
      exact runs_one fun ops => const_pexec n ls ops
  | .l i, _, hc, h => by
      cases hc
      exact runs_one fun ops => lget_pexec h.1 h.2.1 ops
  | .g i, _, hc, h => by
      cases hc
      intro ops rest
      exact global_get_core Pf host cs f rest hg (gidx i) (by rw [gidx_val h.1]; exact h.2.1)
  | .bin o a b, _, hc, h => by
      obtain ⟨ca, cb, hca, hcb, rfl⟩ := bin_code hc
      exact runs_bin (code_runs Pf host cs f hg a hca h.1) (code_runs Pf host cs f hg b hcb h.2.1)
        (eval_lt h.1) (eval_lt h.2.1) h.2.2
  | .eqz a, _, hc, h => by
      obtain ⟨ca, hca, rfl⟩ := eqz_code hc
      intro ops rest
      have e₀ : stackA ops ++ ((ca ++ [Instr.intTestOp .i32 .eqz]).map Admin.plain ++ rest) =
          stackA ops ++ (ca.map Admin.plain ++ (Admin.plain (Instr.intTestOp .i32 .eqz) :: rest)) := by
        simp only [List.map_append, List.append_assoc, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append]
      rw [e₀]
      exact (code_runs Pf host cs f hg a hca h ops _).trans
        (pure_core Pf host cs f (eqz_pexec (eval_lt (e := a) h) ls ops) rest)
  | .ld8 _, _, _, h => h.elim

/-- Every expression that fits compiles. -/
theorem code_some {s : St} {ls gs : List W} : ∀ {e : E}, e.Fits s ls gs → ∃ code, e.code? = some code
  | .c _, _ => ⟨_, rfl⟩
  | .l _, _ => ⟨_, rfl⟩
  | .g _, _ => ⟨_, rfl⟩
  | .bin o a b, h => by
      obtain ⟨ca, hca⟩ := code_some (e := a) h.1
      obtain ⟨cb, hcb⟩ := code_some (e := b) h.2.1
      exact ⟨ca ++ cb ++ [o.core], by simp [E.code?, hca, hcb]⟩
  | .eqz a, h => by
      obtain ⟨ca, hca⟩ := code_some (e := a) h
      exact ⟨ca ++ [Instr.intTestOp .i32 .eqz], by simp [E.code?, hca]⟩
  | .ld8 _, h => h.elim

end Silmaril.Proofs.Wasm.JcoTool.KCoreCore
