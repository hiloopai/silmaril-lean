module

public import Silmaril.Wasm.Execution.Core.Step

/-!
# The Wasm fragment of the dataflow DCE: definitions

The liveness-based dead-code elimination of `Silmaril.Wasm.Dataflow.Dce` is stated on a
fragment of Core 3.0 code: everything that runs inside one frame without calls or
exceptions.

* `fragInstr`/`fragSeq`: `nop`, `unreachable`, `drop`, `select`, `block`, `loop`, `if`,
  `br`, `br_if`, `br_table`, `return`, `local.get`/`local.set`/`local.tee`,
  `global.get`/`global.set`, scalar constants, every scalar numeric instruction
  (including the trapping ones, which DCE keeps) and vector constants.
* `fragAdmin`/`fragAdminSeq`: the administrative code reachable from fragment code:
  fragment instructions, reference values, `LABEL_n{cont}` with fragment continuation and
  body, and `TRAP`. No `FRAME` or `HANDLER`.
* `pureArity?`: the *removable* producers. Applied to their operands they can only step to
  a single value, without changing the store or the frame and without trapping
  (`pureArity_step` in `Silmaril.Wasm.Dataflow.Fragment.Thms`). Integer division and
  remainder (which trap on zero) and conversions (which trap on overflow) are excluded.
* `adminSize`/`codeSize`: the stutter measure of both DCE passes. `local.get` and
  `local.tee` weigh more than the values and `local.set`s they become.

Ported from an earlier development `Silmaril/Wasm/Dataflow/Fragment.lean` (and the
measure and `fragSeq_append` from `DeadCode.lean`); see `docs/projects/wasm-wasi.md`.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-- Integer binary operators that never trap (`intBinOp` is always `.ok`). -/
def intBinOpTotal : IntBinOp → Bool
  | .div _ | .rem _ => false
  | _ => true

/-- Removable producers: a pure, trap-free instruction that consumes `n` operands and
produces one value, or `none`. -/
def pureArity? : Instr → Option Nat
  | .intConst _ _ | .floatConst _ _ | .vecConst _ | .localGet _ => some 0
  | .intUnOp _ _ | .intTestOp _ _ | .floatUnOp _ _ => some 1
  | .intRelOp _ _ | .floatRelOp _ _ | .floatBinOp _ _ => some 2
  | .intBinOp _ op => if intBinOpTotal op then some 2 else none
  | .select _ => some 3
  | _ => none

/-- Removable producers in administrative code: plain removable instructions and
reference values. -/
def adminPureArity? : Admin → Option Nat
  | .plain i => pureArity? i
  | .ref _ => some 0
  | _ => none

mutual
/-- Fragment instructions. -/
def fragInstr : Instr → Bool
  | .nop | .unreachable | .drop | .select _ => true
  | .block _ b | .loop _ b => fragSeq b
  | .if_ _ b₁ b₂ => fragSeq b₁ && fragSeq b₂
  | .br _ | .brIf _ | .brTable _ _ | .return_ => true
  | .localGet _ | .localSet _ | .localTee _ | .globalGet _ | .globalSet _ => true
  | .intConst _ _ | .floatConst _ _ | .vecConst _ => true
  | .intUnOp _ _ | .intBinOp _ _ | .intTestOp _ _ | .intRelOp _ _ => true
  | .floatUnOp _ _ | .floatBinOp _ _ | .floatRelOp _ _ | .convert _ => true
  | _ => false

/-- Fragment instruction sequences. -/
def fragSeq : List Instr → Bool
  | [] => true
  | i :: is => fragInstr i && fragSeq is
end

mutual
/-- Fragment administrative instructions. -/
def fragAdmin : Admin → Bool
  | .plain i => fragInstr i
  | .ref _ => true
  | .label _ cont body => fragSeq cont && fragAdminSeq body
  | .trap => true
  | _ => false

/-- Fragment administrative code. -/
def fragAdminSeq : List Admin → Bool
  | [] => true
  | a :: as => fragAdmin a && fragAdminSeq as
end

mutual
/-- The stutter measure of one administrative instruction. -/
def adminSize : Admin → Nat
  | .plain (.localGet _) => 2
  | .plain (.localTee _) => 3
  | .label _ _ body => 1 + codeSize body
  | _ => 1

/-- The stutter measure of administrative code. -/
def codeSize : List Admin → Nat
  | [] => 0
  | a :: as => adminSize a + codeSize as
end

/-! ## Unfolding lemmas -/

@[simp] theorem fragSeq_nil : fragSeq [] = true := by simp [fragSeq]

@[simp] theorem fragSeq_cons (i : Instr) (is : List Instr) :
    fragSeq (i :: is) = (fragInstr i && fragSeq is) := by simp [fragSeq]

@[simp] theorem fragAdminSeq_nil : fragAdminSeq [] = true := by simp [fragAdminSeq]

@[simp] theorem fragAdminSeq_cons (a : Admin) (as : List Admin) :
    fragAdminSeq (a :: as) = (fragAdmin a && fragAdminSeq as) := by simp [fragAdminSeq]

@[simp] theorem fragAdmin_plain (i : Instr) : fragAdmin (.plain i) = fragInstr i := by
  simp [fragAdmin]

@[simp] theorem fragAdmin_ref (r : Ref) : fragAdmin (.ref r) = true := by simp [fragAdmin]

@[simp] theorem fragAdmin_label (n : Nat) (cont : List Instr) (body : List Admin) :
    fragAdmin (.label n cont body) = (fragSeq cont && fragAdminSeq body) := by
  simp [fragAdmin]

@[simp] theorem fragAdmin_trap : fragAdmin .trap = true := by simp [fragAdmin]

@[simp] theorem fragAdmin_handler (n : Nat) (cs : List Catch) (body : List Admin) :
    fragAdmin (.handler n cs body) = false := by simp [fragAdmin]

@[simp] theorem fragAdmin_frame (n : Nat) (f : Frame) (body : List Admin) :
    fragAdmin (.frame n f body) = false := by simp [fragAdmin]

@[simp] theorem fragAdmin_callRefType (d : Validation.DefType) :
    fragAdmin (.callRefType d) = false := by
  simp [fragAdmin]

@[simp] theorem fragAdmin_returnCallRefType (d : Validation.DefType) :
    fragAdmin (.returnCallRefType d) = false := by
  simp [fragAdmin]

@[simp] theorem fragSeq_append (as bs : List Instr) :
    fragSeq (as ++ bs) = (fragSeq as && fragSeq bs) := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih, Bool.and_assoc]

@[simp] theorem fragAdminSeq_append (as bs : List Admin) :
    fragAdminSeq (as ++ bs) = (fragAdminSeq as && fragAdminSeq bs) := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih, Bool.and_assoc]

@[simp] theorem fragAdmin_toAdmin (v : Val) : fragAdmin v.toAdmin = true := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, fragInstr]

@[simp] theorem fragAdminSeq_vals (vs : List Val) : fragAdminSeq (vals vs) = true := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simpa [vals] using ih

@[simp] theorem fragAdminSeq_expression (e : List Instr) :
    fragAdminSeq (expression e) = fragSeq e := by
  induction e with
  | nil => rfl
  | cons i e ih =>
    simp only [expression, List.map_cons, fragAdminSeq_cons, fragAdmin_plain,
      fragSeq_cons] at ih ⊢
    rw [ih]

theorem codeSize_cons (a : Admin) (as : List Admin) :
    codeSize (a :: as) = adminSize a + codeSize as := by
  simp [codeSize]

@[simp] theorem codeSize_nil : codeSize [] = 0 := by simp [codeSize]

@[simp] theorem codeSize_append (as bs : List Admin) :
    codeSize (as ++ bs) = codeSize as + codeSize bs := by
  induction as with
  | nil => simp
  | cons a as ih => simp only [List.cons_append, codeSize_cons, ih]; omega

@[simp] theorem adminSize_toAdmin (v : Val) : adminSize v.toAdmin = 1 := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

@[simp] theorem codeSize_vals (vs : List Val) : codeSize (vals vs) = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [vals, List.map_cons, codeSize_cons, adminSize_toAdmin, List.length_cons] at ih ⊢
    omega

end Silmaril.Wasm.Dataflow
