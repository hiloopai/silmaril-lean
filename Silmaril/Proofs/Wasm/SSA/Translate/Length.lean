module

public import Silmaril.Proofs.Wasm.SSA.Translate.Basic

/-! # Fragment runs preserve the number of locals -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Translate

open Silmaril.Wasm.SSA

theorem blockExit_len {ty : Option Silmaril.Wasm.IntType} {ls : List WVal}
    {o o' : Out (Option WVal)} (h : BlockExit ty o o') (hl : LenOK ls o) : LenOK ls o' := by
  cases h <;> simp_all [LenOK]

theorem loopExit_len {ty : Option Silmaril.Wasm.IntType} {ls : List WVal}
    {o o' : Out (Option WVal)} (h : LoopExit ty o o') (hl : LenOK ls o) : LenOK ls o' := by
  cases h <;> simp_all [LenOK]

theorem LenOK.trans' {α : Type} {ls ls₁ : List WVal} {o : Out α} (h₁ : ls₁.length = ls.length)
    (h : LenOK ls₁ o) : LenOK ls o := by
  cases o <;> simp_all [LenOK]

mutual

theorem exec_len : ∀ {ls : List WVal} {e : Expr} {o : Out (Option WVal)}, Exec ls e o → LenOK ls o
  | _, _, _, .op ha _ => by have := args_len ha; simpa [LenOK] using this
  | _, _, _, .op_trap _ _ => trivial
  | _, _, _, .op_abrupt ha _ => (args_len ha).cast
  | _, _, _, .localGet _ => rfl
  | _, _, _, .localSet he => by have := exec_len he; simp_all [LenOK]
  | _, _, _, .localSet_abrupt he _ => exec_len he
  | _, _, _, .localTee he => by have := exec_len he; simp_all [LenOK]
  | _, _, _, .localTee_abrupt he _ => exec_len he
  | _, _, _, .drop he => by have := exec_len he; simp_all [LenOK]
  | _, _, _, .drop_abrupt he _ => exec_len he
  | _, _, _, .nop => rfl
  | _, _, _, .unreachable => trivial
  | _, _, _, .block hs hx => blockExit_len hx (seq_len hs)
  | _, _, _, .loop hs hx => loopExit_len hx (seq_len hs)
  | _, _, _, .loop_back hs hr => by
      have h1 := seq_len hs
      exact LenOK.trans' (by simpa [LenOK] using h1) (exec_len hr)
  | _, _, _, .if_ hc _ hs hx => by
      have h1 := exec_len hc
      exact LenOK.trans' (by simpa [LenOK] using h1) (blockExit_len hx (seq_len hs))
  | _, _, _, .if_abrupt hc _ => exec_len hc
  | _, _, _, .br ha => by have := args_len ha; simpa [LenOK] using this
  | _, _, _, .br_abrupt ha _ => (args_len ha).cast
  | _, _, _, .brIf ha _ _ => by
      have := args_len ha
      simp only [LenOK] at this
      split <;> simpa [LenOK] using this
  | _, _, _, .brIf_abrupt ha _ => (args_len ha).cast
  | _, _, _, .return_ _ => trivial
  | _, _, _, .return_abrupt ha _ => (args_len ha).cast

theorem args_len : ∀ {ls : List WVal} {es : List Expr} {o : Out (List WVal)}, Args ls es o → LenOK ls o
  | _, _, _, .nil => rfl
  | _, _, _, .cons he ha => by
      have h1 := exec_len he
      have h2 := args_len ha
      simp_all [LenOK]
  | _, _, _, .head_abrupt he _ => (exec_len he).cast
  | _, _, _, .tail_abrupt he ha _ => by
      have h1 := exec_len he
      exact LenOK.trans' (by simpa [LenOK] using h1) (args_len ha)

theorem seq_len : ∀ {ls : List WVal} {r : Option WVal} {es : List Expr} {o : Out (Option WVal)},
    Seq ls r es o → LenOK ls o
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons he hs => by
      have h1 := exec_len he
      exact LenOK.trans' (by simpa [LenOK] using h1) (seq_len hs)
  | _, _, _, _, .abrupt he _ => exec_len he

end

end Silmaril.Proofs.Wasm.SSA.Translate
