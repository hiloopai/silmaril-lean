module

public import Silmaril.Wasm.Binaryen.Continuation.Defs

public section

namespace Silmaril.Proofs.Wasm.Binaryen.Continuation

open Silmaril.Wasm Silmaril.Wasm.Binaryen.Continuation
open Validation Validation.Intrinsic

theorem readOp_lower (op : Op) : Op.read op.lower = some op := by
  cases op <;> rfl

theorem lowerOp_of_read {instr : Instr} {op : Op} (ok : Op.read instr = some op) :
    op.lower = instr := by
  cases instr <;> simp only [Op.read, Option.some.injEq, reduceCtorEq] at ok
  all_goals subst op; rfl

theorem read_lower (raw : Raw) : Raw.read raw.lower = some raw := by
  induction raw with
  | done => simp [Raw.read, Raw.lower]
  | let_ op next ih => cases op <;> simp [Raw.read, Raw.lower, Op.lower, Op.read, ih]
  | block type body next ihBody ihNext => simp [Raw.read, Raw.lower, ihBody, ihNext]
  | if_ type onTrue onFalse next ihTrue ihFalse ihNext =>
      simp [Raw.read, Raw.lower, ihTrue, ihFalse, ihNext]

theorem lower_of_read {ops : List Instr} {raw : Raw} (ok : Raw.read ops = some raw) :
    raw.lower = ops := by
  induction ops using Raw.read.induct generalizing raw
  · simpa [Raw.read, Raw.lower] using congrArg (Option.map Raw.lower) ok.symm
  · rename_i body next body' next' hn hb ihBody ihNext
    rw [Raw.read.eq_2, hb, hn] at ok
    cases ok
    rw [Raw.lower, ihBody hb, ihNext hn]
  · rename_i bad ihBody ihNext
    rw [Raw.read.eq_2] at ok
    split at ok
    · exact False.elim (bad _ _ (by assumption) (by assumption))
    · simp at ok
  · rename_i thenBody elseBody next thenBody' elseBody' next' hn he ht ihTrue ihFalse ihNext
    rw [Raw.read.eq_3, ht, he, hn] at ok
    cases ok
    rw [Raw.lower, ihTrue ht, ihFalse he, ihNext hn]
  · rename_i bad ihTrue ihFalse ihNext
    rw [Raw.read.eq_3] at ok
    split at ok
    · exact False.elim (bad _ _ _ (by assumption) (by assumption) (by assumption))
    · simp at ok
  · rename_i instr next notBlock notIf op next' hn hop ihNext
    rw [Raw.read.eq_4 instr next notBlock notIf, hop, hn] at ok
    cases ok
    rw [Raw.lower, lowerOp_of_read hop, ihNext hn]
  · rename_i instr next notBlock notIf bad ihNext
    rw [Raw.read.eq_4 instr next notBlock notIf] at ok
    split at ok
    · exact False.elim (bad _ _ (by assumption) (by assumption))
    · simp at ok

theorem core_erase {ctx inputs outputs raw} (code : Code ctx inputs outputs raw) :
    code.toCore.erase = raw.lower := by
  induction code with
  | done valid => exact finish_erase valid
  | let_ prefixOk valid rest ih =>
      simp [Code.toCore, prepend_erase, Step.erase, Raw.lower, ih]
  | block prefixOk valid inner rest ihInner ihRest =>
      simp [Code.toCore, prepend_erase, Step.erase, Raw.lower, ihInner, ihRest]
  | if_ prefixOk valid onTrue onFalse rest ihTrue ihFalse ihRest =>
      simp [Code.toCore, prepend_erase, Step.erase, Raw.lower, ihTrue, ihFalse, ihRest]

theorem cuts_of_code {ctx inputs outputs raw} (code : Code ctx inputs outputs raw) :
    Cuts ctx inputs outputs raw.lower := by
  induction code with
  | done valid => exact .done valid
  | let_ prefixOk valid rest ih => exact .atom (by rw [readOp_lower]; rfl) prefixOk valid ih
  | block prefixOk valid inner rest ihInner ihRest => exact .block prefixOk valid ihInner ihRest
  | if_ prefixOk valid onTrue onFalse rest ihTrue ihFalse ihRest =>
      exact .if_ prefixOk valid ihTrue ihFalse ihRest

theorem code_of_cuts {ctx inputs outputs ops} (cuts : Cuts ctx inputs outputs ops) :
    ∃ raw, Nonempty (Code ctx inputs outputs raw) ∧ raw.lower = ops := by
  induction cuts with
  | done valid => exact ⟨.done, ⟨.done valid⟩, rfl⟩
  | atom supported prefixOk valid rest ih =>
      rename_i instr next
      obtain ⟨restRaw, ⟨restCode⟩, rfl⟩ := ih
      cases hop : Op.read instr with
      | none => simp [hop] at supported
      | some op =>
          have equal := lowerOp_of_read hop
          subst instr
          exact ⟨.let_ op restRaw, ⟨.let_ prefixOk valid restCode⟩, rfl⟩
  | block prefixOk valid inner rest ihInner ihRest =>
      obtain ⟨innerRaw, ⟨innerCode⟩, rfl⟩ := ihInner
      obtain ⟨restRaw, ⟨restCode⟩, rfl⟩ := ihRest
      exact ⟨.block _ innerRaw restRaw, ⟨.block prefixOk valid innerCode restCode⟩, rfl⟩
  | if_ prefixOk valid onTrue onFalse rest ihTrue ihFalse ihRest =>
      obtain ⟨trueRaw, ⟨trueCode⟩, rfl⟩ := ihTrue
      obtain ⟨falseRaw, ⟨falseCode⟩, rfl⟩ := ihFalse
      obtain ⟨restRaw, ⟨restCode⟩, rfl⟩ := ihRest
      exact ⟨.if_ _ trueRaw falseRaw restRaw, ⟨.if_ prefixOk valid trueCode falseCode restCode⟩, rfl⟩

end Silmaril.Proofs.Wasm.Binaryen.Continuation
