module

public import Silmaril.Proofs.Wasm.FnInst.Ground.Opt
public import Silmaril.Wasm.FnInst.Ground.Thms
public import Silmaril.Wasm.FnInst.Opt.Rules.Thms

@[expose] public section

/-! # The opt track's segment equivalences, grounded in Wasm Core

Header of `Silmaril.Proofs.Wasm.FnInst.Ground.Opt`. `good_of_runEq`: an equivalence
`Opt.RunEq ft n E a b` of the opt track (equal outcome sets from every state with at least
`n` operands), between typed stack-only segments whose left side contains a non-constant and
forces its `n` inputs to be `i32`, is a good pair of the grounded fragment, so the generic
transfer `exportEquiv_of_good` applies to it.

`good_neutral_opt` and `good_eqz3_opt` take the opt track's rule lemmas
`Opt.Rules.neutral_runEq` and `Opt.Rules.eqz3_runEq` as they are, and add only the type
forcing of their left sides (`forces_constBin`, `forces_eqz`).

Not covered: opt segments with locals, globals or calls. Locals need a frame correspondence
(opt locals are total maps of `i32`, machine frames are finite lists of any value type, and an
`i64` local makes `local.get x; drop` run where `local.get x; i32.eqz; drop` gets stuck);
calls need the environment models of the opt institution matched against silmaril's
function instances.
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- **An opt equivalence is a good pair.** -/
theorem good_of_runEq {ft : Opt.FTypes} {n m m' : ℕ} {E : Opt.Env} {a b : Opt.Code}
    {ga gb : List GInstr} (hrun : Opt.RunEq ft n E a b) (ha : trStk a = some ga)
    (hb : trStk b = some gb) (hca : Opt.chk ft a n = some m) (hcb : Opt.chk ft b n = some m')
    (hforce : Forces n ga) (hop : ∃ i ∈ ga, i.isConst = false) : Good ga gb :=
  Or.inl ⟨⟨trStk_stk ha, hop⟩, runRef_of_runEq hrun ha hb hca hcb hforce⟩

/-- The opt track's `neutral-ops` rule lemma, grounded. -/
theorem good_neutral_opt {i : Opt.Instr} {k : BitVec 32} (h : Opt.Rules.Neutral i k) :
    ∃ b : Bin, ofOptStk i = some (.bin b) ∧ Good [.const k, .bin b] [] := by
  obtain ⟨b, hb⟩ : ∃ b : Bin, ofOptStk i = some (.bin b) := by
    cases h <;> exact ⟨_, rfl⟩
  have ha : trStk (Opt.Rules.neutralL h).1 = some [.const k, .bin b] := by
    show [Opt.Instr.const k, i].mapM ofOptStk = _
    rw [List.mapM_cons, List.mapM_cons, hb]
    rfl
  have hop : ∃ j ∈ [GInstr.const k, .bin b], j.isConst = false := ⟨.bin b, by simp, rfl⟩
  exact ⟨b, hb, good_of_runEq (Opt.Rules.neutral_runEq h Opt.Env.top) ha rfl
    (Opt.Rules.neutralL h).2 (Opt.Rules.skip 1).2 (forces_constBin k b) hop⟩

/-- The opt track's `eqz-pair` rule lemma (consumer `i32.eqz`), grounded. -/
theorem good_eqz3_opt : Good [.eqz, .eqz, .eqz] [.eqz] := by
  have hop : ∃ j ∈ [GInstr.eqz, .eqz, .eqz], j.isConst = false := ⟨.eqz, by simp, rfl⟩
  exact good_of_runEq (Opt.Rules.eqz3_runEq Opt.Env.top) rfl rfl Opt.Rules.eqz3L.2
    Opt.Rules.eqz1.2 (forces_eqz _) hop

end Silmaril.Wasm.FnInst.Ground
