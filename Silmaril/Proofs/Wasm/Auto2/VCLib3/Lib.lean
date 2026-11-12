module

public import Silmaril.Wasm.Auto2.VCLib3.Defs
public import Silmaril.Wasm.Auto2.VCLib2.Thms

/-!
# VC library with linear arithmetic and recursion: conditions, entries and kernel-checked checks

The proved contracts `dblEntry` and `add3Entry` (their conditions are those of `dblAddProg` and
`add3Prog`), the library `entriesM3` that `wasm-check vc` searches (`entriesM` of `VCLib2`, then
these), and the checks of the demonstration modules by kernel evaluation of `vcCheckM`: the
programs that differ from the contracts' by linear arithmetic are accepted, the mutants are not.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCLib3

open Silmaril.Wasm Silmaril.Wasm.Execution
open Silmaril.Wasm.Auto2.VCGen Silmaril.Wasm.Auto2.VCBridge Silmaril.Wasm.Auto2.VCCheck
open Silmaril.Wasm.Auto2.VCLib (libFuel)

set_option maxRecDepth 100000 in
set_option linter.unusedTactic false in
theorem dbl_vcs : AllValid {} (genFunc dblSpec dblAddProg.funcs[0] libFuel) := by
  vcgen4
  all_goals (intros; simp_all)

set_option maxRecDepth 100000 in
set_option linter.unusedTactic false in
theorem add3_vcs : AllValid {} (genFunc add3Spec add3Prog.funcs[0] libFuel) := by
  vcgen4
  all_goals (intros; simp_all)

/-- `dbl x = x + x`. -/
def dblEntry : VcEntryM where
  name := "dbl"
  F := {}
  S := dblSpec
  fuel := libFuel
  conds := genFunc dblSpec dblAddProg.funcs[0] libFuel
  valid := dbl_vcs
  total := rfl

/-- `add3 a b c = (a + b) + c`. -/
def add3Entry : VcEntryM where
  name := "add3"
  F := {}
  S := add3Spec
  fuel := libFuel
  conds := genFunc add3Spec add3Prog.funcs[0] libFuel
  valid := add3_vcs
  total := rfl

/-! ## Kernel-checked checks: linear arithmetic -/

theorem dblShl_spec (P : Numerics.Profile) : ModTSpecM P dblEntry dblShlProg 0 :=
  modTSpecM_of_vcCheckM (by decide +kernel)

theorem dblMul_spec (P : Numerics.Profile) : ModTSpecM P dblEntry dblMulProg 0 :=
  modTSpecM_of_vcCheckM (by decide +kernel)

theorem add3Assoc_spec (P : Numerics.Profile) : ModTSpecM P add3Entry add3AssocProg 0 :=
  modTSpecM_of_vcCheckM (by decide +kernel)

theorem add3Sub_spec (P : Numerics.Profile) : ModTSpecM P add3Entry add3SubProg 0 :=
  modTSpecM_of_vcCheckM (by decide +kernel)

/-- The mutants are not accepted. -/
example : vcCheckM dblEntry dblShl2Prog 0 = false := by decide +kernel
example : vcCheckM add3Entry add3MutProg 0 = false := by decide +kernel

/-! ## Callees with globals, variants over globals -/

/-- `incr2` with its callee. -/
def incr2SpecC (code : Func) : FnSpec := { incr2Spec with calls := [(0, incrSpec, code)] }

/-- `drain` with its callee. -/
def drainSpecC (code : Func) : FnSpec := { drainSpec with calls := [(0, decSpec, code)] }

set_option maxRecDepth 100000 in
set_option linter.unusedTactic false in
theorem incr_vcs : AllValid {} (genFunc incrSpec incr2Prog.funcs[0] libFuel) := by
  vcgen4
  all_goals (intros; simp_all)

set_option maxRecDepth 100000 in
set_option linter.unusedTactic false in
/-- The conditions of `incr2`: the callee's precondition twice and the postcondition, over the
callee's entry and final globals. -/
theorem incr2_vcs : AllValid {} (genFunc (incr2SpecC incr2Prog.funcs[0]) incr2Prog.funcs[1] libFuel) := by
  vcgen4
  all_goals (intros; simp_all)
  all_goals (try bv_omega)

set_option maxRecDepth 100000 in
set_option linter.unusedTactic false in
theorem dec_vcs : AllValid {} (genFunc decSpec drainProg.funcs[0] libFuel) := by
  vcgen4
  all_goals (intros; simp_all)

set_option maxRecDepth 100000 in
set_option linter.unusedTactic false in
/-- The conditions of `drain`: loop entry, exit, the callee's precondition, the invariant and the
variant after the call (the global, havocked at the loop head because the body calls). -/
theorem drain_vcs : AllValid {} (genFunc (drainSpecC drainProg.funcs[0]) drainProg.funcs[1] libFuel) := by
  vcgen4
  all_goals (intros; try simp_all)
  all_goals bv_omega

set_option maxRecDepth 100000 in
set_option linter.unusedTactic false in
/-- The conditions of `countdown` (a variant over a global). -/
theorem countdown_vcs : AllValid {} (genFunc drainSpec countdownProg.funcs[0] libFuel) := by
  vcgen4
  all_goals (intros; try simp_all)
  all_goals bv_omega

/-- `incr2`: global `0` grows by `2`, through two calls to a callee meeting `incrSpec`. -/
def incr2Entry : VcEntryM where
  name := "incr2"
  F := {}
  S := incr2Spec
  fuel := libFuel
  conds := genFunc (incr2SpecC incr2Prog.funcs[0]) incr2Prog.funcs[1] libFuel
  valid := incr2_vcs
  total := rfl
  calls := [(0, incrSpec, genFunc incrSpec incr2Prog.funcs[0] libFuel)]
  callsOK := by
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact ⟨rfl, rfl, incr_vcs⟩

/-- `drain`: global `0` is counted down to `0` by calls to a callee meeting `decSpec`. -/
def drainEntry : VcEntryM where
  name := "drain"
  F := {}
  S := drainSpec
  fuel := libFuel
  conds := genFunc (drainSpecC drainProg.funcs[0]) drainProg.funcs[1] libFuel
  valid := drain_vcs
  total := rfl
  calls := [(0, decSpec, genFunc decSpec drainProg.funcs[0] libFuel)]
  callsOK := by
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact ⟨rfl, rfl, dec_vcs⟩

/-- `countdown`: global `0` is counted down to `0` (variant: the global). -/
def countdownEntry : VcEntryM where
  name := "countdown"
  F := {}
  S := drainSpec
  fuel := libFuel
  conds := genFunc drainSpec countdownProg.funcs[0] libFuel
  valid := countdown_vcs
  total := rfl

theorem incr2_spec (P : Numerics.Profile) : ModTSpecM P incr2Entry incr2Prog 0 :=
  modTSpecM_of_vcCheckM (by decide +kernel)

theorem drain_spec (P : Numerics.Profile) : ModTSpecM P drainEntry drainProg 0 :=
  modTSpecM_of_vcCheckM (by decide +kernel)

theorem countdown_spec (P : Numerics.Profile) : ModTSpecM P countdownEntry countdownProg 0 :=
  modTSpecM_of_vcCheckM (by decide +kernel)

/-- The mutants are not accepted. -/
example : vcCheckM incr2Entry incr2SubProg 0 = false := by decide +kernel
example : vcCheckM incr2Entry incr1Prog 0 = false := by decide +kernel

/-! ## The library -/

/-- The contracts of `wasm-check vc`. -/
def entriesM3 : List VcEntryM :=
  VCLib2.entriesM ++ [dblEntry, add3Entry, incr2Entry, drainEntry, countdownEntry]

/-- The contract named `n` (`sum` if there is none). -/
def entryM3 (n : String) : VcEntryM := (entriesM3.find? (·.name == n)).getD VCLib.sumEntry.toM

end Silmaril.Wasm.Auto2.VCLib3
