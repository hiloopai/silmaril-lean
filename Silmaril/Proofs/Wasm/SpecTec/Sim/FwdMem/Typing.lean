module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdMem.Bytes
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms
public import Silmaril.Wasm.SpecTec.Sim.IntNumeric.Thms

/-!
# The quantifiers of the value load and store rules are typed

In every `simEnv B`, proved from the script's own type definitions (no assumption):

* `hasTyp_bytes`: an encoded byte string `bytesV b` (and `leBytesV k n`) is a `byte*`
  (`Original.d21`, the premise `i >= 0 /\ i <= 255`);
* `hasTyp_iN_var`: a `%`-wrapped natural below `2^N` is an `iN(n)` in a scope binding `n` to `N`
  (the packed loads' `c`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdMem

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d21)
open IntNumeric (instCases findCase hasTypCase_of_findCase premsOk_if evalExp_and)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem findTyp_byte :
    (simEnv B).findTyp? "byte" = some ([], [.instD [] [] (.variantT (instCases Original.d21 0))]) :=
  rfl

/-- `byte` holds every natural below `256`. -/
theorem hasTyp_byte {ρ : VarEnv} (hρ : ValsOnly ρ) {n : Nat} (hn : n < 256) :
    HasTyp (simEnv B) ρ (.varT "byte" []) (pctV n) := by
  have hl : localTyp? ρ "byte" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  have htup : HasTyp (simEnv B) VarEnv.empty (.tupT [.mk "i" (.numT .natT)]) (.tuple [natV n]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩,
      hasTypTup_nil_iff.2 rfl⟩⟩
  refine hasTyp_varT_case hl findTyp_byte Equiv.evalArgs_nil matchArgs_nil
    (hasTypCase_of_findCase rfl htup (premsOk_if (evalExp_and ?_ ?_)))
  · exact evalExp_cmpNum (evalExp_var (v := natV n) rfl) evalExp_num
      (by simp [Num.cmp])
  · refine evalExp_cmpNum (evalExp_var (v := natV n) rfl)
      evalExp_num ?_
    simp only [Num.cmp, Option.some.injEq, decide_eq_true_eq]
    omega

/-- An encoded byte string is a `byte*`. -/
theorem hasTyp_bytes {ρ : VarEnv} (hρ : ValsOnly ρ) (b : ByteArray) :
    HasTyp (simEnv B) ρ (.iterT (.varT "byte" []) .list) (.list (bytesV b)) :=
  hasTyp_iterT_list_iff.2 ⟨_, rfl, hasTypList_iff.2 fun w hw => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hw
    exact hasTyp_byte hρ c.toNat_lt⟩

/-- `iN(n)` holds every `%`-wrapped natural below `2^N`, in a scope binding `n` to `N`. -/
theorem hasTyp_iN_var {ρ : VarEnv} {y : IL.Id} {N k : Nat}
    (hy : ρ.findVal? y = some (natV N)) (hk : k < 2 ^ N) :
    HasTyp (simEnv B) ρ (.varT "iN" [.expA (.varE y)]) (pctV k) := by
  obtain ⟨ps', qs', htd'⟩ := IntNumeric.findTyp_iN (B := B)
  have hl : localTyp? ρ "iN" [.expA (.varE y)] = none := by
    simp [localTyp?]
  exact hasTyp_varT_of_insts hl htd' (Equiv.evalArgs_cons (evalExp_var hy) Equiv.evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
      (hasTypDef_aliasT_iff.2 (IntNumeric.hasTyp_uN (evalExp_var (by simp)) hk)))

end Silmaril.Wasm.SpecTec.Sim.FwdMem
