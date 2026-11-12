module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Utf8.Name

/-!
# Round 7: with the erratum, export instances are `exportinst`s

* `hasTyp_externaddr`: every external address is an `externaddr`;
* `hasTyp_exportinst`: **an export instance whose name has fewer than `2 ^ 32` UTF-8 bytes is an
  `exportinst`** in `utf8Env B`;
* `exportinst_erratum`: the contrast at a one-character export name, which round 5 showed is
  never an `exportinst` in `simEnv B` (`Round5.Pos.not_hasTyp_exportinst_single`).

The module-instance level is not done here: a typed `moduleinst` also needs its `TYPES` field
typed in `utf8Env B`, and round 5's `typedV_deftype` is about `simEnv B` only (see
`docs/projects/spectec/README.md`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_nil)
open Silmaril.SpecTec.Equiv.RuntimeBridge (charToValue nameToValue externAddrToValue
  exportInstToValue)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d263)

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem findTyp_externaddr (B : Builtins) : (utf8Env B).findTyp? "externaddr" =
    some ([], [.instD [] [] (.variantT (IntNumeric.instCases Original.d263 0))]) := by
  rw [findTyp?_utf8Env]; rfl

set_option maxRecDepth 100000 in
theorem findTyp_addrAlias (B : Builtins) (x : IL.Id) (hx : x ∈ ["tagaddr", "globaladdr",
    "memaddr", "tableaddr", "funcaddr"]) :
    (utf8Env B).findTyp? x = some ([], [.instD [] [] (.aliasT (.varT "addr" []))]) := by
  rw [findTyp?_utf8Env]
  refine Round5.Pos.findTyp_xaddr x ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  rcases hx with h | h | h | h | h <;> simp [h]

set_option maxRecDepth 100000 in
theorem findTyp_addr' (B : Builtins) :
    (utf8Env B).findTyp? "addr" = some ([], [.instD [] [] (.aliasT (.numT .natT))]) := by
  rw [findTyp?_utf8Env]; rfl

/-- A natural is an `xaddr`, for each of the address aliases an export can name. -/
theorem hasTyp_addrAlias (B : Builtins) {ρ : VarEnv} (hρ : ValsOnly ρ) (x : IL.Id)
    (hx : x ∈ ["tagaddr", "globaladdr", "memaddr", "tableaddr", "funcaddr"]) (a : Nat) :
    HasTyp (utf8Env B) ρ (.varT x []) (.num (.natN a)) := by
  have hl : ∀ y, localTyp? ρ y [] = none := fun y => by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  refine hasTyp_varT_of_insts (hl x) (findTyp_addrAlias B x hx) evalArgs_nil
    (hasTypInsts_head matchArgs_nil (hasTypDef_aliasT_iff.2 ?_))
  have hl₀ : localTyp? VarEnv.empty "addr" [] = none := by
    simp [localTyp?, VarEnv.findTyp?, VarEnv.empty, Map.empty]
  exact hasTyp_varT_of_insts hl₀ (findTyp_addr' B) evalArgs_nil
    (hasTypInsts_head matchArgs_nil (hasTypDef_aliasT_iff.2 (hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩)))

/-- **Every external address is an `externaddr`.** -/
theorem hasTyp_externaddr (B : Builtins) {ρ : VarEnv} (hρ : ValsOnly ρ) (a : ExternAddr) :
    HasTyp (utf8Env B) ρ (.varT "externaddr" []) (externAddrToValue a) := by
  have hl : localTyp? ρ "externaddr" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  have he : ValsOnly VarEnv.empty := ⟨rfl, rfl, rfl⟩
  have hc : ∀ (op x : String) (a : Nat), x ∈ ["tagaddr", "globaladdr", "memaddr", "tableaddr",
      "funcaddr"] → IntNumeric.findCase (IntNumeric.instCases Original.d263 0) op =
        some (.varT x [], []) →
      IntNumeric.quantFreeAt (IntNumeric.instCases Original.d263 0) op = true →
      HasTyp (utf8Env B) ρ (.varT "externaddr" []) (.case op (.num (.natN a))) :=
    fun op x a hx hf hq => hasTyp_varT_case hl (findTyp_externaddr B) evalArgs_nil matchArgs_nil
      (IntNumeric.hasTypCase_of_findCase hf (hasTyp_addrAlias B he x hx a) premsOk_nil hq)
  cases a with
  | tag a => exact hc "TAG" "tagaddr" a (by simp) rfl rfl
  | global a => exact hc "GLOBAL" "globaladdr" a (by simp) rfl rfl
  | mem a => exact hc "MEM" "memaddr" a (by simp) rfl rfl
  | table a => exact hc "TABLE" "tableaddr" a (by simp) rfl rfl
  | func a => exact hc "FUNC" "funcaddr" a (by simp) rfl rfl

theorem findTyp_exportinst (B : Builtins) : (utf8Env B).findTyp? "exportinst" = some ([],
    [.instD [] [] (.structT [.mk "NAME" (.varT "name" []) [] [],
      .mk "ADDR" (.varT "externaddr" []) [] []])]) := by
  rw [findTyp?_utf8Env]; exact ConfigOk.findTyp_exportinst

/-- **With the erratum, an export instance within SpecTec's bound is an `exportinst`.** -/
theorem hasTyp_exportinst (B : Builtins) {ρ : VarEnv} (hρ : ValsOnly ρ) (e : ExportInst)
    (hs : e.name.utf8ByteSize < 2 ^ 32) :
    HasTyp (utf8Env B) ρ (.varT "exportinst" []) (exportInstToValue e) := by
  have hl : localTyp? ρ "exportinst" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  have he : ValsOnly VarEnv.empty := ⟨rfl, rfl, rfl⟩
  refine hasTyp_varT_struct hl (findTyp_exportinst B) evalArgs_nil matchArgs_nil ?_
  refine hasTypFields_cons_iff.2 ⟨_, _, rfl, hasTyp_name B he hs, premsOk_nil, ?_⟩
  exact hasTypFields_cons_iff.2 ⟨_, _, rfl, hasTyp_externaddr B he e.addr, premsOk_nil,
    hasTypFields_nil_iff.2 rfl⟩

/-- **The erratum at a one-character export name**: never an `exportinst` in `simEnv B`, an
`exportinst` in `utf8Env B`. -/
theorem exportinst_erratum (B : Builtins) (e : ExportInst) (c : Char)
    (hc : e.name.toList = [c]) :
    ¬ HasTyp (simEnv B) VarEnv.empty (.varT "exportinst" []) (exportInstToValue e) ∧
      HasTyp (utf8Env B) VarEnv.empty (.varT "exportinst" []) (exportInstToValue e) := by
  have hs : e.name.utf8ByteSize < 2 ^ 32 := by
    rw [utf8ByteSize_eq, hc]
    have : (String.utf8EncodeChar c).length ≤ 4 := by
      rw [String.length_utf8EncodeChar]; exact c.utf8Size_le_four
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    omega
  exact ⟨Round5.Pos.not_hasTyp_exportinst_single B ⟨rfl, rfl, rfl⟩ e c hc,
    hasTyp_exportinst B ⟨rfl, rfl, rfl⟩ e hs⟩

end Silmaril.Wasm.SpecTec.Sim.Round7
