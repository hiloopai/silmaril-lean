module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8MonoCall

/-!
# In the 2.0 script, the only `name` is the empty one

An earlier step proved that no one-character string is a `name` of `simEnv20 B`
(`StoreBulk.not_hasTyp_name_single20`) and left longer names open. `$utf8` never returns on a
non-empty list in the 2.0 script (`tryClauses_utf8_single`, `tryClauses_utf8_long20`), so
`name`'s premise `|$utf8(char*)| < 2 ^ 32` has no value on any non-empty string:

* **`not_hasTyp_name_ne20`**, **`typedV_name20_iff`**: a string is a `name` of `simEnv20 B`
  exactly when it is empty;
* **`not_typedV_moduleInst20_ne`**: no module instance exporting a non-empty name is a
  `moduleinst` of `simEnv20 B`;
* **`good20B_names_empty`**: every export of the frame's module of a `Good20B` configuration has
  the empty name. So `Good20B` is, as far as export names go, the export-free case together with
  exports named `""`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Mono

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.ExecNumeric (applies_iff_callDef)
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (utf8Clauses20 findDef_utf8_20 Good20B)

set_option maxRecDepth 100000

/-- `$utf8`'s clauses in `simEnv20 B` are out of fuel on every non-empty list. -/
theorem tryClauses_utf8_ne20 (B : Builtins) {L : List Value} (hL : L ≠ []) (n : Nat) :
    tryClauses n (simEnv20 B) utf8Clauses20 [.val (.list L)] = .error .outOfFuel := by
  rcases L with _ | ⟨u, _ | ⟨u', us⟩⟩
  · exact absurd rfl hL
  · exact tryClauses_utf8_single (findDef_utf8_20 B) u n
  · exact tryClauses_utf8_long20 (findDef_utf8_20 B) u u' us n

/-- **`name`'s premise has no value on a non-empty list** in `simEnv20 B`. -/
theorem not_evalExp_namePrem_ne20 (B : Builtins) {L : List Value} (hL : L ≠ []) (v : Value) :
    ¬ EvalExp (simEnv20 B) (VarEnv.empty.bindVal "char*" (.list L)) Sim.Round5.Pos.namePrem v := by
  intro h
  obtain ⟨v₁, -, h₁, -, -⟩ := evalExp_cmpE_iff.1 h
  obtain ⟨vs, h₂, -⟩ := evalExp_lenE_iff.1 h₁
  have ha : EvalArgs (simEnv20 B) (VarEnv.empty.bindVal "char*" (.list L))
      [.expA (.iterE (.varE "char") Sim.Round5.Pos.charDom)] [.val (.list L)] :=
    evalArgs_cons (Silmaril.SpecTec.Equiv.Execution.evalExp_iterPat (by decide)
      (by simp [VarEnv.findVal?, VarEnv.bindVal, VarEnv.empty, Map.bind])) evalArgs_nil
  have hA := (applies_iff_callDef (by rfl) ha).2 (evalExp_callE_iff.1 h₂)
  obtain ⟨ps, t, cs, hf, hT⟩ := hA
  have hcs : cs = utf8Clauses20 := by
    have h' := hf.symm.trans (findDef_utf8_20 B)
    simp only [Option.some.injEq, Prod.mk.injEq] at h'
    exact h'.2.2
  subst hcs
  rcases hT with ⟨n, hn⟩ | ⟨⟨n, hn⟩, -⟩ <;> simp [tryClauses_utf8_ne20 B hL n] at hn

/-- **A non-empty string is not a `name` of `simEnv20 B`**, in any term-only scope. -/
theorem not_hasTyp_name_ne20 (B : Builtins) {ρ : VarEnv} (hρ : ValsOnly ρ) {L : List Value}
    (hL : L ≠ []) : ¬ HasTyp (simEnv20 B) ρ (.varT "name" []) (.case "%" (.tuple [.list L])) := by
  intro h
  have hl : localTyp? ρ "name" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [StoreBulk.findTyp_name20] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hrest
  · obtain rfl := Sim.IntNumeric.matchArgs_nil_scope hm
    obtain ⟨op, w, he, hc⟩ := hasTypDef_variantT_iff.1 hd
    cases he
    obtain ⟨-, hp⟩ := (hasTypCase_cons_hit_iff rfl).1 hc
    exact not_evalExp_namePrem_ne20 B hL _ (Sim.ConfigOk.evalExp_of_premsOk_if hp)
  · exact absurd hrest not_hasTypInsts_nil

/-- **In `simEnv20 B`, a string is a `name` exactly when it is empty.** -/
theorem typedV_name20_iff (B : Builtins) (s : String) :
    TypedV (simEnv20 B) (.varT "name" []) (nameV s) ↔ s = "" := by
  constructor
  · intro h
    by_contra hs
    have hL : s.toList.map (fun c => Silmaril.SpecTec.Equiv.Execution.pctV c.toNat) ≠ [] := by
      simpa using hs
    exact not_hasTyp_name_ne20 B (ρ := VarEnv.empty) ⟨rfl, rfl, rfl⟩ hL
      (by simpa [nameV] using h VarEnv.empty ⟨rfl, rfl, rfl⟩)
  · rintro rfl
    exact StoreBulk.typedV_name_nil20

/-- **No module instance exporting a non-empty name is a `moduleinst` of `simEnv20 B`.** -/
theorem not_typedV_moduleInst20_ne (B : Builtins) {m : ModuleInst} {x : ExportInst}
    (hx : x ∈ m.exports) (hne : x.name ≠ "") :
    ¬ TypedV (simEnv20 B) (.varT "moduleinst" []) (moduleInstV m) := by
  intro h
  have hF := Whole.hasTypFields_of_closed StoreBulk.findTyp_moduleinst20 h
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨hE, -⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  have hx' : TypedV (simEnv20 B) (.varT "exportinst" [])
      (.struct [("NAME", nameV x.name), ("ADDR", externAddrV x.addr)]) :=
    Whole.typedV_of_empty20 (Sim.typedV_list_iff.1 (Whole.typedV_list_of_empty20 hE) _
      (List.mem_map_of_mem (f := fun x : ExportInst =>
        Value.struct [("NAME", nameV x.name), ("ADDR", externAddrV x.addr)]) hx) _ ⟨rfl, rfl, rfl⟩)
  have hX := Whole.hasTypFields_of_closed StoreBulk.findTyp_exportinst20 hx'
  obtain ⟨hN, -⟩ := Whole.hasTypFields_cons_nil_iff.1 hX
  exact hne ((typedV_name20_iff B x.name).1 (Whole.typedV_of_empty20 hN))

/-- **Every export of the frame's module of a `Good20B` configuration has the empty name.** -/
theorem good20B_names_empty {H : Type} {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile}
    {cfg : Config H} (hg : Good20B hn P cfg) : ∀ x ∈ cfg.frame.module.exports, x.name = "" := by
  intro x hx
  by_contra hne
  obtain ⟨-, hfr⟩ := Whole.typedV_stateV_iff.1 hg.typ.state
  have hF := Whole.hasTypFields_of_closed Whole.findTyp_frame20 hfr
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨hM, -⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  exact not_typedV_moduleInst20_ne _ hx hne (Whole.typedV_of_empty20 hM)

end Silmaril.Wasm.SpecTec.Sim20.Utf8Mono
