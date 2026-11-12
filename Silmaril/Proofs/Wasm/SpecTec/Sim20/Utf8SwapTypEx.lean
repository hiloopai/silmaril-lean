module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8SwapTyp

/-!
# Typing the exchanged export lists

* `typedV_externAddrU`: every extern address is an `externaddr` of `utf8Env20T B`.
* `typedV_rep_sim`, `typedV_rep_U`: a re-encoding (copies of the empty-named `exp0`) is an
  `exportinst*` of `simEnv20 B` and of `utf8Env20T B`.
* **`typedV_exports_U`**: the exports of a `moduleinst` of `utf8Env20 B` are an `exportinst*` of
  `utf8Env20T B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (utf8Env20T)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (utf8Env20 findTyp_exportinst20 findTyp_externaddr20
  findTyp_globaladdr20 findTyp_tableaddr20 findTyp_memaddr20)

variable {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-- An address at an alias of `addr`, in `utf8Env20T B`. -/
theorem typedV_addrAliasU {x : IL.Id} (ha : x ≠ "admininstr") (hi : x ≠ "instr")
    (htd : (E20 StoreBulk.noBuiltins).findTyp? x =
      some ([], [.instD [] [] (.aliasT (.varT "addr" []))])) (k : Nat) :
    TypedV (utf8Env20T B) (.varT x []) (.num (.natN k)) :=
  Whole.typedV_aliasG (findTypU ha hi htd)
    (Whole.typedV_aliasG (findTypU (by decide) (by decide)
      (Whole.findTyp_addr20 (B := StoreBulk.noBuiltins))) (Whole.hasTyp_nat _ _ k) _
      ⟨rfl, rfl, rfl⟩)

/-- **Every extern address is an `externaddr`** of `utf8Env20T B`. -/
theorem typedV_externAddrU (a : ExternAddr) :
    TypedV (utf8Env20T B) (.varT "externaddr" []) (externAddrV a) := by
  have hx := findTypU (B := B) (by decide) (by decide)
    (findTyp_externaddr20 (B := StoreBulk.noBuiltins))
  cases a with
  | func k =>
    exact Pure.typedV_closedCase20 hx (op := "FUNC") rfl
      (typedV_addrAliasU (by decide) (by decide) (Whole.findTyp_funcaddr20 (B := _)) k _
        ⟨rfl, rfl, rfl⟩)
  | global k =>
    exact Pure.typedV_closedCase20 hx (op := "GLOBAL") rfl
      (typedV_addrAliasU (by decide) (by decide) (findTyp_globaladdr20 (B := _)) k _
        ⟨rfl, rfl, rfl⟩)
  | table k =>
    exact Pure.typedV_closedCase20 hx (op := "TABLE") rfl
      (typedV_addrAliasU (by decide) (by decide) (findTyp_tableaddr20 (B := _)) k _
        ⟨rfl, rfl, rfl⟩)
  | mem k =>
    exact Pure.typedV_closedCase20 hx (op := "MEM") rfl
      (typedV_addrAliasU (by decide) (by decide) (findTyp_memaddr20 (B := _)) k _
        ⟨rfl, rfl, rfl⟩)

/-- A bounded name is a `name` of `utf8Env20T B`. -/
theorem typedV_nameU {s : String} (hs : s.utf8ByteSize < 2 ^ 32) :
    TypedV (utf8Env20T B) (.varT "name" []) (nameV s) := fun _ hρ => hasTyp_name20UT hρ hs

/-- **A re-encoding is an `exportinst*` of `simEnv20 B`.** -/
theorem typedV_rep_sim (k : Nat) :
    TypedV (E20 B) exportsT (expV (List.replicate k exp0)) :=
  typedV_expV_of fun x hx => by
    obtain rfl := List.eq_of_mem_replicate hx
    exact typedV_export_of (B := B) rfl StoreBulk.typedV_name_nil20
      (StoreBulk.typedV_externAddrE (StoreBulk.types20_simEnv20 B) _)

/-- **A re-encoding is an `exportinst*` of `utf8Env20T B`.** -/
theorem typedV_rep_U (k : Nat) :
    TypedV (utf8Env20T B) exportsT (expV (List.replicate k exp0)) :=
  typedV_expV_of fun x hx => by
    obtain rfl := List.eq_of_mem_replicate hx
    exact typedV_export_of (B := B) (findTypU_off _ (by decide) (by decide))
      (typedV_nameU (by decide)) (typedV_externAddrU _)

/-- The `EXPORTS` field of a `moduleinst` of `utf8Env20 B`, typed there. -/
theorem exports_of_moduleInst {m : ModuleInst}
    (h : TypedV (utf8Env20 B) (.varT "moduleinst" []) (moduleInstV m)) :
    HasTyp (utf8Env20 B) VarEnv.empty exportsT (expV m.exports) := by
  have hF := Whole.hasTypFields_of_closed
    ((StoreBulk.types20_utf8Env20 B).find (StoreBulk.findTyp_moduleinst20 (B := B))) h
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Whole.hasTypFields_cons_nil_iff.1 hF
  exact (Whole.hasTypFields_cons_nil_iff.1 hF).1

/-- **The exports of a `moduleinst` of `utf8Env20 B` are an `exportinst*` of `utf8Env20T B`.** -/
theorem typedV_exports_U {m : ModuleInst}
    (h : TypedV (utf8Env20 B) (.varT "moduleinst" []) (moduleInstV m)) :
    TypedV (utf8Env20T B) exportsT (expV m.exports) := by
  have hE := exports_of_moduleInst h
  refine typedV_expV_of fun x hx => ?_
  have hx' : TypedV (utf8Env20 B) (.varT "exportinst" [])
      (.struct [("NAME", nameV x.name), ("ADDR", externAddrV x.addr)]) :=
    Whole.typedV_of_empty20 (Sim.typedV_list_iff.1 (Whole.typedV_list_of_empty20 hE) _
      (List.mem_map_of_mem (f := fun x : ExportInst =>
        Value.struct [("NAME", nameV x.name), ("ADDR", externAddrV x.addr)]) hx) _ ⟨rfl, rfl, rfl⟩)
  have hX := Whole.hasTypFields_of_closed
    ((StoreBulk.types20_utf8Env20 B).find (findTyp_exportinst20 (B := B))) hx'
  obtain ⟨hN, -⟩ := Whole.hasTypFields_cons_nil_iff.1 hX
  exact typedV_export_of (B := B) (findTypU_off _ (by decide) (by decide))
    (typedV_nameU (name_bnd_of_typed20U (Whole.typedV_of_empty20 hN))) (typedV_externAddrU _)

end Silmaril.Wasm.SpecTec.Sim20.Utf8Swap
