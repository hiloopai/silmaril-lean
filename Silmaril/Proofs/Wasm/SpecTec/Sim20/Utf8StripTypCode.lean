module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripTypMod

/-!
# Typing across the `$utf8` erratum at export-free code

* `typedV_instr_of_admin_u20`: in `utf8Env20 B`, a plain instruction typed as an `admininstr` is a
  typed `instr`.
* **`typedV_admin_strip`**, `typedV_admins_strip`: code typed in `utf8Env20 B`, with the exports
  of the modules of its frames removed, is typed in `simEnv20 B`. Plain instructions, arities and
  continuations type alike off `badU20`; a frame's frame goes through `typedV_frame_strip`; the
  other administrative forms are typed in `simEnv20 B` outright.
* `eDA_stripAdmin20`: the body erasure  commutes with removing exports.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Strip

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (recCases)
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d295)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (utf8Env20 types20_utf8Env20)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.StoreDeep (eDA eDAL)

variable {B : Builtins}

/-- **In `utf8Env20 B`, an `admininstr` with a non-administrative head is an `instr`.** -/
theorem typedV_instr_of_admin_u20 {op : MixopS} {w : Value} (hop : op ∉ Whole.adminHeads20)
    (h : TypedV (utf8Env20 B) (.varT "admininstr" []) (.case op w)) :
    TypedV (utf8Env20 B) (.varT "instr" []) (.case op w) := by
  have hd : op ∉ Whole.adminCases20.map Whole.caseHead := Whole.adminCases20_heads ▸ hop
  have hT := (types20_utf8Env20 B).find (Whole.findTyp_admininstr20 (B := StoreBulk.noBuiltins))
  obtain ⟨op', w', he, hc⟩ :=
    hasTypDef_variantT_iff.1 (Whole.hasTypDef_of_closed hT (h _ Whole.valsOnly_empty20))
  obtain ⟨rfl, rfl⟩ : op = op' ∧ w = w' := by simpa using he
  have hc' := (Whole.hasTypCase_append_iff hd).1 (by rw [← Whole.recCases_admininstr20]; exact hc)
  exact Whole.typedV_of_empty20 (hasTyp_varT_case rfl
    ((types20_utf8Env20 B).find (Whole.findTyp_instr20 (B := StoreBulk.noBuiltins)))
    Equiv.evalArgs_nil matchArgs_nil hc')

/-- The payload of a typed `admininstr` case of `utf8Env20 B`, at the case's declared type. -/
theorem hasTyp_adminCase_u20 {op : MixopS} {t : Typ} {prems : List Prem} {w : Value}
    (hf : Sim.IntNumeric.findCase (recCases Original.d295 0 0) op = some (t, prems))
    (h : TypedV (utf8Env20 B) (.varT "admininstr" []) (.case op w)) :
    HasTyp (utf8Env20 B) VarEnv.empty t w := by
  have hT := (types20_utf8Env20 B).find (Whole.findTyp_admininstr20 (B := StoreBulk.noBuiltins))
  obtain ⟨op', w', he, hc⟩ :=
    hasTypDef_variantT_iff.1 (Whole.hasTypDef_of_closed hT (h _ Whole.valsOnly_empty20))
  obtain ⟨rfl, rfl⟩ : op = op' ∧ w = w' := by simpa using he
  exact Sim.IntNumeric.hasTyp_of_hasTypCase hc hf

mutual
/-- **An `admininstr` of `utf8Env20 B` with the exports of its frames removed is an
`admininstr` of `simEnv20 B`.** -/
theorem typedV_admin_strip (hB : ∀ ws, B.call "utf8" ws = none) : ∀ a : Admin,
    TypedV (utf8Env20 B) (.varT "admininstr" []) (adminToV a) →
      TypedV (simEnv20 B) (.varT "admininstr" []) (adminToV (stripAdmin20 a))
  | .plain i, h => by
    obtain ⟨op, w, he, hop⟩ := Whole.instrToV_notAdmin20 i
    have hu : TypedV (utf8Env20 B) (.varT "admininstr" []) (.case op w) := he ▸ h
    have hi : TypedV (simEnv20 B) (.varT "instr" []) (.case op w) :=
      typedV_u20 hB (by decide) (by decide) (typedV_instr_of_admin_u20 hop hu)
    exact (Whole.typedV_plain20_iff i).2 (he ▸ hi)
  | .label n cont body, h => by
    obtain ⟨h₁, h₂, h₃⟩ := Whole.hasTyp_tup3_inv20 (hasTyp_adminCase_u20 Whole.findCase_label20 h)
    exact Whole.typedV_adminLabel20_iff.2 ⟨typedV_u20 hB (by decide) (by decide) h₁,
      typedV_u20 hB (by decide) (by decide) (Whole.typedV_list_of_valsOnly20 ⟨rfl, rfl, rfl⟩ h₂),
      typedV_admins_strip hB body h₃⟩
  | .frame n f body, h => by
    obtain ⟨h₁, h₂, h₃⟩ := Whole.hasTyp_tup3_inv20 (hasTyp_adminCase_u20 Whole.findCase_frame20 h)
    exact Whole.typedV_adminFrame20_iff.2 ⟨typedV_u20 hB (by decide) (by decide) h₁,
      typedV_frame_strip hB (Whole.typedV_of_valsOnly20 ⟨rfl, rfl, rfl⟩ h₂),
      typedV_admins_strip hB body h₃⟩
  | .trap, _ => Whole.typedV_admins_single20_iff.1 Whole.typedV_admins_trap20
  | .callAddr a, _ => Whole.typedV_admins_single20_iff.1 (Whole.typedV_admins_callAddr20 a)
  | .refFuncAddr a, _ => StoreBulk.typedV_admin_val20 (.ref (.funcAddr a))
  | .refHostAddr a, _ => StoreBulk.typedV_admin_val20 (.ref (.hostAddr a))

/-- `typedV_admin_strip` on a sequence. -/
theorem typedV_admins_strip (hB : ∀ ws, B.call "utf8" ws = none) : ∀ l : List Admin,
    TypedV (utf8Env20 B) adminsTy (.list (adminsToV l)) →
      TypedV (simEnv20 B) adminsTy (.list (adminsToV (stripAdmins20 l)))
  | [], _ => typedV_listNil
  | a :: l, h => by
    obtain ⟨ha, hl⟩ := Sim.typedV_list_cons_iff.1 h
    exact Sim.typedV_list_cons_iff.2 ⟨typedV_admin_strip hB a ha, typedV_admins_strip hB l hl⟩
end

end Silmaril.Wasm.SpecTec.Sim20.Utf8Strip
