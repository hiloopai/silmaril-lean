module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8SwapTypMod

/-!
# Typing across the `$utf8` erratum at re-encoded code

Round 7's `Utf8StripTypCode` for a re-encoding `F` whose export images are typed in `simEnv20 B`:
**`typedV_admin_exp`**, `typedV_admins_exp`: code typed in `utf8Env20 B`, with the exports of the
modules of its frames re-encoded, is typed in `simEnv20 B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Swap

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
open Silmaril.Wasm.SpecTec.Sim20.Utf8Strip (typedV_u20 typedV_listNil typedV_instr_of_admin_u20
  hasTyp_adminCase_u20)

variable {B : Builtins} {F : ModuleInst → List ExportInst}

mutual
/-- **An `admininstr` of `utf8Env20 B` with the exports of its frames removed is an
`admininstr` of `simEnv20 B`.** -/
theorem typedV_admin_exp (hB : ∀ ws, B.call "utf8" ws = none)
    (hF : ∀ m : ModuleInst, TypedV (simEnv20 B) exportsT (expV (F m))) : ∀ a : Admin,
    TypedV (utf8Env20 B) (.varT "admininstr" []) (adminToV a) →
      TypedV (simEnv20 B) (.varT "admininstr" []) (adminToV (expAdmin20 F a))
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
      typedV_admins_exp hB hF body h₃⟩
  | .frame n f body, h => by
    obtain ⟨h₁, h₂, h₃⟩ := Whole.hasTyp_tup3_inv20 (hasTyp_adminCase_u20 Whole.findCase_frame20 h)
    exact Whole.typedV_adminFrame20_iff.2 ⟨typedV_u20 hB (by decide) (by decide) h₁,
      typedV_frame_exp hB hF (Whole.typedV_of_valsOnly20 ⟨rfl, rfl, rfl⟩ h₂),
      typedV_admins_exp hB hF body h₃⟩
  | .trap, _ => Whole.typedV_admins_single20_iff.1 Whole.typedV_admins_trap20
  | .callAddr a, _ => Whole.typedV_admins_single20_iff.1 (Whole.typedV_admins_callAddr20 a)
  | .refFuncAddr a, _ => StoreBulk.typedV_admin_val20 (.ref (.funcAddr a))
  | .refHostAddr a, _ => StoreBulk.typedV_admin_val20 (.ref (.hostAddr a))

/-- `typedV_admin_exp` on a sequence. -/
theorem typedV_admins_exp (hB : ∀ ws, B.call "utf8" ws = none)
    (hF : ∀ m : ModuleInst, TypedV (simEnv20 B) exportsT (expV (F m))) : ∀ l : List Admin,
    TypedV (utf8Env20 B) adminsTy (.list (adminsToV l)) →
      TypedV (simEnv20 B) adminsTy (.list (adminsToV (expAdmins20 F l)))
  | [], _ => typedV_listNil
  | a :: l, h => by
    obtain ⟨ha, hl⟩ := Sim.typedV_list_cons_iff.1 h
    exact Sim.typedV_list_cons_iff.2 ⟨typedV_admin_exp hB hF a ha, typedV_admins_exp hB hF l hl⟩
end

end Silmaril.Wasm.SpecTec.Sim20.Utf8Swap
