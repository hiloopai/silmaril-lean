module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeNest
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms

/-!
# `STORE` is never typed: the store rules 11–14 are vacuous forward

Earlier passes recorded, as prose (track F2's upstream note 1), that `STORE` has no IL type in the
wasm-2.0 script, so typed configuration images never contain it. This module proves it.

The `STORE` case of `admininstr` (`Original.d295`) carries `numtype; sz?; memarg` and the premise

  `(if numtype = Inn /\ sz.0 < $sizenn(Inn))?{Inn <- Inn?, sz <- sz?}`

whose first domain `Inn?` is bound neither by the payload nor by a defining quantifier. Its
evaluation is undefined, so `premsOk` answers `false` at every fuel (`not_premsOk_unboundOpt`),
and no value is a `STORE` (`not_typedV_store20`).

So every V2 store step, `storeIntTrap`, `storeIntVal`, `storeFloatTrap`, `storeFloatVal`,
`storePackTrap`, `storePackVal` (`Step` 11–14 of the script), starts from a configuration whose
image is not typed, at every builtins and every nesting (`not_typed20_store`,
`not_typed20_nestStore`). A forward statement on those rules from typed images holds vacuously.
The meaningful restatement needs an erratum that binds `Inn` in `STORE`'s premise (as 3.0
does). That is not done here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (recCases)
open Silmaril.Wasm.SpecTec.Sim.Typing (findCaseQ)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d295)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Inverting a case with quantifiers and premises -/

/-- A payload typed by a variant's case: its type, the defined quantifiers and the premises. -/
theorem hasTypCase_inv_findCaseQ {env : Env} {σ : VarEnv} :
    ∀ {cs : List TypCase} {op : MixopS} {t : Typ} {qs : List Param} {prems : List Prem}
      {w : Value}, HasTypCase env σ cs op w → findCaseQ cs op = some (t, qs, prems) →
      HasTyp env σ t w ∧ ∃ ρq, BindQuants env (caseScope σ t w) (quantDefs qs prems) ρq ∧
        PremsOk env ρq prems
  | [], _, _, _, _, _, h, _ => absurd h not_hasTypCase_nil
  | .mk o t' qs' prems' :: cs, op, t, qs, prems, w, h, hf => by
      by_cases ho : o = op
      · simp only [findCaseQ, ho, ite_true, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl, rfl⟩ := hf
        exact (hasTypCase_cons_hit_iffQ ho).1 h
      · simp only [findCaseQ, ho, ite_false] at hf
        exact hasTypCase_inv_findCaseQ ((hasTypCase_cons_miss_iff ho).1 h) hf

/-! ## An option iteration over an unbound domain -/

/-- **An option-iterated premise whose first domain is unbound never holds**: its domain is
undefined, so `premsOk` answers `false` (or runs out of fuel), never `true`. -/
theorem not_premsOk_unboundOpt {env : Env} {ρ : VarEnv} {pr : Prem} {x y : IL.Id}
    {ds : List Dom} (hy : ρ.findVal? y = none) :
    ¬ PremsOk env ρ [.iterPr pr (.mk .opt (.mk x (.varE y) :: ds))] := by
  rintro ⟨n, h⟩
  rcases n with _ | _ | _ | _ | _ | n <;>
    simp [premsOk, premsHold, premHolds, premIter, evalDoms, evalExp, domSrc, hy, Res.elimUndef,
      Res.ofOption] at h

/-! ## `STORE` -/

/-- The `STORE` case of `admininstr`: its payload type, and one premise iterating over `Inn?`. -/
theorem findCaseQ_store20 : ∃ qs pr ds, findCaseQ (recCases Original.d295 0 0) "STORE" =
    some (.tupT [.mk "numtype" (.varT "numtype" []), .mk "sz?" (.iterT (.varT "sz" []) .opt),
      .mk "memarg" (.varT "memarg" [])], qs, [.iterPr pr (.mk .opt (.mk "Inn" (.varE "Inn?") :: ds))]) :=
  ⟨_, _, _, rfl⟩

/-- `Inn?` is not bound by the `STORE` payload's binders. -/
theorem findVal_innOpt_caseScope (w : Value) :
    (caseScope VarEnv.empty (.tupT [.mk "numtype" (.varT "numtype" []),
      .mk "sz?" (.iterT (.varT "sz" []) .opt), .mk "memarg" (.varT "memarg" [])]) w).findVal?
        "Inn?" = none := by
  cases w with
  | tuple vs =>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
      simp [caseScope, typBinds]
  | _ => rfl

/-- **No value is a `STORE`**, at every builtins. -/
theorem not_typedV_store20 (w : Value) :
    ¬ TypedV (simEnv20 B) (.varT "admininstr" []) (.case "STORE" w) := by
  intro h
  obtain ⟨op, w', he, hc⟩ :=
    hasTypDef_variantT_iff.1 (hasTypDef_of_closed findTyp_admininstr20 (h _ valsOnly_empty))
  obtain ⟨rfl, rfl⟩ : "STORE" = op ∧ w = w' := by simpa using he
  obtain ⟨qs, pr, ds, hf⟩ := findCaseQ_store20
  obtain ⟨-, ρq, hb, hp⟩ := hasTypCase_inv_findCaseQ hc hf
  have hq : quantDefs qs [.iterPr pr (.mk .opt (.mk "Inn" (.varE "Inn?") :: ds))] = [] := by
    simp [quantDefs]
  rw [hq, bindQuants_nil_iff] at hb
  subst hb
  exact not_premsOk_unboundOpt (findVal_innOpt_caseScope w) hp

/-- Every V2 integer or float store instruction is encoded as a `STORE`. -/
theorem not_typedV_intStore20 (t : IntType) (p : Option PackSize) (ao : V2.MemArg) :
    ¬ TypedV (simEnv20 B) (.varT "admininstr" []) (adminToV (.plain (.intStore t p ao))) :=
  not_typedV_store20 _

theorem not_typedV_floatStore20 (t : FloatType) (ao : V2.MemArg) :
    ¬ TypedV (simEnv20 B) (.varT "admininstr" []) (adminToV (.plain (.floatStore t ao))) :=
  not_typedV_store20 _

/-- A store instruction of V2. -/
inductive IsStore20 : Admin → Prop where
  | int (t : IntType) (p : Option PackSize) (ao : V2.MemArg) : IsStore20 (.plain (.intStore t p ao))
  | float (t : FloatType) (ao : V2.MemArg) : IsStore20 (.plain (.floatStore t ao))

/-- **A configuration whose code contains a store instruction has no typed image.** -/
theorem not_typed20_store {c : Config H} {a : Admin} (ha : a ∈ c.code) (hs : IsStore20 a) :
    ¬ Typed20 (simEnv20 B) hn c := by
  intro hc
  have hcode := (typed20_iff.1 hc).2
  have hel : TypedV (simEnv20 B) (.varT "admininstr" []) (adminToV a) :=
    Sim.typedV_list_iff.1 hcode _ (by rw [Pure.adminsToV_eq_map]; exact List.mem_map_of_mem ha)
  cases hs with
  | int t p ao => exact not_typedV_intStore20 t p ao hel
  | float t ao => exact not_typedV_floatStore20 t ao hel

/-- The redexes of `Step` 11–14 contain a store instruction. -/
def StoreRedex20 (code : List Admin) : Prop := ∃ a ∈ code, IsStore20 a

/-- **No typed image is a store redex**, nor contains one under any nesting of labels, frames and
value-prefix/suffix contexts. -/
theorem not_typed20_nestStore {R : Config H → Config H → Prop}
    (hR : ∀ c c', R c c' → StoreRedex20 c.code) {c c' : Config H} (h : Nest20 R c c') :
    ¬ Typed20 (simEnv20 B) hn c := by
  induction h with
  | base h =>
    obtain ⟨a, ha, hs⟩ := hR _ _ h
    exact not_typed20_store ha hs
  | @ctx s s' f f' vs is is' rest _ _ ih =>
    intro hc
    obtain ⟨hz, hcode⟩ := typed20_iff.1 hc
    obtain ⟨hvi, -⟩ := typedV_admins_append20_iff.1 hcode
    obtain ⟨-, his⟩ := typedV_admins_append20_iff.1 hvi
    exact ih (typed20_iff.2 ⟨hz, his⟩)
  | label _ ih =>
    intro hc
    obtain ⟨hz, hcode⟩ := typed20_iff.1 hc
    obtain ⟨-, -, his⟩ := typedV_adminLabel20_iff.1 (typedV_admins_single20_iff.1 hcode)
    exact ih (typed20_iff.2 ⟨hz, his⟩)
  | frame _ ih =>
    intro hc
    obtain ⟨hz, hcode⟩ := typed20_iff.1 hc
    obtain ⟨hs, -⟩ := typedV_stateV_iff.1 hz
    obtain ⟨-, hfi, his⟩ := typedV_adminFrame20_iff.1 (typedV_admins_single20_iff.1 hcode)
    exact ih (typed20_iff.2 ⟨typedV_stateV_iff.2 ⟨hs, hfi⟩, his⟩)

/-- **V2's store rules (`Step` 11–14).** -/
inductive StoreStep20 (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) :
    Config H → Config H → Prop where
  | mk {c c' : Config H} (h : Step P host c c') (hs : StoreRedex20 c.code) : StoreStep20 P host c c'

/-- **The forward half on the store rules is vacuous**: no step of `Nest20 (StoreStep20 P host)`
starts from a typed image, at any builtins. -/
theorem not_typed20_storeStep {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    {c c' : Config H} (h : Nest20 (StoreStep20 P host) c c') : ¬ Typed20 (simEnv20 B) hn c :=
  not_typed20_nestStore (fun _ _ h => by cases h with | mk _ hs => exact hs) h

end Silmaril.Wasm.SpecTec.Sim20.Whole
