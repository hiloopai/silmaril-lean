module

public import Silmaril.X86.Link.Contract.Defs
public import Silmaril.X86.Sep.Defs

/-! # Link environments: unit families and code environments

A generalisation of `Contract.TU.Sat` for two needs: specs that depend on a unit's placement
and the link valuation (allocators), and a code environment Γ for function pointers. The
composition theorem for these contracts is not part of this module.

* `Env Code := Nat → Code → Prop`: a **code environment** relates addresses to spec *codes*.
  `Code : Type` is chosen by the user. An interpretation `I : Env Code → Code → Spec` turns a
  code into a spec and may mention `Γ` in any position: `Γ` is a fixed relation, not a fixed
  point, so no monotonicity is needed.
* `Env.Safe L I Γ n ctx`: every entry `(a, c)` of `Γ` is `L.Safe n` at `a` for `I Γ c`.
* `Own Code := Placement → Valuation → Env Code`: a unit's own entries (exports or static
  functions whose address it hands out), at its placement and the link valuation.
* `UnitFam Tag Spec`: a unit whose specs (exports, imports, ownership) may depend on its own
  placement and the link valuation; the object file is fixed (`object_const`).
  `UnitFam.const u` is the constant family; `UnitFam.inst fams layout absolute` is the list of
  units a link uses: slot `k` at `restrict layout k` and the link valuation `σ*`
  (`UnitFam.linkValuation`).
* `TU.SatEnvAt L I Γ own relocate u slot p σ`: the contract of `u` at one slot, placement and
  valuation. If `own ⊆ Γ`, the imports are safe for `n` steps and Γ is safe for `n` steps,
  then the exports and the own entries are safe for `n + 1` steps.
  `TU.SatEnv` is the uniform version (every slot, placement and valuation);
  `UnitFam.SatEnv` is the family version at one slot, placement and valuation.
* `UnitFam.SatAt L relocate U slot p σ`: the contract `TU.SatAt` without code pointers
  (code pointers are `own` entries).
* `FnPtr L I Γ p S`: the word `p` is the address of some Γ entry whose spec refines `S`.
  `fnptr L I Γ p S := ⌜FnPtr L I Γ p S⌝` is its separation-logic form (pure, so duplicable:
  `fnptr_dup`).
-/

@[expose] public section

namespace Silmaril.X86.Link.Env

-- The topic namespace is `Env`, and so is the type of code environments.
set_option linter.dupNamespace false

universe u

open Silmaril.Formats.ELF
open Silmaril.Formats.ELF.Link (Layout AbsoluteSymbols Relocator)
open Silmaril.X86.Link.Unit
open Silmaril.X86.Link.Contract

/-- A code environment: which addresses hold code meeting which spec code. -/
abbrev Env (Code : Type) := Nat → Code → Prop

/-- A unit's own code-environment entries, at its placement and the link valuation. -/
abbrev Own (Code : Type) := Placement → Valuation → Env Code

/-- The empty environment. -/
def Env.empty {Code : Type} : Env Code := fun _ _ => False

/-- No own entries. -/
def Own.empty {Code : Type} : Own Code := fun _ _ _ _ => False

/-- The own entries of slot `slot` (empty past the end of the list). -/
def ownAt {Code : Type} (owns : List (Own Code)) (slot : Nat) : Own Code :=
  owns.getD slot Own.empty

variable {Tag : Type} {Spec : Type u} {Code : Type}

/-- Every entry of `Γ` is safe for `n` steps, at its address, for its interpreted spec. -/
def Env.Safe (L : Logic Spec) (I : Env Code → Code → Spec) (Γ : Env Code) (n : Nat)
    (ctx : Contract.Image) : Prop :=
  ∀ a c, Γ a c → L.Safe n a (I Γ c) ctx

/-- A translation unit whose specs may depend on its placement and on the link valuation.
The object file does not. -/
structure UnitFam (Tag : Type) (Spec : Type u) where
  tu : Placement → Valuation → TU Tag Spec
  object_const : ∀ p σ p' σ', (tu p σ).object = (tu p' σ').object

/-- The object file of a family. -/
def UnitFam.object (U : UnitFam Tag Spec) : ObjectFile := (U.tu [] fun _ => none).object

/-- The constant family of a unit. -/
def UnitFam.const (u : TU Tag Spec) : UnitFam Tag Spec := ⟨fun _ _ => u, fun _ _ _ _ => rfl⟩

/-- The link valuation `σ*` of a list of families. -/
def UnitFam.linkValuation (fams : List (UnitFam Tag Spec)) (layout : Layout)
    (absolute : AbsoluteSymbols) : Valuation :=
  globalValuation (fams.map UnitFam.object) layout absolute

/-- The units of a link: slot `k` instantiated at `restrict layout k` and `σ*`. -/
def UnitFam.inst (fams : List (UnitFam Tag Spec)) (layout : Layout)
    (absolute : AbsoluteSymbols) : List (TU Tag Spec) :=
  fams.mapIdx fun slot U => U.tu (restrict layout slot) (UnitFam.linkValuation fams layout absolute)

/-- **The contract of a unit at one slot, placement and valuation, with a code
environment.** -/
def _root_.Silmaril.X86.Link.Unit.TU.SatEnvAt (L : Logic Spec) (I : Env Code → Code → Spec)
    (Γ : Env Code) (own : Env Code) (relocate : Relocator) (u : TU Tag Spec) (slot : Nat)
    (p : Placement) (σ : Valuation) : Prop :=
  WellPlaced u.object p → ∀ img, u.image slot p σ relocate = some img →
    (∀ a c, own a c → Γ a c) →
    ∀ (n : Nat) (ctx : Contract.Image), Extends img ctx →
      (∀ i ∈ u.imports, ∀ a, σ i.name = some a → L.Safe n a i.spec ctx) →
      Env.Safe L I Γ n ctx →
      (∀ e ∈ u.exports, ∀ a, u.exportAddr p e.name = some a → L.Safe (n + 1) a e.spec ctx) ∧
      (∀ a c, own a c → L.Safe (n + 1) a (I Γ c) ctx)

/-- The uniform contract: every slot, placement and valuation. -/
def _root_.Silmaril.X86.Link.Unit.TU.SatEnv (L : Logic Spec) (I : Env Code → Code → Spec)
    (Γ : Env Code) (own : Own Code) (relocate : Relocator) (u : TU Tag Spec) : Prop :=
  ∀ slot p σ, u.SatEnvAt L I Γ (own p σ) relocate slot p σ

/-- The family contract at one slot, placement and valuation. -/
def UnitFam.SatEnv (L : Logic Spec) (I : Env Code → Code → Spec) (Γ : Env Code)
    (own : Own Code) (relocate : Relocator) (U : UnitFam Tag Spec) (slot : Nat)
    (p : Placement) (σ : Valuation) : Prop :=
  (U.tu p σ).SatEnvAt L I Γ (own p σ) relocate slot p σ

/-- The malloc M1 contract (`TU.SatAt`) of a family, without code pointers: the specs may
mention the unit's own placement and the link valuation. -/
def UnitFam.SatAt (L : Logic Spec) (relocate : Relocator) (U : UnitFam Tag Spec) (slot : Nat)
    (p : Placement) (σ : Valuation) : Prop :=
  WellPlaced (U.tu p σ).object p → ∀ img, (U.tu p σ).image slot p σ relocate = some img →
    ∀ (n : Nat) (ctx : Contract.Image), Extends img ctx →
      (∀ i ∈ (U.tu p σ).imports, ∀ a, σ i.name = some a → L.Safe n a i.spec ctx) →
      ∀ e ∈ (U.tu p σ).exports, ∀ a, (U.tu p σ).exportAddr p e.name = some a →
        L.Safe (n + 1) a e.spec ctx

/-- **Function pointer.** `p` is the address of a Γ entry whose spec refines `S`. -/
def FnPtr (L : Logic Spec) (I : Env Code → Code → Spec) (Γ : Env Code) (p : Silmaril.X86.Word)
    (S : Spec) : Prop :=
  ∃ c, Γ p.toNat c ∧ L.Sub (I Γ c) S

open Silmaril.X86.Sep in
/-- The separation-logic form of `FnPtr`: a pure assertion. -/
def fnptr (L : Logic Spec) (I : Env Code → Code → Spec) (Γ : Env Code) (p : Silmaril.X86.Word)
    (S : Spec) : SProp :=
  spure (FnPtr L I Γ p S)

end Silmaril.X86.Link.Env
