module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxSites.Thms

/-!
# Round 7, REH route 2: conformance of values checked against their declared types

`Step`'s rule quantifiers are typed at runtime (`Sim.QuantsOk`): each holds a value `v` with
`Sem.HasTyp env ρ t v` for its declared type `t`. Round 6 showed such a value export-free when
`t` is (`NxSites.nxB_of_quantsOk`). This header states what the general case needs: that `v`
conforms to `toAT t` (`NxTyped.vtB sigX`) at every type, including the ten that may hold a
module record.

The induction on `Sem.hasTyp` reads the instances of a type through the entries `sigX` records
for it. Three side conditions make that sound; `typVtItems` checks them on the script:

* a type with an entry in `sigX` has no type parameters, its instances have no type
  patterns, and its record instances have distinct field atoms; and its entries agree with its
  instances (`NxSites.sigTypOk`);
* `aliasFuelOk`: the aliases of `sigX` are fully unfolded within seven steps.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped

/-- `S` has an alias, field or case entry for `x`. -/
def hasEntry (S : Sig) (x : String) : Bool :=
  S.aliases.any (·.1 == x) || S.fields.any (·.1 == x) || S.cases.any (·.1 == x)

/-- The atoms of record fields. -/
def fieldAtoms (fs : List TypField) : List String :=
  fs.map fun f => match f with | .mk a _ _ _ => a

/-- `b` is a list without repetitions. -/
def nodupS : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupS xs

/-- An instance without type patterns, whose record fields (if any) have distinct atoms. -/
def instOk : Inst → Bool
  | .instD _ pats dt => (pats.all fun a => !(a matches .typA _)) && match dt with
    | .structT fs => nodupS (fieldAtoms fs)
    | _ => true

/-- **The side conditions on one type definition.** -/
def typVt (S : Sig) (x : String) (ps : List Param) (insts : List Inst) : Bool :=
  !hasEntry S x || (sigTypOk S x ps insts && (typParams ps).isEmpty && insts.all instOk)

mutual
/-- `typVt` on every type definition of a top-level definition. -/
def typVtItem (S : Sig) : Def → Bool
  | .typD x ps insts => typVt S x ps insts
  | .recD ds => typVtItems S ds
  | _ => true

/-- `typVtItem` on a list. -/
def typVtItems (S : Sig) : List Def → Bool
  | [] => true
  | d :: ds => typVtItem S d && typVtItems S ds
end

/-- The aliases of `S` unfold completely within seven steps. -/
def aliasFuelOk (S : Sig) : Bool :=
  S.aliases.all fun p => atEq (unalias S 7 p.2) (unalias S 8 p.2)

end Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant
