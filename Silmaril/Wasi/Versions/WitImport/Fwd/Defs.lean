module

public import Silmaril.Wasi.Versions.WitImport.RFree.Thms
public import Silmaril.Wasi.Versions.WitImport.Compare.Defs
public import Silmaril.Wasi.Versions.WitImport.Pick.Defs
public import Silmaril.Wasi.Versions.WitImport.NetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.Http3Table.Defs
public import Silmaril.Wasi.Versions.Stateful.Defs

@[expose] public section

/-!
# Forwarding adapters between WIT packages with the same signatures

The simplest adapter between two versions of a WASI interface forwards each call to the
function of the other version with the same name, and returns its answer. It is correct for
the WIT typing when the two functions have the same parameter and result types and those
types mention no named type (so the resolved typing does not depend on the package version of
the type environment, `Silmaril.Wasi.Versions.WitImport.RFree`).

* `FwdMap`: pairs `(exported function, imported function)`.
* `fwdPairs P Q`: for an import package `P` and an export package `Q`, the functions of `Q`
  (outside `wasi:cli/run`, an export of the command world, not a host function) with a function
  of `P` in the same interface (version dropped, `unver`) with the same name, both signatures
  free of named types and with the same types (`sigTypes`). Computed from the imported tables.
* `fwdBody M`: the stateless component exporting `fwdX M` and importing `fwdI M` that forwards.
* `FwdOk P Q M`: every pair of `M` has free signatures with the same types in `Q` and `P`.

`Silmaril.Wasi.Versions.WitImport.Fwd.Thms` proves that over every host of the import package's
typing `witRTh P` the forwarder is a model of the export package's typing `witRTh Q`, and lists
the pairs between 0.2.12 and 0.3.2 in both directions.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Wit
open Silmaril.Wasi.Versions (SBody SProg)

/-- Pairs (exported function, imported function). -/
abbrev FwdMap := List (FnName × FnName)

/-- The exported functions of a forwarding map. -/
def fwdX (M : FwdMap) : Set FnName := {f | f ∈ M.map Prod.fst}

/-- The imported functions of a forwarding map. -/
def fwdI (M : FwdMap) : Set FnName := {g | g ∈ M.map Prod.snd}

/-- The function a call is forwarded to. -/
def fwdTo (M : FwdMap) (f : FnName) : FnName := (M.lookup f).getD f

/-- The two functions match: same name and interface (version dropped), free signatures with
the same types. The name is compared first: `&&` stops there for most pairs, so the kernel
rarely evaluates `unver`, which decodes the interface string. -/
def fwdMatch (x y : FnName × Binary.IfaceName × Binary.Sig) : Bool :=
  x.1.fn == y.1.fn && unver x.1.iface == unver y.1.iface && sigFree x.2.2 && sigFree y.2.2 &&
    decide (sigTypes x.2.2 = sigTypes y.2.2)

/-- **The forwarding pairs** from the functions of `Q` to those of `P`. -/
def fwdPairs (P Q : RPkg) : FwdMap :=
  (Q.1.filter fun x => unver x.1.iface != "wasi:cli/run").filterMap fun x =>
    (P.1.find? (fwdMatch x)).map fun y => (x.1, y.1)

/-- The pairs have free signatures with the same types. -/
def FwdOk (P Q : RPkg) (M : FwdMap) : Bool :=
  M.all fun fg =>
    match Q.1.lookup fg.1, P.1.lookup fg.2 with
    | some (_, s), some (_, s') => sigFree s && sigFree s' && decide (sigTypes s = sigTypes s')
    | _, _ => false

/-- A key of a list of pairs has a lookup. -/
theorem lookup_some_of_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {L : List (α × β)} {a : α} {b : β}, (a, b) ∈ L → ∃ b', L.lookup a = some b'
  | [], _, _, h => absurd h List.not_mem_nil
  | (x, y) :: L, a, b, h => by
    by_cases hx : a = x
    · subst hx
      exact ⟨y, by simp [List.lookup]⟩
    · have hL : (a, b) ∈ L := by
        rcases List.mem_cons.1 h with e | e
        · exact absurd (congrArg Prod.fst e) hx
        · exact e
      simpa [List.lookup, beq_false_of_ne hx] using lookup_some_of_mem hL

theorem fwdTo_mem {M : FwdMap} {f : FnName} (hf : f ∈ fwdX M) : fwdTo M f ∈ fwdI M := by
  obtain ⟨⟨f', g⟩, hm, rfl⟩ := List.mem_map.1 hf
  obtain ⟨g', hg'⟩ := lookup_some_of_mem hm
  show (M.lookup f').getD f' ∈ M.map Prod.snd
  rw [hg', Option.getD_some]
  exact List.mem_map.2 ⟨(f', g'), rlookup_mem hg', rfl⟩

/-- **The forwarder**: each call is passed to the paired function, its answer returned. -/
def fwdBody (M : FwdMap) : SBody Unit (fwdI M) (fwdX M) := fun _ q =>
  .call (⟨fwdTo M q.1.1, fwdTo_mem q.1.2⟩, q.2) fun n => .pure ((), n)

end Silmaril.Wasi.Versions.WitImport
