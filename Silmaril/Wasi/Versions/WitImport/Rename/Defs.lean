module

public import Silmaril.Wasi.Versions.WitImport.Resolve.Defs

@[expose] public section

/-!
# Renaming the interfaces of a resolved package

A resolved package (`RPkg`) names interfaces (`Binary.IfaceName`, with the package version)
in three places: the interface of each table entry, the keys of the type environment, and the
`.iface j` owners of type references inside types and kinds. `rnPkg ρ P` applies a map `ρ` of
interface names everywhere. `Silmaril.Wasi.Versions.WitImport.Rename.Thms` shows that an
injective `ρ` does not change the resolved typing (`witROk_rn`).

`swapVer a b` exchanges the package versions `a` and `b` (an involution, so injective). Two
releases of a WASI package whose WIT differs only in the version are related by
`rnPkg (swapVer a b) P = Q`, decided by the kernel; then `witROk P = witROk Q`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasm.Wit

variable (ρ : Binary.IfaceName → Binary.IfaceName)

/-- Rename the owner of a reference. -/
def rnOwner : Binary.Owner → Binary.Owner
  | .local => .local
  | .iface j => .iface (ρ j)

/-- Rename a reference. -/
def rnRef (r : Binary.TyRef) : Binary.TyRef := ⟨rnOwner ρ r.owner, r.name⟩

mutual
/-- Rename the references of a type. -/
def rnTy : Binary.Ty → Binary.Ty
  | .prim p => .prim p
  | .ref r => .ref (rnRef ρ r)
  | .list t => .list (rnTy t)
  | .fixedList t n => .fixedList (rnTy t) n
  | .map k w => .map (rnTy k) (rnTy w)
  | .option t => .option (rnTy t)
  | .result a b => .result (rnTyOpt a) (rnTyOpt b)
  | .tuple ts => .tuple (rnTyList ts)
  | .own r => .own (rnRef ρ r)
  | .borrow r => .borrow (rnRef ρ r)
  | .future t => .future (rnTyOpt t)
  | .stream t => .stream (rnTyOpt t)

/-- Rename an optional type. -/
def rnTyOpt : Option Binary.Ty → Option Binary.Ty
  | none => none
  | some t => some (rnTy t)

/-- Rename a list of types. -/
def rnTyList : List Binary.Ty → List Binary.Ty
  | [] => []
  | t :: ts => rnTy t :: rnTyList ts
end

/-- Rename the types of a kind. -/
def rnKind : Binary.TyDefKind → Binary.TyDefKind
  | .record fs => .record (fs.map fun f => { f with ty := rnTy ρ f.ty })
  | .variant cs => .variant (cs.map fun c => { c with ty := rnTyOpt ρ c.ty })
  | .type t => .type (rnTy ρ t)
  | k => k

/-- Rename a type environment: its keys and kinds. -/
def rnEnv (E : TyEnv) : TyEnv :=
  E.map fun x => (ρ x.1, x.2.map fun d => (d.1, rnKind ρ d.2))

/-- Rename a signature. -/
def rnSig (s : Binary.Sig) : Binary.Sig :=
  ⟨s.async, s.params.map fun p => (p.1, rnTy ρ p.2), rnTyOpt ρ s.result⟩

/-- **Rename a package**: table interfaces, signatures and environment. -/
def rnPkg (P : RPkg) : RPkg :=
  (P.1.map fun x => (x.1, ρ x.2.1, rnSig ρ x.2.2), rnEnv ρ P.2)

/-- Exchange the package versions `a` and `b` of an interface name. -/
def swapVer (a b : String) (j : Binary.IfaceName) : Binary.IfaceName :=
  if j.pkg.version = some a then { j with pkg := { j.pkg with version := some b } }
  else if j.pkg.version = some b then { j with pkg := { j.pkg with version := some a } }
  else j

end Silmaril.Wasi.Versions.WitImport
