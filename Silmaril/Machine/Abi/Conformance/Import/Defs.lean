module

public import Silmaril.Machine.Abi.Conformance.Defs
public import Silmaril.Data.Layout.Header.Import.Defs

/-!
# Coverage and `Declares` from a clang import

The conformance statement reads its prototype through the subset reader (`Declares`,
`Coverage.check`). A clang import (`Data.Layout.Header.Import.Imported`) gives the same
information for headers the subset reader refuses, with what `CProto` does not carry: the
calling convention and the attributes. Here it feeds the same notions.

* `status A ccs e`: what a declaration is for an ABI `A` whose conventions are `ccs`:
  - `claimable`: an external function with a prototype `A.lower` accepts (with the import's
    tag definitions, `imp.header.env`), in one of `ccs`;
  - `unsupported why`: an external function that is not, with the reason. The reason is the
    import's (clang's type is outside `CProto`; the strict decoder refused the node), the
    convention's, an asm label (the binary's symbol is not the C name, which `CodeOf` binds),
    or `A.lower`'s message;
  - `internal why`: a function a binary does not export for the header (clang's implicit
    declaration of a builtin; a `static` function);
  - `notFunction`: a typedef, a tag, a variable.
* `interface`: the first external declaration of each function name, with its
  status. **Every function of the import is in it** or is `internal`; nothing is dropped.
* `coverage A ccs imp claimed`: a `Coverage` that claims `claimed` and excludes every
  other interface function: `unsupported` with its reason, or `unclaimed`.
  `checkCoverage` checks any `Coverage` against the import (as `Coverage.check` does
  against the subset reader's header); `absent` and `unclaimed` exclusions are checked against
  a file by the ELF form, as for the subset route.
* `DeclaresImport A ccs imp f p`: the import gives `f` a prototype that `A` lowers to `p`, in a
  convention of `ccs`. `Thms.declares_iff` gives `Declares ↔ DeclaresImport` when the two
  routes read the same header.

The lowering reads by-value structs and unions in the import's tag definitions
(`imp.header.env`). The import records none yet (`Imported.header` has no `decls`), so on this
route a by-value struct or union is refused as incomplete; an ABI whose lowering ignores tag
definitions (`sysvInt`) lowers alike on both routes.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance

open Silmaril.Data.Layout.Header (CProto)
open Silmaril.Data.Layout.Header.Import

/-- The conventions of `sysvInt` on an x86-64 System V target: the default C convention, and
`sysv_abi`, which there is the default. -/
def sysvCcs : List CallConv := [.c, .sysvAbi]

/-- A convention's spelling. -/
def ccSpelling : CallConv → String
  | .c => "the default C convention"
  | .msAbi => "ms_abi"
  | .sysvAbi => "sysv_abi"
  | .regcall => "regcall"
  | .vectorcall => "vectorcall"
  | .other s => s

/-- What a declaration of the import is for an ABI. -/
inductive Status where
  | claimable
  | unsupported (why : String)
  | internal (why : String)
  | notFunction
  deriving DecidableEq, Repr

/-- The status of a declaration for `A` with conventions `ccs`, its by-value structs and unions
read in `env`. -/
def status (A : AbiDef) (ccs : List CallConv) (env : Silmaril.Data.Layout.Env) (e : Entry) :
    Status :=
  match e.kind, e.body with
  | .function, .function f =>
    if e.implicit then .internal "implicit: clang's declaration of a library builtin"
    else if f.storage == some "static" then .internal "static: internal linkage"
    else if f.symbol != e.name then
      .unsupported ("asm label: the symbol is " ++ f.symbol ++ ", and a row binds the C name")
    else match f.proto with
      | .unsupported why => .unsupported why
      | .ok cp =>
        if !ccs.contains f.cc then .unsupported ("calling convention " ++ ccSpelling f.cc)
        else match A.lower env cp with
          | .error why => .unsupported why
          | .ok _ => .claimable
  | .function, .unsupported why => .unsupported why
  | _, _ => .notFunction

/-- Every declaration with its status, in order, lowered with the import's tag definitions
(`imp.header.env`). -/
def table (A : AbiDef) (ccs : List CallConv) (imp : Imported) : List (String × Status) :=
  imp.entries.map fun e => (e.name, status A ccs imp.header.env e)

/-- Whether a status is a function of the header's interface. -/
def Status.interface : Status → Bool
  | .claimable | .unsupported _ => true
  | .internal _ | .notFunction => false

/-- **The functions a coverage accounts for**: the first external declaration of each name. -/
def interface (A : AbiDef) (ccs : List CallConv) (imp : Imported) :
    List (String × Status) :=
  firstOfEach ((table A ccs imp).filter (·.2.interface)) []

/-- The claimable functions. -/
def claimable (A : AbiDef) (ccs : List CallConv) (imp : Imported) : List String :=
  (interface A ccs imp).filterMap fun (f, s) => if s == .claimable then some f else none

/-- The unsupported functions, with the reasons. -/
def unsupportedFns (A : AbiDef) (ccs : List CallConv) (imp : Imported) :
    List (String × String) :=
  (interface A ccs imp).filterMap fun (f, s) => match s with
    | .unsupported w => some (f, w)
    | _ => none

/-- **A coverage from the import**: `claimed`, and every other interface function excluded,
`unsupported` with the import's reason or `unclaimed` with `why`. -/
def coverage (A : AbiDef) (ccs : List CallConv) (imp : Imported) (claimed : List String)
    (why : String := "not claimed") : Coverage where
  claimed := claimed
  excluded := (interface A ccs imp).filterMap fun (f, s) =>
    if claimed.contains f then none else match s with
      | .unsupported w => some (f, .unsupported w)
      | _ => some (f, .unclaimed why)

/-- **A coverage checked against the import**: every interface function is claimed or
excluded, not both; claimed functions are claimable; excluded names are interface functions,
and an `unsupported` exclusion is a function the import or the lowering refuses. -/
def checkCoverage (A : AbiDef) (ccs : List CallConv) (imp : Imported) (cov : Coverage) :
    Bool :=
  let fs := interface A ccs imp
  fs.all (fun (f, _) => cov.claimed.contains f != cov.excluded.any (·.1 == f)) &&
  cov.claimed.all (fun f => fs.contains (f, .claimable)) &&
  cov.excluded.all fun (f, e) => match e with
    | .unsupported _ => fs.any fun (g, s) => g == f && s.interface && s != .claimable
    | _ => fs.any (·.1 == f)

/-- The convention of every function of the import's `Header` is one of `ccs`. -/
def ccsOk (ccs : List CallConv) (imp : Imported) : Bool :=
  imp.header.names.all fun f => (imp.fn? f).any fun (_, x) => ccs.contains x.cc

/-- **The import declares `f` with a C prototype that `A` lowers to `p`**, in a convention of
`ccs`, with the import's tag definitions (`imp.header.env`). -/
def DeclaresImport (A : AbiDef) (ccs : List CallConv) (imp : Imported) (f : String)
    (p : A.V.Proto) : Prop :=
  ∃ cp, imp.proto? f = some cp ∧ (imp.fn? f).any (fun (_, x) => ccs.contains x.cc) = true ∧
    A.lower imp.header.env cp = .ok p

end Silmaril.Machine.Abi.Conformance

end
