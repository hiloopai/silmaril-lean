module

public import Silmaril.Wasi.Versions.WitImport.RNetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables3.Defs

@[expose] public section

/-!
# WIT-derived constants below the hand-written WASI modules

The definitions of this module are read off the resolved tables and type environments that the
WIT importer produces from `specs/wasi` (`Silmaril.Wasi.Versions.WitImport.RNetTables`,
`Silmaril.Wasi.Versions.WitImport.RTables3`). Unlike the check module `Switch`,
this module imports **no hand-written WASI module**, so the hand-written modules
(`Silmaril.Wasi.Versions.Net3`, …) can be defined from it:

* `caseNames`, `caseIdx`: the case labels of an enum or variant, and the number of a label;
* `codes2W`, `codes3W`: the cases of 0.2 `wasi:sockets/network.error-code` and 0.3
  `wasi:sockets/types.error-code`; `eNotInProgressW`, `eWouldBlockW`, `eConnRefusedW`,
  `eOther3W`: case numbers by name;
* `e2to3W`, `e3to2W`: socket codes translated between the versions by case *name*;
* `cases3W`, `payloads3W`, `ecV3W`: the 0.3 code value, with the `option` payload `none` for a
  case whose WIT payload is an `option` (`other(option<string>)`);
* `eDnsTimeout2W`, `eDnsTimeout3W`: `DNS-timeout` in the HTTP `error-code` of both versions.

What is trusted: the importer glue that produced the quoted tables (see
`Silmaril.Wasi.Versions.WitImport.RCheck`). Everything here is kernel-reducible Lean code on those
tables.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasm.Wit

/-- The case labels of a named type's definition (enum or variant). -/
def caseNames : Option (Binary.IfaceName × Binary.TyDefKind) → List String
  | some (_, .enum cs) => cs.map (·.name)
  | some (_, .variant cs) => cs.map (·.name)
  | _ => []

/-- The case number of a label (the number of cases when absent). -/
def caseIdx (cs : List String) (n : String) : Nat := cs.idxOf n

/-- The cases of 0.2 `wasi:sockets/network.error-code`, from the WIT. -/
def codes2W : List String :=
  caseNames (findTy sock2P.2 ⟨⟨"wasi", "sockets", some "0.2.12"⟩, "network"⟩
    ⟨.local, "error-code"⟩)

/-- The cases of 0.3 `wasi:sockets/types.error-code`, from the WIT. -/
def codes3W : List String :=
  caseNames (findTy sock3P.2 ⟨⟨"wasi", "sockets", some "0.3.2"⟩, "types"⟩
    ⟨.local, "error-code"⟩)

/-- `error-code.not-in-progress`, by name. -/
def eNotInProgressW : Nat := caseIdx codes2W "not-in-progress"
/-- `error-code.would-block`, by name. -/
def eWouldBlockW : Nat := caseIdx codes2W "would-block"
/-- `error-code.connection-refused`, by name. -/
def eConnRefusedW : Nat := caseIdx codes2W "connection-refused"
/-- 0.3 `error-code.other`, by name. -/
def eOther3W : Nat := caseIdx codes3W "other"

/-- A 0.2 code as the 0.3 code of the same name (`other` without one). -/
def e2to3W (k : Nat) : Nat :=
  match codes2W[k]? with
  | some n => if n ∈ codes3W then caseIdx codes3W n else eOther3W
  | none => eOther3W

/-- A 0.3 code as the 0.2 code of the same name (`unknown` without one). -/
def e3to2W (k : Nat) : Nat :=
  match codes3W[k]? with
  | some n => if n ∈ codes2W then caseIdx codes2W n else caseIdx codes2W "unknown"
  | none => caseIdx codes2W "unknown"

/-- The cases of 0.3 `error-code` with their payload types. -/
def cases3W : List (Binary.Labeled (Option Binary.Ty)) :=
  match findTy sock3P.2 ⟨⟨"wasi", "sockets", some "0.3.2"⟩, "types"⟩ ⟨.local, "error-code"⟩ with
  | some (_, .variant cs) => cs
  | _ => []

/-- The payload types of the 0.3 `error-code` cases. -/
def payloads3W : List (Option Binary.Ty) := cases3W.map (·.ty)

/-- The value of a 0.3 code: an `option` payload is `none`, as WIT's `other(option<string>)`. -/
def ecV3W (k : Nat) : Silmaril.Wasm.Component.Val :=
  match payloads3W[k]? with
  | some (some (.option _)) => .variant k (some (.variant 0 none))
  | _ => .variant k none

/-- `DNS-timeout`, by name, in the HTTP `error-code` of 0.2. -/
def eDnsTimeout2W : Nat :=
  caseIdx (caseNames (findTy http2P.2 ⟨⟨"wasi", "http", some "0.2.12"⟩, "types"⟩
    ⟨.local, "error-code"⟩)) "DNS-timeout"

/-- `DNS-timeout`, by name, in the HTTP `error-code` of 0.3. -/
def eDnsTimeout3W : Nat :=
  caseIdx (caseNames (findTy http3P.2 ⟨⟨"wasi", "http", some "0.3.2"⟩, "types"⟩
    ⟨.local, "error-code"⟩)) "DNS-timeout"

end Silmaril.Wasi.Versions.WitImport
