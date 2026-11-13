module

public import Silmaril.Wasm.Component.Conformance.Extra.Defs

/-!
# Rules of wasmparser 1.262.0 that neither the copied validator nor `Conformance.Extra` has

Executable checks on the reference syntax, run by `Validate.check` after `checkCore3?` and
`Conformance.Extra.extraProblem`. Each one is transcribed from
`crates/wasmparser/src/validator/component.rs` of wasm-tools 1.262.0 and was found by the
differential suite `tools/wasm-tools/tests/compval/validate.sh` (a binary upstream rejects and
the reference accepts):

* **`version-suffix`** (🔗, `validate_and_register_named_types`'s name check, and
  `validation/version-suffix.wast` at component-model `d095e2f`): the attribute needs the
  `cm-canon-names` feature, is allowed on instances only, is not empty, and applies to an
  interface name with a version (the `implements` value when there is one, else the name);
  that version `v` followed by the suffix is a SemVer version `full`, and `v` is the
  canonical version of `full` (build metadata dropped; with a pre-release part, the version
  itself; else its major version, `0.minor` or `0.0.patch`). Without a suffix, an interface version (of the
  name or of `implements`) must be a SemVer version: a bare canonical version such as `@1`
  needs a suffix. Messages follow wasmparser's (`is not the canonical version of`, `version
  suffix cannot be empty`, `only instances can have a `version-suffix``, …).
* **`context.get`/`context.set` immediates** (`check_context_immediate`): an index above 0
  needs 🧵 `cm-threading`, and no index is above 1.

Not here (still open): wasmparser's limit on the nesting depth of value types (`type nesting
is too deep`), and the rules listed as not modelled in `Conformance.Extra`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Gates

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Conformance

/-- The version of an interface name, if it is one and has a version. -/
def ifaceVersion? (s : String) : Option (Option String) :=
  match Syntax.externNameKind s with
  | .interface i => some i.version
  | _ => none

/-- The leading decimal number of a list of characters. -/
def natOf (cs : List Char) : Nat := cs.foldl (fun n c => 10 * n + (c.toNat - 48)) 0

/-- The canonical version of a SemVer version (`canonversion` of `Explainer.md`, as wasmparser
1.262.0 computes it): build metadata is dropped; a version with a pre-release part is its own
canonical version (without the build part); otherwise the major version when non-zero, else
`0.minor` when the minor version is non-zero, else `0.0.patch`. -/
def canonOf (full : String) : String :=
  let cs := full.toList.takeWhile (· != '+')
  if cs.contains '-' then String.ofList cs
  else match Syntax.splitAll '.' cs with
    | [a, b, c] =>
      if natOf a ≠ 0 then String.ofList a
      else if natOf b ≠ 0 then "0." ++ String.ofList b
      else "0.0." ++ String.ofList c
    | _ => full

/-- What is wrong with the version part of a name and its attributes (`inst`: whether the
item is an instance, `none` when unknown). -/
def versionProblem (canonNames : Bool) (n : Syntax.ExternName) (inst : Option Bool) :
    Option String :=
  let impl := n.attrs.findSome? fun | .implements i => some i | _ => none
  let suffix := n.attrs.findSome? fun | .versionSuffix s => some s | _ => none
  let target := impl.getD n.name
  match suffix with
  | some s =>
    if !canonNames then some "the `cm-canon-names` feature is not active"
    else if inst == some false then some "only instances can have a `version-suffix`"
    else if s.isEmpty then some "version suffix cannot be empty"
    else match ifaceVersion? target with
      | none => some "`version-suffix` requires an interface name or `implements`"
      | some none => some "a version suffix requires the name to have a version"
      | some (some v) =>
        let full := v ++ s
        if !Extra.semver full.toList then some s!"`{full}` is not valid: not a SemVer version"
        else if canonOf full != v then some s!"`{v}` is not the canonical version of `{full}`"
        else none
  | none =>
    match ifaceVersion? target with
    | some (some v) =>
      if Extra.semver v.toList then none
      else if impl.isSome then some s!"invalid interface version: `{v}`"
      else some s!"name `{n.name}` is not valid: `{v}` is not a SemVer version"
    | _ => none

/-- `context.get`/`context.set` immediates. -/
def contextProblem (threads : Bool) (op : String) (i : Nat) : Option String :=
  if i = 0 then none
  else if i > 1 then some s!"`{op}` immediate must be zero or one: {i}"
  else if !threads then some s!"`{op}` immediate must be zero: {i}"
  else none

/-- Is a descriptor an instance? -/
def descInst (d : Syntax.ExternDesc) : Bool := Extra.descSort d == .instance_

mutual

def defType (F : Features) : Syntax.DefType → Option String
  | .component ds => componentDecls F ds
  | .instance_ ds => instanceDecls F ds
  | _ => none

def instanceDecl (F : Features) : Syntax.InstanceDecl → Option String
  | .type t => defType F t
  | .export_ n e => versionProblem F.canonicalNames n (some (descInst e))
  | _ => none

def instanceDecls (F : Features) : List Syntax.InstanceDecl → Option String
  | [] => none
  | d :: ds => instanceDecl F d <|> instanceDecls F ds

def componentDecls (F : Features) : List Syntax.ComponentDecl → Option String
  | [] => none
  | d :: ds =>
    let p := match d with
      | .import_ n e => versionProblem F.canonicalNames n (some (descInst e))
      | .decl d => instanceDecl F d
    p <|> componentDecls F ds

end

mutual

/-- One definition. -/
def definition (F : Features) : Syntax.Definition Silmaril.Wasm.Module → Option String
  | .component defs => definitions F defs
  | .type t => defType F t
  | .import_ n d => versionProblem F.canonicalNames n (some (descInst d))
  | .export_ n si _ => versionProblem F.canonicalNames n (some (si.sort == .instance_))
  | .instance_ (.exports items) =>
    items.findSome? fun (n, si) => versionProblem F.canonicalNames n (some (si.sort == .instance_))
  | .canon (.builtin (.contextGet _ i)) => contextProblem F.threads "context.get" i
  | .canon (.builtin (.contextSet _ i)) => contextProblem F.threads "context.set" i
  | _ => none

def definitions (F : Features) :
    List (Syntax.Definition Silmaril.Wasm.Module) → Option String
  | [] => none
  | d :: ds => definition F d <|> definitions F ds

end

/-- **The gate rules** on a component: the first problem, if any. -/
def gateProblem (F : Features) (c : RefComponent) : Option String := definitions F c

end Silmaril.Wasm.Tools.Component.Gates
