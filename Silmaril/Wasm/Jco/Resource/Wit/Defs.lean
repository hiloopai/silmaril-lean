module

public import Silmaril.Wasm.Jco.Resource.Wrap.Defs
public import Silmaril.Wasm.Jco.Meta.Defs

/-!
# Metadata with resources from a resolved WIT world

`Meta.ofWorld` of `Silmaril.Wasm.Jco.Meta` reads freestanding exported functions only. It rejects
handle types, resource functions and interfaces. This module is a variant, `MetaR.ofWorld`. It
also reads the **resource types and their functions** of exported inline interfaces
(`WorldItem.ifaceInline`, over `Silmaril.Wasm.Wit.Binary.World`).

* Resource types are numbered by the order in which the world's exported interfaces declare
  them (`resEnv`). `own<r>` and `borrow<r>` of a declared resource become `RTy.own`/`RTy.borrow`
  of its number (`RTy.ofWit`). The other types are those of `PTy.ofWit`.
* A function of interface `i` is the world function `i#m`, where `m` is its binary name
  (`Func.mangled`): `f`, `[method]r.f`, `[static]r.f`, `[constructor]r`. A method's `self` is its
  first parameter, a `borrow<r>`, as in the binary encoding. This is the core export name the
  thin wrapper lifts.
* Each resource type `r` of interface `i` also gets its destructor's core export name `i#[dtor]r`
  (`ResWorld.dtors`). Whether the module exports it is not part of the world.
* Freestanding world functions are read as by `Meta.ofWorld`. They may not mention resource
  types: a world has no resource types of its own among its exports.

Rejected, with a message: world imports, interfaces exported by reference (`ifaceRef`, whose
body is in the environment), async functions, handles nested in compound types, other named
types, and signatures over the flat limits after erasure (`Sig.Ok` of `RSig.erase`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Res

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Wit.Binary (Ty TyRef Owner Func Interface WorldItem World TyDefKind)

/-- The resource types of the world: each is the pair (interface name, type name), numbered by
position. -/
abbrev ResEnv := List (String × String)

/-- The number of a resource type of the environment. -/
def ResEnv.find? (env : ResEnv) (key : String × String) : Option RtId := env.idxOf? key

/-- Whether a type definition is a resource type. -/
def isResource : TyDefKind → Bool
  | .resource => true
  | _ => false

/-- The resource types an exported inline interface declares, in order. -/
def ifaceResources (iname : String) (body : Interface) : ResEnv :=
  body.types.filterMap fun d => if isResource d.kind then some (iname, d.name) else none

/-- The resource types of a world's exports. -/
def resEnv (w : World) : ResEnv :=
  w.exports.flatMap fun
    | .ifaceInline n b => ifaceResources n b
    | _ => []

/-- A resolved WIT type with handles of the resources of interface `iname`. -/
def RTy.ofWit (env : ResEnv) (iname : Option String) : Silmaril.Wasm.Wit.Binary.Ty → Option RTy
  | .own ⟨.local, r⟩ => do
    let i ← iname
    (env.find? (i, r)).map .own
  | .borrow ⟨.local, r⟩ => do
    let i ← iname
    (env.find? (i, r)).map .borrow
  | t => (PTy.ofWit t).map .base

/-- The world function of a WIT function, named `name`, inside interface `iname` (if any). -/
def RSig.ofWit (env : ResEnv) (iname : Option String) (name : String) (f : Silmaril.Wasm.Wit.Binary.Func) :
    Except String RSig := do
  if f.async then throw s!"{name}: async functions are not in the fragment"
  let ps ← f.params.mapM fun (p, t) => match RTy.ofWit env iname t with
    | some t' => pure t'
    | none => throw s!"{name}: parameter {p} is not in the fragment"
  let r ← match f.result with
    | none => pure none
    | some t => match RTy.ofWit env iname t with
      | some t' => pure (some t')
      | none => throw s!"{name}: the result is not in the fragment"
  let s : RSig := ⟨name, ps, r⟩
  if s.erase.Ok then pure s else throw s!"{name}: too many flat parameters or a wide flat result"

/-- The world functions of one exported item. -/
def exportSigsR (env : ResEnv) : WorldItem → Except String (List RSig)
  | .func f => do
    if f.kind ≠ .freestanding then throw s!"{f.name}: a resource function outside an interface"
    let s ← RSig.ofWit env none f.name f
    pure [s]
  | .ifaceInline n b => b.funcs.mapM fun f => RSig.ofWit env (some n) (n ++ "#" ++ f.mangled) f
  | .ifaceRef _ _ _ => throw "interfaces exported by reference are not in the fragment"
  | .type _ => throw "types are not exported items"

/-- Metadata with resources, the names of the resource types, and their destructors' core
export names. -/
structure ResWorld where
  md : MetaR
  resources : ResEnv
  dtors : List (RtId × String)
  deriving Repr, Inhabited, DecidableEq

/-- **Metadata with resources from a resolved WIT world** (no imports). -/
def MetaR.ofWorld (w : World) (alloc : String := "alloc") : Except String ResWorld := do
  if !w.imports.isEmpty then throw "imports are not in the fragment"
  let env := resEnv w
  let sss ← w.exports.mapM (exportSigsR env)
  pure { md := ⟨sss.flatten, alloc⟩, resources := env,
         dtors := (List.range env.length).zip (env.map fun (i, r) => i ++ "#[dtor]" ++ r) }

end Silmaril.Wasm.Jco.Res
