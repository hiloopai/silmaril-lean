module

public import Silmaril.Wasm.Component.BinaryP3.Encode.Defs
public import Silmaril.Wasm.Binary.Core.Decode

/-!
# A report on one component binary, for cross-checks against `wasm-tools`

`report bs` parses `bs` with the async-aware parser (`BinaryP3.parse`) and with the
old one (`Binary.parse`), re-encodes the result, and lists the canonical built-ins
in order (nested components included). A test driver prints it
and compares it with `wasm-tools validate`/`print`.

```
parse ok|err <error>              BinaryP3.parse
v0 ok|err <error>                 Binary.parse (8505ba7, no async built-ins)
v0-agrees yes|no|n/a              when both parse: the encodings of `Ast.ofV0 old` and new agree
reencode same|differs|fail        encode (parse bs) = bs
core-modules <n> decoded <k>      embedded core modules; how many silmaril's core decoder takes
outer-alias-sorts ok|bad          every `outer` alias is of a core module, core type, type or
                                  component (`outeraliassort`, see below)
attributes ok|bad                 no `nameattributes` repeats an attribute kind
canons <n>                        the number of built-ins, then one line each:
canon <kind>
```

The last three are checks the grammar does not make: `Binary.md` keeps core modules
opaque bytes (`core:module` is Core WebAssembly's grammar), puts `(if s in outeraliassort)`
on outer aliases without defining `outeraliassort` (the set here is the one `wasm-tools`
1.262.0 enforces in its binary reader), and states attribute uniqueness as a validation
rule, which `wasm-tools` and the component-model tests treat as malformed binaries. They
are executable checks, not proved.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryP3.Check

def errStr (e : Silmaril.Parse.ByteParse.Error) : String := reprStr e

def bytesEq (a b : ByteArray) : Bool := a.data == b.data

open Silmaril.Wasm.Component.Binary (ItemSort CoreSort ExternName NameForm Attribute DefType
  InstanceDecl ComponentDecl AliasTarget)

/-- `outeraliassort`. -/
def outerSortOk : ItemSort → Bool
  | .core .module | .core .type | .type | .component => true
  | _ => false

def aliasOk (a : Binary.Alias) : Bool :=
  match a.target with
  | .outer .. => outerSortOk a.sort
  | _ => true

def attrKind : Attribute → Nat
  | .implements _ => 0 | .versionSuffix _ => 1 | .externalId _ => 2

def nameOk (n : ExternName) : Bool :=
  match n.form with
  | .attrs as => let ks := as.map attrKind; ks.eraseDups.length == ks.length
  | _ => true

def both (a b : Bool × Bool) : Bool × Bool := (a.1 && b.1, a.2 && b.2)

mutual
def defTypeOk : DefType → Bool × Bool
  | .component ds => componentDeclsOk (true, true) ds
  | .instance ds => instanceDeclsOk (true, true) ds
  | _ => (true, true)

def instanceDeclOk : InstanceDecl → Bool × Bool
  | .type t => defTypeOk t
  | .alias a => (aliasOk a, true)
  | .export n _ => (true, nameOk n)
  | .coreType _ => (true, true)

def componentDeclOk : ComponentDecl → Bool × Bool
  | .import n _ => (true, nameOk n)
  | .inst d => instanceDeclOk d

/-- `ds.foldl (fun acc d => both acc (instanceDeclOk d)) acc`. -/
def instanceDeclsOk (acc : Bool × Bool) : List InstanceDecl → Bool × Bool
  | [] => acc
  | d :: ds => instanceDeclsOk (both acc (instanceDeclOk d)) ds

/-- `ds.foldl (fun acc d => both acc (componentDeclOk d)) acc`. -/
def componentDeclsOk (acc : Bool × Bool) : List ComponentDecl → Bool × Bool
  | [] => acc
  | d :: ds => componentDeclsOk (both acc (componentDeclOk d)) ds
end

/-- One step of `strict`: combine the running triple with a section's own triple. -/
def strictStep (acc r : Bool × Bool × List ByteArray) : Bool × Bool × List ByteArray :=
  let (o, att, ms) := acc
  let (o', at', ms') := r
  (o && o', att && at', ms ++ ms')

mutual
/-- The triple of one section (its nested component's, for a `component` section). -/
def strictSection : Section → Bool × Bool × List ByteArray
  | .aliases xs => (xs.all aliasOk, true, [])
  | .types xs => let r := xs.foldl (fun acc t => both acc (defTypeOk t)) (true, true)
    (r.1, r.2, [])
  | .imports xs => (true, xs.all (nameOk ·.name), [])
  | .exports xs => (true, xs.all (nameOk ·.name), [])
  | .instances xs => (true, xs.all (fun
      | .exports es => es.all (nameOk ·.1)
      | _ => true), [])
  | .coreModule b => (true, true, [b])
  | .component c => strict c
  | _ => (true, true, [])

/-- `ss.foldl (fun acc s => strictStep acc (strictSection s)) acc`. -/
def strictSections (acc : Bool × Bool × List ByteArray) : List Section → Bool × Bool × List ByteArray
  | [] => acc
  | s :: ss => strictSections (strictStep acc (strictSection s)) ss

/-- (outer alias sorts ok, attributes ok, core modules) of a component, nested ones included. -/
def strict : Ast → Bool × Bool × List ByteArray
  | .mk ss => strictSections (true, true, []) ss
end

def okBad (b : Bool) : String := if b then "ok" else "bad"

/-- The report lines for one binary. -/
def report (bs : ByteArray) : List String :=
  let new := parse bs
  let old := Binary.parse bs
  let pl := match new with
    | .ok _ => "parse ok" | .error e => s!"parse err {errStr e}"
  let ol := match old with
    | .ok _ => "v0 ok" | .error e => s!"v0 err {errStr e}"
  let agree := match new, old with
    | .ok n, .ok o =>
      match encode n, encode (Ast.ofV0 o) with
      | some a, some b => if bytesEq a b then "v0-agrees yes" else "v0-agrees no"
      | _, _ => "v0-agrees no"
    | _, _ => "v0-agrees n/a"
  match new with
  | .error _ => [pl, ol, agree]
  | .ok c =>
    let re := match encode c with
      | some b => if bytesEq b bs then "reencode same"
        else match parse b with
          | .ok _ => "reencode differs"
          | .error _ => "reencode fail"
      | none => "reencode fail"
    let (oa, att, ms) := strict c
    let dec := (ms.filter fun m => (Silmaril.Wasm.Binary.Core.decode? m).isSome).length
    let cs := c.canons
    [pl, ol, agree, re, s!"core-modules {ms.length} decoded {dec}",
      s!"outer-alias-sorts {okBad oa}", s!"attributes {okBad att}", s!"canons {cs.length}"] ++
      cs.map fun x => s!"canon {x.kind}"

end Silmaril.Wasm.Component.BinaryP3.Check
