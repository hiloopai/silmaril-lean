module

public import Silmaril.Wasm.Tools.Meta.Names.Defs
public import Silmaril.Wasm.Tools.Meta.Demangle.Rust.Defs
public import Silmaril.Wasm.Tools.Meta.Demangle.Cpp.Defs

/-!
# `wasm-tools demangle`: the core

`demangle bs` is what `wasm-tools demangle` (1.262.0, `src/bin/wasm-tools/demangle.rs`) writes
for the binary `bs`:

1. A component is refused ("demangling components is not supported"), as soon as its header
   is read.
2. The module is walked with wasmparser's `Parser` (`parseBinary`); a parse error is the error
   of the command.
3. Each section is written back as a `RawSection` (id, minimal size, contents), except a
   custom section named `name` whose contents decode fully (`decodeNames true`: every map,
   no unknown subsection): it is replaced by the encoding of the same subsections with every
   name of every (indirect) name map demangled (`demangleName`); the module name subsection
   is kept. A name section that does not decode is written back unchanged.
4. `demangleName`: Rust (`rustDemangle`) first, then C++ (`cppDemangle`), else the name.

Theorems: `Silmaril.Wasm.Tools.Meta.Demangle.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta.Demangle

open Silmaril.Wasm.Tools.Meta

/-- `demangle.rs`'s `name_map` on one name: Rust, else C++, else unchanged. -/
def demangleName (s : List UInt8) : List UInt8 :=
  match String.fromUTF8? (ByteArray.mk s.toArray) with
  | none => s
  | some str =>
    match rustDemangle str with
    | some t => t.toUTF8.data.toList
    | none =>
      match cppDemangle str with
      | some t => t.toUTF8.data.toList
      | none => s

/-- Demangle every name of a name map. -/
def demangleMap (m : NMap) : NMap := m.map fun (i, s) => (i, demangleName s)

/-- Demangle every name of a decoded subsection (the module name is kept). -/
def demangleSub : NSub → NSub
  | .name n => .name n
  | .map id pre m => .map id pre (demangleMap m)
  | .ind id ms => .ind id (ms.map fun (i, m) => (i, demangleMap m))
  | .raw id d => .raw id d

/-- The new contents of a section: a decodable `name` section is demangled. -/
def demangleSecBody (id : UInt8) (body : List UInt8) : List UInt8 :=
  if id != 0 then rawSec id body else
  match customOf body with
  | .error _ => rawSec id body
  | .ok (nm, data) =>
    if nm != nameName then rawSec id body else
    match decodeNames true data with
    | .error _ => rawSec id body
    | .ok subs => customSec nameName (encNames (subs.map demangleSub))

/-- The output bytes of one item of a module. -/
def demangleItem : Item → List UInt8
  | .sec s => demangleSecBody s.id s.body
  | .nest id _ _ _ => rawSec id []  -- not in a module

/-- **`wasm-tools demangle`** on the bytes of a binary. -/
def demangle (bs : List UInt8) : Except String (List UInt8) :=
  match readHeader none bs with
  | .ok (.component, _) => .error "demangling components is not supported"
  | _ =>
    match parseBinary bs with
    | .error e => .error e
    | .ok (_, items) => .ok (Enc.module.header ++ items.flatMap demangleItem)

end Silmaril.Wasm.Tools.Meta.Demangle

end
