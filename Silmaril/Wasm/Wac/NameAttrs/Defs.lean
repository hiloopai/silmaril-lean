module

public import Silmaril.Wasm.Component.Binary.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs

/-!
# WAC: name attributes of imports and exports

An import or export name of a component may carry attributes (`nameattributes`, the `0x02`
form): `(implements "a:b/i")` says that the instance `b` implements the interface `a:b/i` (the WIT
`import b: a:b/i;`). The composition pipeline names imports and exports by plain strings (kinds
are `List (String × Kind)`), so a composition of a component with `implements` imports wrote
them without the attribute, and the WIT of the result showed inline interfaces where wac's shows
`a:b/i`.

`patch pkgs out` puts the attributes back: the top-level imports of the packages `pkgs` that
carry attributes, by name, are given the same attributes in the composed component `out`, on
its top-level imports of that name written without attributes. Exports are left as they are:
wac 0.12.0 writes the exports of a composition without attributes, and so does wasm-wac. A name
whose packages disagree on its attributes is left alone. Attributes do not change what an
import or export *is* (its sort and type), only its name's spelling and the WIT reading.

When no package name carries an attribute the bytes are unchanged (`patch_of_nil` in this
module), so the theorems about the composed bytes apply as before.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.NameAttrs

open Silmaril.Wasm.Component.Binary

/-- The attributed top-level import names of a component. -/
def attrsOf (b : ByteArray) : List (String × NameForm) :=
  match parse b with
  | .ok a => a.sections.flatMap fun
    | .imports xs => xs.filterMap fun i => match i.name.form with
      | .attrs (_ :: _) => some (i.name.name, i.name.form)
      | _ => none
    | _ => []
  | .error _ => []

/-- The attributes of the packages, one entry per name on which they all agree. -/
def table (pkgs : List ByteArray) : List (String × NameForm) :=
  let all := pkgs.flatMap attrsOf
  all.foldl (fun acc p =>
    if acc.any (·.1 == p.1) then acc
    else if all.all (fun q => q.1 != p.1 || q.2 == p.2) then acc ++ [p] else acc) []

/-- A name spelled without attributes, given those of the table. -/
def fixName (t : List (String × NameForm)) (n : ExternName) : ExternName :=
  match n.form, t.lookup n.name with
  | .attrs (_ :: _), _ => n
  | _, some f => { n with form := f }
  | _, none => n

/-- The top-level imports of a section, given their attributes. -/
def fixSection (t : List (String × NameForm)) : Section → Section
  | .imports xs => .imports (xs.map fun i => { i with name := fixName t i.name })
  | s => s

/-- **The attributes of the packages' names put back on the composed component.** -/
def patch (pkgs : List ByteArray) (out : ByteArray) : ByteArray :=
  match table pkgs with
  | [] => out
  | t =>
    match parse out with
    | .ok a => (encode (.mk (a.sections.map (fixSection t)))).getD out
    | .error _ => out

theorem patch_of_nil {pkgs : List ByteArray} {out : ByteArray} (h : table pkgs = []) :
    patch pkgs out = out := by
  simp [patch, h]

end Silmaril.Wasm.Wac.NameAttrs
