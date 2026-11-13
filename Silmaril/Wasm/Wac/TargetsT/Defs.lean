module

public import Silmaril.Wasm.Wac.TypeOf.Defs

/-!
# WAC: typed `targets` on component binaries (`wasm-wac targets`)

`wac targets COMP --wit W --world w` (wac-types' `validate_target`) checks that every import of
the component is an import of the world at a supertype and every export of the world is an
export of the component at a subtype. `Wac.Targets.check` decides only the names and sorts of
that (by projection); the elaborator's `checkTarget` decides it with types for a composition
graph. Here it is decided for a *binary*: the component's kinds from `TypeOf.decodeAny`, the
world's kinds from a WIT package, and the verdict is WIT subtyping of component types,

  `fitsB c w = sub (.comp none c.imports c.exports) (.comp none (promote w.imports) (promote w.exports))`

(`Silmaril.Wasm.Wac.TargetsT.Thms`: `fitsB_iff`, the verdict is `Sub` of the two component kinds;
`fitsB_iff_items`: item by item, as `checkTargetImports`/`checkTargetExports` state it, up to
picking any rather than the first item of a name). `misfits` lists the failing items for the
message; only `fitsB` is the verdict.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.TargetsT

/-- The items of a world as wac compares them (`ItemKind::promote`). -/
def promoteEx (es : Externs) : Externs := es.map fun p => (p.1, p.2.promote)

/-- **The verdict**: the component (imports `ci`, exports `ce`) is a subtype of the world. -/
def fitsB (ci ce wi we : Externs) : Bool :=
  sub (.comp none ci ce) (.comp none (promoteEx wi) (promoteEx we))

/-- The failing items, for the message. -/
def misfits (ci ce wi we : Externs) : List String :=
  (ci.filterMap fun (n, k) =>
    if anyMatch (promoteEx wi) n k then none
    else some s!"the component's import `{n}` is not an import of the world at a supertype") ++
  (we.filterMap fun (n, k) =>
    if anyMatch ce n k.promote then none
    else some s!"the world's export `{n}` is not an export of the component at a subtype")

/-- The world `w` (or the only world) of a WIT package's definitions. -/
def worldOf (defs : Externs) (w : Option String) : Except String (Externs × Externs) :=
  let ws := defs.filterMap fun
    | (n, .type (.comp _ is es)) => some (n, is, es)
    | _ => none
  match w, ws with
  | none, [(_, is, es)] => .ok (is, es)
  | none, _ => .error "the WIT package does not have exactly one world: name one with --world"
  | some n, _ => match ws.find? (·.1 == n) with
    | some (_, is, es) => .ok (is, es)
    | none => .error s!"no world `{n}` in the WIT package"

/-- **`wasm-wac targets`**: the misfits of the component binary `comp` against the world `w`
of the WIT package `wit` (empty: it fits), with the verdict `fitsB`. -/
def check (comp wit : ByteArray) (w : Option String) : Except String (Bool × List String) := do
  let (p, _) ← TypeOf.decodeAny comp
  let (q, _) ← Bridge.decodePkg wit
  let (wi, we) ← worldOf q.defs w
  pure (fitsB p.imports p.exports wi we, misfits p.imports p.exports wi we)

end Silmaril.Wasm.Wac.TargetsT
