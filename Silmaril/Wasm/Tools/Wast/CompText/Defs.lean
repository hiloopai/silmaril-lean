module

public import Silmaril.Wasm.Tools.Wast.Lex.Defs
public import Silmaril.Wasm.Tools.WastEnc.Defs

/-!
# Component text: core modules in text, encoded by the `wast` crate transcription

The component WAT reader (`Silmaril.Wasm.Wac.WatX.readX`) assembles a core module written in
text inside a component with silmaril-lean's certified elaborator, which does not take every
core module (post-3.0 proposals, identifiers in places it does not resolve…). The `wast` crate
encodes a nested core module exactly as a top-level one. `inlineCoreModules src` replaces
every core module **definition** `(core module $id? field…)` that is an item of a component
(not an import descriptor) by `(core module $id? binary "…")`, its bytes from the transcription
of the `wast` crate's encoder (`WastEnc.encodeModule`), so that the reader takes it as bytes.
A module the transcription does not encode is left as it is.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast.CompText

/-- The `\hh` escapes of bytes in a string literal. -/
def hexEscapes (b : ByteArray) : String :=
  let hex := "0123456789abcdef".toList
  String.ofList (b.toList.flatMap fun x =>
    ['\\', hex.getD (x.toNat / 16) '0', hex.getD (x.toNat % 16) '0'])

/-- A core module text `(module …)` through the `wast` crate transcription. -/
def encText (text : String) : Except String ByteArray :=
  match Silmaril.Formats.SExpEncoding.Wat.sexpWatFullExec? .core3 (Annot.stripTrivia text) with
  | none => .error "malformed WAT lexical or bracket syntax"
  | some tree =>
    match elems? tree with
    | some [x] => WastEnc.encodeModuleSrc x text
    | _ => .error "not one module"

def isSymAt (s : String) : PNode → Bool
  | .atom _ (.sym k) => k == s
  | _ => false

/-- Is the list a core module definition `(core module $id? field…)` (not `binary`/`quote`,
not an import descriptor with only a type use)? -/
def coreModuleDef : List PNode → Bool
  | c :: m :: rest =>
    isSymAt "core" c && isSymAt "module" m &&
      (let rest := match rest with
        | .atom _ (.id _) :: r => r
        | r => r
       match rest with
       | .atom _ (.sym "binary") :: _ | .atom _ (.sym "quote") :: _ => false
       | _ => true)
  | _ => false

/-- The replacement (start, stop, text) for the core module definition `kids` spanning
`p`…`q`, if the transcription encodes it. -/
def moduleReplacement (src : ByteArray) (p q : Nat) (kids : List PNode) :
    List (Nat × Nat × String) :=
  match kids with
  | _ :: m :: rest =>
    let text := "(" ++ String.fromUTF8! (src.extract m.pos (q + 1))
    match encText text with
    | .ok b =>
      let idPart := match rest with
        | .atom ip (.id _) :: r =>
          let stopId := match r with
            | y :: _ => y.pos
            | [] => q
          (String.fromUTF8! (src.extract ip stopId)).trimAsciiEnd.toString ++ " "
        | _ => ""
      [(p, q, "(core module " ++ idPart ++ "binary \"" ++ hexEscapes b ++ "\")")]
    | .error _ => []
  | _ => []

/-- The replacements (start, stop, text) for the core module definitions among the items of
the component lists in `xs` (`top`: `xs` are the items of a component). -/
def replacements (src : ByteArray) (top : Bool) (xs : List PNode) :
    List (Nat × Nat × String) :=
  xs.attach.flatMap fun ⟨x, hx⟩ =>
    match x, hx with
    | .list p q kids, hx =>
      if top && coreModuleDef kids then moduleReplacement src p q kids
      else
        match kids, hx with
        | k :: ks, _ => if isSymAt "component" k then replacements src true ks else []
        | [], _ => []
    | .atom .., _ => []
termination_by sizeOf xs
decreasing_by
  have := List.sizeOf_lt_of_mem ‹PNode.list _ _ (_ :: _) ∈ xs›
  simp only [PNode.list.sizeOf_spec, List.cons.sizeOf_spec] at this
  omega

/-- Apply sorted, non-overlapping replacements. -/
def splice (src : ByteArray) (rs : List (Nat × Nat × String)) : String := Id.run do
  let mut out := ""
  let mut i := 0
  for (p, q, t) in rs do
    out := out ++ String.fromUTF8! (src.extract i p) ++ t
    i := q + 1
  out ++ String.fromUTF8! (src.extract i src.size)

/-- Every core module definition of a component text, in bytes (see the module docstring). -/
def inlineCoreModules (s : String) : String :=
  let b := s.toUTF8
  match lexBytes b >>= bracket with
  | .ok xs =>
    let rs := replacements b false xs
    if rs.isEmpty then s else splice b rs
  | .error _ => s

end Silmaril.Wasm.Tools.Wast.CompText
