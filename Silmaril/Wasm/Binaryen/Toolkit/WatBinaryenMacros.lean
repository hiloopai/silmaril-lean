module

public import Silmaril.Wasm.Binaryen.Toolkit.WatSource
public import Silmaril.Wasm.Text.Extensions.BinaryenMacros

@[expose] public section

/-! Proof-carrying expansion of explicitly specified Binaryen source macros.
The executable is a candidate for the independent expansion relation; success
still requires the existing Core text grammar for the expanded module. -/

namespace Silmaril.Wasm.Binaryen.Toolkit.Wat.BinaryenMacros

open Silmaril Silmaril.Wasm Silmaril.Wasm.Text
open Silmaril.Formats.SExpEncoding (doc toList?)
open Text.Extensions.BinaryenMacros

def fields? (I : Core.IdCtx) (xs : List SExp) :
    {ys : List SExp // List.Forall₂ FieldExpansion xs ys} :=
  match xs with
  | [] => ⟨[], .nil⟩
  | x :: xs =>
      let tail := fields? I xs
      match Source.fieldType? I x with
      | some f => ⟨L [K "field", x] :: tail.1, .cons (.bare f.2) tail.2⟩
      | none => ⟨x :: tail.1, .cons (.kept x) tail.2⟩

def localTree? (I : Core.IdCtx) (x : SExp) :
    {y : SExp // TreeExpansion x y} :=
  match Source.list? x with
  | none => ⟨x, .refl x⟩
  | some items =>
      match hi : items.1 with
      | .atom (.sym "struct") :: xs =>
          let fs := fields? I xs
          ⟨L (K "struct" :: fs.1), by rw [items.2, hi]; exact .structFields fs.2⟩
      | [.atom (.sym "array"), fx] =>
          match Source.list? fx with
          | none => ⟨x, .refl x⟩
          | some inner =>
              match hf : inner.1 with
              | [.atom (.sym "field"), z] =>
                  match Source.fieldType? I z with
                  | none => ⟨x, .refl x⟩
                  | some f => ⟨L [K "array", z], by
                      rw [items.2, hi, inner.2, hf]; exact .arrayField f.2⟩
              | _ => ⟨x, .refl x⟩
      | _ => ⟨x, .refl x⟩

def treeFuel (I : Core.IdCtx) : Nat → (x : SExp) →
    {y : SExp // TreeExpansion x y}
  | 0, x => ⟨x, .refl x⟩
  | fuel + 1, .cons a b =>
      let a' := treeFuel I fuel a
      let b' := treeFuel I fuel b
      let lowered := match a'.1 with
        | .atom (.sym "struct") | .atom (.sym "array") => localTree? I (.cons a'.1 b'.1)
        | _ => ⟨.cons a'.1 b'.1, TreeExpansion.refl _⟩
      ⟨lowered.1, .trans (.cons a'.2 b'.2) lowered.2⟩
  | _ + 1, x => ⟨x, .refl x⟩

def declLocal? (I : Core.IdCtx) (x : SExp) :
    {y : SExp // DeclLocal x y} := Id.run do
  let some items := Source.list? x | return ⟨x, .refl x⟩
  let .atom (.sym "elem") :: rest := items.1 | return ⟨x, .refl x⟩
  let (name, body) := Source.stripId rest
  match body with
  | .atom (.sym "declare") :: fxs =>
      match Source.mapCertified (Source.index? (k := .func) I.funcs) fxs with
      | none => return ⟨x, .refl x⟩
      | some fs =>
          if hx : x = L (K "elem" :: (Source.idSyntax name ++ K "declare" :: fxs)) then
            return ⟨L (K "elem" :: (Source.idSyntax name ++ K "declare" :: K "func" :: fxs)),
              hx ▸ .declarative (Source.idSyntax_sound name) fs.2⟩
          else return ⟨x, .refl x⟩
  | fxs =>
      match Source.mapCertified (Source.index? (k := .func) I.funcs) fxs with
      | none => return ⟨x, .refl x⟩
      | some fs =>
          if hx : x = L (K "elem" :: (Source.idSyntax name ++ fxs)) then
            return ⟨L (K "elem" :: (Source.idSyntax name ++ K "func" :: fxs)),
              hx ▸ .passive (Source.idSyntax_sound name) fs.2⟩
          else return ⟨x, .refl x⟩

def decl? (I : Core.IdCtx) (x : SExp) :
    {y : SExp // DeclExpansion x y} :=
  let t := treeFuel I (syntaxNodes x + 1) x
  let d := declLocal? I t.1
  ⟨d.1, ⟨t.1, t.2, d.2⟩⟩

def expandFields (xs : List SExp) :
    {ys : List SExp // List.Forall₂ DeclExpansion xs ys} :=
  let names : Core.IdCtx := { types := xs.flatMap Source.rawTypeNames }
  let hints := xs.map (Source.fieldHintAt names)
  let J := Core.IdCtx.concat (hints.map Prod.fst)
  let I := { J with types := names.types }
  let rec go : (xs : List SExp) → {ys : List SExp // List.Forall₂ DeclExpansion xs ys}
    | [] => ⟨[], .nil⟩
    | x :: xs =>
        let y := decl? I x
        let tail := go xs
        ⟨y.1 :: tail.1, .cons y.2 tail.2⟩
  go xs

/-- Expand only documented macros, with an exact certificate for the input. -/
def expand? (x : SExp) : Option {y : SExp // ModuleExpansion x y} := do
  let all ← toList? x
  match all with
  | [top] =>
      match toList? top with
      | some (.atom (.sym "module") :: rest) =>
          let (name, xs) := Source.stripId rest
          let ys := expandFields xs
          if hx : x = doc [L (K "module" :: (Source.idSyntax name ++ xs))] then
            some ⟨doc [L (K "module" :: (Source.idSyntax name ++ ys.1))],
              hx ▸ .wrapped (Source.idSyntax_sound name) ys.2⟩
          else none
      | _ =>
          let ys := expandFields all
          if hx : x = doc all then some ⟨doc ys.1, hx ▸ .bare ys.2⟩ else none
  | _ =>
      let ys := expandFields all
      if hx : x = doc all then some ⟨doc ys.1, hx ▸ .bare ys.2⟩ else none

/-- Every accepted original tree expands to its Core grammar interpretation. -/
def parse? (x : SExp) : Option {m : Wasm.Module // ModuleT x m} := do
  let expanded ← expand? x
  match hm : Wat.parseSupported? expanded.1 with
  | none => none
  | some m => pure ⟨m, ⟨expanded.1, expanded.2, .inl (Wat.parseSupported?_sound hm)⟩⟩

/-- Infer a declaration-only element segment. Every original element access
is checked against its old bound before the new segment can be appended. -/
def parseDeclared? (x : SExp) : Option {m : Wasm.Module // ModuleT x m} := do
  let expanded ← expand? x
  match hm : Wat.parseSupported? expanded.1 with
  | none => none
  | some source =>
      let fs ← (List.range source.functionTypes.length).mapM (Idx.ofNat? (kind := .func))
      if hr : fs.map (·.toNat) = List.range source.functionTypes.length then
        if hs : PreservesElementSpace source then
          let segment : Elem := ⟨⟨false, .abstract .func⟩,
            fs.map (fun f => [.refFunc f]), .declarative⟩
          pure ⟨{ source with elems := source.elems ++ [segment] },
            ⟨expanded.1, expanded.2, .inr ⟨source, Wat.parseSupported?_sound hm,
              ⟨segment, hs, ⟨fs, hr, rfl⟩, rfl⟩⟩⟩⟩
        else none
      else none

end Silmaril.Wasm.Binaryen.Toolkit.Wat.BinaryenMacros
