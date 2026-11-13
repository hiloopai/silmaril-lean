module

public import Silmaril.Automata.Spec.Defs
import all Lean.Data.Json.Basic

/-!
# The JSON codec of machine documents: proofs

Round trips of `Silmaril.Automata.Spec`'s codec, at the level of `Lean.Json` values.
-/

@[expose] public section

namespace Silmaril.Proofs.Automata

open Lean Silmaril.Automata

theorem mapM_getStr (xs : List String) :
    (xs.map Json.str).mapM Json.getStr? = (.ok xs : Except String (List String)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.mapM_cons, ih]
    rfl

theorem strsOfJson?_strsToJson (xs : List String) : strsOfJson? (strsToJson xs) = .ok xs := by
  unfold strsOfJson? strsToJson
  simp only [Json.getArr?]
  exact mapM_getStr xs

theorem edge_ofJson?_toJson (e : Edge) : Edge.ofJson? e.toJson = .ok e := by
  unfold Edge.ofJson? Edge.toJson
  rw [strsOfJson?_strsToJson]
  rfl

theorem mapM_edge (es : List Edge) :
    (es.map Edge.toJson).mapM Edge.ofJson? = (.ok es : Except String (List Edge)) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, List.mapM_cons, ih, edge_ofJson?_toJson]
    rfl

theorem edgesOfJson?_edgesToJson (es : List Edge) : edgesOfJson? (edgesToJson es) = .ok es := by
  unfold edgesOfJson? edgesToJson
  simp only [Json.getArr?]
  exact mapM_edge es

theorem spec_ofJson?_toJson (sp : Spec) : Spec.ofJson? sp.toJson = .ok sp := by
  obtain ⟨a, b, c⟩ := sp
  show (do
      return ⟨← strsOfJson? (strsToJson a), ← strsOfJson? (strsToJson b),
        ← edgesOfJson? (edgesToJson c)⟩ : Except String Spec) = _
  rw [strsOfJson?_strsToJson, strsOfJson?_strsToJson, edgesOfJson?_edgesToJson]
  rfl

theorem layers_ofJson?_toJson (ly : Layers) : Layers.ofJson? ly.toJson = .ok ly := by
  obtain ⟨a, b, c, d⟩ := ly
  show (do
      return ⟨← strsOfJson? (strsToJson a), ← strsOfJson? (strsToJson b),
        ← strsOfJson? (strsToJson c), ← strsOfJson? (strsToJson d)⟩ : Except String Layers) = _
  simp only [strsOfJson?_strsToJson]
  rfl

theorem document_ofJson?_toJson (d : Document) : Document.ofJson? d.toJson = .ok d := by
  obtain ⟨i, ⟨a, b, c⟩, ly⟩ := d
  show (do
      let layers ← Layers.ofJson? ly.toJson
      return ⟨← (Json.str i).getStr?, ← (do
        return ⟨← strsOfJson? (strsToJson a), ← strsOfJson? (strsToJson b),
          ← edgesOfJson? (edgesToJson c)⟩ : Except String Spec), layers⟩ :
      Except String Document) = _
  rw [layers_ofJson?_toJson, strsOfJson?_strsToJson, strsOfJson?_strsToJson,
    edgesOfJson?_edgesToJson]
  rfl

end Silmaril.Proofs.Automata
