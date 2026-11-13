module

public import Silmaril.Wasm.Wit.Binary.Custom.Defs
public import Silmaril.Proofs.Wasm.Wit.Binary.Json
public import Silmaril.Proofs.Wasm.Wit.Binary.Sim.Items
public import Silmaril.Wasm.Component.Binary.Thms

/-!
# WIT packages as bytes

`decodePackage_encodePackage`: the bytes wit-component writes for a valid
package decode to its normal form with the metadata of `package-docs` put
back (`p.normalize.inject p.docsJson`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary

/-- The `package-docs` section reads back. -/
theorem readDocsSection_docsSection (p : Package) : readDocsSection (docsSection p) = some p.docsJson := by
  have hd : (docsSection p).data.toList = 1 :: (String.ofList p.docsJson.print).toUTF8.data.toList := by
    simp [docsSection, ByteArray.data_append]
  have hb : (⟨(String.ofList p.docsJson.print).toUTF8.data.toList.toArray⟩ : ByteArray) =
      (String.ofList p.docsJson.print).toByteArray := by simp
  simp only [readDocsSection, hd, hb, String.fromUTF8Lossy_toByteArray, String.toList_ofList,
    JVal.parse_print]
  simp

/-- Whether a section is a custom section. -/
def isCustomSec : Section → Bool
  | .custom .. => true
  | _ => false

theorem splitCustom_customs : ∀ cs : List (String × ByteArray),
    splitCustom (cs.map fun c => .custom c.1 c.2) = ([], cs)
  | [] => rfl
  | c :: cs => by simp [splitCustom, splitCustom_customs cs]

theorem splitCustom_items : ∀ (items : List Section) (cs : List (String × ByteArray)),
    (∀ s ∈ items, isCustomSec s = false) →
    splitCustom (items ++ cs.map fun c => .custom c.1 c.2) = (items, cs)
  | [], cs, _ => splitCustom_customs cs
  | s :: items, cs, hs => by
    have hc : isCustomSec s = false := hs s (by simp)
    have ih := splitCustom_items items cs (fun t ht => hs t (by simp [ht]))
    cases s <;> simp_all [isCustomSec, splitCustom]

theorem allItemSections_noCustom (L : List (String × List ComponentDecl)) (k : Nat) :
    ∀ s ∈ allItemSections L k, isCustomSec s = false := by
  intro s hs
  simp only [allItemSections, List.mem_flatMap, itemSections] at hs
  obtain ⟨_, -, hs⟩ := hs
  simp at hs; rcases hs with rfl | rfl <;> rfl

/-- The sections of a package: items, then `package-docs` and `producers`. -/
theorem packageSections_eq {deps : Env} {p : Package} {ss : List Section}
    (h : packageSections deps p = .ok ss) :
    ∃ items x, encodeItems deps p = .ok items ∧
      ss = items ++ [("package-docs", docsSection p), ("producers", x)].map fun c => .custom c.1 c.2 := by
  unfold packageSections at h
  cases hi : encodeItems deps p with
  | error e => rw [hi] at h; cases h
  | ok items =>
    rw [hi] at h
    cases hp : producersSection witComponentProducers with
    | none => simp only [hp, bind, Except.bind] at h; cases h
    | some prod =>
      have hprod : ∃ x, prod = .custom "producers" x := by
        unfold producersSection at hp
        cases he : Producers.encode witComponentProducers with
        | none => rw [he] at hp; cases hp
        | some l => rw [he] at hp; cases hp; exact ⟨_, rfl⟩
      obtain ⟨x, rfl⟩ := hprod
      simp only [hp, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact ⟨items, x, rfl, by simp⟩

/-- Encoded items are item sections. -/
theorem encodeItems_shape {deps : Env} {p : Package} {items : List Section} (h : encodeItems deps p = .ok items) :
    ∃ L, items = allItemSections L := by
  unfold encodeItems at h
  dsimp only at h
  cases hi : p.interfaces.mapM (encodeIfaceItem (p.env deps) p.name) with
  | error e => rw [hi] at h; cases h
  | ok ifs =>
    rw [hi] at h
    cases hw : p.worlds.mapM (encodeWorldItem (p.env deps) p.name) with
    | error e => rw [hw] at h; cases h
    | ok ws => rw [hw] at h; exact ⟨ifs ++ ws, (Except.ok.inj h).symm⟩

/-- The sections of a package decode to its normal form with its metadata. -/
theorem decodeSections_package {deps : Env} {p : Package} (hv : p.Valid deps) {items : List Section}
    (hi : encodeItems deps p = .ok items) (x : ByteArray) :
    decodeSections (items ++ [("package-docs", docsSection p), ("producers", x)].map fun c => .custom c.1 c.2) =
      .ok (p.normalize.inject p.docsJson) := by
  have hsplit := splitCustom_items items [("package-docs", docsSection p), ("producers", x)]
    (by obtain ⟨L, rfl⟩ : ∃ L, items = allItemSections L := encodeItems_shape hi
        exact allItemSections_noCustom L 0)
  have hf : [("package-docs", docsSection p), ("producers", x)].find? (fun c => decide (c.1 = "package-docs")) =
      some ("package-docs", docsSection p) := by simp
  simp only [decodeSections, hsplit, decodeItems_encodeItems hv hi, bind, Except.bind, hf,
    readDocsSection_docsSection]; rfl

/-- **WIT packages round-trip through bytes**: the bytes wit-component writes
for a valid package decode to its normal form, with the docs and stability of
`package-docs` put back. -/
theorem decodePackage_encodePackage {deps : Env} {p : Package} (hv : p.Valid deps) {b : ByteArray}
    (h : encodePackage deps p = .ok b) : decodePackage b = .ok (p.normalize.inject p.docsJson) := by
  unfold encodePackage at h
  cases hs : packageSections deps p with
  | error e => rw [hs] at h; cases h
  | ok ss =>
    rw [hs] at h
    obtain ⟨items, x, hi, rfl⟩ := packageSections_eq hs
    cases he : encode (.mk (items ++ [("package-docs", docsSection p), ("producers", x)].map
        fun c => .custom c.1 c.2)) with
    | none => simp only [he, bind, Except.bind] at h; cases h
    | some b' =>
      have hb : b = b' := by simpa only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using h.symm
      rw [hb]
      simp only [decodePackage, parse_encode he]
      exact decodeSections_package hv hi x

end Silmaril.Wasm.Wit.Binary

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary

theorem ofByte_byte (se : StringEncoding) : StringEncoding.ofByte? se.byte = some se := by
  cases se <;> rfl

theorem producersSection_some {s : Section} (h : producersSection witComponentProducers = some s) :
    ∃ x, s = .custom "producers" x := by
  unfold producersSection at h
  cases he : Producers.encode witComponentProducers with
  | none => rw [he] at h; cases h
  | some l => rw [he] at h; cases h; exact ⟨_, rfl⟩

/-- The sections of a `component-type` payload read back. -/
theorem decodeWorldTypeSections_eq {env : Env} (henv : ∀ ib ∈ env, ib.1.Valid ∧ ib.2.Valid)
    {p : PackageName} {n : String} {w : World} (hv : (p.iface n).Valid) (hw : w.Valid)
    {se : StringEncoding} {ss : List Section} (h : worldTypeSections env p n w se = .ok ss) :
    decodeWorldTypeSections ss = .ok (p, n, w.normalize, se) := by
  unfold worldTypeSections at h
  cases hd : encodeWorld env w with
  | error e => rw [hd] at h; cases h
  | ok decls =>
    cases hp : producersSection witComponentProducers with
    | none => simp only [hd, hp, bind, Except.bind] at h; cases h
    | some prod =>
      simp only [hd, hp, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      rw [← h]
      have ht := decTop_world hv (decWorld_encodeWorld henv hw hd)
      simp only [decodeWorldTypeSections, ofByte_byte, ht]; rfl

/-- **A world embedded in a core module reads back**: the `component-type`
payload decodes to the package, the world's name, its normal form and the
string encoding. -/
theorem decodeWorldType_encodeWorldType {env : Env} (henv : ∀ ib ∈ env, ib.1.Valid ∧ ib.2.Valid)
    {p : PackageName} {n : String} {w : World} (hv : (p.iface n).Valid) (hw : w.Valid)
    {se : StringEncoding} {b : ByteArray} (h : encodeWorldType env p n w se = .ok b) :
    decodeWorldType b = .ok (p, n, w.normalize, se) := by
  unfold encodeWorldType at h
  cases hs : worldTypeSections env p n w se with
  | error e => rw [hs] at h; cases h
  | ok ss =>
    rw [hs] at h
    cases he : encode (.mk ss) with
    | none => simp only [he, bind, Except.bind] at h; cases h
    | some b' =>
      have hb : b = b' := by simpa only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using h.symm
      rw [hb]
      simp only [decodeWorldType, parse_encode he]
      exact decodeWorldTypeSections_eq henv hv hw hs

end Silmaril.Wasm.Wit.Binary
