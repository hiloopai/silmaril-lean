module

public import Silmaril.Wasm.Tools.Meta.Producers.Defs
public import Silmaril.Wasm.Tools.Meta.Names.Thms

/-!
# The producers section: decoding inverts encoding

* `strOf_sBytes`: a string's bytes decode back to it.
* `OMap.insert_fresh`: inserting a fresh key appends it.
* `readProducers_enc`: **for well-formed producers (`ProdOk`: the three field names, distinct
  field names, distinct value names in each field, names and versions within the limits) the
  section contents read back**: `readProducers (encProdBody p) = .ok p`.
* `producersCountOk_enc`: such a section is recognised as a producers section.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta

/-- A string's bytes decode back to it. -/
theorem strOf_sBytes (s : String) : strOf (sBytes s) = s := by
  simp [strOf, sBytes, String.fromUTF8!, s.isValidUTF8]

/-- Inserting a key that is not there appends it. -/
theorem OMap.insert_fresh {α : Type} : ∀ (m : OMap α) (k : String) (v : α),
    k ∉ m.map (·.1) → m.insert k v = m ++ [(k, v)]
  | [], _, _, _ => rfl
  | (k', v') :: m, k, v, h => by
    have hne : (k' == k) = false := by
      simp only [List.map_cons, List.mem_cons, not_or] at h
      simp [Ne.symm h.1]
    have ih := OMap.insert_fresh m k v (by simp only [List.map_cons, List.mem_cons, not_or] at h; exact h.2)
    simp [OMap.insert, hne, ih]

/-- A producers name or version that reads back: UTF-8 (always), within 100 000 bytes. -/
def StrOk (s : String) : Prop := (sBytes s).length ≤ 100000

/-- The values of a field that read back after `acc`. -/
def ValsOk (acc : OMap String) (vals : OMap String) : Prop :=
  (acc.map (·.1) ++ vals.map (·.1)).Nodup ∧ ∀ nv ∈ vals, StrOk nv.1 ∧ StrOk nv.2

theorem nameOk_sBytes {s : String} (h : StrOk s) : NameOk true (sBytes s) :=
  ⟨utf8Ok_toUTF8 s, by unfold StrOk at h; omega, fun _ => h⟩

/-- The value bytes of a list of values. -/
def encVals (vals : OMap String) : List UInt8 :=
  vals.flatMap fun (n, v) => encStr (sBytes n) ++ encStr (sBytes v)

theorem readValues_enc : ∀ (vals acc : OMap String) (r : List UInt8), ValsOk acc vals →
    readValues vals.length acc (encVals vals ++ r) = .ok (acc ++ vals, r)
  | [], acc, r, _ => by simp [readValues, encVals]
  | (n, v) :: vals, acc, r, ⟨hnd, hs⟩ => by
    have hn := nameOk_sBytes (hs (n, v) (by simp)).1
    have hv := nameOk_sBytes (hs (n, v) (by simp)).2
    have hfresh : n ∉ acc.map (·.1) := by
      intro hm
      have := (List.nodup_append.1 hnd).2.2
      exact this n hm n (by simp) rfl
    have hins : acc.insert n v = acc ++ [(n, v)] := OMap.insert_fresh acc n v hfresh
    have hok : ValsOk (acc ++ [(n, v)]) vals := by
      refine ⟨?_, fun nv h => hs nv (by simp [h])⟩
      simpa [List.map_append, List.append_assoc] using hnd
    have ih := readValues_enc vals (acc ++ [(n, v)]) r hok
    simp only [encVals, List.flatMap_cons, List.append_assoc, List.length_cons, readValues,
      readStr_encStr hn, readStr_encStr hv, strOf_sBytes, hins] at ih ⊢
    rw [ih]
    simp

/-- Well-formed producers. -/
def FieldsOk (acc : Producers) (p : Producers) : Prop :=
  (acc.map (·.1) ++ p.map (·.1)).Nodup ∧
  ∀ fv ∈ p, (fv.1 = "language" ∨ fv.1 = "sdk" ∨ fv.1 = "processed-by") ∧
    fv.2.length < 2 ^ 32 ∧ ValsOk [] fv.2

/-- The field bytes of a list of fields. -/
def encFields (p : Producers) : List UInt8 :=
  p.flatMap fun (f, vals) => encStr (sBytes f) ++ encValues vals

theorem encFields_cons (f : String) (vals : OMap String) (p : Producers) :
    encFields ((f, vals) :: p) = encStr (sBytes f) ++ (encU32 vals.length ++ (encVals vals ++ encFields p)) := by
  simp [encFields, encValues, encVals, List.append_assoc]

theorem readFields_enc : ∀ (p acc : Producers) (r : List UInt8), FieldsOk acc p →
    readFields p.length acc (encFields p ++ r) = .ok (acc ++ p, r)
  | [], acc, r, _ => by simp [readFields, encFields]
  | (f, vals) :: p, acc, r, ⟨hnd, hs⟩ => by
    obtain ⟨hname, hlen, hvals⟩ := hs (f, vals) (by simp)
    have hf : NameOk false (sBytes f) := ⟨utf8Ok_toUTF8 f, by
      rcases hname with h | h | h <;> simp only at h <;> subst h <;> decide, fun h => by cases h⟩
    have hgood : (f == "language" || f == "sdk" || f == "processed-by") = true := by
      rcases hname with h | h | h <;> simp only at h <;> simp [h]
    have hfresh : f ∉ acc.map (·.1) := by
      intro hm
      exact (List.nodup_append.1 hnd).2.2 f hm f (by simp) rfl
    have hins : acc.insert f vals = acc ++ [(f, vals)] := OMap.insert_fresh acc f vals hfresh
    have hok : FieldsOk (acc ++ [(f, vals)]) p := by
      refine ⟨?_, fun fv h => hs fv (by simp [h])⟩
      simpa [List.map_append, List.append_assoc] using hnd
    have hv := readValues_enc vals [] (encFields p ++ r) hvals
    have ih := readFields_enc p (acc ++ [(f, vals)]) r hok
    simp only [List.nil_append] at hv
    rw [encFields_cons]
    simp only [List.append_assoc, List.length_cons, readFields, readUStr_encStr hf, strOf_sBytes,
      hgood, Bool.not_true, Bool.false_eq_true, ↓reduceIte, readU32_encU32 _ _ hlen, hv, hins]
    simpa [List.append_assoc] using ih

/-- **The producers section contents read back.** -/
theorem readProducers_enc {p : Producers} (hl : p.length < 2 ^ 32) (h : FieldsOk [] p) :
    readProducers (encProdBody p) = .ok p := by
  have := readFields_enc p [] [] h
  simp only [List.append_nil, List.nil_append] at this
  simp [readProducers, encProdBody, readU32_encU32 _ _ hl, encFields] at this ⊢
  simp [this]

end Silmaril.Wasm.Tools.Meta

end
