module

public import Silmaril.Elf.Index.Defs
public import Silmaril.Elf.Lookup.Thms

/-! # The index answers the declarative lookups

* `nameKey_inj`: a name key determines the name;
* `entry_checkMatch`: `check_match` on an index entry is `File.checkMatch` on its symbol;
* `firstEntry_mapM`: the first accepted entry is the entry of the first accepted symbol;
* `index_lookup_sound'`, `index_symtab_sound'`: `Index.lookup` and `Index.symtabFind` answer
  `scanLookup` (through `defAt`) and `File.symtabFind`.
-/

public section

namespace Silmaril.Elf

open Silmaril.Formats.ELF (NameBytes ObjectSymbol)
open Silmaril.X86.Link (Blob)

theorem valueLE_inj : ∀ {a b : List (BitVec 8)}, a.length = b.length →
    Blob.valueLE a = Blob.valueLE b → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | x :: xs, y :: ys, hl, hv => by
    simp only [Blob.valueLE] at hv
    have hx := x.isLt
    have hy := y.isLt
    have h1 : x.toNat = y.toNat := by omega
    have h2 : Blob.valueLE xs = Blob.valueLE ys := by omega
    rw [BitVec.eq_of_toNat_eq h1, valueLE_inj (by simpa using hl) h2]

theorem nameKey_inj {a b : NameBytes} (h : nameKey a = nameKey b) : a = b := by
  simp only [nameKey, Prod.mk.injEq] at h
  exact valueLE_inj h.1 h.2

@[simp] theorem nameKey_eq_iff {a b : NameBytes} : nameKey a = nameKey b ↔ a = b :=
  ⟨nameKey_inj, congrArg _⟩

namespace Index

theorem entryAt_eq_some {A : File} {i : Nat} {e : Entry} (h : entryAt A i = some e) :
    ∃ s, A.dynsyms[i]? = some s ∧ e = entryOf A i s (A.versyms.bind (·[i]?)) := by
  simp only [entryAt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨s, hs, rfl⟩ := h
  exact ⟨s, hs, rfl⟩

/-- `check_match` on the entry of symbol `i` is `check_match` on symbol `i`. -/
theorem entry_checkMatch {A : File} {i : Nat} {e : Entry} (he : entryAt A i = some e)
    (r : Ref) (plt : Bool) : e.checkMatch A.versyms.isSome r plt = A.checkMatch r plt i := by
  obtain ⟨s, hs, rfl⟩ := entryAt_eq_some he
  simp only [entryOf]
  by_cases hn : s.name = r.name
  · cases hv : A.versyms with
    | none => simp [Entry.checkMatch, File.checkMatch, hs, hn, hv]
    | some vs =>
      cases hvi : vs[i]? with
      | none => simp [Entry.checkMatch, File.checkMatch, hs, hn, hv, hvi]
      | some ndx =>
        cases hr : r.ver with
        | none => simp [Entry.checkMatch, File.checkMatch, hs, hn, hv, hvi, hr]
        | some v =>
          cases hd : A.verdefOf (ndx % 0x8000) with
          | none => simp [Entry.checkMatch, File.checkMatch, hs, hn, hv, hvi, hr, hd]
          | some p =>
            obtain ⟨h, n⟩ := p
            simp [Entry.checkMatch, File.checkMatch, hs, hn, hv, hvi, hr, hd, Decidable.imp_iff_not_or]
  · simp [Entry.checkMatch, File.checkMatch, hs, hn]

/-! ## The search tree -/

namespace Tree

theorem find_insert (e : Entry) (k : Nat × Nat) :
    ∀ t : Tree, (t.insert e).find k = t.find k ++ (if e.key = k then [e] else [])
  | .leaf => by
    by_cases h : e.key = k
    · subst h; simp [insert, find]
    · have : (k == e.key) = false := by simp; exact Ne.symm h
      simp [insert, find, h, this]
  | .node l k' es r => by
    by_cases h1 : e.key = k'
    · subst h1
      by_cases h2 : k = e.key
      · subst h2; simp [insert, find]
      · simp [insert, find, h2, Ne.symm h2]
    · by_cases hl : keyLt e.key k' = true
      · have ih := find_insert e k l
        by_cases h2 : k = k'
        · subst h2; simp [insert, find, h1, hl]
        · by_cases h3 : keyLt k k' = true
          · simp [insert, find, h1, hl, h2, h3, ih]
          · have : e.key ≠ k := fun he => h3 (he ▸ hl)
            simp [insert, find, h1, hl, h2, h3, this]
      · have ih := find_insert e k r
        by_cases h2 : k = k'
        · subst h2; simp [insert, find, h1, hl]
        · by_cases h3 : keyLt k k' = true
          · have : e.key ≠ k := fun he => hl (he ▸ h3)
            simp [insert, find, h1, hl, h2, h3, this]
          · simp [insert, find, h1, hl, h2, h3, ih]

theorem find_foldl (k : Nat × Nat) :
    ∀ (es : List Entry) (t : Tree),
      (es.foldl (fun t e => t.insert e) t).find k = t.find k ++ es.filter (·.key == k)
  | [], t => by simp
  | e :: es, t => by
    rw [List.foldl_cons, find_foldl k es, find_insert, List.filter_cons]
    by_cases h : e.key = k <;> simp [h]

/-- **The tree finds exactly the entries with the key**, in order. -/
theorem find_ofList (es : List Entry) (k : Nat × Nat) :
    (ofList es).find k = es.filter (·.key == k) := by
  simp [ofList, find_foldl, find]

end Tree

theorem firstEntry_cons (v : Bool) (r : Ref) (plt : Bool) (e : Entry) (es : List Entry) :
    firstEntry v r plt (e :: es) =
      (e.checkMatch v r plt).bind fun b => if b then some (some e) else firstEntry v r plt es := by
  simp only [firstEntry]
  cases e.checkMatch v r plt with
  | none => rfl
  | some b => cases b <;> rfl

/-- Entries with another name are rejected, so the first accepted entry is the first accepted
entry with the reference's key. -/
theorem firstEntry_filter (v : Bool) (r : Ref) (plt : Bool) :
    ∀ es : List Entry,
      firstEntry v r plt es = firstEntry v r plt (es.filter (·.key == nameKey r.name))
  | [] => rfl
  | e :: es => by
    have ih := firstEntry_filter v r plt es
    by_cases h : e.key = nameKey r.name
    · rw [List.filter_cons_of_pos (by simpa using h), firstEntry_cons, firstEntry_cons, ← ih]
    · have hc : e.checkMatch v r plt = some false := by simp [Entry.checkMatch, h]
      rw [List.filter_cons_of_neg (by simpa using h), firstEntry_cons, hc]
      simpa using ih

/-- The first accepted entry is the entry of the first accepted symbol. -/
theorem firstEntry_from (A : File) (r : Ref) (plt : Bool) :
    ∀ n i, A.dynsyms.length - i = n →
      firstEntry A.versyms.isSome r plt
          (entriesFrom A i (A.dynsyms.drop i) (A.versyms.map (·.drop i))) =
        (firstMatch (A.checkMatch r plt) (List.range' i n)).map (·.bind (entryAt A))
  | 0, i, h => by
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | n + 1, i, h => by
    have hi : i < A.dynsyms.length := by omega
    rw [List.drop_eq_getElem_cons hi]
    have hvs : (A.versyms.map (·.drop i)).bind (·.head?) = A.versyms.bind (·[i]?) := by
      cases A.versyms <;> simp [List.head?_drop]
    have hvt : (A.versyms.map (·.drop i)).map (·.tail) = A.versyms.map (·.drop (i + 1)) := by
      cases A.versyms <;> simp [List.tail_drop]
    have he : entryAt A i = some (entryOf A i A.dynsyms[i] (A.versyms.bind (·[i]?))) := by
      simp [entryAt, List.getElem?_eq_getElem hi]
    simp only [entriesFrom, hvs, hvt]
    rw [firstEntry_cons, List.range'_succ, firstMatch_cons, entry_checkMatch he,
      firstEntry_from A r plt n (i + 1) (by omega)]
    cases A.checkMatch r plt i with
    | none => rfl
    | some b => cases b <;> simp [he]

theorem firstMatch_mem {p : Nat → Option Bool} :
    ∀ {l : List Nat} {i : Nat}, firstMatch p l = some (some i) → i ∈ l
  | [], _, h => by simp [firstMatch] at h
  | j :: l, i, h => by
    rw [firstMatch_cons] at h
    cases hp : p j with
    | none => simp [hp] at h
    | some b =>
      cases b with
      | true => simp [hp] at h; simp [h]
      | false => simp only [hp, Option.bind_some, Bool.false_eq_true, ite_false] at h;
                 exact List.mem_cons_of_mem _ (firstMatch_mem h)

theorem build_eq_some {A : File} {ix : Index} (h : build A = some ix) :
    ix = ⟨A.gnuHashTab.isSome, A.versyms.isSome,
      entriesFrom A ((A.gnuHashTab.map (·.symoffset)).getD A.dynsyms.length)
        (A.dynsyms.drop ((A.gnuHashTab.map (·.symoffset)).getD A.dynsyms.length))
        (A.versyms.map (·.drop ((A.gnuHashTab.map (·.symoffset)).getD A.dynsyms.length))),
      (A.sectionOfType SHT_SYMTAB).isSome, (A.symbols .symtab).zipIdx.filterMap funcOf,
      Tree.ofList (entriesFrom A ((A.gnuHashTab.map (·.symoffset)).getD A.dynsyms.length)
        (A.dynsyms.drop ((A.gnuHashTab.map (·.symoffset)).getD A.dynsyms.length))
        (A.versyms.map (·.drop ((A.gnuHashTab.map (·.symoffset)).getD A.dynsyms.length))))⟩ := by
  simp only [build, Option.pure_def, Option.some.injEq] at h
  exact h.symm

/-- **The index answers the declarative lookup** (`Task.index_lookup_sound`). -/
theorem lookup_sound (A : File) (ix : Index) (hb : build A = some ix) (r : Ref) (plt : Bool) :
    ix.lookup r plt = (do
      match ← A.scanLookup r plt with
      | none => pure none
      | some i => some <$> A.defAt i) := by
  cases build_eq_some hb
  cases hg : A.gnuHashTab with
  | none => simp [lookup, File.scanLookup, hg]
  | some g =>
    have hfe := firstEntry_from A r plt _ g.symoffset rfl
    rw [firstEntry_filter] at hfe
    simp only [lookup, File.scanLookup, hg, Option.isSome_some, guard, ite_true, Tree.find_ofList,
      Option.map_some, Option.getD_some]
    rw [hfe]
    cases hm : firstMatch (A.checkMatch r plt)
        (List.range' g.symoffset (A.dynsyms.length - g.symoffset)) with
    | none => simp [hm]
    | some x =>
      cases x with
      | none => simp [hm]
      | some i =>
        have hi := firstMatch_mem hm
        obtain ⟨e, he⟩ : ∃ e, entryAt A i = some e := by
          simp only [List.mem_range'_1] at hi
          obtain ⟨s, hs⟩ : ∃ s, A.dynsyms[i]? = some s :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          simp [entryAt, hs]
        obtain ⟨s, hs, rfl⟩ := entryAt_eq_some he
        simp only [he, Option.map_some, Option.bind_some, File.defAt, guard, entryOf]
        by_cases hbd : s.raw.binding = 1 ∨ s.raw.binding = 2 <;> simp [hbd, hm, hs]

theorem find_filterMap_funcOf (n : NameBytes) :
    ∀ es : List (ObjectSymbol × Nat),
      ((es.filterMap funcOf).find? (·.1 == nameKey n)).map (·.2) =
        es.findSome? fun si => if si.1.name = n then File.funcDef si else none
  | [] => rfl
  | si :: es => by
    have ih := find_filterMap_funcOf n es
    cases hf : File.funcDef si with
    | none =>
      have : funcOf si = none := by simp [funcOf, hf]
      rw [List.filterMap_cons_none this, ih, List.findSome?_cons]
      split <;> simp_all
    | some d =>
      have : funcOf si = some (nameKey si.1.name, d) := by simp [funcOf, hf]
      rw [List.filterMap_cons_some this, List.find?_cons, List.findSome?_cons]
      by_cases hn : si.1.name = n
      · simp [hn, hf]
      · have hk : (nameKey si.1.name == nameKey n) = false := by simp [hn]
        simp only [hk, hn, ite_false]
        exact ih

/-- **The index answers static selection** (`Task.index_symtab_sound`). -/
theorem symtab_sound (A : File) (ix : Index) (hb : build A = some ix) (n : NameBytes) :
    ix.symtabFind n = A.symtabFind n := by
  cases build_eq_some hb
  unfold symtabFind File.symtabFind
  cases hs : A.sectionOfType SHT_SYMTAB with
  | none => simp [guard]
  | some x =>
    simp only [Option.isSome_some]
    rw [find_filterMap_funcOf]
    rfl

end Index

end Silmaril.Elf
