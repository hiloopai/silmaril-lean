module

public import Silmaril.Data.Cells.Defs

/-!
# Cells: stores, separation and the update rule

The one store lemma every data-structure lemma of `Silmaril.Data` reduces to
(`Frag.holds_update`): given a separated *slot* fragment `S` (the locations a structure may
occupy, values irrelevant), a fragment `f` that holds, and stores `st` into slots at pairwise
distinct addresses, every cell of the new fragment `f'` that is either stored or an old cell at an
unstored slot holds after the stores. Instance proofs then only show list membership facts.
-/

@[expose] public section

namespace Silmaril.Data

/-! ## Loads and single stores -/

theorem MemView.load_of_bytes (v : MemView) :
    ∀ (k a x : Nat), (∀ i < k, v.byte (a + i) = some (x / 256 ^ i % 256)) →
      v.load a k = some (x % 256 ^ k)
  | 0, _, x, _ => by simp [MemView.load, Nat.mod_one]
  | k + 1, a, x, h => by
    have h0 : v.byte a = some (x % 256) := by simpa using h 0 (Nat.succ_pos k)
    have hr : v.load (a + 1) k = some (x / 256 % 256 ^ k) :=
      MemView.load_of_bytes v k (a + 1) (x / 256) fun i hi => by
        have := h (i + 1) (Nat.succ_lt_succ hi)
        rw [show a + (i + 1) = a + 1 + i by omega, Nat.pow_succ, Nat.mul_comm,
          ← Nat.div_div_eq_div_mul] at this
        exact this
    simp only [MemView.load, h0, hr]
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ k), Nat.mod_mul]
    rfl

@[simp] theorem MemView.store_writable (v : MemView) (c : Cell) :
    (v.store c).writable = v.writable := rfl

theorem MemView.storeAll_writable : ∀ (v : MemView) (st : List Cell),
    (v.storeAll st).writable = v.writable
  | _, [] => rfl
  | v, d :: ds => by
    show ((v.store d).storeAll ds).writable = _
    rw [MemView.storeAll_writable]; rfl

theorem MemView.storeAll_cons (v : MemView) (d : Cell) (ds : List Cell) :
    v.storeAll (d :: ds) = (v.store d).storeAll ds := rfl

/-- A stored cell holds, when its value fits and its bytes are writable. -/
theorem Cell.holds_store_self {v : MemView} {c : Cell} (hfit : c.val < 256 ^ c.width)
    (hw : ∀ i < c.width, v.writable (c.addr + i) = true) : c.Holds (v.store c) := by
  refine ⟨?_, hw⟩
  rw [MemView.load_of_bytes (v.store c) c.width c.addr c.val fun i hi => ?_,
    Nat.mod_eq_of_lt hfit]
  have h1 : c.addr ≤ c.addr + i ∧ c.addr + i < c.addr + c.width := ⟨by omega, by omega⟩
  simp only [MemView.store, h1, and_self, ↓reduceIte, show c.addr + i - c.addr = i by omega]

/-- **Frame for one store**: a cell apart from the stored one holds after the store iff before. -/
theorem Cell.holds_store_apart {v : MemView} {c d : Cell} (h : c.Apart d) :
    c.Holds (v.store d) ↔ c.Holds v := by
  have hl : (v.store d).load c.addr c.width = v.load c.addr c.width :=
    MemView.load_congr _ _ _ _ fun i hi => by
      have h1 : ¬(d.addr ≤ c.addr + i ∧ c.addr + i < d.addr + d.width) :=
        fun hh => h (c.addr + i) (by omega) (by omega) hh.1 hh.2
      simp only [MemView.store, h1, ↓reduceIte]
  simp only [Cell.Holds, hl, MemView.store_writable]

/-! ## Many stores -/

/-- **The store rule**: after stores `st` (each fitting and writable, pairwise apart), a cell
holds if it is one of the stores, or held before and is apart from every store. -/
theorem Cell.holds_storeAll : ∀ {v : MemView} {st : List Cell} {c : Cell},
    (∀ d ∈ st, d.val < 256 ^ d.width ∧ ∀ i < d.width, v.writable (d.addr + i) = true) →
    st.Pairwise Cell.Apart →
    (c ∈ st ∨ (c.Holds v ∧ ∀ d ∈ st, c.Apart d)) → c.Holds (v.storeAll st)
  | _, [], _, _, _, h => h.elim (fun h => nomatch h) (·.1)
  | v, d :: ds, c, hfit, hpw, h => by
    rw [MemView.storeAll_cons]
    have hfit' : ∀ d' ∈ ds, d'.val < 256 ^ d'.width ∧
        ∀ i < d'.width, (v.store d).writable (d'.addr + i) = true := fun d' hd' =>
      hfit d' (List.mem_cons_of_mem _ hd')
    have hpw' := (List.pairwise_cons.1 hpw)
    by_cases hin : c ∈ ds
    · exact Cell.holds_storeAll hfit' hpw'.2 (.inl hin)
    rcases h with h | ⟨hc, hap⟩
    · have hcd : c = d := by
        rcases List.mem_cons.1 h with h | h
        · exact h
        · exact absurd h hin
      subst hcd
      exact Cell.holds_storeAll hfit' hpw'.2
        (.inr ⟨Cell.holds_store_self (hfit c (List.mem_cons_self ..)).1
          (hfit c (List.mem_cons_self ..)).2, hpw'.1⟩)
    · exact Cell.holds_storeAll hfit' hpw'.2
        (.inr ⟨(Cell.holds_store_apart (hap d (List.mem_cons_self ..))).2 hc,
          fun d' hd' => hap d' (List.mem_cons_of_mem _ hd')⟩)

/-! ## Separation -/

theorem Frag.bytes_cons (c : Cell) (f : Frag) :
    Frag.bytes (c :: f) = List.range' c.addr c.width ++ Frag.bytes f := by
  simp [Frag.bytes]

theorem Frag.bytes_append (f g : Frag) : Frag.bytes (f ++ g) = f.bytes ++ g.bytes := by
  simp [Frag.bytes]

theorem Frag.mem_bytes {a : Nat} {c : Cell} {f : Frag} (hc : c ∈ f) (h1 : c.addr ≤ a)
    (h2 : a < c.addr + c.width) : a ∈ f.bytes :=
  List.mem_flatMap.2 ⟨c, hc, List.mem_range'.2 ⟨a - c.addr, by omega, by omega⟩⟩

theorem Frag.sep_cons {c : Cell} {f : Frag} :
    Frag.Sep (c :: f) ↔ f.Sep ∧ ∀ d ∈ f, c.Apart d := by
  unfold Frag.Sep
  rw [Frag.bytes_cons, List.nodup_append]
  refine ⟨fun ⟨_, hf, hd⟩ => ⟨hf, fun d hd' a h1 h2 h3 h4 =>
    hd a (List.mem_range'.2 ⟨a - c.addr, by omega, by omega⟩) a (Frag.mem_bytes hd' h3 h4) rfl⟩,
    fun ⟨hf, hd⟩ => ⟨List.nodup_range', hf, fun a ha b hb hab => ?_⟩⟩
  obtain ⟨i, hi, hai⟩ := List.mem_range'.1 ha
  obtain ⟨d, hd', hb'⟩ := List.mem_flatMap.1 hb
  obtain ⟨j, hj, hbj⟩ := List.mem_range'.1 hb'
  exact hd d hd' a (by omega) (by omega) (by omega) (by omega)

theorem Cell.Apart.symm {c d : Cell} (h : c.Apart d) : d.Apart c :=
  fun a h1 h2 h3 h4 => h a h3 h4 h1 h2

theorem Cell.Apart.of_eq {c d c' d' : Cell} (h : c.Apart d) (hc : c'.addr = c.addr)
    (hcw : c'.width = c.width) (hd : d'.addr = d.addr) (hdw : d'.width = d.width) :
    c'.Apart d' := by
  intro a; rw [hc, hcw, hd, hdw]; exact h a

/-- In a separated fragment, two cells at different addresses are apart. -/
theorem Frag.Sep.apart : ∀ {f : Frag}, f.Sep → ∀ {c d : Cell}, c ∈ f → d ∈ f →
    c.addr ≠ d.addr → c.Apart d
  | [], _, _, _, hc, _, _ => nomatch hc
  | e :: f, h, c, d, hc, hd, hne => by
    obtain ⟨hf, he⟩ := Frag.sep_cons.1 h
    rcases List.mem_cons.1 hc with hc | hc <;> rcases List.mem_cons.1 hd with hd | hd
    · exact absurd (by rw [hc, hd]) hne
    · exact hc ▸ he d hd
    · exact hd ▸ (he c hc).symm
    · exact Frag.Sep.apart hf hc hd hne

theorem Frag.sep_append {f g : Frag} :
    Frag.Sep (f ++ g) ↔ f.Sep ∧ g.Sep ∧ ∀ c ∈ f, ∀ d ∈ g, c.Apart d := by
  induction f with
  | nil => simp [Frag.Sep, Frag.bytes]
  | cons e f ih =>
    rw [List.cons_append, Frag.sep_cons, ih, Frag.sep_cons]
    simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro ⟨⟨hf, hg, hfg⟩, he⟩
      exact ⟨⟨hf, fun d hd => he d (.inl hd)⟩, hg, fun c hc d hd => hc.elim
        (fun h => h ▸ he d (.inr hd)) (fun hc => hfg c hc d hd)⟩
    · rintro ⟨⟨hf, he⟩, hg, hfg⟩
      exact ⟨⟨hf, hg, fun c hc d hd => hfg c (.inr hc) d hd⟩,
        fun d hd => hd.elim (he d) (fun hd => hfg e (.inl rfl) d hd)⟩

/-- A separated fragment of cells of positive width has pairwise distinct addresses. -/
theorem Frag.Sep.addrs_nodup : ∀ {f : Frag}, f.Sep → (∀ c ∈ f, 0 < c.width) →
    (f.map Cell.addr).Nodup
  | [], _, _ => List.nodup_nil
  | e :: f, h, hw => by
    obtain ⟨hf, he⟩ := Frag.sep_cons.1 h
    refine List.nodup_cons.2 ⟨fun hm => ?_,
      Frag.Sep.addrs_nodup hf fun c hc => hw c (List.mem_cons_of_mem _ hc)⟩
    obtain ⟨d, hd, hda⟩ := List.mem_map.1 hm
    have h1 : 0 < e.width := hw e (List.mem_cons_self ..)
    have h2 : 0 < d.width := hw d (List.mem_cons_of_mem _ hd)
    exact he d hd e.addr (Nat.le_refl _) (by omega) (by omega) (by omega)

/-- **The update rule.** `S` is a separated fragment of *slots* (only addresses and widths
matter). If `f` holds and the stores `st` fit, are writable, go to slots and to pairwise distinct
addresses, then `f'` holds after them provided each of its cells is a store or an old cell of
`f` in a slot no store touches. -/
theorem Frag.holds_update {v : MemView} {S f st f' : Frag} (hS : S.Sep) (hf : f.Holds v)
    (hst : ∀ d ∈ st, d.val < 256 ^ d.width ∧ (∀ i < d.width, v.writable (d.addr + i) = true) ∧
      ∃ e ∈ S, e.addr = d.addr ∧ e.width = d.width)
    (hnd : (st.map Cell.addr).Nodup)
    (hf' : ∀ c ∈ f', c ∈ st ∨
      (c ∈ f ∧ (∃ e ∈ S, e.addr = c.addr ∧ e.width = c.width) ∧ c.addr ∉ st.map Cell.addr)) :
    f'.Holds (v.storeAll st) := by
  have hslot : ∀ {c d : Cell}, (∃ e ∈ S, e.addr = c.addr ∧ e.width = c.width) →
      (∃ e ∈ S, e.addr = d.addr ∧ e.width = d.width) → c.addr ≠ d.addr → c.Apart d := by
    rintro c d ⟨e₁, he₁, h₁, w₁⟩ ⟨e₂, he₂, h₂, w₂⟩ hne
    exact (hS.apart he₁ he₂ (by rw [h₁, h₂]; exact hne)).of_eq h₁.symm w₁.symm h₂.symm w₂.symm
  have hpw : st.Pairwise Cell.Apart :=
    (List.pairwise_map.1 hnd).imp_of_mem fun ha hb hne => hslot (hst _ ha).2.2 (hst _ hb).2.2 hne
  intro c hc
  refine Cell.holds_storeAll (fun d hd => ⟨(hst d hd).1, (hst d hd).2.1⟩) hpw ?_
  rcases hf' c hc with h | ⟨hcf, hcs, hna⟩
  · exact .inl h
  · exact .inr ⟨hf c hcf, fun d hd => hslot hcs (hst d hd).2.2 fun he =>
      hna (List.mem_map.2 ⟨d, hd, he.symm⟩)⟩

/-- A fragment's cells are writable and their values fit, so they can be stored back. -/
theorem Frag.Holds.writable {v : MemView} {f : Frag} (h : f.Holds v) {c : Cell} (hc : c ∈ f)
    {i : Nat} (hi : i < c.width) : v.writable (c.addr + i) = true := (h c hc).2 i hi

end Silmaril.Data
