module

public import Silmaril.X86.Loose.Listing.Defs
public import Silmaril.X86.Loose.Decode.Thms

/-!
# Image listings and their loose decode tables: proofs

The header is `Silmaril/X86/Loose/Listing/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Loose.Listing

open Silmaril.X86 (State Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.Loose Silmaril.X86.Loose.Listing

/-! ## Forms -/

theorem full_eq_some {α : Type} {n : Nat} {o : Option (α × Nat)} {a : α}
    (h : full n o = some a) : o = some (a, n) := by
  unfold full at h
  split at h
  · split at h
    · cases h; subst_vars; rfl
    · cases h
  · cases h

theorem classify_int {b : List Byte} {i : Silmaril.X86.Ext9.Instr}
    (h : classify b = .loose (.int i)) : Silmaril.X86.Ext9.decode b = some (i, b.length) := by
  unfold classify at h
  split at h
  · rename_i j hj; cases h; exact full_eq_some hj
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h <;> cases h

theorem classify_xmm {b : List Byte} {i : Silmaril.X86.Sse9.Instr}
    (h : classify b = .loose (.xmm i)) : Silmaril.X86.Sse9.decodeL b = some (i, b.length) := by
  unfold classify at h
  split at h
  · cases h
  · split at h
    · rename_i j hj; cases h; exact full_eq_some hj
    · split at h
      · cases h
      · split at h <;> cases h

theorem classify_float {b : List Byte} {i : Silmaril.X86.Float.Instr}
    (h : classify b = .loose (.float i)) : Silmaril.X86.Float.decode b = some (i, b.length) := by
  unfold classify at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rename_i j hj; cases h; exact full_eq_some hj
        · cases h

theorem classify_str {b : List Byte} {s : Silmaril.X86.Str9.Str}
    (h : classify b = .str s) : Silmaril.X86.Str9.decodeL b = some (s, b.length) := by
  unfold classify at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i j hj; cases h; exact full_eq_some hj
      · split at h <;> cases h

theorem mem_loosePart {D : DTable LForm} {e : DEntry Form} (h : e ∈ loosePart D) :
    ∃ e' ∈ D, e'.bytes = e.bytes ∧ e'.form = .loose e.form := by
  unfold loosePart at h
  rw [List.mem_filterMap] at h
  obtain ⟨e', hm, he⟩ := h
  split at he
  · rename_i f hf; cases he; exact ⟨e', hm, rfl, hf⟩
  · cases he

theorem table_form {bs : List (List Nat)} {e : DEntry LForm} (h : e ∈ table bs) :
    e.form = classify e.bytes := by
  unfold table at h
  rw [List.mem_map] at h
  obtain ⟨b, _, rfl⟩ := h
  rfl

theorem loosePart_okExt9 (bs : List (List Nat)) : (loosePart (table bs)).okExt9 = true := by
  unfold DTable.okExt9
  rw [List.all_eq_true]
  intro e he
  obtain ⟨e', hm, hb, hf⟩ := mem_loosePart he
  split
  · rename_i i hi
    rw [table_form hm, hi] at hf
    simpa [← hb] using classify_int hf
  · rfl

theorem loosePart_okSse9 (bs : List (List Nat)) : (loosePart (table bs)).okSse9 = true := by
  unfold DTable.okSse9
  rw [List.all_eq_true]
  intro e he
  obtain ⟨e', hm, hb, hf⟩ := mem_loosePart he
  split
  · rename_i i hi
    rw [table_form hm, hi] at hf
    simpa [← hb] using classify_xmm hf
  · rfl

theorem loosePart_okFloat (bs : List (List Nat)) : (loosePart (table bs)).okFloat = true := by
  unfold DTable.okFloat
  rw [List.all_eq_true]
  intro e he
  obtain ⟨e', hm, hb, hf⟩ := mem_loosePart he
  split
  · rename_i i hi
    rw [table_form hm, hi] at hf
    simpa [← hb] using classify_float hf
  · rfl

theorem table_functional (bs : List (List Nat)) : (table bs).functional = true := by
  unfold DTable.functional
  rw [List.all_eq_true]
  intro e he
  rw [List.all_eq_true]
  intro e' he'
  rw [table_form he, table_form he']
  by_cases h : e.bytes = e'.bytes
  · simp [h]
  · simp [h]

theorem loosePart_functional (bs : List (List Nat)) :
    (loosePart (table bs)).functional = true := by
  unfold DTable.functional
  rw [List.all_eq_true]
  intro e he
  rw [List.all_eq_true]
  intro e' he'
  obtain ⟨d, hd, hb, hf⟩ := mem_loosePart he
  obtain ⟨d', hd', hb', hf'⟩ := mem_loosePart he'
  rw [table_form hd] at hf
  rw [table_form hd'] at hf'
  by_cases h : e.bytes = e'.bytes
  · have h2 : LForm.loose e.form = LForm.loose e'.form := by
      rw [← hf, ← hf', hb, hb', h]
    injection h2 with h3
    simp [h, h3]
  · simp [h]

theorem mem_str9Part {D : DTable LForm} {e : DEntry Silmaril.X86.Str9.Instr}
    (h : e ∈ str9Part D) :
    ∃ e' ∈ D, e'.bytes = e.bytes ∧
      ((∃ i, e.form = .ext9 i ∧ e'.form = .loose (.int i)) ∨
        (∃ s, e.form = .str s ∧ e'.form = .str s)) := by
  unfold str9Part at h
  rw [List.mem_filterMap] at h
  obtain ⟨e', hm, he⟩ := h
  split at he
  · rename_i i hf; cases he; exact ⟨e', hm, rfl, Or.inl ⟨i, rfl, hf⟩⟩
  · rename_i s hf; cases he; exact ⟨e', hm, rfl, Or.inr ⟨s, rfl, hf⟩⟩
  · cases he

theorem str9Part_functional (bs : List (List Nat)) : (str9Part (table bs)).functional = true := by
  unfold DTable.functional
  rw [List.all_eq_true]
  intro e he
  rw [List.all_eq_true]
  intro e' he'
  by_cases h : e.bytes = e'.bytes
  · obtain ⟨d, hd, hb, hf⟩ := mem_str9Part he
    obtain ⟨d', hd', hb', hf'⟩ := mem_str9Part he'
    have hdd : d.form = d'.form := by rw [table_form hd, table_form hd', hb, hb', h]
    have hform : e.form = e'.form := by
      rcases hf with ⟨i, hi, hdi⟩ | ⟨s, hs, hds⟩ <;>
        rcases hf' with ⟨i', hi', hdi'⟩ | ⟨s', hs', hds'⟩
      · rw [hdi, hdi'] at hdd; cases hdd; rw [hi, hi']
      · rw [hdi, hds'] at hdd; cases hdd
      · rw [hds, hdi'] at hdd; cases hdd
      · rw [hds, hds'] at hdd; cases hdd; rw [hs, hs']
    simp [h, hform]
  · simp [h]

/-! ## The lexicographic order -/

theorem lexLt_irrefl : ∀ x : List Nat, lexLt x x = false
  | [] => rfl
  | a :: as => by simp [lexLt, lexLt_irrefl as]

theorem lexLt_trans : ∀ {x y z : List Nat}, lexLt x y = true → lexLt y z = true →
    lexLt x z = true
  | [], [], _, h, _ => by simp [lexLt] at h
  | [], _ :: _, [], _, h => by simp [lexLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [lexLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexLt] at h
  | a :: as, b :: bs, c :: cs, h, h' => by
    simp only [lexLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h h' ⊢
    rcases h with h | ⟨rfl, h⟩ <;> rcases h' with h' | ⟨rfl, h'⟩
    · exact .inl (by omega)
    · exact .inl h
    · exact .inl h'
    · exact .inr ⟨rfl, lexLt_trans h h'⟩

theorem lexLt_asymm {x y : List Nat} (h : lexLt x y = true) : lexLt y x = false := by
  cases h' : lexLt y x
  · rfl
  · have := lexLt_trans h h'; rw [lexLt_irrefl] at this; cases this

/-- A prefix is equal or smaller. -/
theorem prefix_le : ∀ {x y : List Nat}, x.isPrefixOf y = true → x = y ∨ lexLt x y = true
  | [], [], _ => .inl rfl
  | [], _ :: _, _ => .inr rfl
  | _ :: _, [], h => by simp [List.isPrefixOf] at h
  | a :: as, b :: bs, h => by
    simp only [List.isPrefixOf, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    rcases prefix_le h with h | h
    · exact .inl (by rw [h])
    · exact .inr (by simp [lexLt, h])

/-- **Sandwich**: whatever lies between a string and one of its extensions extends it. -/
theorem prefix_between : ∀ {p z c : List Nat}, p.isPrefixOf c = true →
    (p = z ∨ lexLt p z = true) → (z = c ∨ lexLt z c = true) → p.isPrefixOf z = true
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, [], h, _, _ => by simp [List.isPrefixOf] at h
  | a :: ps, z, b :: cs, h, h1, h2 => by
    simp only [List.isPrefixOf, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    match z, h1, h2 with
    | [], h1, _ => rcases h1 with h1 | h1 <;> simp [lexLt] at h1
    | d :: zs, h1, h2 =>
      simp only [List.cons.injEq, lexLt, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at h1 h2
      have hd : d = a := by
        rcases h1 with ⟨h1, _⟩ | h1 | ⟨h1, _⟩ <;>
          rcases h2 with ⟨h2, _⟩ | h2 | ⟨h2, _⟩ <;> omega
      subst hd
      have h1' : ps = zs ∨ lexLt ps zs = true := by
        rcases h1 with ⟨_, h1⟩ | h1 | ⟨_, h1⟩
        · exact .inl h1
        · omega
        · exact .inr h1
      have h2' : zs = cs ∨ lexLt zs cs = true := by
        rcases h2 with ⟨_, h2⟩ | h2 | ⟨_, h2⟩
        · exact .inl h2
        · omega
        · exact .inr h2
      simp [List.isPrefixOf, prefix_between h h1' h2']

/-- In a `sortedAdj` list, the head is below every later element. -/
theorem sortedAdj_lt : ∀ {x : List Nat} {rest : List (List Nat)}, sortedAdj (x :: rest) = true →
    ∀ y ∈ rest, lexLt x y = true
  | _, [], _, _, h => by simp at h
  | x, y1 :: rest, h, y, hy => by
    simp only [sortedAdj, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h1, _⟩, h3⟩ := h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h1
    · exact lexLt_trans h1 (sortedAdj_lt h3 y hy)

theorem sortedAdj_tail {x : List Nat} {rest : List (List Nat)} (h : sortedAdj (x :: rest) = true) :
    sortedAdj rest = true := by
  match rest, h with
  | [], _ => rfl
  | _ :: _, h =>
    simp only [sortedAdj, Bool.and_eq_true] at h
    exact h.2

/-- In a `sortedAdj` list, the head is a prefix of no later element. -/
theorem sortedAdj_not_prefix : ∀ {x : List Nat} {rest : List (List Nat)},
    sortedAdj (x :: rest) = true → ∀ y ∈ rest, x.isPrefixOf y = false
  | _, [], _, _, h => by simp at h
  | x, y1 :: rest, h, y, hy => by
    have hs := h
    simp only [sortedAdj, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h2
    · cases hp : x.isPrefixOf y
      · rfl
      · have := prefix_between hp (.inr h1) (.inr (sortedAdj_lt h3 y hy))
        rw [h2] at this; cases this

/-- **`sortedAdj` gives pairwise prefix-freeness.** -/
theorem sortedAdj_pairwise : ∀ {bs : List (List Nat)}, sortedAdj bs = true →
    ∀ x ∈ bs, ∀ y ∈ bs, x ≠ y → x.isPrefixOf y = false
  | [], _, _, hx, _, _, _ => by simp at hx
  | z :: rest, h, x, hx, y, hy, hne => by
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · exact absurd rfl hne
    · exact sortedAdj_not_prefix h y hy'
    · have hl := sortedAdj_lt h x hx'
      cases hp : x.isPrefixOf y
      · rfl
      · rcases prefix_le hp with h' | h'
        · exact absurd h' hne
        · rw [lexLt_asymm hl] at h'; cases h'
    · exact sortedAdj_pairwise (sortedAdj_tail h) x hx' y hy' hne

/-! ## From byte values to bytes -/

theorem ofNat8_inj {x y : Nat} (hx : x < 256) (hy : y < 256)
    (h : BitVec.ofNat 8 x = BitVec.ofNat 8 y) : x = y := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem toBytes_isPrefixOf : ∀ {x y : List Nat}, (∀ a ∈ x, a < 256) → (∀ a ∈ y, a < 256) →
    (toBytes x).isPrefixOf (toBytes y) = x.isPrefixOf y
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | a :: as, b :: bs, hx, hy => by
    simp only [toBytes, List.map_cons, List.isPrefixOf] at *
    have ha := hx a (by simp)
    have hb := hy b (by simp)
    have ih := toBytes_isPrefixOf (x := as) (y := bs) (fun c hc => hx c (by simp [hc]))
      (fun c hc => hy c (by simp [hc]))
    simp only [toBytes] at ih
    rw [ih]
    congr 1
    by_cases h : a = b
    · simp [h]
    · have : BitVec.ofNat 8 a ≠ BitVec.ofNat 8 b := fun h' => h (ofNat8_inj ha hb h')
      simp [h, this]

theorem tableOk_mem {bs : List (List Nat)} (h : tableOk bs = true) {b : List Nat} (hb : b ∈ bs) :
    b ≠ [] ∧ ∀ a ∈ b, a < 256 := by
  unfold tableOk at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have := h.1 b hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
    decide_eq_true_eq] at this
  exact this

/-- **The table of a checked list is prefix-free** (and so has no empty entry). -/
theorem table_prefixFree {bs : List (List Nat)} (h : tableOk bs = true) :
    (table bs).prefixFree = true := by
  have hs : sortedAdj bs = true := by
    unfold tableOk at h; rw [Bool.and_eq_true] at h; exact h.2
  unfold DTable.prefixFree table
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨?_, ?_⟩
  · intro e he
    rw [List.mem_map] at he
    obtain ⟨b, hb, rfl⟩ := he
    have := (tableOk_mem h hb).1
    simp [entryOf, toBytes, this]
  · intro e he
    rw [List.all_eq_true]
    intro e' he'
    rw [List.mem_map] at he he'
    obtain ⟨b, hb, rfl⟩ := he
    obtain ⟨b', hb', rfl⟩ := he'
    have h1 := (tableOk_mem h hb).2
    have h2 := (tableOk_mem h hb').2
    simp only [entryOf]
    by_cases hne : b = b'
    · subst hne; simp
    · have hp := sortedAdj_pairwise hs b hb b' hb' hne
      rw [toBytes_isPrefixOf h1 h2, hp]
      simp

/-! ## Function listings -/

theorem at2_mem {bs : List (List (List Nat))} {ij : Nat × Nat} (hi : ij.1 < bs.length)
    (hj : ij.2 < (bs.getD ij.1 []).length) : at2 bs ij ∈ bs.flatten := by
  unfold at2
  have h1 : bs.getD ij.1 [] ∈ bs := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi
  have h2 : (bs.getD ij.1 []).getD ij.2 [] ∈ bs.getD ij.1 [] := by
    rw [List.getD_eq_getElem?_getD (l := bs.getD ij.1 []), List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  exact List.mem_flatten.2 ⟨_, h1, h2⟩

theorem stripPrefix_some : ∀ {p r r' : List Nat}, stripPrefix p r = some r' → r = p ++ r'
  | [], _, _, h => by simp [stripPrefix] at h; simp [h]
  | _ :: _, [], _, h => by simp [stripPrefix] at h
  | a :: as, b :: bs, r', h => by
    simp only [stripPrefix] at h
    split at h
    · rename_i hab; subst hab; simp [stripPrefix_some h]
    · cases h

theorem walk_sound (bs : List (List (List Nat))) : ∀ (ks : List (Nat × Nat)) (rest : List Nat)
    (a : Nat), walk bs rest ks = true → ∀ x ∈ itemsFrom bs a ks,
      ∃ o, x.1 = a + o ∧ x.2 ∈ bs.flatten ∧ (rest.drop o).take x.2.length = x.2
  | [], _, _, _, x, hx => by simp [itemsFrom] at hx
  | ij :: ks, rest, a, h, x, hx => by
    simp only [walk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, hj⟩, hw⟩ := h
    have hmem := at2_mem hi hj
    split at hw
    · rename_i rest' hs
      have hr := stripPrefix_some hs
      simp only [itemsFrom, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨0, by simp, hmem, by simp [hr]⟩
      · obtain ⟨o, h1, h2, h3⟩ := walk_sound bs ks _ _ hw x hx
        refine ⟨(at2 bs ij).length + o, by rw [h1]; omega, h2, ?_⟩
        rw [hr, ← List.drop_drop, List.drop_left]
        exact h3
    · cases hw

theorem walkR_sound (bs : List (List (List Nat))) : ∀ (ks : List (Nat × Nat)) (rest r : List Nat)
    (n : Nat), walkR bs rest ks = some (r, n) → walk bs rest ks = true ∧ r = rest.drop n
  | [], rest, r, n, h => by
    simp only [walkR, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [walk]
  | ij :: ks, rest, r, n, h => by
    simp only [walkR] at h
    split at h
    · rename_i hc
      split at h
      · rename_i rest' hs
        cases hw : walkR bs rest' ks with
        | none => rw [hw] at h; cases h
        | some p =>
          rw [hw] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2⟩ := walkR_sound bs ks rest' p.1 p.2 hw
          have hr := stripPrefix_some hs
          refine ⟨?_, ?_⟩
          · simp only [walk, Bool.and_eq_true, decide_eq_true_eq]
            refine ⟨hc, ?_⟩
            rw [hs]; exact h1
          · rw [h2, hr, ← List.drop_drop, List.drop_left]
      · cases h
    · cases h

theorem checkFrom_sound {img : List Nat} {base : Nat} (bs : List (List (List Nat))) :
    ∀ (fns : List FnListing) (cur : Nat) (rest : List Nat), base ≤ cur →
      rest = img.drop (cur - base) → checkFrom bs cur rest fns = true →
      ∀ f ∈ fns, f.check img base bs = true
  | [], _, _, _, _, _, f, hf => by simp at hf
  | g :: gs, cur, rest, hb, hr, h, f, hf => by
    simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hc, h⟩ := h
    split at h
    · rename_i rest' n hw
      obtain ⟨h1, h2⟩ := walkR_sound bs g.instrs _ rest' n hw
      have hd : rest.drop (g.start - cur) = img.drop (g.start - base) := by
        rw [hr, List.drop_drop]; congr 1; omega
      rcases List.mem_cons.mp hf with rfl | hf
      · unfold FnListing.check
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by omega, by rw [← hd]; exact h1⟩
      · refine checkFrom_sound bs gs (g.start + n) rest' (by omega) ?_ h f hf
        rw [h2, hd, List.drop_drop]; congr 1; omega
    · cases h

/-- **One pass checks every listing.** -/
theorem checkAll_sound {bs : List (List (List Nat))} {img : List Nat} {base : Nat}
    {fns : List FnListing} (h : checkAll bs img base fns = true) :
    ∀ f ∈ fns, f.check img base bs = true :=
  checkFrom_sound bs fns base img (Nat.le_refl _) (by simp) h

/-- **What a checked listing says**: each listed instruction lies in the image at its address,
and its bytes are a string of the table. -/
theorem check_sound {img : List Nat} {base : Nat} {bs : List (List (List Nat))} {f : FnListing}
    (h : f.check img base bs = true) {a : Nat} {b : List Nat} (hx : (a, b) ∈ f.items bs) :
    base ≤ a ∧ b ∈ bs.flatten ∧ (img.drop (a - base)).take b.length = b := by
  unfold FnListing.check at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨o, h1, h2, h3⟩ := walk_sound bs f.instrs _ f.start h.2 (a, b) hx
  simp only at h1 h2 h3
  refine ⟨by omega, h2, ?_⟩
  rw [List.drop_drop] at h3
  rw [show a - base = f.start - base + o by omega]
  exact h3

theorem mem_table {bs : List (List Nat)} {b : List Nat} (h : b ∈ bs) : entryOf b ∈ table bs :=
  List.mem_map_of_mem h

theorem toBytes_drop_take (img : List Nat) (o l : Nat) :
    ((toBytes img).drop o).take l = toBytes ((img.drop o).take l) := by
  simp [toBytes, List.map_drop, List.map_take]

/-- **A checked listing meets `AtEntry`**: in a memory where the image is loaded at `base`,
the table entry of a listed instruction is at that instruction's address. -/
theorem atEntry_of_check {img : List Nat} {base : Nat} {bs : List (List (List Nat))}
    {f : FnListing} (hT : tableOk bs.flatten = true) (h : f.check img base bs = true) {a : Nat} {b : List Nat}
    (hx : (a, b) ∈ f.items bs) {m : Memory} (hbase : base < 2 ^ 64)
    (hL : Loaded m (BitVec.ofNat 64 base) (toBytes img)) {c : State} (hrip : c.rip.toNat = a) :
    entryOf b ∈ table bs.flatten ∧ AtEntry (entryOf b) c m := by
  obtain ⟨hle, hb, ht⟩ := check_sound h hx
  refine ⟨mem_table hb, ?_⟩
  have hne := (tableOk_mem hT hb).1
  have hpos : 0 < b.length := List.length_pos_iff.mpr hne
  have hfit : a - base + b.length ≤ (toBytes img).length := by
    have := congrArg List.length ht
    simp only [List.length_take, List.length_drop] at this
    simp only [toBytes, List.length_map]
    omega
  have hs := hL.fetchBytes_sub hpos hfit
  have hb64 : (BitVec.ofNat 64 base).toNat = base := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hbase
  rw [hb64, show base + (a - base) = a by omega, toBytes_drop_take, ht] at hs
  unfold AtEntry entryOf
  simp only [toBytes, List.length_map] at hs ⊢
  rw [hrip]
  exact hs

/-- **A checked set of listings is covered by its table**: every listed address holds an entry
of the table, in a memory where the image is loaded. -/
theorem covers {img : List Nat} {base : Nat} {bs : List (List (List Nat))}
    {fns : List FnListing} (hT : tableOk bs.flatten = true) (hfs : ∀ f ∈ fns, f.check img base bs = true) {a : Nat}
    (ha : a ∈ fns.flatMap (FnListing.addrs bs)) (hbase : base < 2 ^ 64) {m : Memory}
    (hL : Loaded m (BitVec.ofNat 64 base) (toBytes img)) {c : State} (hrip : c.rip.toNat = a) :
    ∃ e ∈ table bs.flatten, AtEntry e c m := by
  simp only [List.mem_flatMap, FnListing.addrs, List.mem_map] at ha
  obtain ⟨f, hf, ⟨a', b⟩, hx, rfl⟩ := ha
  exact ⟨_, atEntry_of_check hT (hfs f hf) hx hbase hL hrip⟩

end Silmaril.Proofs.X86.Loose.Listing
