module

public import Silmaril.Wasm.Tools.Gen.Cmd.Sections.Defs

/-!
# Custom sections at the byte level: `split` inverts `join`

`Silmaril.Wasm.Tools.Gen.Cmd.Sections` splices custom sections into section *lists*; the bytes
written are `join header secs`. This module closes the gap to the bytes:

* `readLeb_encLeb`: the LEB128 reader reads back the encoder's bytes (`n < 128^5`);
* `split_join`: **`split (join header secs) = some secs`** for an 8-byte header and payloads
  below `2^35` bytes;
* `split_restore`: so the bytes `restore cs enc` writes split into exactly the spliced section
  list, `splice cs (non-custom sections of enc)`;
* `readLeb_bound`, `split_framable`: every payload `split` reads is below `2^35` bytes, so
  `split_join_split`: re-joining a split module splits back to the same sections (the byte
  round trip in the other direction holds up to the LEB128 spelling of the section sizes,
  which `join` writes minimally).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Sections

/-! ## Bytes -/

theorem get!_append_left {a b : ByteArray} {i : Nat} (h : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  rw [getElem!_pos (a ++ b) i (by simp; omega), getElem!_pos a i h]
  exact ByteArray.getElem_append_left h

theorem get!_append_right {a b : ByteArray} {i : Nat} :
    (a ++ b)[a.size + i]! = b[i]! := by
  by_cases h : i < b.size
  · rw [getElem!_pos (a ++ b) _ (by simp; omega), getElem!_pos b i h,
      ByteArray.getElem_append_right (by omega)]
    simp
  · rw [getElem!_neg (a ++ b) _ (by simp; omega), getElem!_neg b i h]

theorem get!_toByteArray {l : List UInt8} {i : Nat} : l.toByteArray[i]! = l[i]! := by
  by_cases h : i < l.length
  · rw [getElem!_pos l.toByteArray i (by simpa using h), getElem!_pos l i h]
    simp
  · rw [getElem!_neg l.toByteArray i (by simpa using h), getElem!_neg l i h]

theorem mk_toArray (l : List UInt8) : (⟨l.toArray⟩ : ByteArray) = l.toByteArray := by
  ext1
  simp

/-! ## LEB128 -/

theorem encLeb_length_le : ∀ (k n : Nat), (encLeb k n).length ≤ k
  | 0, _ => by simp [encLeb]
  | k + 1, n => by
    unfold encLeb
    split
    · simp
    · simpa using encLeb_length_le k (n / 128)

theorem encLeb_length_pos (k n : Nat) : 0 < (encLeb (k + 1) n).length := by
  unfold encLeb
  split <;> simp

theorem toNat_small {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8, UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The step of `readLeb` at a continuation byte. -/
theorem readLeb_cont (b : ByteArray) (k pos acc sh x : Nat) (hp : pos < b.size)
    (hx : b[pos]!.toNat = x) (hc : ¬ x < 128) :
    readLeb b (k + 1) pos acc sh = readLeb b k (pos + 1) (acc + x % 128 * 2 ^ sh) (sh + 7) := by
  have hx' : b[pos].toNat = x := by rw [← getElem!_pos b pos hp]; exact hx
  simp [readLeb, hp, hx', hc]

/-- The step of `readLeb` at the last byte. -/
theorem readLeb_last (b : ByteArray) (k pos acc sh x : Nat) (hp : pos < b.size)
    (hx : b[pos]!.toNat = x) (hc : x < 128) :
    readLeb b (k + 1) pos acc sh = some (acc + x % 128 * 2 ^ sh, pos + 1) := by
  have hx' : b[pos].toNat = x := by rw [← getElem!_pos b pos hp]; exact hx
  simp [readLeb, hp, hx', hc]

/-- Bytes at `pos` that spell `l`. -/
def Spells (b : ByteArray) (pos : Nat) (l : List UInt8) : Prop :=
  pos + l.length ≤ b.size ∧ ∀ i, i < l.length → b[pos + i]! = l[i]!

theorem Spells.head {b : ByteArray} {pos : Nat} {x : UInt8} {l : List UInt8}
    (h : Spells b pos (x :: l)) : pos < b.size ∧ b[pos]! = x := by
  have h0 := h.2 0 (by simp)
  exact ⟨by have := h.1; simp at this; omega, by simpa using h0⟩

theorem Spells.tail {b : ByteArray} {pos : Nat} {x : UInt8} {l : List UInt8}
    (h : Spells b pos (x :: l)) : Spells b (pos + 1) l := by
  refine ⟨by have := h.1; simp at this; omega, fun i hi => ?_⟩
  have := h.2 (i + 1) (by simp; omega)
  rw [show pos + 1 + i = pos + (i + 1) by omega, this]
  simp

/-- **The LEB128 reader reads back the encoder's bytes.** -/
theorem readLeb_encLeb (b : ByteArray) :
    ∀ (k n pos acc sh : Nat), n < 128 ^ (k + 1) → Spells b pos (encLeb (k + 1) n) →
      readLeb b (k + 1) pos acc sh = some (acc + n * 2 ^ sh, pos + (encLeb (k + 1) n).length)
  | k, n, pos, acc, sh, hn, hs => by
    by_cases hsm : n < 128
    · have he : encLeb (k + 1) n = [n.toUInt8] := by simp [encLeb, hsm]
      rw [he] at hs ⊢
      obtain ⟨hp, hb⟩ := hs.head
      rw [readLeb_last b k pos acc sh n hp (by rw [hb]; exact toNat_small (by omega)) hsm]
      simp [Nat.mod_eq_of_lt hsm]
    · exact readLeb_encLeb_cont b k n pos acc sh hn hs hsm
where
  readLeb_encLeb_cont (b : ByteArray) (k n pos acc sh : Nat) (hn : n < 128 ^ (k + 1))
      (hs : Spells b pos (encLeb (k + 1) n)) (hsm : ¬ n < 128) :
      readLeb b (k + 1) pos acc sh = some (acc + n * 2 ^ sh, pos + (encLeb (k + 1) n).length) := by
    have he : encLeb (k + 1) n = (n % 128 + 128).toUInt8 :: encLeb k (n / 128) := by
      simp [encLeb, hsm]
    rw [he] at hs ⊢
    obtain ⟨hp, hb⟩ := hs.head
    have hx : b[pos]!.toNat = n % 128 + 128 := by rw [hb]; exact toNat_small (by omega)
    rw [readLeb_cont b k pos acc sh _ hp hx (by omega)]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by
      rcases k with _ | k
      · simp at hn; omega
      · simp⟩
    have hn' : n / 128 < 128 ^ (k' + 1) := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]; simpa [Nat.pow_succ] using hn
    rw [readLeb_encLeb b k' (n / 128) (pos + 1) _ (sh + 7) hn' hs.tail]
    have hm : (n % 128 + 128) % 128 = n % 128 := by omega
    have hd : n = n % 128 + 128 * (n / 128) := (Nat.mod_add_div n 128).symm
    simp only [hm, List.length_cons, Option.some.injEq, Prod.mk.injEq]
    refine ⟨?_, by omega⟩
    conv => rhs; rw [hd]
    rw [Nat.pow_add, Nat.add_mul, Nat.add_assoc]
    congr 1
    rw [show (2 : Nat) ^ 7 = 128 by rfl]
    simp only [Nat.mul_comm, Nat.mul_left_comm]

/-! ## Joining -/

/-- The bytes of one section. -/
def secBytes (s : Sec) : ByteArray :=
  [s.id].toByteArray ++ (encLeb 5 s.payload.size).toByteArray ++ s.payload

theorem join_nil (h : ByteArray) : join h [] = h := rfl

theorem join_cons (h : ByteArray) (s : Sec) (ss : List Sec) :
    join h (s :: ss) = join (h ++ secBytes s) ss := by
  have : (h.push s.id ++ ⟨(encLeb 5 s.payload.size).toArray⟩) ++ s.payload =
      h ++ secBytes s := by
    rw [← ByteArray.append_toByteArray_singleton, mk_toArray, secBytes]
    simp only [ByteArray.append_assoc]
  simp only [join, List.foldl_cons, this]

theorem join_append : ∀ (h x : ByteArray) (ss : List Sec), join (h ++ x) ss = h ++ join x ss
  | h, x, [] => rfl
  | h, x, s :: ss => by
    rw [join_cons, join_cons, ByteArray.append_assoc, join_append h (x ++ secBytes s) ss]

theorem join_eq (h : ByteArray) (ss : List Sec) : join h ss = h ++ join ByteArray.empty ss := by
  rw [← join_append, ByteArray.append_empty]

theorem secBytes_size (s : Sec) :
    (secBytes s).size = 1 + (encLeb 5 s.payload.size).length + s.payload.size := by
  simp [secBytes]

theorem join_size_ge : ∀ (h : ByteArray) (ss : List Sec), h.size + ss.length ≤ (join h ss).size
  | h, [] => by simp [join_nil]
  | h, s :: ss => by
    have ih := join_size_ge (h ++ secBytes s) ss
    rw [join_cons]
    simp only [ByteArray.size_append, secBytes_size, List.length_cons] at ih ⊢
    omega

/-! ## Splitting what was joined -/

/-- Payloads `join` can frame: below `2^35 = 128^5` bytes. -/
def Framable (s : Sec) : Prop := s.payload.size < 128 ^ 5

/-- The bytes of `join h (s :: ss)` at `h.size`: the section's id, size and payload. -/
theorem join_cons_facts (h : ByteArray) (s : Sec) (ss : List Sec) :
    let B := join h (s :: ss)
    B = (h ++ secBytes s) ++ join ByteArray.empty ss ∧ B[h.size]! = s.id ∧
      Spells B (h.size + 1) (encLeb 5 s.payload.size) ∧
      B.extract (h.size + 1 + (encLeb 5 s.payload.size).length)
        (h.size + 1 + (encLeb 5 s.payload.size).length + s.payload.size) = s.payload := by
  intro B
  have hB : B = h ++ ([s.id].toByteArray ++ ((encLeb 5 s.payload.size).toByteArray ++
      (s.payload ++ join ByteArray.empty ss))) := by
    show join h (s :: ss) = _
    rw [join_cons, join_eq, secBytes]
    simp only [ByteArray.append_assoc]
  refine ⟨by show join h (s :: ss) = _; rw [join_cons, join_eq], ?_, ?_, ?_⟩
  · rw [hB, show h.size = h.size + 0 by rfl, get!_append_right, get!_append_left (by simp),
      get!_toByteArray]
    simp
  · refine ⟨by rw [hB]; simp; omega, fun i hi => ?_⟩
    rw [hB, Nat.add_assoc, get!_append_right,
      show 1 + i = [s.id].toByteArray.size + i by simp, get!_append_right,
      get!_append_left (by simpa using hi), get!_toByteArray]
  · have hB2 : B = (h ++ [s.id].toByteArray ++ (encLeb 5 s.payload.size).toByteArray) ++
        (s.payload ++ join ByteArray.empty ss) := by
      rw [hB]; simp only [ByteArray.append_assoc]
    have e1 : (h ++ [s.id].toByteArray ++ (encLeb 5 s.payload.size).toByteArray).size =
        h.size + 1 + (encLeb 5 s.payload.size).length := by simp
    rw [hB2, ← e1]
    have hx := ByteArray.extract_append_size_add
      (a := h ++ [s.id].toByteArray ++ (encLeb 5 s.payload.size).toByteArray)
      (b := s.payload ++ join ByteArray.empty ss) (i := 0) (j := s.payload.size)
    simp only [Nat.add_zero] at hx
    rw [hx, ByteArray.extract_append_eq_left rfl]

/-- **`splitFrom` reads back the sections `join` wrote after any prefix.** -/
theorem splitFrom_join :
    ∀ (ss : List Sec) (h : ByteArray) (fuel : Nat), ss.length ≤ fuel → (∀ s ∈ ss, Framable s) →
      splitFrom (join h ss) fuel h.size = some ss
  | [], h, fuel, _, _ => by
    cases fuel <;> simp [splitFrom, join_nil]
  | s :: ss, h, fuel, hf, hsz => by
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    obtain ⟨hB, hid, hsp, hpay⟩ := join_cons_facts h s ss
    have hlen : (join h (s :: ss)).size =
        (h ++ secBytes s).size + (join ByteArray.empty ss).size := by rw [hB]; simp
    have hsz' : (h ++ secBytes s).size = h.size + 1 + (encLeb 5 s.payload.size).length +
        s.payload.size := by simp [secBytes_size]; omega
    have hrd := readLeb_encLeb (join h (s :: ss)) 4 s.payload.size (h.size + 1) 0 0
      (hsz s (by simp)) hsp
    have ih := splitFrom_join ss (h ++ secBytes s) fuel (by simp at hf; omega)
      (fun t ht => hsz t (by simp [ht]))
    rw [← join_cons, hsz'] at ih
    simp only [Nat.zero_add, Nat.pow_zero, Nat.mul_one] at hrd
    have hnot : ¬ (join h (s :: ss)).size ≤ h.size := by
      have := encLeb_length_pos 4 s.payload.size; omega
    simp [splitFrom, hrd, hid, hpay, ih, hlen, hsz']
    omega

/-- **The byte round trip**: the sections of `join header secs` are `secs`. -/
theorem split_join (header : ByteArray) (secs : List Sec) (hh : header.size = 8)
    (hsz : ∀ s ∈ secs, Framable s) : split (join header secs) = some secs := by
  have hge := join_size_ge header secs
  unfold split
  rw [ite_eq_right (by omega), ← hh]
  exact splitFrom_join secs header _ (by omega) hsz

/-! ## What `split` reads is framable -/

theorem readLeb_bound_last (acc sh k y : Nat) (hy : y < 128) :
    acc + y * 2 ^ sh + 2 ^ sh ≤ acc + 2 ^ sh * 128 ^ (k + 1) := by
  have h1 : y * 2 ^ sh + 2 ^ sh = (y + 1) * 2 ^ sh := by rw [Nat.add_mul, Nat.one_mul]
  have h2 : (y + 1) * 2 ^ sh ≤ 128 ^ (k + 1) * 2 ^ sh :=
    Nat.mul_le_mul_right _ (Nat.le_trans hy (by
      rw [Nat.pow_succ]; exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (by simp))))
  rw [Nat.mul_comm (2 ^ sh)]
  omega

theorem readLeb_bound_cont (acc sh k y n : Nat) (hy : y < 128)
    (ih : n + 2 ^ (sh + 7) ≤ acc + y * 2 ^ sh + 2 ^ (sh + 7) * 128 ^ k) :
    n + 2 ^ sh ≤ acc + 2 ^ sh * 128 ^ (k + 1) := by
  have e1 : 2 ^ (sh + 7) = 128 * 2 ^ sh := by rw [Nat.pow_add, Nat.mul_comm]
  have e2 : 128 * 2 ^ sh * 128 ^ k = 2 ^ sh * 128 ^ (k + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm 128 (2 ^ sh), Nat.mul_assoc, Nat.mul_comm 128]
  have h3 : y * 2 ^ sh ≤ 127 * 2 ^ sh := Nat.mul_le_mul_right _ (by omega)
  rw [e1, e2] at ih
  generalize 2 ^ sh = P at *
  generalize P * 128 ^ (k + 1) = R at *
  generalize y * P = Y at *
  omega

/-- What `readLeb` reads with `k` bytes at shift `sh` adds less than `2^sh · 128^k`. -/
theorem readLeb_bound (b : ByteArray) :
    ∀ (k pos acc sh n p : Nat), readLeb b k pos acc sh = some (n, p) →
      n + 2 ^ sh ≤ acc + 2 ^ sh * 128 ^ k
  | 0, _, _, _, _, _, h => by simp [readLeb] at h
  | k + 1, pos, acc, sh, n, p, h => by
    by_cases hp : pos < b.size
    · have hy : b[pos]!.toNat % 128 < 128 := Nat.mod_lt _ (by decide)
      by_cases hc : b[pos]!.toNat < 128
      · rw [readLeb_last b k pos acc sh _ hp rfl hc] at h
        have hn : acc + b[pos]!.toNat % 128 * 2 ^ sh = n := by simp at h; exact h.1
        rw [← hn]
        exact readLeb_bound_last acc sh k _ hy
      · rw [readLeb_cont b k pos acc sh _ hp rfl hc] at h
        exact readLeb_bound_cont acc sh k _ n hy (readLeb_bound b k _ _ _ n p h)
    · simp [readLeb, hp] at h

theorem splitFrom_succ_some {b : ByteArray} {fuel pos : Nat} {secs : List Sec}
    (h : splitFrom b (fuel + 1) pos = some secs) (hn : ¬ b.size ≤ pos) :
    ∃ n p tail, readLeb b 5 (pos + 1) 0 0 = some (n, p) ∧ ¬ b.size < p + n ∧
      splitFrom b fuel (p + n) = some tail ∧ secs = ⟨b[pos]!, b.extract p (p + n)⟩ :: tail := by
  rw [splitFrom, ite_eq_right hn] at h
  cases hr : readLeb b 5 (pos + 1) 0 0 with
  | none => simp [hr] at h
  | some np =>
    obtain ⟨n, p⟩ := np
    by_cases hc : b.size < p + n
    · simp [hr, hc] at h
    · cases ht : splitFrom b fuel (p + n) with
      | none => simp [hr, hc, ht] at h
      | some tail =>
        simp [hr, hc, ht] at h
        exact ⟨n, p, tail, rfl, hc, ht, h.symm⟩

theorem splitFrom_framable (b : ByteArray) :
    ∀ (fuel pos : Nat) (secs : List Sec), splitFrom b fuel pos = some secs →
      ∀ s ∈ secs, Framable s
  | 0, pos, secs, h => by
    unfold splitFrom at h
    split at h <;> simp_all
  | fuel + 1, pos, secs, h => by
    by_cases hn : b.size ≤ pos
    · rw [splitFrom, ite_eq_left hn] at h
      cases h
      simp
    · obtain ⟨n, p, tail, hr, hc, ht, rfl⟩ := splitFrom_succ_some h hn
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · have hb := readLeb_bound b 5 (pos + 1) 0 0 n p hr
        show (b.extract p (p + n)).size < 128 ^ 5
        simp only [ByteArray.size_extract, Nat.pow_zero, Nat.one_mul, Nat.zero_add] at hb ⊢
        omega
      · exact splitFrom_framable b fuel _ tail ht s hs

theorem split_framable {b : ByteArray} {secs : List Sec} (h : split b = some secs) :
    ∀ s ∈ secs, Framable s := by
  unfold split at h
  split at h
  · simp at h
  · exact splitFrom_framable b _ _ secs h

/-- **Re-joining a split module splits back to the same sections.** -/
theorem split_join_split {b : ByteArray} {secs : List Sec} (h : split b = some secs) :
    split (join (b.extract 0 8) secs) = some secs := by
  have h8 : 8 ≤ b.size := by
    unfold split at h; split at h <;> first | simp at h | omega
  exact split_join _ secs (by simp; omega) (split_framable h)

/-- **The bytes `restore` writes split into the spliced section list.** -/
theorem split_restore (cs : List (Nat × Sec)) (enc : ByteArray) (secs : List Sec)
    (hne : cs ≠ []) (h : split enc = some secs) (hc : ∀ c ∈ cs, Framable c.2) :
    split (restore cs enc) = some (splice cs (secs.filter (fun s => !s.isCustom))) := by
  have h8 : 8 ≤ enc.size := by
    unfold split at h; split at h <;> first | simp at h | omega
  have hne' : cs.isEmpty = false := by cases cs <;> simp_all
  have hfr : ∀ s ∈ splice cs (secs.filter (fun s => !s.isCustom)), Framable s := by
    intro s hs
    rcases mem_splice hs with hs | ⟨c, hc', rfl⟩
    · exact split_framable h s (List.mem_filter.mp hs).1
    · exact hc c hc'
  simp only [restore, hne', h, Bool.false_eq_true, ↓reduceIte]
  exact split_join _ _ (by simp; omega) hfr
where
  mem_span {cs : List (Nat × Sec)} {q : Nat × Sec → Bool} {c : Nat × Sec}
      (h : c ∈ (cs.span q).1 ∨ c ∈ (cs.span q).2) : c ∈ cs := by
    have hsp : (cs.span q).1 ++ (cs.span q).2 = cs := by
      rw [List.span_eq_takeWhile_dropWhile]
      exact List.takeWhile_append_dropWhile
    rw [← hsp]
    exact List.mem_append.mpr h
  mem_splice {cs : List (Nat × Sec)} {ss : List Sec} {s : Sec} (h : s ∈ splice cs ss) :
      s ∈ ss ∨ ∃ c ∈ cs, s = c.2 := by
    induction ss generalizing cs with
    | nil =>
      simp only [splice, List.mem_map] at h
      obtain ⟨c, hc, rfl⟩ := h
      exact .inr ⟨c, hc, rfl⟩
    | cons t ts ih =>
      simp only [splice, List.mem_append, List.mem_map, List.mem_cons] at h
      rcases h with ⟨c, hc, rfl⟩ | rfl | h
      · exact .inr ⟨c, mem_span (.inl hc), rfl⟩
      · exact .inl (by simp)
      · rcases ih h with h | ⟨c, hc, rfl⟩
        · exact .inl (by simp [h])
        · exact .inr ⟨c, mem_span (.inr hc), rfl⟩

end Silmaril.Wasm.Tools.Gen.Cmd.Sections
