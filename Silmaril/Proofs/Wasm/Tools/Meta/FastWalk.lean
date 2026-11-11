module

public import Silmaril.Proofs.Wasm.Tools.Meta.Fast
public import Silmaril.Wasm.Tools.Meta.Frame.Thms

/-!
# Proofs: the pieces of the array walk agree with the list walk

Restated in `Silmaril.Wasm.Tools.Meta.FastCmd.Thms`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Tools.Meta

open Silmaril.Wasm.Tools.Meta

/-- A read at limit `j` that succeeds succeeds at a larger limit. -/
theorem rdU32_up (ba : ByteArray) (j k i n p : Nat) (hjk : j ≤ k) (h : rdU32 ba j i = .ok (n, p)) :
    rdU32 ba k i = .ok (n, p) := by
  rw [rdU32] at h ⊢
  by_cases hi : i < j
  · simp only [hi, show i < k by omega, ↓reduceIte] at h ⊢
    split at h
    · rename_i hb; simp only [hb, ↓reduceIte]; exact h
    · rename_i hb; simp only [hb, ↓reduceIte]
      exact rdU32Go_up ba j k hjk _ _ _ _ n p rfl h
  · simp only [hi, ↓reduceIte] at h; cases h

/-- A read ends after its start. -/
theorem rdU32_lt (ba : ByteArray) (k i n p : Nat) (h : rdU32 ba k i = .ok (n, p)) : i < p := by
  rw [rdU32] at h
  by_cases hi : i < k
  · simp only [hi, ↓reduceIte] at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
    · have := rdU32Go_lt ba k _ _ _ _ n p rfl h; omega
  · simp only [hi, ↓reduceIte] at h; cases h

/-- A read that succeeds at limit `k` ending at `p ≤ j` succeeds at `j`. -/
theorem rdU32_down (ba : ByteArray) (j k i n p : Nat) (h : rdU32 ba k i = .ok (n, p)) (hp : p ≤ j) :
    rdU32 ba j i = .ok (n, p) := by
  have hip := rdU32_lt ba k i n p h
  rw [rdU32] at h ⊢
  have hik : i < k := by
    by_cases hc : i < k
    · exact hc
    · simp only [hc, ↓reduceIte] at h; cases h
  simp only [hik, show i < j by omega, ↓reduceIte] at h ⊢
  split at h
  · rename_i hb; simp only [hb, ↓reduceIte]; exact h
  · rename_i hb; simp only [hb, ↓reduceIte]
    exact rdU32Go_down ba j k _ _ _ _ n p rfl h hp

/-- A read ends inside its limit. -/
theorem rdU32_le (ba : ByteArray) (k i n p : Nat) (h : rdU32 ba k i = .ok (n, p)) (hk : k ≤ ba.size) :
    p ≤ k := by
  have := rdU32_spec ba k i hk
  rw [h] at this
  exact this.2.2

/-- `readU32` on a slice, as `rdU32`: success with the rest of the slice, or failure. -/
theorem readU32_sl (ba : ByteArray) (j i : Nat) (hj : j ≤ ba.size) :
    (readU32 (sl ba i j)).toOption = ((rdU32 ba j i).toOption.map fun (n, p) => (n, sl ba p j)) := by
  have := rdU32_spec ba j i hj
  split at this
  · rename_i n p heq; rw [heq, this.1]; rfl
  · rename_i e heq; obtain ⟨e', he⟩ := this; rw [heq, he]; rfl

/-- The bytes of a slice, back in an array. -/
theorem mk_sl (ba : ByteArray) (i j : Nat) : ByteArray.mk (sl ba i j).toArray = ba.extract i j := by
  simp only [sl, toList_eq, Array.toArray_toList]

theorem utf8Ok_sl (ba : ByteArray) (i j : Nat) : utf8Ok (sl ba i j) = utf8OkB ba i j := by
  simp only [utf8Ok, utf8OkB, mk_sl]

/-- `readStr` on a slice, as `rdStr`. -/
theorem readStr_sl (ba : ByteArray) (j i : Nat) (hj : j ≤ ba.size) :
    (readStr (sl ba i j)).toOption =
      ((rdStr ba j i).toOption.map fun (p, e) => (sl ba p e, sl ba e j)) := by
  have hs := rdU32_spec ba j i hj
  unfold readStr readStrBytes rdStr
  split at hs
  · rename_i n p heq
    obtain ⟨h1, h2, h3⟩ := hs
    simp only [bind, Except.bind, h1, heq, Bool.true_and]
    by_cases hn : 100000 < n
    · simp [hn, throw, throwThe, MonadExceptOf.throw, Except.toOption]
    · simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [sl_take, sl_length ba _ _ (by omega), sl_drop]
      unfold rdBytes
      by_cases hb : p + n ≤ j
      · have hm : min j (p + n) = p + n := by omega
        by_cases hu : utf8OkB ba p (p + n) <;> simp [hm, hb, utf8Ok_sl, hu, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw, Except.toOption]
      · simp [show min j (p + n) - p < n by omega, hb, throw, throwThe, MonadExceptOf.throw,
          Except.toOption]
  · obtain ⟨e', he⟩ := hs
    simp [bind, Except.bind, he, *, Except.toOption]

/-- Four bytes at the front of a slice. -/
theorem sl_cons4 (ba : ByteArray) (i j : Nat) (h : i + 4 ≤ j) (hj : j ≤ ba.size) :
    sl ba i j = byteAt ba i :: byteAt ba (i + 1) :: byteAt ba (i + 2) :: byteAt ba (i + 3) ::
      sl ba (i + 4) j := by
  rw [sl_cons ba i j (by omega) hj, sl_cons ba (i + 1) j (by omega) hj,
    sl_cons ba (i + 2) j (by omega) hj, sl_cons ba (i + 3) j (by omega) hj]

theorem u8_eq_iff (a b : UInt8) : a = b ↔ a.toNat = b.toNat := by
  constructor
  · rintro rfl; rfl
  · intro h; exact UInt8.toNat_inj.mp h

/-- The magic number check. -/
theorem magicAt_iff (ba : ByteArray) (i : Nat) :
    magicAt ba i = true ↔
      [byteAt ba i, byteAt ba (i + 1), byteAt ba (i + 2), byteAt ba (i + 3)] = magic := by
  simp [magicAt, magic, and_assoc]

/-- The version word. -/
theorem u32At_eq (ba : ByteArray) (i v0 v1 v2 v3 : Nat) (h0 : v0 < 256) (h1 : v1 < 256)
    (h2 : v2 < 256) (h3 : v3 < 256) :
    u32At ba i = v0 + 256 * v1 + 65536 * v2 + 16777216 * v3 ↔
      [byteAt ba i, byteAt ba (i + 1), byteAt ba (i + 2), byteAt ba (i + 3)] =
        [v0.toUInt8, v1.toUInt8, v2.toUInt8, v3.toUInt8] := by
  have b0 := (byteAt ba i).toNat_lt
  have b1 := (byteAt ba (i + 1)).toNat_lt
  have b2 := (byteAt ba (i + 2)).toNat_lt
  have b3 := (byteAt ba (i + 3)).toNat_lt
  simp only [u32At, List.cons.injEq, and_true, u8_eq_iff, Nat.toUInt8_eq, UInt8.toNat_ofNat',
    Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3]
  omega

/-- The version word is `1` exactly when its bytes are `01 00 00 00`. -/
theorem version1_iff (ba : ByteArray) (pos : Nat) :
    u32At ba (pos + 4) = 1 ↔
      [byteAt ba (pos + 4), byteAt ba (pos + 5), byteAt ba (pos + 6), byteAt ba (pos + 7)] =
        [1, 0, 0, 0] := by
  have e := u32At_eq ba (pos + 4) 1 0 0 0 (by omega) (by omega) (by omega) (by omega)
  have c0 : Nat.toUInt8 0 = 0 := rfl
  have c1 : Nat.toUInt8 1 = 1 := rfl
  simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, c0, c1] using e

/-- The version word is `0x1000d` exactly when its bytes are `0d 00 01 00`. -/
theorem version2_iff (ba : ByteArray) (pos : Nat) :
    u32At ba (pos + 4) = 0x1000d ↔
      [byteAt ba (pos + 4), byteAt ba (pos + 5), byteAt ba (pos + 6), byteAt ba (pos + 7)] =
        [13, 0, 1, 0] := by
  have e := u32At_eq ba (pos + 4) 0x0d 0 1 0 (by omega) (by omega) (by omega) (by omega)
  have c0 : Nat.toUInt8 0 = 0 := rfl
  have c1 : Nat.toUInt8 1 = 1 := rfl
  have c13 : Nat.toUInt8 13 = 13 := rfl
  simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, c0, c1, c13] using e

/-- The header readers agree on an input shorter than the magic number. -/
theorem readHeader_sl_short (ba : ByteArray) (e : Option Enc) (lim pos : Nat) (hl : lim ≤ ba.size)
    (h4 : lim < pos + 4) :
    (readHeader e (sl ba pos lim)).toOption =
      ((readHeaderB ba e lim pos).toOption.map fun (en, p) => (en, sl ba p lim)) := by
  unfold readHeader readHeaderB
  have hlen : min 4 (sl ba pos lim).length < 4 := by rw [sl_length ba _ _ hl]; omega
  simp [hlen, h4, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Except.toOption]

/-- The header readers agree on a bad magic number. -/
theorem readHeader_sl_magic (ba : ByteArray) (e : Option Enc) (lim pos : Nat) (hl : lim ≤ ba.size)
    (h4 : ¬ lim < pos + 4) (hm : ¬ magicAt ba pos = true) :
    (readHeader e (sl ba pos lim)).toOption =
      ((readHeaderB ba e lim pos).toOption.map fun (en, p) => (en, sl ba p lim)) := by
  unfold readHeader readHeaderB
  rw [sl_cons4 ba pos lim (by omega) hl]
  have hm' : ¬ [byteAt ba pos, byteAt ba (pos + 1), byteAt ba (pos + 2),
      byteAt ba (pos + 3)] = magic := fun h => hm ((magicAt_iff ba pos).mpr h)
  simp [hm, hm', h4, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Except.toOption]

/-- The header readers agree on an input that ends inside the version word. -/
theorem readHeader_sl_short8 (ba : ByteArray) (e : Option Enc) (lim pos : Nat)
    (hl : lim ≤ ba.size) (h4 : ¬ lim < pos + 4) (hm : magicAt ba pos = true) (h8 : lim < pos + 8) :
    (readHeader e (sl ba pos lim)).toOption =
      ((readHeaderB ba e lim pos).toOption.map fun (en, p) => (en, sl ba p lim)) := by
  unfold readHeader readHeaderB
  rw [sl_cons4 ba pos lim (by omega) hl]
  have hm' := (magicAt_iff ba pos).mp hm
  have hlen : min 4 (sl ba (pos + 4) lim).length < 4 := by rw [sl_length ba _ _ hl]; omega
  simp [hlen, h4, h8, hm, hm', bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
    Except.toOption]

/-- The header readers agree on a module header. -/
theorem readHeader_sl_v1 (ba : ByteArray) (e : Option Enc) (lim pos : Nat) (hl : lim ≤ ba.size)
    (h8 : ¬ lim < pos + 8) (hm : magicAt ba pos = true) (v1 : u32At ba (pos + 4) = 1) :
    (readHeader e (sl ba pos lim)).toOption =
      ((readHeaderB ba e lim pos).toOption.map fun (en, p) => (en, sl ba p lim)) := by
  unfold readHeader readHeaderB
  rw [sl_cons4 ba pos lim (by omega) hl, sl_cons4 ba (pos + 4) lim (by omega) hl]
  have h4 : ¬ lim < pos + 4 := by omega
  have hm' := (magicAt_iff ba pos).mp hm
  have hv := (version1_iff ba pos).mp v1
  have hs : sl ba (pos + 4 + 4) lim = sl ba (pos + 8) lim := by rw [Nat.add_assoc]
  have ml : magic.length = 4 := rfl
  cases e with
  | none => simp [ml, hv, hm, hm', h4, h8, v1, hs, bind, Except.bind, pure, Except.pure,
      Except.toOption]
  | some en => cases en <;> simp [ml, hv, hm, hm', h4, h8, v1, hs, bind, Except.bind, pure,
      Except.pure, throw, throwThe, MonadExceptOf.throw, Except.toOption]

/-- The header readers agree on a component header. -/
theorem readHeader_sl_v2 (ba : ByteArray) (e : Option Enc) (lim pos : Nat) (hl : lim ≤ ba.size)
    (h8 : ¬ lim < pos + 8) (hm : magicAt ba pos = true) (v1 : ¬ u32At ba (pos + 4) = 1)
    (v2 : u32At ba (pos + 4) = 0x1000d) :
    (readHeader e (sl ba pos lim)).toOption =
      ((readHeaderB ba e lim pos).toOption.map fun (en, p) => (en, sl ba p lim)) := by
  unfold readHeader readHeaderB
  rw [sl_cons4 ba pos lim (by omega) hl, sl_cons4 ba (pos + 4) lim (by omega) hl]
  have h4 : ¬ lim < pos + 4 := by omega
  have hm' := (magicAt_iff ba pos).mp hm
  have hv : ¬ [byteAt ba (pos + 4), byteAt ba (pos + 5), byteAt ba (pos + 6),
      byteAt ba (pos + 7)] = [1, 0, 0, 0] := fun h => v1 ((version1_iff ba pos).mpr h)
  have hv2 := (version2_iff ba pos).mp v2
  have hs : sl ba (pos + 4 + 4) lim = sl ba (pos + 8) lim := by rw [Nat.add_assoc]
  have ml : magic.length = 4 := rfl
  cases e with
  | none => simp [ml, hv, hv2, hm, hm', h4, h8, v1, v2, hs, bind, Except.bind, pure,
      Except.pure, Except.toOption]
  | some en => cases en <;> simp [ml, hv, hv2, hm, hm', h4, h8, v1, v2, hs, bind,
      Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Except.toOption]

/-- The header readers agree on an unknown version. -/
theorem readHeader_sl_badVersion (ba : ByteArray) (e : Option Enc) (lim pos : Nat)
    (hl : lim ≤ ba.size) (h8 : ¬ lim < pos + 8) (hm : magicAt ba pos = true)
    (v1 : ¬ u32At ba (pos + 4) = 1) (v2 : ¬ u32At ba (pos + 4) = 0x1000d) :
    (readHeader e (sl ba pos lim)).toOption =
      ((readHeaderB ba e lim pos).toOption.map fun (en, p) => (en, sl ba p lim)) := by
  unfold readHeader readHeaderB
  rw [sl_cons4 ba pos lim (by omega) hl, sl_cons4 ba (pos + 4) lim (by omega) hl]
  have h4 : ¬ lim < pos + 4 := by omega
  have hm' := (magicAt_iff ba pos).mp hm
  have hv : ¬ [byteAt ba (pos + 4), byteAt ba (pos + 5), byteAt ba (pos + 6),
      byteAt ba (pos + 7)] = [1, 0, 0, 0] := fun h => v1 ((version1_iff ba pos).mpr h)
  have hv2 : ¬ [byteAt ba (pos + 4), byteAt ba (pos + 5), byteAt ba (pos + 6),
      byteAt ba (pos + 7)] = [13, 0, 1, 0] := fun h => v2 ((version2_iff ba pos).mpr h)
  have ml : magic.length = 4 := rfl
  simp only [List.cons.injEq, and_true] at hv hv2
  simp [Nat.add_assoc, ml, hv, hv2, hm, hm', h4, h8, v1, v2, Except.bind, throw,
    throwThe, MonadExceptOf.throw, Except.toOption]

/-- **The header readers agree.** -/
theorem readHeader_sl (ba : ByteArray) (e : Option Enc) (lim pos : Nat) (hl : lim ≤ ba.size) :
    (readHeader e (sl ba pos lim)).toOption =
      ((readHeaderB ba e lim pos).toOption.map fun (en, p) => (en, sl ba p lim)) := by
  by_cases h4 : lim < pos + 4
  · exact readHeader_sl_short ba e lim pos hl h4
  by_cases hm : magicAt ba pos = true
  · by_cases h8 : lim < pos + 8
    · exact readHeader_sl_short8 ba e lim pos hl h4 hm h8
    by_cases v1 : u32At ba (pos + 4) = 1
    · exact readHeader_sl_v1 ba e lim pos hl h8 hm v1
    by_cases v2 : u32At ba (pos + 4) = 0x1000d
    · exact readHeader_sl_v2 ba e lim pos hl h8 hm v1 v2
    · exact readHeader_sl_badVersion ba e lim pos hl h8 hm v1 v2
  · exact readHeader_sl_magic ba e lim pos hl h4 hm

/-! ## Agreement of `Except` computations -/

/-- The list computation succeeds exactly when the array one does, with the related value. -/
def Ag {α β : Type} (f : Except FErr α) (s : Except String β) (r : α → β) : Prop :=
  s.toOption = f.toOption.map r

theorem Ag.ok_iff {α β : Type} {f : Except FErr α} {s : Except String β} {r : α → β}
    (h : Ag f s r) (a : α) (hf : f = .ok a) : s = .ok (r a) := by
  unfold Ag at h; rw [hf] at h
  cases s with
  | ok b => simp [Except.toOption] at h; rw [h]
  | error _ => simp [Except.toOption] at h

theorem Ag.err {α β : Type} {f : Except FErr α} {s : Except String β} {r : α → β}
    (h : Ag f s r) (e : FErr) (hf : f = .error e) : ∃ e', s = .error e' := by
  unfold Ag at h; rw [hf] at h
  cases s with
  | ok b => simp [Except.toOption] at h
  | error e' => exact ⟨e', rfl⟩

theorem Ag.bind {α β γ δ : Type} {f : Except FErr α} {s : Except String β} {r : α → β}
    {g : α → Except FErr γ} {h : β → Except String δ} {r' : γ → δ}
    (h1 : Ag f s r) (h2 : ∀ a, f = .ok a → Ag (g a) (h (r a)) r') :
    Ag (f >>= g) (s >>= h) r' := by
  cases hf : f with
  | ok a =>
    have hs := h1.ok_iff a hf
    rw [hs]
    exact h2 a hf
  | error e =>
    obtain ⟨e', hs⟩ := h1.err e hf
    rw [hs]; rfl

theorem Ag.pure {α β : Type} (a : α) (b : β) (r : α → β) (h : r a = b) :
    Ag (Except.ok a : Except FErr α) (Except.ok b : Except String β) r := by
  simp [Ag, Except.toOption, h]

theorem Ag.errs {α β : Type} (e : FErr) (e' : String) (r : α → β) :
    Ag (Except.error e : Except FErr α) (Except.error e' : Except String β) r := by
  simp [Ag, Except.toOption]

theorem rdU32_ag (ba : ByteArray) (j i : Nat) (hj : j ≤ ba.size) :
    Ag (rdU32 ba j i) (readU32 (sl ba i j)) (fun (n, p) => (n, sl ba p j)) :=
  readU32_sl ba j i hj

theorem rdStr_ag (ba : ByteArray) (j i : Nat) (hj : j ≤ ba.size) :
    Ag (rdStr ba j i) (readStr (sl ba i j)) (fun (p, e) => (sl ba p e, sl ba e j)) :=
  readStr_sl ba j i hj

/-- `single_item` over a `var_u32`. -/
theorem singleU32_ag (ba : ByteArray) (desc : String) (a b : Nat) (hb : b ≤ ba.size) :
    Ag (singleU32B ba desc a b) (singleU32 desc (sl ba a b)) id := by
  unfold singleU32B singleU32
  apply Ag.bind (rdU32_ag ba b a hb)
  intro ⟨n, p⟩ hf
  have hp := rdU32_le ba b a n p hf hb
  by_cases hpb : p = b
  · subst hpb
    simp [sl_nil, bne, pure, Except.pure, Ag, Except.toOption]
  · have hne : (sl ba p b).isEmpty = false := by
      rw [List.isEmpty_eq_false_iff_exists_mem]
      rw [sl_cons ba p b (by omega) hb]; exact ⟨_, List.mem_cons_self⟩
    simp [hne, hpb, bne, throw, throwThe, MonadExceptOf.throw, Ag, Except.toOption, Except.bind,
      Functor.map, Except.map]

theorem checkDataCount_ag (st : PState) (o : Nat) :
    Ag (checkDataCountB st o) (checkDataCount st) id := by
  unfold checkDataCountB
  cases checkDataCount st <;> simp [Ag, Except.toOption]

theorem checkFuncCode_ag (st : PState) (o : Nat) :
    Ag (checkFuncCodeB st o) (checkFuncCode st) id := by
  unfold checkFuncCodeB
  cases checkFuncCode st <;> simp [Ag, Except.toOption]

/-- The argument-skipping fold of the component start section. -/
theorem foldSkip_ag (ba : ByteArray) (b : Nat) (hb : b ≤ ba.size) :
    ∀ (l : List Nat) (q : Nat),
      Ag (l.foldlM (fun r _ => do let (_, r) ← rdU32 ba b r; pure r) q)
        (l.foldlM (fun r _ => do let (_, r) ← readU32 r; pure r) (sl ba q b)) (fun r => sl ba r b)
  | [], q => Ag.pure _ _ _ rfl
  | x :: l, q => by
    simp only [List.foldlM_cons]
    apply Ag.bind (r := fun r => sl ba r b)
    · apply Ag.bind (rdU32_ag ba b q hb)
      intro ⟨n, p⟩ _
      exact Ag.pure _ _ _ rfl
    · intro q' _
      exact foldSkip_ag ba b hb l q'

theorem readCompStart_ag (ba : ByteArray) (a b : Nat) (hb : b ≤ ba.size) :
    Ag (readCompStartB ba a b) (readCompStart (sl ba a b)) id := by
  unfold readCompStartB readCompStart
  apply Ag.bind (rdU32_ag ba b a hb)
  intro ⟨_, p⟩ _
  apply Ag.bind (rdU32_ag ba b p hb)
  intro ⟨k, q⟩ _
  by_cases hk : 1000 < k <;> simp only [hk, ↓reduceIte]
  · exact Ag.errs _ _ _
  apply Ag.bind (foldSkip_ag ba b hb (List.range k) q)
  intro r _
  apply Ag.bind (rdU32_ag ba b r hb)
  intro ⟨m, t⟩ hf
  have ht : t ≤ b := rdU32_le ba b r m t hf hb
  by_cases hm : 1000 < m <;> simp only [hm, ↓reduceIte]
  · exact Ag.errs _ _ _
  by_cases htb : t = b
  · subst htb; simp [sl_nil, bne, pure, Except.pure, Ag, Except.toOption]
  have hne : (sl ba t b).isEmpty = false := by
    rw [List.isEmpty_eq_false_iff_exists_mem, sl_cons ba t b (by omega) hb]
    exact ⟨_, List.mem_cons_self⟩
  simp [hne, htb, bne, throw, throwThe, MonadExceptOf.throw, Ag, Except.toOption]

theorem customOf_ag (ba : ByteArray) (a b : Nat) (hb : b ≤ ba.size) :
    Ag (rdStr ba b a) (customOf (sl ba a b)) (fun (p, e) => (sl ba p e, sl ba e b)) :=
  rdStr_ag ba b a hb

/-- The module section checks of the counted sections (everything but the custom, start, data
count and code sections): the count, then the data-count check of a data section. -/
theorem checkModuleSec_counted_ag (ba : ByteArray) (st : PState) (id a b : Nat)
    (hb : b ≤ ba.size) (h0 : id ≠ 0) (h8 : id ≠ 8) (h10 : id ≠ 10) (h12 : id ≠ 12) {o : Nat}
    (ho : moduleOrder id = some o) (hle : ¬ o ≤ st.order) :
    Ag (checkModuleSecB ba st id a b) (checkModuleSec st id (sl ba a b)) _root_.id := by
  unfold checkModuleSecB checkModuleSec
  simp only [show (id == 0) = false by simpa using h0, show (id == 8) = false by simpa using h8,
    show (id == 10) = false by simpa using h10, show (id == 12) = false by simpa using h12, ho,
    hle, Bool.false_eq_true, ↓reduceIte]
  apply Ag.bind (rdU32_ag ba b a hb)
  intro ⟨n, _⟩ _
  by_cases h3 : id = 3
  · subst h3; exact Ag.pure _ _ _ rfl
  simp only [show (id == 3) = false by simpa using h3, Bool.false_eq_true, ↓reduceIte]
  by_cases h11 : id = 11
  · subst h11
    simp only [beq_self_eq_true, ↓reduceIte]
    exact Ag.bind (checkDataCount_ag _ b) fun _ _ => Ag.pure _ _ _ rfl
  simp only [show (id == 11) = false by simpa using h11, Bool.false_eq_true, ↓reduceIte]
  exact Ag.pure _ _ _ rfl

/-- The module section checks of a section in order (not custom): the start and data count
sections, then the counted ones. -/
theorem checkModuleSec_ordered_ag (ba : ByteArray) (st : PState) (id a b : Nat)
    (hb : b ≤ ba.size) (h0 : id ≠ 0) (h10 : id ≠ 10) {o : Nat}
    (ho : moduleOrder id = some o) (hle : ¬ o ≤ st.order) :
    Ag (checkModuleSecB ba st id a b) (checkModuleSec st id (sl ba a b)) _root_.id := by
  by_cases h8 : id = 8
  · subst h8
    unfold checkModuleSecB checkModuleSec
    simp only [ho, hle, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
    exact Ag.bind (singleU32_ag ba "start" a b hb) fun _ _ => Ag.pure _ _ _ rfl
  by_cases h12 : id = 12
  · subst h12
    unfold checkModuleSecB checkModuleSec
    simp only [ho, hle, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
    exact Ag.bind (singleU32_ag ba "data count" a b hb) fun _ _ => Ag.pure _ _ _ rfl
  exact checkModuleSec_counted_ag ba st id a b hb h0 h8 h10 h12 ho hle

/-- **The module section checks agree** (all sections but the code section, which the walk
handles itself). -/
theorem checkModuleSec_ag (ba : ByteArray) (st : PState) (id a b : Nat) (hb : b ≤ ba.size)
    (h10 : id ≠ 10) :
    Ag (checkModuleSecB ba st id a b) (checkModuleSec st id (sl ba a b)) _root_.id := by
  by_cases h0 : id = 0
  · subst h0
    unfold checkModuleSecB checkModuleSec
    simp only [beq_self_eq_true, ↓reduceIte]
    exact Ag.bind (customOf_ag ba a b hb) fun _ _ => Ag.pure _ _ _ rfl
  cases ho : moduleOrder id with
  | none =>
    unfold checkModuleSecB checkModuleSec
    simp only [show (id == 0) = false by simpa using h0, Bool.false_eq_true, ↓reduceIte, ho]
    exact Ag.pure _ _ _ rfl
  | some o =>
    by_cases hle : o ≤ st.order
    · unfold checkModuleSecB checkModuleSec
      simp only [show (id == 0) = false by simpa using h0, Bool.false_eq_true, ↓reduceIte, ho, hle]
      exact Ag.errs _ _ _
    exact checkModuleSec_ordered_ag ba st id a b hb h0 h10 ho hle

/-- **The component section checks agree.** -/
theorem checkComponentSec_ag (ba : ByteArray) (st : PState) (id a b : Nat) (hb : b ≤ ba.size) :
    Ag (checkComponentSecB ba st id a b) (checkComponentSec st id (sl ba a b)) _root_.id := by
  unfold checkComponentSecB checkComponentSec
  by_cases h0 : id = 0
  · subst h0
    simp only [beq_self_eq_true, ↓reduceIte]
    exact Ag.bind (customOf_ag ba a b hb) fun _ _ => Ag.pure _ _ _ rfl
  simp only [show (id == 0) = false by simpa using h0, Bool.false_eq_true, ↓reduceIte]
  by_cases h9 : id = 9
  · subst h9
    simp only [beq_self_eq_true, ↓reduceIte]
    by_cases hs : st.start = true <;> simp only [hs, Bool.false_eq_true, ↓reduceIte]
    · exact Ag.errs _ _ _
    · exact Ag.bind (readCompStart_ag ba a b hb) fun _ _ => Ag.pure _ _ _ rfl
  simp only [show (id == 9) = false by simpa using h9, Bool.false_eq_true, ↓reduceIte]
  by_cases hm : id ∈ [2, 3, 5, 6, 7, 8, 10, 11] <;> simp only [hm, ↓reduceIte]
  · exact Ag.bind (rdU32_ag ba b a hb) fun _ _ => Ag.pure _ _ _ rfl
  · exact Ag.pure _ _ _ rfl

/-! ## Code sections -/

theorem rdBytes_ok (lim pos n e : Nat) (h : rdBytes lim pos n = .ok e) : e = pos + n ∧ pos + n ≤ lim := by
  unfold rdBytes at h
  split at h
  · cases h; constructor <;> omega
  · cases h

/-- Function bodies that read end where their length says, inside the input. -/
theorem codeBodiesB_end (ba : ByteArray) (lim : Nat) (hl : lim ≤ ba.size) :
    ∀ (k pos len e : Nat), pos ≤ lim → codeBodiesB ba lim k pos len = .ok e →
      e = pos + len ∧ e ≤ lim
  | 0, pos, len, e, hp, h => by
    unfold codeBodiesB at h
    split at h
    · cases h; rename_i hz; simp at hz; constructor <;> omega
    · cases h
  | k + 1, pos, len, e, hp, h => by
    unfold codeBodiesB at h
    cases hq : rdU32 ba lim pos with
    | error _ => simp [hq, bind, Except.bind] at h
    | ok v =>
      obtain ⟨n, q⟩ := v
      have hql := rdU32_le ba lim pos n q hq hl
      have hpq := rdU32_lt ba lim pos n q hq
      cases hr : rdBytes lim q n with
      | error _ => simp [hq, hr, bind, Except.bind] at h
      | ok e' =>
        obtain ⟨rfl, hle⟩ := rdBytes_ok lim q n e' hr
        simp only [hq, hr, bind, Except.bind] at h
        split at h
        · cases h
        · rename_i hlen
          simp only [Nat.not_lt] at hlen
          have := codeBodiesB_end ba lim hl k _ _ e (by omega) h
          constructor <;> omega

/-- What `codeBodies_ag` states for `k` bodies from `pos`: the array read succeeds exactly when
the list read does, and then ends at `bEnd`. -/
def CodeAg (ba : ByteArray) (lim bEnd k pos : Nat) : Prop :=
  ((∃ e, codeBodiesB ba lim k pos (bEnd - pos) = .ok e) ↔ codeBodies k (sl ba pos bEnd) = .ok ()) ∧
    (∀ e, codeBodiesB ba lim k pos (bEnd - pos) = .ok e → e = bEnd)

/-- No bodies: both reads succeed exactly at the end of the section. -/
theorem codeAg_zero (ba : ByteArray) (lim bEnd pos : Nat) (hl : lim ≤ ba.size) (hb : bEnd ≤ lim)
    (hp : pos ≤ bEnd) : CodeAg ba lim bEnd 0 pos := by
  unfold CodeAg codeBodiesB
  by_cases hz : pos = bEnd
  · subst hz
    simp [sl_nil, codeBodies, pure, Except.pure]
  · have hne : sl ba pos bEnd ≠ [] := by
      rw [sl_cons ba pos bEnd (by omega) (by omega)]; simp
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
    simp [show bEnd - pos ≠ 0 by omega, hx, codeBodies]

/-- A successful array read of `k + 1` bodies reads a first body inside the section, then `k`. -/
theorem codeBodiesB_succ_ok (ba : ByteArray) (lim bEnd k pos e : Nat)
    (h : codeBodiesB ba lim (k + 1) pos (bEnd - pos) = .ok e) :
    ∃ n q, rdU32 ba lim pos = .ok (n, q) ∧ q + n ≤ bEnd ∧
      codeBodiesB ba lim k (q + n) (bEnd - (q + n)) = .ok e := by
  unfold codeBodiesB at h
  cases hq : rdU32 ba lim pos with
  | error _ => simp [hq, bind, Except.bind] at h
  | ok v =>
    obtain ⟨n, q⟩ := v
    have hpq := rdU32_lt ba lim pos n q hq
    cases hr : rdBytes lim q n with
    | error _ => simp [hq, hr, bind, Except.bind] at h
    | ok e' =>
      obtain ⟨rfl, _⟩ := rdBytes_ok lim q n e' hr
      simp only [hq, hr, bind, Except.bind] at h
      split at h
      · cases h
      · rename_i hlen
        refine ⟨n, q, rfl, by omega, ?_⟩
        rwa [show bEnd - pos - (q + n - pos) = bEnd - (q + n) by omega] at h

/-- The list read of `k + 1` bodies after a size field that reads. -/
theorem codeBodies_succ_eq (ba : ByteArray) (bEnd k pos n q : Nat)
    (hs : readU32 (sl ba pos bEnd) = .ok (n, sl ba q bEnd)) :
    codeBodies (k + 1) (sl ba pos bEnd) =
      (if ((sl ba q bEnd).take n).length < n then .error errEof
       else codeBodies k ((sl ba q bEnd).drop n)) := by
  conv => lhs; unfold codeBodies
  simp only [hs, bind, Except.bind]
  split <;> simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- `k + 1` bodies whose first one fits in the section, from the facts for the other `k`. -/
theorem codeAg_succ_fit (ba : ByteArray) (lim bEnd k pos n q : Nat) (hl : lim ≤ ba.size) (hb : bEnd ≤ lim)
    (hq : rdU32 ba bEnd pos = .ok (n, q))
    (hs : readU32 (sl ba pos bEnd) = .ok (n, sl ba q bEnd)) (hpq : pos < q) (hqb : q ≤ bEnd)
    (hn : q + n ≤ bEnd) (ih : CodeAg ba lim bEnd k (q + n)) : CodeAg ba lim bEnd (k + 1) pos := by
  have hql := rdU32_up ba bEnd lim pos n q hb hq
  have hfe : codeBodiesB ba lim (k + 1) pos (bEnd - pos) =
      codeBodiesB ba lim k (q + n) (bEnd - (q + n)) := by
    conv => lhs; unfold codeBodiesB
    simp only [hql, bind, Except.bind, rdBytes, show q + n ≤ lim by omega, ↓reduceIte,
      show ¬ bEnd - pos < q + n - pos by omega,
      show bEnd - pos - (q + n - pos) = bEnd - (q + n) by omega]
  have hc : ¬ (min bEnd (q + n) - q < n) := by omega
  unfold CodeAg
  rw [codeBodies_succ_eq ba bEnd k pos n q hs, sl_take, sl_drop, sl_length ba _ _ (by omega)]
  simp only [hfe, hc, ↓reduceIte]
  simpa [CodeAg] using ih

/-- `k + 1` bodies whose first one overruns the section: both reads fail. -/
theorem codeAg_succ_over (ba : ByteArray) (lim bEnd k pos n q : Nat) (hl : lim ≤ ba.size) (hb : bEnd ≤ lim)
    (hq : rdU32 ba bEnd pos = .ok (n, q))
    (hs : readU32 (sl ba pos bEnd) = .ok (n, sl ba q bEnd)) (hqb : q ≤ bEnd)
    (hn : ¬ q + n ≤ bEnd) : CodeAg ba lim bEnd (k + 1) pos := by
  have hql := rdU32_up ba bEnd lim pos n q hb hq
  have hc : min bEnd (q + n) - q < n := by omega
  have hno : ∀ e, codeBodiesB ba lim (k + 1) pos (bEnd - pos) ≠ .ok e := by
    intro e he
    obtain ⟨n', q', h1, h2, _⟩ := codeBodiesB_succ_ok ba lim bEnd k pos e he
    rw [hql] at h1; cases h1; omega
  unfold CodeAg
  rw [codeBodies_succ_eq ba bEnd k pos n q hs, sl_take, sl_drop, sl_length ba _ _ (by omega)]
  simp only [hc, ↓reduceIte]
  exact ⟨⟨fun ⟨e, he⟩ => absurd he (hno e), fun h => by cases h⟩, fun e he => absurd he (hno e)⟩

/-- `k + 1` bodies whose first size field does not read in the section: both reads fail. -/
theorem codeAg_succ_fail (ba : ByteArray) (lim bEnd k pos : Nat) (ef : FErr)
    (hq : rdU32 ba bEnd pos = .error ef) (e' : String)
    (hs : readU32 (sl ba pos bEnd) = .error e') : CodeAg ba lim bEnd (k + 1) pos := by
  have hcb : codeBodies (k + 1) (sl ba pos bEnd) = .error e' := by
    unfold codeBodies; simp [hs, bind, Except.bind]
  have hno : ∀ e, codeBodiesB ba lim (k + 1) pos (bEnd - pos) ≠ .ok e := by
    intro e he
    obtain ⟨n', q', h1, h2, _⟩ := codeBodiesB_succ_ok ba lim bEnd k pos e he
    have hpq := rdU32_lt ba lim pos n' q' h1
    have := rdU32_down ba bEnd lim pos n' q' h1 (by omega)
    rw [hq] at this; cases this
  unfold CodeAg
  rw [hcb]
  exact ⟨⟨fun ⟨e, he⟩ => absurd he (hno e), fun h => by cases h⟩, fun e he => absurd he (hno e)⟩

/-- **The function bodies agree**, reading to `lim` upstream-style or within `[pos, bEnd)`. -/
theorem codeBodies_ag (ba : ByteArray) (lim bEnd : Nat) (hl : lim ≤ ba.size) (hb : bEnd ≤ lim) :
    ∀ (k pos : Nat), pos ≤ bEnd →
      ((∃ e, codeBodiesB ba lim k pos (bEnd - pos) = .ok e) ↔ codeBodies k (sl ba pos bEnd) = .ok ()) ∧
      (∀ e, codeBodiesB ba lim k pos (bEnd - pos) = .ok e → e = bEnd)
  | 0, pos, hp => codeAg_zero ba lim bEnd pos hl hb hp
  | k + 1, pos, hp => by
    have hspec := rdU32_spec ba bEnd pos (by omega)
    split at hspec
    · rename_i n q hq
      obtain ⟨hs, hpq, hqb⟩ := hspec
      by_cases hn : q + n ≤ bEnd
      · exact codeAg_succ_fit ba lim bEnd k pos n q hl hb hq hs hpq hqb hn
          (codeBodies_ag ba lim bEnd hl hb k (q + n) hn)
      · exact codeAg_succ_over ba lim bEnd k pos n q hl hb hq hs hqb hn
    · rename_i ef hq
      obtain ⟨e', hs⟩ := hspec
      exact codeAg_succ_fail ba lim bEnd k pos ef hq e' hs

/-! ## A truncated unit fails -/

theorem readHeaderB_pos (ba : ByteArray) (e : Option Enc) (lim pos : Nat) (en : Enc) (p : Nat)
    (h : readHeaderB ba e lim pos = .ok (en, p)) : p = pos + 8 ∧ p ≤ lim := by
  unfold readHeaderB at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  rename_i h4 _ h8
  split at h
  · split at h; · cases h
    cases h; constructor <;> omega
  · split at h
    · split at h; · cases h
      cases h; constructor <;> omega
    · cases h

mutual
/-- A walk that succeeds with a declared end `m` reaches it inside the input. -/
theorem secs_ok_le (ba : ByteArray) (hk : Hook) :
    ∀ (f : Nat) (enc : Enc) (st : PState) (pos lim m : Nat) (v : List ItemB),
      lim ≤ ba.size → pos ≤ lim → parseSecsHB ba hk f enc st pos lim (some m) = .ok v → m ≤ lim
  | 0, _, _, _, _, _, _, _, _, h => by simp [parseSecsHB] at h
  | f + 1, enc, st, pos, lim, m, v, hl, hp, h => by
    unfold parseSecsHB at h
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    split at h
    · split at h; · cases h
      rename_i hlp hm
      split at h; · cases h
      omega
    · split at h; · cases h
      split at h; · cases h
      split at h; · cases h
      rename_i _ r hr
      rcases r with ⟨len, a⟩
      have hal := rdU32_le ba lim (pos + 1) len a hr hl
      split at h; · cases h
      split at h
      · -- nested
        split at h; · cases h
        split at h; · cases h
        rename_i _ r hu
        rcases r with ⟨enc', items⟩
        split at h; · cases h
        rename_i _ is hs
        cases h
        have hb : a + len ≤ lim := by
          by_cases hc : a + len ≤ lim
          · exact hc
          · have hmin : Nat.min (a + len) lim = lim := by
              unfold Nat.min; omega
            dsimp only at hu
            rw [hmin] at hu
            have := unit_ok_le ba hk f _ a lim (a + len) _ hl hu
            omega
        exact secs_ok_le ba hk f enc st (a + len) lim m is hl hb hs
      · split at h
        · -- code
          split at h; · cases h
          rename_i o _
          split at h; · cases h
          split at h; · cases h
          rename_i _ r hq
          rcases r with ⟨n, p⟩
          have hpl := rdU32_le ba lim a n p hq hl
          split at h; · cases h
          split at h; · cases h
          split at h; · cases h
          rename_i _ e he
          have := codeBodiesB_end ba lim hl n p _ e hpl he
          split at h; · cases h
          rename_i _ is hs
          cases h
          exact secs_ok_le ba hk f enc _ e lim m is hl this.2 hs
        · -- other sections
          split at h; · cases h
          rename_i _ e he
          obtain ⟨rfl, hle⟩ := rdBytes_ok lim a len e he
          split at h <;>
          · split at h; · cases h
            split at h
            · split at h; · cases h
              split at h; · cases h
              rename_i _ is hs
              cases h
              exact secs_ok_le ba hk f _ _ (a + len) lim m is hl hle hs
            · split at h; · cases h
              rename_i _ is hs
              cases h
              exact secs_ok_le ba hk f _ _ (a + len) lim m is hl hle hs
/-- A unit that succeeds with a declared end `m` reaches it inside the input. -/
theorem unit_ok_le (ba : ByteArray) (hk : Hook) :
    ∀ (f : Nat) (ex : Option Enc) (pos lim m : Nat) (v : Enc × List ItemB),
      lim ≤ ba.size → parseUnitHB ba hk f ex pos lim (some m) = .ok v → m ≤ lim
  | 0, _, _, _, _, _, _, h => by simp [parseUnitHB] at h
  | f + 1, ex, pos, lim, m, v, hl, h => by
    unfold parseUnitHB at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i _ r hh
    rcases r with ⟨enc, p⟩
    have hp := readHeaderB_pos ba ex lim pos enc p hh
    split at h; · cases h
    rename_i _ is hs
    exact secs_ok_le ba hk f enc {} p lim m is hl hp.2 hs
end

/-! ## Section framing -/

theorem lebLen_le : ∀ l : List UInt8, lebLen l ≤ l.length
  | [] => by simp [lebLen]
  | b :: l => by
    have := lebLen_le l
    simp only [lebLen, List.length_cons]; split <;> omega

/-- The magic-number check of a section start. -/
theorem magic_take (ba : ByteArray) (pos lim : Nat) (h : pos < lim) (hl : lim ≤ ba.size) :
    ((byteAt ba pos :: sl ba (pos + 1) lim).take 4 == magic) =
      (decide (pos + 4 ≤ lim) && magicAt ba pos) := by
  rw [← sl_cons ba pos lim h hl]
  by_cases h4 : pos + 4 ≤ lim
  · rw [sl_cons4 ba pos lim h4 hl]
    have := magicAt_iff ba pos
    simp only [List.take_succ_cons, List.take_zero, h4, decide_true, Bool.true_and]
    cases hm : magicAt ba pos
    · simp only [hm, Bool.false_eq_true, false_iff] at this
      simpa using this
    · simp only [hm, true_iff] at this
      simp [this]
  · have hlen : ((sl ba pos lim).take 4).length < 4 := by
      rw [List.length_take, sl_length ba _ _ hl]; omega
    have : ((sl ba pos lim).take 4 == magic) = false := by
      rw [beq_eq_false_iff_ne]; intro he; rw [he] at hlen; simp [magic] at hlen
    simp [this, h4]

/-- **A section that reads**: size field, contents and rest are the slices. -/
theorem readSec_ok (ba : ByteArray) (pos lim len a : Nat) (h : pos < lim) (hl : lim ≤ ba.size)
    (hm : (decide (pos + 4 ≤ lim) && magicAt ba pos) = false) (hid : ¬ 128 ≤ (byteAt ba pos).toNat)
    (hr : rdU32 ba lim (pos + 1) = .ok (len, a)) (hb : a + len ≤ lim) :
    readSec (byteAt ba pos) (sl ba (pos + 1) lim) =
      .ok (sl ba (pos + 1) a, sl ba a (a + len), sl ba (a + len) lim) := by
  have hs := rdU32_spec ba lim (pos + 1) hl
  rw [hr] at hs
  obtain ⟨hs, hpa, hal⟩ := hs
  unfold readSec
  rw [magic_take ba pos lim h hl, hm]
  simp only [Bool.false_eq_true, ↓reduceIte, hid, hs]
  have hL := readU32_drop hs
  have hL2 := lebLen_le (sl ba (pos + 1) lim)
  rw [sl_drop, sl_length ba _ _ hl] at *
  have hlen : a = pos + 1 + lebLen (sl ba (pos + 1) lim) := by
    have := congrArg List.length hL
    rw [sl_length ba _ _ hl, sl_length ba _ _ hl] at this
    omega
  have e1 : min lim (pos + 1 + lebLen (sl ba (pos + 1) lim)) = a := by omega
  have e2 : min lim (a + len) = a + len := by omega
  simp only [sl_take, sl_drop, e1, e2]
  rw [sl_length ba _ _ (by omega)]
  simp only [show ¬ (a + len - a < len) by omega, ↓reduceIte]

/-- A section that starts with the magic number does not read. -/
theorem readSec_err_magic (ba : ByteArray) (pos lim : Nat) (h : pos < lim) (hl : lim ≤ ba.size)
    (hm : (decide (pos + 4 ≤ lim) && magicAt ba pos) = true) :
    ∃ e, readSec (byteAt ba pos) (sl ba (pos + 1) lim) = .error e := by
  unfold readSec
  rw [magic_take ba pos lim h hl]
  simp [hm]

/-- A section with a malformed id does not read. -/
theorem readSec_err_id (ba : ByteArray) (pos lim : Nat) (h : pos < lim) (hl : lim ≤ ba.size)
    (hm : ¬ (decide (pos + 4 ≤ lim) && magicAt ba pos) = true) (hid : 128 ≤ (byteAt ba pos).toNat) :
    ∃ e, readSec (byteAt ba pos) (sl ba (pos + 1) lim) = .error e := by
  unfold readSec
  rw [magic_take ba pos lim h hl]
  simp only [hm, Bool.false_eq_true, ↓reduceIte, hid]
  exact ⟨_, rfl⟩

/-- A section whose size field does not read does not read. -/
theorem readSec_err_size (ba : ByteArray) (pos lim : Nat) (h : pos < lim) (hl : lim ≤ ba.size)
    (hm : ¬ (decide (pos + 4 ≤ lim) && magicAt ba pos) = true) (hid : ¬ 128 ≤ (byteAt ba pos).toNat)
    (e : FErr) (he : rdU32 ba lim (pos + 1) = .error e) :
    ∃ e, readSec (byteAt ba pos) (sl ba (pos + 1) lim) = .error e := by
  unfold readSec
  rw [magic_take ba pos lim h hl]
  have hs := rdU32_spec ba lim (pos + 1) hl
  rw [he] at hs
  obtain ⟨e', hs⟩ := hs
  simp [hm, hid, hs]

/-- A section larger than the rest of the input does not read. -/
theorem readSec_err_large (ba : ByteArray) (pos lim : Nat) (h : pos < lim) (hl : lim ≤ ba.size)
    (hm : ¬ (decide (pos + 4 ≤ lim) && magicAt ba pos) = true) (hid : ¬ 128 ≤ (byteAt ba pos).toNat)
    (len a : Nat) (hr : rdU32 ba lim (pos + 1) = .ok (len, a)) (hb : lim < a + len) :
    ∃ e, readSec (byteAt ba pos) (sl ba (pos + 1) lim) = .error e := by
  unfold readSec
  rw [magic_take ba pos lim h hl]
  have hs := rdU32_spec ba lim (pos + 1) hl
  rw [hr] at hs
  obtain ⟨hs, _, hal⟩ := hs
  simp only [hm, Bool.false_eq_true, ↓reduceIte, hid, hs, sl_take]
  rw [sl_length ba _ _ (by omega)]
  split
  · exact ⟨_, rfl⟩
  · omega

/-- A section that does not read fits nothing. -/
theorem readSec_err (ba : ByteArray) (pos lim : Nat) (h : pos < lim) (hl : lim ≤ ba.size)
    (hc : (decide (pos + 4 ≤ lim) && magicAt ba pos) = true ∨ 128 ≤ (byteAt ba pos).toNat ∨
      (∃ e, rdU32 ba lim (pos + 1) = .error e) ∨
      (∃ len a, rdU32 ba lim (pos + 1) = .ok (len, a) ∧ lim < a + len)) :
    ∃ e, readSec (byteAt ba pos) (sl ba (pos + 1) lim) = .error e := by
  by_cases hm : (decide (pos + 4 ≤ lim) && magicAt ba pos) = true
  · exact readSec_err_magic ba pos lim h hl hm
  by_cases hid : 128 ≤ (byteAt ba pos).toNat
  · exact readSec_err_id ba pos lim h hl hm hid
  rcases hc with hm' | hid' | ⟨e, he⟩ | ⟨len, a, hr, hb⟩
  · exact absurd hm' hm
  · exact absurd hid' hid
  · exact readSec_err_size ba pos lim h hl hm hid e he
  · exact readSec_err_large ba pos lim h hl hm hid len a hr hb

/-! ## The walk -/

theorem ok_bind {ε α β : Type} (a : α) (g : α → Except ε β) : ((Except.ok a : Except ε α) >>= g) = g a :=
  rfl

theorem err_bind {ε α β : Type} (e : ε) (g : α → Except ε β) :
    ((Except.error e : Except ε α) >>= g) = Except.error e := rfl

theorem toItem_nest (ba : ByteArray) (id : UInt8) (sa a b : Nat) (enc : Enc) (items : List ItemB) :
    ItemB.toItem ba (.nest id sa a b enc items) =
      .nest id (sl ba sa a) enc (items.map (ItemB.toItem ba)) := by
  rw [ItemB.toItem]
  simp

theorem toItem_sec (ba : ByteArray) (s : SecB) : ItemB.toItem ba (.sec s) = .sec (s.toSec ba) := by
  rw [ItemB.toItem]

theorem Ag.none {α β : Type} {f : Except FErr α} {s : Except String β} (r : α → β)
    (hf : f.toOption = none) (hs : s.toOption = none) : Ag f s r := by
  simp [Ag, hf, hs]

theorem toOption_none_iff {α ε : Type} (x : Except ε α) : x.toOption = none ↔ ∃ e, x = .error e := by
  cases x <;> simp [Except.toOption]

theorem checkEnd_ag (enc : Enc) (st : PState) (pos : Nat) :
    Ag (checkEndB enc st pos) (checkEnd enc st) _root_.id := by
  cases enc
  · unfold checkEndB checkEnd
    apply Ag.bind (checkFuncCode_ag st pos)
    intro _ _; exact checkDataCount_ag st pos
  · exact Ag.pure _ _ _ rfl

set_option hygiene false in
/-- The first steps of a successful outer walk `h` whose first size field reads as `hr0`, up to
the choice of the kind of section. Not hygienic: it rewrites the hypothesis `h` and uses `hpl`
and `hr0` of the context. -/
local macro "first_sec_prefix" : tactic => `(tactic| (
  unfold parseSecsHB at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h; · omega
  split at h; · cases h
  split at h; · cases h
  rw [hr0] at h))

/-- `first_sec_le` for a nested unit. -/
theorem first_sec_le_nest (ba : ByteArray) (hk : Hook) (f : Nat) (enc : Enc) (st : PState)
    (pos lim len a : Nat) (v : List ItemB) (hl : lim ≤ ba.size) (hpl : pos < lim)
    (hr0 : rdU32 ba lim (pos + 1) = .ok (len, a)) (hn : isNest enc (byteAt ba pos) = true)
    (h : parseSecsHB ba hk (f + 1) enc st pos lim none = .ok v) : a + len ≤ lim := by
  first_sec_prefix
  simp only [hn, ↓reduceIte] at h
  split at h; · cases h
  split at h; · cases h
  rename_i _ r hu
  by_cases hc : a + len ≤ lim
  · exact hc
  · have hmin : Nat.min (a + len) lim = lim := by unfold Nat.min; omega
    rw [hmin] at hu
    have := unit_ok_le ba hk f _ a lim (a + len) _ hl hu
    omega

/-- `first_sec_le` for a code section. -/
theorem first_sec_le_code (ba : ByteArray) (hk : Hook) (f : Nat) (enc : Enc) (st : PState)
    (pos lim len a : Nat) (v : List ItemB) (hl : lim ≤ ba.size) (hpl : pos < lim)
    (hr0 : rdU32 ba lim (pos + 1) = .ok (len, a)) (hn : ¬ isNest enc (byteAt ba pos) = true)
    (hc : (enc == Enc.module && byteAt ba pos == 10) = true)
    (h : parseSecsHB ba hk (f + 1) enc st pos lim none = .ok v) : a + len ≤ lim := by
  first_sec_prefix
  simp only [hn, hc, Bool.false_eq_true, ↓reduceIte] at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  rename_i _ r hq
  split at h; · cases h
  rename_i hlen
  split at h; · cases h
  split at h; · cases h
  rename_i _ e he
  have h1 := codeBodiesB_end ba lim hl r.1 r.2 _ e (rdU32_le ba lim a r.1 r.2 hq hl) he
  have h2 := rdU32_lt ba lim a r.1 r.2 hq
  omega

/-- `first_sec_le` for any other section. -/
theorem first_sec_le_other (ba : ByteArray) (hk : Hook) (f : Nat) (enc : Enc) (st : PState)
    (pos lim len a : Nat) (v : List ItemB) (hpl : pos < lim)
    (hr0 : rdU32 ba lim (pos + 1) = .ok (len, a)) (hn : ¬ isNest enc (byteAt ba pos) = true)
    (hc : ¬ (enc == Enc.module && byteAt ba pos == 10) = true)
    (h : parseSecsHB ba hk (f + 1) enc st pos lim none = .ok v) : a + len ≤ lim := by
  first_sec_prefix
  simp only [hn, hc, Bool.false_eq_true, ↓reduceIte] at h
  split at h; · cases h
  rename_i _ e he
  exact (rdBytes_ok lim a len e he).2

/-- In an outer unit (no declared end), a walk that succeeds has its first section inside the
input. -/
theorem first_sec_le (ba : ByteArray) (hk : Hook) (f : Nat) (enc : Enc) (st : PState)
    (pos lim len a : Nat) (v : List ItemB) (hl : lim ≤ ba.size) (hpl : pos < lim)
    (hr0 : rdU32 ba lim (pos + 1) = .ok (len, a))
    (h : parseSecsHB ba hk (f + 1) enc st pos lim none = .ok v) : a + len ≤ lim := by
  by_cases hn : isNest enc (byteAt ba pos) = true
  · exact first_sec_le_nest ba hk f enc st pos lim len a v hl hpl hr0 hn h
  by_cases hc : (enc == Enc.module && byteAt ba pos == 10) = true
  · exact first_sec_le_code ba hk f enc st pos lim len a v hl hpl hr0 hn hc h
  · exact first_sec_le_other ba hk f enc st pos lim len a v hpl hr0 hn hc h

/-! ### The walks agree, by induction on the fuel -/

/-- The agreement of the section walks at fuel `f` from `pos`. -/
def SecsAgAt (ba : ByteArray) (f : Nat) (enc : Enc) (st : PState) (pos lim : Nat)
    (max : Option Nat) : Prop :=
  Ag (parseSecsHB ba noHook f enc st pos lim max) (parseSecs f enc st (sl ba pos lim))
    (List.map (ItemB.toItem ba))

/-- What `secs_ag` states at fuel `f`. -/
def SecsAg (ba : ByteArray) (f : Nat) : Prop :=
  ∀ (enc : Enc) (st : PState) (pos lim : Nat) (max : Option Nat), lim ≤ ba.size → pos ≤ lim →
    (max = none ∨ max = some lim) → SecsAgAt ba f enc st pos lim max

/-- What `unit_ag` states at fuel `f`. -/
def UnitAg (ba : ByteArray) (f : Nat) : Prop :=
  ∀ (ex : Option Enc) (pos lim : Nat) (max : Option Nat), lim ≤ ba.size →
    (max = none ∨ max = some lim) →
    Ag (parseUnitHB ba noHook f ex pos lim max) (parseUnit f ex (sl ba pos lim))
      (fun r => (r.1, r.2.map (ItemB.toItem ba)))

/-- A section at `pos` whose size field reads `len` and whose contents `[a, a + len)` fit in
the input. -/
structure SecOk (ba : ByteArray) (pos lim len a : Nat) : Prop where
  hlt : pos < lim
  hl : lim ≤ ba.size
  hmag : (decide (pos + 4 ≤ lim) && magicAt ba pos) = false
  hid : ¬ 128 ≤ (byteAt ba pos).toNat
  hr : rdU32 ba lim (pos + 1) = .ok (len, a)
  hb : a + len ≤ lim

/-- Two walks over `[a, b)` that end at `b` and agree on success, then two that agree. -/
theorem Ag.bind_end {α β : Type} {f : Except FErr Nat} {s : Except String Unit}
    {g : Nat → Except FErr α} {h : Except String β} {r : α → β} (b : Nat)
    (hiff : (∃ e, f = .ok e) ↔ s = .ok ()) (hb : ∀ e, f = .ok e → e = b) (hk : Ag (g b) h r) :
    Ag (f >>= g) (s >>= fun _ => h) r := by
  cases hf : f with
  | ok e =>
    obtain rfl := hb e hf
    rw [hiff.mp ⟨_, hf⟩]
    exact hk
  | error e =>
    cases hs : s with
    | ok u => obtain ⟨e', he⟩ := hiff.mpr hs; rw [hf] at he; cases he
    | error _ => rfl

/-- The end of the input. -/
theorem secsAg_end (ba : ByteArray) (f : Nat) (enc : Enc) (st : PState) (pos : Nat)
    (max : Option Nat) (hm : max = none ∨ max = some pos) :
    SecsAgAt ba (f + 1) enc st pos pos max := by
  unfold SecsAgAt
  rw [sl_nil ba pos pos (Nat.le_refl _)]
  unfold parseSecsHB parseSecs
  simp only [Nat.le_refl, ↓reduceIte]
  rcases hm with rfl | rfl <;>
  · simp only [Nat.lt_irrefl, ↓reduceIte]
    apply Ag.bind (checkEnd_ag enc st pos)
    intro _ _; exact Ag.pure _ _ _ rfl

/-- A section that the list walk cannot read (`he`) and the array walk rejects (`hb`). -/
theorem secsAg_bad (ba : ByteArray) (f : Nat) (enc : Enc) (st : PState) (pos lim : Nat)
    (max : Option Nat) (hlt : pos < lim) (hl : lim ≤ ba.size) (e : String)
    (he : readSec (byteAt ba pos) (sl ba (pos + 1) lim) = .error e)
    (hb : (parseSecsHB ba noHook (f + 1) enc st pos lim max).toOption = none) :
    SecsAgAt ba (f + 1) enc st pos lim max := by
  unfold SecsAgAt
  rw [sl_cons ba pos lim hlt hl]
  apply Ag.none _ hb
  unfold parseSecs
  simp [he, bind, Except.bind, Except.toOption]

/-- The array walk rejects a section starting with the magic number, with a malformed id or
with a size field that does not read. -/
theorem secsHB_bad (ba : ByteArray) (f : Nat) (enc : Enc) (st : PState) (pos lim : Nat)
    (max : Option Nat) (hend : ¬ lim ≤ pos)
    (hc : (decide (pos + 4 ≤ lim) && magicAt ba pos) = true ∨ 128 ≤ (byteAt ba pos).toNat ∨
      (∃ e, rdU32 ba lim (pos + 1) = .error e)) :
    (parseSecsHB ba noHook (f + 1) enc st pos lim max).toOption = none := by
  unfold parseSecsHB
  by_cases hmag : (decide (pos + 4 ≤ lim) && magicAt ba pos) = true
  · simp [hend, hmag, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Except.toOption]
  have hmag' : (decide (pos + 4 ≤ lim) && magicAt ba pos) = false := by simpa using hmag
  by_cases hid : 128 ≤ (byteAt ba pos).toNat
  · simp [hend, hmag', hid, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
      Except.toOption]
  obtain ⟨er, hr⟩ : ∃ e, rdU32 ba lim (pos + 1) = .error e := by
    rcases hc with h | h | h
    · exact absurd h hmag
    · exact absurd h hid
    · exact h
  simp [hend, hmag', hid, hr, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
    Except.toOption]

/-- The array walk rejects a section whose contents go past the end of the input. -/
theorem secsHB_large (ba : ByteArray) (f : Nat) (enc : Enc) (st : PState) (pos lim : Nat)
    (max : Option Nat) (hm : max = none ∨ max = some lim) (hlt : pos < lim) (hl : lim ≤ ba.size)
    (hmag' : (decide (pos + 4 ≤ lim) && magicAt ba pos) = false)
    (hid : ¬ 128 ≤ (byteAt ba pos).toNat) (len a : Nat) (hr : rdU32 ba lim (pos + 1) = .ok (len, a))
    (hb : ¬ a + len ≤ lim) :
    (parseSecsHB ba noHook (f + 1) enc st pos lim max).toOption = none := by
  rcases hm with rfl | rfl
  · cases hfx : parseSecsHB ba noHook (f + 1) enc st pos lim none with
    | error _ => rfl
    | ok v => exact absurd (first_sec_le ba noHook f enc st pos lim len a v hl hlt hr hfx) hb
  · unfold parseSecsHB
    simp [show ¬ lim ≤ pos by omega, hmag', hid, hr, ok_bind, show lim < a + len by omega, throw,
      throwThe, MonadExceptOf.throw, Except.toOption, err_bind]

set_option hygiene false in
/-- The steps of both walks up to the kind of a section that reads (`hs : SecOk …`). Not
hygienic: it uses `ba`, `pos`, `lim`, `len`, `a`, `hs` and `hm` of the context, names the fields
of `hs`, and leaves one goal per value of `max`. -/
local macro "sec_ok_prefix" : tactic => `(tactic| (
  obtain ⟨hlt, hl, hmag', hid, hr, hb⟩ := hs
  have hrs := readSec_ok ba pos lim len a hlt hl hmag' hid hr hb
  have hmin : Nat.min (a + len) lim = a + len := by unfold Nat.min; omega
  have hbl : (sl ba a (a + len)).length = len := by
    rw [sl_length ba a (a + len) (by omega)]; omega
  unfold SecsAgAt
  rw [sl_cons ba pos lim hlt hl]
  unfold parseSecsHB parseSecs
  simp only [show ¬ lim ≤ pos by omega, ↓reduceIte, hmag', hid, hr, Bool.false_eq_true, hrs,
    ok_bind]
  rcases hm with rfl | rfl <;>
    simp only [show ¬ lim < a + len by omega, ↓reduceIte, hmin, hbl]))

/-- A nested unit. -/
theorem secsAg_nest (ba : ByteArray) (f : Nat) (ih : SecsAg ba f) (ihu : UnitAg ba f) (enc : Enc)
    (st : PState) (pos lim len a : Nat) (max : Option Nat) (hs : SecOk ba pos lim len a)
    (hm : max = none ∨ max = some lim) (hn : isNest enc (byteAt ba pos) = true) :
    SecsAgAt ba (f + 1) enc st pos lim max := by
  sec_ok_prefix
  all_goals
    simp only [hn, ↓reduceIte]
    by_cases hg : 1073741824 < len
    · simp only [hg, ↓reduceIte]; exact Ag.errs _ _ _
    simp only [hg, ↓reduceIte]
    apply Ag.bind (ihu _ a (a + len) _ (by omega) (Or.inr rfl))
    intro r _
    apply Ag.bind (ih enc st (a + len) lim _ hl hb (by simp))
    intro is _
    exact Ag.pure _ _ _ (by simp [toItem_nest])

/-- A section of a module other than the code section. -/
theorem secsAg_otherM (ba : ByteArray) (f : Nat) (ih : SecsAg ba f) (st : PState)
    (pos lim len a : Nat) (max : Option Nat) (hs : SecOk ba pos lim len a)
    (hm : max = none ∨ max = some lim) (hi : ¬ byteAt ba pos = 10) :
    SecsAgAt ba (f + 1) .module st pos lim max := by
  have h10 : (byteAt ba pos).toNat ≠ 10 := fun h => hi (UInt8.toNat_inj.mp h)
  have hst := checkModuleSec_ag ba st _ a (a + len) (by have := hs.hb; have := hs.hl; omega) h10
  have hbytes : rdBytes lim a len = .ok (a + len) := by unfold rdBytes; simp [hs.hb]
  sec_ok_prefix
  all_goals
    simp only [isNest, hi, beq_self_eq_true, Bool.true_and, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte, hbytes, ok_bind, beq_iff_eq]
    apply Ag.bind hst
    intro st' _
    by_cases h0 : byteAt ba pos = 0 <;>
    · simp only [h0, beq_iff_eq, ↓reduceIte]
      apply Ag.bind (ih .module st' (a + len) lim _ hl hb (by simp))
      intro is _
      exact Ag.pure _ _ _ (by simp [toItem_sec, SecB.toSec])

/-- A section of a component other than a nested unit. -/
theorem secsAg_otherC (ba : ByteArray) (f : Nat) (ih : SecsAg ba f) (st : PState)
    (pos lim len a : Nat) (max : Option Nat) (hs : SecOk ba pos lim len a)
    (hm : max = none ∨ max = some lim) (hn : ¬ isNest .component (byteAt ba pos) = true) :
    SecsAgAt ba (f + 1) .component st pos lim max := by
  have hst := checkComponentSec_ag ba st (byteAt ba pos).toNat a (a + len)
    (by have := hs.hb; have := hs.hl; omega)
  have hbytes : rdBytes lim a len = .ok (a + len) := by unfold rdBytes; simp [hs.hb]
  sec_ok_prefix
  all_goals
    simp only [hn, Bool.false_eq_true, ↓reduceIte, hbytes, ok_bind, reduceCtorEq,
      Bool.false_and]
    apply Ag.bind hst
    intro st' _
    by_cases h0 : byteAt ba pos = 0 <;>
    · simp only [h0, beq_iff_eq, ↓reduceIte]
      apply Ag.bind (ih .component st' (a + len) lim _ hl hb (by simp))
      intro is _
      exact Ag.pure _ _ _ (by simp [toItem_sec, SecB.toSec])

set_option hygiene false in
/-- `sec_ok_prefix` for the code section of a module (`hi : byteAt ba pos = 10`), up to the
order check. Not hygienic, like `sec_ok_prefix`; also uses `f`, `st` and `hi`. -/
local macro "code_prefix" : tactic => `(tactic| (
  have hn : ¬ isNest Enc.module (byteAt ba pos) = true := by simp [isNest]
  have hc : (Enc.module == Enc.module && byteAt ba pos == 10) = true := by simp [hi]
  sec_ok_prefix
  all_goals
    simp only [hn, hc, Bool.false_eq_true, ↓reduceIte]
    rw [hi]
    show Ag _ (do
      let st ← checkModuleSec st 10 (sl ba a (a + len))
      let is ← parseSecs f Enc.module st (sl ba (a + len) lim)
      pure (Item.sec ⟨10, sl ba (pos + 1) a, sl ba a (a + len)⟩ :: is)) _
    unfold checkModuleSec
    simp only [moduleOrder, show ((10 : Nat) == 0) = false from rfl,
      show ((10 : Nat) == 8) = false from rfl, show ((10 : Nat) == 12) = false from rfl,
      show ((10 : Nat) == 10) = true from rfl, Bool.false_eq_true, ↓reduceIte]))

/-- A code section out of order. -/
theorem secsAg_code_order (ba : ByteArray) (f : Nat) (st : PState) (pos lim len a : Nat)
    (max : Option Nat) (hs : SecOk ba pos lim len a) (hm : max = none ∨ max = some lim)
    (hi : byteAt ba pos = 10) (ho : 12 ≤ st.order) :
    SecsAgAt ba (f + 1) .module st pos lim max := by
  code_prefix
  all_goals simp only [ho, ↓reduceIte]; exact Ag.errs _ _ _

/-- The function count of a code section, read in the section, fails where the array read at
`lim` fails or ends past the section. -/
theorem readU32_body_err {er : FErr} (ba : ByteArray) (lim len a : Nat) (hl : lim ≤ ba.size)
    (hb : a + len ≤ lim)
    (hq : rdU32 ba lim a = .error er ∨ ∃ n p, rdU32 ba lim a = .ok (n, p) ∧ len < p - a) :
    ∃ e', readU32 (sl ba a (a + len)) = .error e' := by
  have hs := rdU32_spec ba (a + len) a (by omega)
  cases hq' : rdU32 ba (a + len) a with
  | ok v' =>
    obtain ⟨n', p'⟩ := v'
    have hup := rdU32_up ba (a + len) lim a n' p' (by omega) hq'
    rw [hq'] at hs
    rcases hq with hq | ⟨n, p, hq, hlen⟩ <;> rw [hq] at hup <;> cases hup
    omega
  | error _ => rw [hq'] at hs; exact hs

/-- A code section whose function count does not read. -/
theorem secsAg_code_count {er : FErr} (ba : ByteArray) (f : Nat) (st : PState) (pos lim len a : Nat)
    (max : Option Nat) (hs : SecOk ba pos lim len a) (hm : max = none ∨ max = some lim)
    (hi : byteAt ba pos = 10) (ho : ¬ 12 ≤ st.order)
    (hq : rdU32 ba lim a = .error er ∨ ∃ n p, rdU32 ba lim a = .ok (n, p) ∧ len < p - a) :
    SecsAgAt ba (f + 1) .module st pos lim max := by
  obtain ⟨e', he'⟩ := readU32_body_err ba lim len a hs.hl hs.hb hq
  code_prefix
  all_goals
    simp only [ho, ↓reduceIte]
    apply Ag.none
    · rcases hq with hq | ⟨n, p, hq, hlen⟩ <;>
        simp [hq, throw, throwThe, MonadExceptOf.throw, err_bind, bind, Except.bind,
          Except.toOption, *]
    · simp [he', err_bind, bind, Except.bind, Except.toOption]

/-- A code section whose function count reads. -/
theorem secsAg_code_ok (ba : ByteArray) (f : Nat) (ih : SecsAg ba f) (st : PState)
    (pos lim len a : Nat) (max : Option Nat) (hs : SecOk ba pos lim len a)
    (hm : max = none ∨ max = some lim) (hi : byteAt ba pos = 10) (ho : ¬ 12 ≤ st.order)
    (n p : Nat) (hq : rdU32 ba lim a = .ok (n, p)) (hlen : ¬ len < p - a) :
    SecsAgAt ba (f + 1) .module st pos lim max := by
  have hpb : p ≤ a + len := by have := rdU32_lt ba lim a n p hq; omega
  have hsp := rdU32_spec ba (a + len) a (by have := hs.hb; have := hs.hl; omega)
  rw [rdU32_down ba (a + len) lim a n p hq hpb] at hsp
  have hcb := codeBodies_ag ba lim (a + len) hs.hl hs.hb n p hpb
  code_prefix
  all_goals
    simp only [ho, ↓reduceIte, hq, hlen, hsp.1, ok_bind, bind_assoc, pure_bind,
      show len - (p - a) = a + len - p by omega]
    apply Ag.bind (checkFuncCode_ag _ a)
    intro _ _
    exact Ag.bind_end (a + len) hcb.1 hcb.2 (Ag.bind (ih _ _ (a + len) lim _ hl hb (by simp))
      fun is _ => Ag.pure _ _ _ (by simp [toItem_sec, SecB.toSec]))

/-- A code section. -/
theorem secsAg_code (ba : ByteArray) (f : Nat) (ih : SecsAg ba f) (st : PState)
    (pos lim len a : Nat) (max : Option Nat) (hs : SecOk ba pos lim len a)
    (hm : max = none ∨ max = some lim) (hi : byteAt ba pos = 10) :
    SecsAgAt ba (f + 1) .module st pos lim max := by
  by_cases ho : 12 ≤ st.order
  · exact secsAg_code_order ba f st pos lim len a max hs hm hi ho
  cases hq : rdU32 ba lim a with
  | error er => exact secsAg_code_count ba f st pos lim len a max hs hm hi ho (.inl hq)
  | ok v =>
    obtain ⟨n, p⟩ := v
    by_cases hlen : len < p - a
    · exact secsAg_code_count (er := ("", 0)) ba f st pos lim len a max hs hm hi ho
        (.inr ⟨n, p, hq, hlen⟩)
    · exact secsAg_code_ok ba f ih st pos lim len a max hs hm hi ho n p hq hlen

/-- A section that reads and fits, by its kind. -/
theorem secsAg_ok (ba : ByteArray) (f : Nat) (ih : SecsAg ba f) (ihu : UnitAg ba f) (enc : Enc)
    (st : PState) (pos lim len a : Nat) (max : Option Nat) (hs : SecOk ba pos lim len a)
    (hm : max = none ∨ max = some lim) : SecsAgAt ba (f + 1) enc st pos lim max := by
  by_cases hn : isNest enc (byteAt ba pos) = true
  · exact secsAg_nest ba f ih ihu enc st pos lim len a max hs hm hn
  cases enc with
  | component => exact secsAg_otherC ba f ih st pos lim len a max hs hm hn
  | module =>
    by_cases hi : byteAt ba pos = 10
    · exact secsAg_code ba f ih st pos lim len a max hs hm hi
    · exact secsAg_otherM ba f ih st pos lim len a max hs hm hi

/-- The section walks agree at fuel `f + 1` if both walks agree at `f`. -/
theorem secsAg_succ (ba : ByteArray) (f : Nat) (ih : SecsAg ba f) (ihu : UnitAg ba f) :
    SecsAg ba (f + 1) := by
  intro enc st pos lim max hl hp hm
  by_cases hend : lim ≤ pos
  · obtain rfl : pos = lim := by omega
    exact secsAg_end ba f enc st pos max hm
  have hlt : pos < lim := by omega
  by_cases hbad : (decide (pos + 4 ≤ lim) && magicAt ba pos) = true ∨
      128 ≤ (byteAt ba pos).toNat ∨ (∃ e, rdU32 ba lim (pos + 1) = .error e)
  · obtain ⟨e, he⟩ := readSec_err ba pos lim hlt hl (by rcases hbad with h | h | h <;> simp [h])
    exact secsAg_bad ba f enc st pos lim max hlt hl e he (secsHB_bad ba f enc st pos lim max hend hbad)
  simp only [not_or, not_exists, Bool.not_eq_true] at hbad
  obtain ⟨hmag', hid, hr⟩ := hbad
  obtain ⟨⟨len, a⟩, hr⟩ : ∃ v, rdU32 ba lim (pos + 1) = .ok v := by
    cases h : rdU32 ba lim (pos + 1) with
    | ok v => exact ⟨v, rfl⟩
    | error e => exact absurd h (hr e)
  by_cases hb : a + len ≤ lim
  · exact secsAg_ok ba f ih ihu enc st pos lim len a max ⟨hlt, hl, hmag', hid, hr, hb⟩ hm
  obtain ⟨e, he⟩ := readSec_err ba pos lim hlt hl (.inr (.inr (.inr ⟨len, a, hr, by omega⟩)))
  exact secsAg_bad ba f enc st pos lim max hlt hl e he
    (secsHB_large ba f enc st pos lim max hm hlt hl hmag' hid len a hr hb)

/-- The unit walks agree at fuel `f + 1` if the section walks agree at `f`. -/
theorem unitAg_succ (ba : ByteArray) (f : Nat) (ih : SecsAg ba f) : UnitAg ba (f + 1) := by
  intro ex pos lim max hl hm
  unfold parseUnitHB parseUnit
  apply Ag.bind (readHeader_sl ba ex lim pos hl)
  intro ⟨en, p⟩ hh
  have hp := readHeaderB_pos ba ex lim pos en p hh
  apply Ag.bind (ih en {} p lim max hl hp.2 hm)
  intro is _
  exact Ag.pure _ _ _ rfl

/-- Both walks agree at every fuel. -/
theorem walk_ag (ba : ByteArray) : ∀ f, SecsAg ba f ∧ UnitAg ba f
  | 0 => ⟨fun _ _ _ _ _ _ _ _ => by unfold SecsAgAt parseSecsHB parseSecs; exact Ag.errs _ _ _,
      fun _ _ _ _ _ _ => by unfold parseUnitHB parseUnit; exact Ag.errs _ _ _⟩
  | f + 1 =>
    have ih := walk_ag ba f
    ⟨secsAg_succ ba f ih.1 ih.2, unitAg_succ ba f ih.1⟩

/-- **The section walks agree.** -/
theorem secs_ag (ba : ByteArray) : ∀ (f : Nat) (enc : Enc) (st : PState) (pos lim : Nat)
    (max : Option Nat), lim ≤ ba.size → pos ≤ lim → (max = none ∨ max = some lim) →
    Ag (parseSecsHB ba noHook f enc st pos lim max) (parseSecs f enc st (sl ba pos lim))
      (List.map (ItemB.toItem ba)) :=
  fun f => (walk_ag ba f).1

/-- **The unit walks agree.** -/
theorem unit_ag (ba : ByteArray) : ∀ (f : Nat) (ex : Option Enc) (pos lim : Nat)
    (max : Option Nat), lim ≤ ba.size → (max = none ∨ max = some lim) →
    Ag (parseUnitHB ba noHook f ex pos lim max) (parseUnit f ex (sl ba pos lim))
      (fun r => (r.1, r.2.map (ItemB.toItem ba))) :=
  fun f => (walk_ag ba f).2

/-- **The array walk agrees with the list walk.** -/
theorem parseBinaryB_spec_raw (ba : ByteArray) :
    (parseBinary ba.data.toList).toOption =
      (parseBinaryB ba).toOption.map (fun r => (r.1, r.2.map (ItemB.toItem ba))) := by
  have hs : sl ba 0 ba.size = ba.data.toList := by
    rw [sl_eq, List.drop_zero, Nat.sub_zero, ← length_data, List.take_length]
  have hlen : ba.data.toList.length = ba.size := length_data ba
  have := unit_ag ba (ba.size + 2) none 0 ba.size none (Nat.le_refl _) (Or.inl rfl)
  unfold Ag at this
  rw [hs] at this
  unfold parseBinary parseBinaryB parseBinaryHB
  rw [hlen]
  exact this

end Silmaril.Proofs.Wasm.Tools.Meta

end
