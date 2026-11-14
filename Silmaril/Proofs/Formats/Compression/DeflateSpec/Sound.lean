module

public import Silmaril.Proofs.Formats.Compression.DeflateSpec.Basic

/-!
# Soundness of `Deflate.deflateTake` against `DeflateSpec`

Every decoding step of the decoder is mirrored by a derivation of the matching
`DeflateSpec` relation, under `Policy.strict`.
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.DeflateSpec

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Deflate

/-! ### Symbols -/

/-- What one decoding step means for the spec. -/
def StepOK (Cl Cd : DeflateSpec.Code) (out : List UInt8) (bs : List Bool) : SymbolStep → Prop
  | .done o r' => o = out ∧ ∃ rest, Cl.Reads bs 256 rest ∧ RR r' rest
  | .more o r' => ∃ rest, RR r' rest ∧ ∀ out' rest', DeflateSpec.Symbols Cl Cd o rest out' rest' →
      DeflateSpec.Symbols Cl Cd out bs out' rest'

theorem decodeStep_sound {lt dt : HuffmanTable} {Cl Cd : DeflateSpec.Code}
    (hl : TSound lt Cl) (hd : TSound dt Cd) {r : LSBReader} {bs : List Bool}
    {out : List UInt8} {step : SymbolStep}
    (h : decodeStep lt dt r out = .ok step) (hr : RR r bs) : StepOK Cl Cd out bs step := by
  unfold decodeStep at h
  split at h
  · cases h
  next sym r1 hs =>
  obtain ⟨rest1, hR1, hr1⟩ := hl hr hs
  by_cases h1 : sym < 256
  · rw [ite_eq_left h1] at h
    cases h
    exact ⟨rest1, hr1, fun _ _ hsyms => .literal h1 hR1 hsyms⟩
  rw [ite_eq_right h1] at h
  by_cases h2 : sym = 256
  · rw [ite_eq_left h2] at h
    cases h
    subst h2
    exact ⟨rfl, rest1, hR1, hr1⟩
  rw [ite_eq_right h2] at h
  by_cases h3 : sym ≤ 285
  · rw [ite_eq_left h3] at h
    simp only at h
    split at h
    · cases h
    next x r2 hx =>
    obtain ⟨hxlt, rest2, hrest1, hr2⟩ := hr1.readBits hx
    split at h
    · cases h
    next dsym r3 hds =>
    obtain ⟨rest3, hD, hr3⟩ := hd hr2 hds
    split at h
    · cases h
    next hd30 =>
    split at h
    · cases h
    next y r4 hy =>
    obtain ⟨hylt, rest4, hrest3, hr4⟩ := hr3.readBits hy
    split at h
    · cases h
    next hle =>
    cases h
    refine ⟨rest4, hr4, fun out' rest' hsyms => ?_⟩
    have hlc := lengthCode_eq sym
    rw [ite_eq_left ⟨by omega, h3⟩] at hlc
    have hdc := distCode_eq dsym
    rw [ite_eq_left (by omega)] at hdc
    exact .reference hR1 hlc ⟨hxlt, by rw [fieldBits_eq]; exact hrest1⟩ hD hdc
      ⟨hylt, by rw [fieldBits_eq]; exact hrest3⟩
      (by omega) (by rw [← copyBack_eq]; exact hsyms)
  · rw [ite_eq_right h3] at h
    cases h

theorem decodeSymbolsFuel_sound {lt dt : HuffmanTable} {Cl Cd : DeflateSpec.Code}
    (hl : TSound lt Cl) (hd : TSound dt Cd) : ∀ (fuel : Nat) {r r' : LSBReader}
    {bs : List Bool} {out out' : List UInt8},
    decodeSymbolsFuel lt dt fuel r out = .ok (out', r') → RR r bs →
    ∃ rest, DeflateSpec.Symbols Cl Cd out bs out' rest ∧ RR r' rest := by
  intro fuel
  induction fuel with
  | zero => intro r r' bs out out' h; cases h
  | succ n ih =>
    intro r r' bs out out' h hr
    simp only [decodeSymbolsFuel] at h
    split at h
    · cases h
    · next o r1 hstep =>
      obtain ⟨rfl, rest, hR, hr1⟩ := decodeStep_sound hl hd hstep hr
      cases h
      exact ⟨rest, .endOfBlock hR, hr1⟩
    · next o r1 hstep =>
      obtain ⟨rest1, hr1, k⟩ := decodeStep_sound hl hd hstep hr
      obtain ⟨rest, hs, hr'⟩ := ih h hr1
      exact ⟨rest, k _ _ hs, hr'⟩

/-! ### Stored blocks -/

theorem decompressStored_sound {r r' : LSBReader} {bs : List Bool} {bytes : List UInt8}
    (h : decompressStored r = .ok (bytes, r')) (hr : RR r bs) :
    ∃ pad r2 len r3 nlen r4 rest, bs = pad ++ r2 ∧ pad.length < 8 ∧ r2.length % 8 = 0 ∧
      DeflateSpec.Field 16 r2 len r3 ∧ DeflateSpec.Field 16 r3 nlen r4 ∧
      nlen = len ^^^ 0xFFFF ∧ bytes.length = len ∧ r4 = DeflateSpec.inputBits bytes ++ rest ∧
      RR r' rest := by
  unfold decompressStored at h
  obtain ⟨pad, r2, rfl, hpad, hmod, hr2⟩ := hr.alignToByte
  simp only at h
  split at h
  · cases h
  next len r3 hlen =>
  obtain ⟨hlt, rest3, rfl, hr3⟩ := hr2.readBits hlen
  split at h
  · cases h
  next nlen r4 hnlen =>
  obtain ⟨hnlt, rest4, rfl, hr4⟩ := hr3.readBits hnlen
  split at h
  · cases h
  next hx =>
  obtain ⟨data, rest, hacc, hdl, rfl, hr'⟩ := readStoredBytes_sound len h hr4
  simp only [List.nil_append] at hacc
  subst hacc
  refine ⟨pad, _, len, _, nlen, _, rest, rfl, by have := hr.2; omega, hmod, ⟨hlt, by rw [fieldBits_eq]⟩,
    ⟨hnlt, by rw [fieldBits_eq]⟩, (nlen_iff hlt hnlt).mp (by simpa using hx), hdl,
    by rw [inputBits_eq], hr'⟩

/-! ### Dynamic headers -/

/-- The code-length-code lengths the decoder has assigned after reading some values. -/
def clStep (acc : List Nat) (p : Nat × Nat) : List Nat :=
  acc.set (DeflateSpec.codeLengthOrder.getD p.2 0) p.1

theorem readCLLengths_sound : ∀ (n : Nat) {i : Nat} {acc acc' : List Nat} {r r' : LSBReader}
    {bs : List Bool}, readCLLengths n i acc r = .ok (acc', r') → RR r bs →
    ∃ vals rest, vals.length = n ∧ DeflateSpec.Fields 3 bs vals rest ∧ RR r' rest ∧
      acc' = (vals.zipIdx i).foldl clStep acc := by
  intro n
  induction n with
  | zero =>
    intro i acc acc' r r' bs h hr
    simp only [readCLLengths, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], bs, rfl, ⟨by simp, by simp⟩, hr, rfl⟩
  | succ n ih =>
    intro i acc acc' r r' bs h hr
    simp only [readCLLengths] at h
    split at h
    · cases h
    next v r1 hv =>
    obtain ⟨hvlt, rest1, rfl, hr1⟩ := hr.readBits hv
    obtain ⟨vals, rest, hlen, ⟨hall, rfl⟩, hr', rfl⟩ := ih h hr1
    refine ⟨v :: vals, rest, by simp [hlen], ⟨?_, ?_⟩, hr', rfl⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hvlt
      · exact hall x hx
    · simp [fieldBits_eq]

theorem clLengths_eq (vals : List Nat) :
    DeflateSpec.clLengths vals = (vals.zipIdx 0).foldl clStep (List.replicate 19 0) := rfl

theorem readCodeLengths_sound {clTable : HuffmanTable} {C : DeflateSpec.Code} {total : Nat}
    (hc : TSound clTable C) : ∀ (fuel : Nat) {acc lens : List Nat} {r r' : LSBReader}
    {bs : List Bool}, readCodeLengths clTable total fuel acc r = .ok (lens, r') → RR r bs →
    ∃ rest, DeflateSpec.LengthRuns C acc bs lens rest ∧ RR r' rest ∧ lens.length = total := by
  intro fuel
  induction fuel with
  | zero =>
    intro acc lens r r' bs h hr
    simp only [readCodeLengths] at h
    split at h
    · next he =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨bs, .done, hr, he⟩
    · cases h
  | succ n ih =>
    intro acc lens r r' bs h hr
    simp only [readCodeLengths] at h
    split at h
    · split at h
      · next he =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨bs, .done, hr, he⟩
      · cases h
    split at h
    · cases h
    next sym r1 hs =>
    obtain ⟨rest1, hR1, hr1⟩ := hc hr hs
    split at h
    · next h16 =>
      obtain ⟨rest, hruns, hr', hl⟩ := ih h hr1
      exact ⟨rest, .length h16 hR1 hruns, hr', hl⟩
    split at h
    · next h16 =>
      subst h16
      split at h
      · cases h
      next prev hprev =>
      split at h
      · cases h
      next e r2 he =>
      obtain ⟨helt, rest2, rfl, hr2⟩ := hr1.readBits he
      obtain ⟨rest, hruns, hr', hl⟩ := ih h hr2
      exact ⟨rest, .copyPrevious hR1 ⟨helt, by rw [fieldBits_eq]⟩ hprev hruns, hr', hl⟩
    split at h
    · next h17 =>
      subst h17
      split at h
      · cases h
      next e r2 he =>
      obtain ⟨helt, rest2, rfl, hr2⟩ := hr1.readBits he
      obtain ⟨rest, hruns, hr', hl⟩ := ih h hr2
      exact ⟨rest, .zeros hR1 ⟨helt, by rw [fieldBits_eq]⟩ hruns, hr', hl⟩
    split at h
    · next h18 =>
      subst h18
      split at h
      · cases h
      next e r2 he =>
      obtain ⟨helt, rest2, rfl, hr2⟩ := hr1.readBits he
      obtain ⟨rest, hruns, hr', hl⟩ := ih h hr2
      exact ⟨rest, .longZeros hR1 ⟨helt, by rw [fieldBits_eq]⟩ hruns, hr', hl⟩
    · cases h

theorem kraft_eq_kraftTotal (M : Nat) (L : List Nat) : DeflateSpec.kraft M L = kraftTotal L M :=
  rfl

theorem complete_of_isCompleteCode {L : List Nat} {M : Nat} (h : isCompleteCode L M = true) :
    DeflateSpec.Complete M L := by
  simp only [isCompleteCode, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  rw [kraftSum, kraft_foldl, Nat.zero_add, Nat.shiftLeft_eq, Nat.one_mul] at h2
  rw [kraft_eq_kraftTotal, h2]

theorem kraft_of_le_one (M : Nat) : ∀ {L : List Nat}, (∀ l ∈ L, l ≤ 1) →
    DeflateSpec.kraft M L = L.count 1 * 2 ^ (M - 1)
  | [], _ => by simp [DeflateSpec.kraft]
  | x :: L, h => by
    have hx := h x List.mem_cons_self
    have ih := kraft_of_le_one M (L := L) (fun l hl => h l (List.mem_cons_of_mem _ hl))
    simp only [DeflateSpec.kraft, List.map_cons, List.sum_cons, List.count_cons,
      beq_iff_eq] at ih ⊢
    rw [ih]
    rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;> simp [Nat.add_mul] <;> omega

theorem strict_codeOK_of_valid {L : List Nat} (hv : validCodeLengths L 15 = true)
    (hk : isValidLengths L 15 = true) : DeflateSpec.Policy.strict.codeOK L := by
  simp only [validCodeLengths, Bool.or_eq_true] at hv
  rcases hv with hc | hs
  · exact Or.inl (complete_of_isCompleteCode hc)
  · simp only [List.all_eq_true, decide_eq_true_eq] at hs
    have hk' : kraftTotal L 15 ≤ 2 ^ 15 := by
      have := kraftTotal_le L 15 hk; exact this
    rw [← kraft_eq_kraftTotal, kraft_of_le_one 15 hs] at hk'
    by_cases h2 : L.count 1 ≤ 1
    · exact Or.inr ⟨hs, h2⟩
    · refine Or.inl ⟨fun l hl => by have := hs l hl; omega, ?_⟩
      rw [kraft_of_le_one 15 hs]
      have : L.count 1 = 2 := by simp at hk'; omega
      rw [this]

theorem readDynamicTables_sound {r r' : LSBReader} {bs : List Bool} {lt dt : HuffmanTable}
    (h : readDynamicTables r = .ok (lt, dt, r')) (hr : RR r bs) :
    ∃ lit dist rest, DeflateSpec.DynamicHeader .strict bs lit dist rest ∧ RR r' rest ∧
      TSound lt lit ∧ TSound dt dist := by
  unfold readDynamicTables at h
  split at h
  · cases h
  next hlit r1 hhlit =>
  obtain ⟨hlitlt, rest1, rfl, hr1⟩ := hr.readBits hhlit
  split at h
  · cases h
  next hdist r2 hhdist =>
  obtain ⟨hdistlt, rest2, rfl, hr2⟩ := hr1.readBits hhdist
  split at h
  · cases h
  next hclen r3 hhclen =>
  obtain ⟨hclenlt, rest3, rfl, hr3⟩ := hr2.readBits hhclen
  simp only at h
  split at h
  · cases h
  next hrange =>
  split at h
  · cases h
  next clLens r4 hcl =>
  obtain ⟨vals, rest4, hvlen, hfields, hr4, hclLens⟩ := readCLLengths_sound _ hcl hr3
  rw [← clLengths_eq] at hclLens
  subst hclLens
  split at h
  · cases h
  next hcomplete =>
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hcomplete
  split at h
  · cases h
  next clTable hclTable =>
  split at h
  · cases h
  next lens r5 hlens =>
  obtain ⟨rest5, hruns, hr5, hlenslen⟩ :=
    readCodeLengths_sound (tSound_ofLengths hclTable) _ hlens hr4
  split at h
  · cases h
  next h256 =>
  split at h
  · cases h
  next hvlit =>
  split at h
  · cases h
  next hvdist =>
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hvlit hvdist
  split at h
  · next lt' dt' hlt hdt =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨_, _, rest5, ?_, hr5, tSound_ofLengths hlt, tSound_ofLengths hdt⟩
    exact .mk ⟨hlitlt, by rw [fieldBits_eq]⟩ (by omega) ⟨hdistlt, by rw [fieldBits_eq]⟩
      (by show _ ≤ 30; omega) ⟨hclenlt, by rw [fieldBits_eq]⟩ hfields (by omega)
      (complete_of_isCompleteCode hcomplete) hruns (by omega)
      (strict_codeOK_of_valid hvlit (ofLengths_entries hlt).2.1)
      (strict_codeOK_of_valid hvdist (ofLengths_entries hdt).2.1)
  · cases h

/-! ### Blocks -/

theorem decompressBlockBody_sound {btype : Nat} {r r' : LSBReader} {bs : List Bool}
    {out out' : List UInt8} (hb : btype < 2 ^ 2)
    (h : decompressBlockBody btype r out = .ok (out', r')) (hr : RR r bs) :
    ∃ rest, DeflateSpec.Block .strict out (natBits btype 2 ++ bs) out' rest ∧ RR r' rest := by
  have hf : DeflateSpec.Field 2 (natBits btype 2 ++ bs) btype bs := ⟨hb, by rw [fieldBits_eq]⟩
  unfold decompressBlockBody at h
  split at h
  · next h0 =>
    subst h0
    split at h
    · cases h
    next bytes r1 hs =>
    cases h
    obtain ⟨pad, r2, len, r3, nlen, r4, rest, rfl, hpad, hmod, hlen, hnlen, hx, hdl, rfl, hr'⟩ :=
      decompressStored_sound hs hr
    exact ⟨rest, .stored hf rfl hpad hmod hlen hnlen hx hdl rfl, hr'⟩
  split at h
  · next h1 =>
    subst h1
    obtain ⟨lt, dt, hlt, hdt, hls, _, hds, _⟩ := fixed_tables
    rw [hlt, hdt] at h
    obtain ⟨rest, hs, hr'⟩ := decodeSymbolsFuel_sound hls hds _ h hr
    exact ⟨rest, .fixed hf hs, hr'⟩
  split at h
  · next h2 =>
    subst h2
    split at h
    · cases h
    next lt dt r1 hdyn =>
    obtain ⟨lit, dist, rest1, hdh, hr1, hls, hds⟩ := readDynamicTables_sound hdyn hr
    obtain ⟨rest, hs, hr'⟩ := decodeSymbolsFuel_sound hls hds _ h hr1
    exact ⟨rest, .dynamic hf hdh hs, hr'⟩
  · cases h

theorem decompressBlocks_sound : ∀ (fuel : Nat) {r r' : LSBReader} {bs : List Bool}
    {out out' : List UInt8}, decompressBlocks fuel r out = .ok (out', r') → RR r bs →
    ∃ rest, DeflateSpec.Blocks .strict out bs out' rest ∧ RR r' rest := by
  intro fuel
  induction fuel with
  | zero => intro r r' bs out out' h; cases h
  | succ n ih =>
    intro r r' bs out out' h hr
    simp only [decompressBlocks] at h
    split at h
    · cases h
    next bfinal r1 hbit =>
    obtain ⟨bs1, rfl, hr1⟩ := hr.readBit hbit
    split at h
    · cases h
    next btype r2 hbt =>
    obtain ⟨hblt, bs2, rfl, hr2⟩ := hr1.readBits hbt
    split at h
    · cases h
    next out1 r3 hbody =>
    obtain ⟨rest1, hblock, hr3⟩ := decompressBlockBody_sound hblt hbody hr2
    cases bfinal
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨rest, hbl, hr'⟩ := ih h hr3
      exact ⟨rest, .notLast hblock hbl, hr'⟩
    · simp only [↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rest1, .last hblock, hr3⟩

theorem deflateTake_sound {input out rest : List UInt8}
    (h : deflateTake input = .ok (out, rest)) : DeflateSpec.Stream .strict input out rest := by
  unfold deflateTake at h
  dsimp only at h
  split at h
  · cases h
  next out' r' hblocks =>
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨bits, hbl, hr'⟩ := decompressBlocks_sound _ hblocks (RR.init input)
  obtain ⟨pad, hpad, rfl⟩ := hr'.pad
  exact ⟨pad, hpad, by rw [inputBits_eq, inputBits_eq]; exact hbl⟩

end Silmaril.Proofs.Formats.Compression.DeflateSpec
