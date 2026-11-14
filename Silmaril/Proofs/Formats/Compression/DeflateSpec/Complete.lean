module

public import Silmaril.Proofs.Formats.Compression.DeflateSpec.Sound

/-!
# Completeness of `Deflate.deflateTake` against `DeflateSpec`

Every derivation of a `DeflateSpec` relation under `Policy.strict` is followed
by the decoder, with enough fuel.
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.DeflateSpec

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Deflate

/-- Every codeword of `C` is nonempty. -/
def NonEmpty (C : DeflateSpec.Code) : Prop := ∀ {s w}, C s = some w → w ≠ []

theorem length_codeBits (c n : Nat) : (DeflateSpec.codeBits c n).length = n := by
  rw [codeBits_eq, length_msbBits]

theorem nonEmpty_ofLengths (L : List Nat) : NonEmpty (DeflateSpec.Code.ofLengths L) := by
  intro s w h hw
  obtain ⟨_, h0, rfl⟩ := ofLengths_eq_some h
  have := congrArg List.length hw
  rw [length_codeBits] at this
  exact h0 (by simpa using this)

theorem nonEmpty_fixedDist : NonEmpty DeflateSpec.fixedDistCode := by
  rw [fixedDistCode_eq]; exact nonEmpty_ofLengths _

/-! ### Lengths: every relation consumes a prefix -/

theorem reads_length {C : DeflateSpec.Code} {bs rest : List Bool} {s : Nat}
    (h : C.Reads bs s rest) : rest.length ≤ bs.length := by
  obtain ⟨w, _, rfl⟩ := h; simp

theorem reads_length_lt {C : DeflateSpec.Code} (hne : NonEmpty C) {bs rest : List Bool}
    {s : Nat} (h : C.Reads bs s rest) : rest.length < bs.length := by
  obtain ⟨w, hw, rfl⟩ := h
  have := hne hw
  have : 0 < w.length := List.length_pos_iff.mpr this
  simp; omega

theorem field_length {n v : Nat} {bs rest : List Bool} (h : DeflateSpec.Field n bs v rest) :
    rest.length ≤ bs.length := by
  obtain ⟨_, rfl⟩ := h; simp

theorem symbols_length {Cl Cd : DeflateSpec.Code} {out out' : List UInt8} {bs rest : List Bool}
    (h : DeflateSpec.Symbols Cl Cd out bs out' rest) : rest.length ≤ bs.length := by
  induction h with
  | endOfBlock h => exact reads_length h
  | literal _ h _ ih => have := reads_length h; omega
  | reference h1 _ h2 h3 _ h4 _ _ ih =>
    have := reads_length h1; have := field_length h2; have := reads_length h3
    have := field_length h4; omega

theorem runs_length {C : DeflateSpec.Code} {acc lens : List Nat} {bs rest : List Bool}
    (h : DeflateSpec.LengthRuns C acc bs lens rest) :
    rest.length ≤ bs.length ∧ acc.length ≤ lens.length := by
  induction h with
  | done => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | length _ h _ ih => have := reads_length h; simp at ih; omega
  | copyPrevious h1 h2 _ _ ih =>
    have := reads_length h1; have := field_length h2; simp at ih; omega
  | zeros h1 h2 _ ih => have := reads_length h1; have := field_length h2; simp at ih; omega
  | longZeros h1 h2 _ ih =>
    have := reads_length h1; have := field_length h2; simp at ih; omega

theorem runs_lt16 {C : DeflateSpec.Code} {acc lens : List Nat} {bs rest : List Bool}
    (h : DeflateSpec.LengthRuns C acc bs lens rest) : (∀ l ∈ acc, l < 16) → ∀ l ∈ lens, l < 16 := by
  induction h with
  | done => exact id
  | length hl _ _ ih =>
    intro ha; apply ih; intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ha x hx
    · exact hl
  | copyPrevious _ _ hp _ ih =>
    intro ha; apply ih; intro x hx
    simp only [List.mem_append, List.mem_replicate] at hx
    rcases hx with hx | ⟨_, rfl⟩
    · exact ha x hx
    · exact ha _ (List.mem_of_getLast? hp)
  | zeros _ _ _ ih =>
    intro ha; apply ih; intro x hx
    simp only [List.mem_append, List.mem_replicate] at hx
    rcases hx with hx | ⟨_, rfl⟩
    · exact ha x hx
    · omega
  | longZeros _ _ _ ih =>
    intro ha; apply ih; intro x hx
    simp only [List.mem_append, List.mem_replicate] at hx
    rcases hx with hx | ⟨_, rfl⟩
    · exact ha x hx
    · omega

theorem dynamicHeader_length {p : DeflateSpec.Policy} {bs rest : List Bool}
    {lit dist : DeflateSpec.Code} (h : DeflateSpec.DynamicHeader p bs lit dist rest) :
    rest.length ≤ bs.length := by
  cases h with
  | mk h1 _ h2 _ h3 hf _ _ hr _ _ _ =>
    have := field_length h1; have := field_length h2; have := field_length h3
    have := (runs_length hr).1
    obtain ⟨_, rfl⟩ := hf
    simp at *; omega

theorem block_length {p : DeflateSpec.Policy} {out out' : List UInt8} {bs rest : List Bool}
    (h : DeflateSpec.Block p out bs out' rest) : rest.length ≤ bs.length := by
  cases h with
  | stored h1 hp _ _ h2 h3 _ _ h4 =>
    have := field_length h1; have := field_length h2; have := field_length h3
    subst hp h4; simp at *; omega
  | fixed h1 h2 => have := field_length h1; have := symbols_length h2; omega
  | dynamic h1 h2 h3 =>
    have := field_length h1; have := dynamicHeader_length h2; have := symbols_length h3; omega

/-! ### Symbols -/

/-- A block's data ends with the end-of-block symbol, so it has a code. -/
theorem symbols_endOfBlock_isSome {Cl Cd : DeflateSpec.Code} {out out' : List UInt8}
    {bs rest : List Bool} (h : DeflateSpec.Symbols Cl Cd out bs out' rest) : (Cl 256).isSome := by
  induction h with
  | endOfBlock h => obtain ⟨w, hw, _⟩ := h; simp [hw]
  | literal _ _ _ ih => exact ih
  | reference _ _ _ _ _ _ _ _ ih => exact ih

theorem decodeSymbolsFuel_complete {lt dt : HuffmanTable} {Cl Cd : DeflateSpec.Code}
    (hl : TComplete lt Cl) (hd : TComplete dt Cd) (hne : NonEmpty Cl)
    {out out' : List UInt8} {bs rest : List Bool}
    (h : DeflateSpec.Symbols Cl Cd out bs out' rest) :
    ∀ (fuel : Nat) {r : LSBReader}, RR r bs → bs.length < rest.length + fuel →
      ∃ r', decodeSymbolsFuel lt dt fuel r out = .ok (out', r') ∧ RR r' rest := by
  induction h with
  | @endOfBlock out bs rest hR =>
    intro fuel r hr hf
    obtain ⟨w, hw, rfl⟩ := hR
    obtain ⟨r', h1, hr'⟩ := hl hw hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by
      have := hne hw; have := List.length_pos_iff.mpr this; simp at hf; omega⟩
    refine ⟨r', ?_, hr'⟩
    simp [decodeSymbolsFuel, decodeStep, h1]
  | @literal out bs r1 out' rest v hv hR hsub ih =>
    intro fuel r hr hf
    have := symbols_length hsub
    have hlt := reads_length_lt hne hR
    obtain ⟨w, hw, rfl⟩ := hR
    obtain ⟨r1', h1, hr1⟩ := hl hw hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨r', h2, hr'⟩ := ih f hr1 (by omega)
    refine ⟨r', ?_, hr'⟩
    simp only [decodeSymbolsFuel, decodeStep, h1, hv, ↓reduceIte]
    exact h2
  | @reference out bs out' rest sym r1 lenExtra lenBase x r2 dsym r3 distExtra distBase y r4
      hR hlc hx hD hdc hy hle hsub ih =>
    intro fuel r hr hf
    have := symbols_length hsub
    have hlt := reads_length_lt hne hR
    have := field_length hx; have := reads_length hD; have := field_length hy
    obtain ⟨w, hw, rfl⟩ := hR
    obtain ⟨r1', h1, hr1⟩ := hl hw hr
    obtain ⟨hxlt, rfl⟩ := hx
    obtain ⟨r2', h2, hr2⟩ := RR.readBits_of hxlt (by rw [← fieldBits_eq]; exact hr1)
    obtain ⟨w', hw', rfl⟩ := hD
    obtain ⟨r3', h3, hr3⟩ := hd hw' hr2
    obtain ⟨hylt, rfl⟩ := hy
    obtain ⟨r4', h4, hr4⟩ := RR.readBits_of hylt (by rw [← fieldBits_eq]; exact hr3)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨r', h5, hr'⟩ := ih f hr4 (by simp at *; omega)
    refine ⟨r', ?_, hr'⟩
    have hl2 := lengthCode_eq sym
    rw [hlc] at hl2
    split at hl2
    · next hs =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hl2
      obtain ⟨hE, hB⟩ := hl2
      have hd2 := distCode_eq dsym
      rw [hdc] at hd2
      split at hd2
      · next hds =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hd2
        obtain ⟨hDE, hDB⟩ := hd2
        have hn1 : ¬ sym < 256 := by omega
        have hn2 : ¬ sym = 256 := by omega
        have hn3 : ¬ 30 ≤ dsym := by omega
        have hn4 : ¬ distBase + y > out.length := by omega
        simp only [decodeSymbolsFuel, decodeStep, h1, hn1, hn2, hs.2, ← hE, ← hB, h2, h3, hn3,
          ← hDE, ← hDB, h4, hn4, ↓reduceIte, copyBack_eq]
        exact h5
      · cases hd2
    · cases hl2

theorem decodeSymbol_complete {lt dt : HuffmanTable} {Cl Cd : DeflateSpec.Code}
    (hl : TComplete lt Cl) (hd : TComplete dt Cd) (hne : NonEmpty Cl)
    {out out' : List UInt8} {bs rest : List Bool} {r : LSBReader}
    (h : DeflateSpec.Symbols Cl Cd out bs out' rest) (hr : RR r bs) :
    ∃ r', decodeSymbol lt dt r out = .ok (out', r') ∧ RR r' rest := by
  unfold decodeSymbol
  rw [hr.1.bitsLeft]
  exact decodeSymbolsFuel_complete hl hd hne h _ hr (by omega)

/-! ### Dynamic headers -/

theorem readCLLengths_complete : ∀ (vals : List Nat) {i : Nat} {acc : List Nat} {r : LSBReader}
    {bs rest : List Bool}, DeflateSpec.Fields 3 bs vals rest → RR r bs →
    ∃ r', readCLLengths vals.length i acc r = .ok ((vals.zipIdx i).foldl clStep acc, r') ∧
      RR r' rest := by
  intro vals
  induction vals with
  | nil =>
    intro i acc r bs rest hf hr
    obtain ⟨_, rfl⟩ := hf
    exact ⟨r, rfl, by simpa using hr⟩
  | cons v vals ih =>
    intro i acc r bs rest hf hr
    obtain ⟨hall, rfl⟩ := hf
    simp only [List.map_cons, List.flatten_cons, List.append_assoc] at hr
    obtain ⟨r1, h1, hr1⟩ := RR.readBits_of (hall v List.mem_cons_self)
      (by rw [← fieldBits_eq]; exact hr)
    obtain ⟨r', h2, hr'⟩ := ih (i := i + 1) (acc := clStep acc (v, i))
      ⟨fun x hx => hall x (List.mem_cons_of_mem _ hx), rfl⟩ hr1
    refine ⟨r', ?_, hr'⟩
    simp only [List.length_cons, readCLLengths, h1, List.zipIdx_cons, List.foldl_cons]
    exact h2

theorem readCodeLengths_complete {clTable : HuffmanTable} {C : DeflateSpec.Code} {total : Nat}
    (hc : TComplete clTable C) {acc lens : List Nat} {bs rest : List Bool}
    (h : DeflateSpec.LengthRuns C acc bs lens rest) (ht : lens.length = total) :
    ∀ (fuel : Nat) {r : LSBReader}, RR r bs → lens.length < acc.length + fuel →
      ∃ r', readCodeLengths clTable total fuel acc r = .ok (lens, r') ∧ RR r' rest := by
  induction h with
  | done =>
    intro fuel r hr hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    exact ⟨r, by simp [readCodeLengths, ht], hr⟩
  | @length acc bs r1 lens rest len hl hR hruns ih =>
    intro fuel r hr hf
    have := (runs_length hruns).2
    simp only [List.length_append, List.length_singleton] at this
    obtain ⟨w, hw, rfl⟩ := hR
    obtain ⟨r1', h1, hr1⟩ := hc hw hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨r', h2, hr'⟩ := ih ht f hr1 (by simp; omega)
    refine ⟨r', ?_, hr'⟩
    have hn : ¬ total ≤ acc.length := by omega
    simp only [readCodeLengths, hn, h1, hl, ↓reduceIte]
    exact h2
  | @copyPrevious acc bs r1 e r2 lens rest prev hR he hp hruns ih =>
    intro fuel r hr hf
    have := (runs_length hruns).2
    simp only [List.length_append, List.length_replicate] at this
    obtain ⟨w, hw, rfl⟩ := hR
    obtain ⟨r1', h1, hr1⟩ := hc hw hr
    obtain ⟨helt, rfl⟩ := he
    obtain ⟨r2', h2, hr2⟩ := RR.readBits_of helt (by rw [← fieldBits_eq]; exact hr1)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨r', h3, hr'⟩ := ih ht f hr2 (by simp; omega)
    refine ⟨r', ?_, hr'⟩
    have hn : ¬ total ≤ acc.length := by omega
    simp only [readCodeLengths, hn, h1, hp, h2, ↓reduceIte]
    exact h3
  | @zeros acc bs r1 e r2 lens rest hR he hruns ih =>
    intro fuel r hr hf
    have := (runs_length hruns).2
    simp only [List.length_append, List.length_replicate] at this
    obtain ⟨w, hw, rfl⟩ := hR
    obtain ⟨r1', h1, hr1⟩ := hc hw hr
    obtain ⟨helt, rfl⟩ := he
    obtain ⟨r2', h2, hr2⟩ := RR.readBits_of helt (by rw [← fieldBits_eq]; exact hr1)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨r', h3, hr'⟩ := ih ht f hr2 (by simp; omega)
    refine ⟨r', ?_, hr'⟩
    have hn : ¬ total ≤ acc.length := by omega
    simp only [readCodeLengths, hn, h1, h2, ↓reduceIte]
    exact h3
  | @longZeros acc bs r1 e r2 lens rest hR he hruns ih =>
    intro fuel r hr hf
    have := (runs_length hruns).2
    simp only [List.length_append, List.length_replicate] at this
    obtain ⟨w, hw, rfl⟩ := hR
    obtain ⟨r1', h1, hr1⟩ := hc hw hr
    obtain ⟨helt, rfl⟩ := he
    obtain ⟨r2', h2, hr2⟩ := RR.readBits_of helt (by rw [← fieldBits_eq]; exact hr1)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨r', h3, hr'⟩ := ih ht f hr2 (by simp; omega)
    refine ⟨r', ?_, hr'⟩
    have hn : ¬ total ≤ acc.length := by omega
    simp only [readCodeLengths, hn, h1, h2, ↓reduceIte]
    exact h3

theorem isCompleteCode_of_complete {L : List Nat} {M : Nat} (h : DeflateSpec.Complete M L) :
    isCompleteCode L M = true := by
  simp only [isCompleteCode, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨h.1, ?_⟩
  rw [kraftSum, kraft_foldl, Nat.zero_add, Nat.shiftLeft_eq, Nat.one_mul, ← kraft_eq_kraftTotal]
  exact h.2

theorem isValidLengths_of_complete {L : List Nat} {M : Nat} (h : DeflateSpec.Complete M L) :
    isValidLengths L M = true :=
  isValidLengths_of_kraftTotal L M h.1 (by rw [← kraft_eq_kraftTotal, h.2]; exact Nat.le_refl _)

theorem valid_of_strict_codeOK {L : List Nat} (hb : ∀ l ∈ L, l ≤ 15)
    (h : DeflateSpec.Policy.strict.codeOK L) :
    isValidLengths L 15 = true ∧ validCodeLengths L 15 = true := by
  rcases h with hc | ⟨hs, h1⟩
  · exact ⟨isValidLengths_of_complete hc, by simp [validCodeLengths, isCompleteCode_of_complete hc]⟩
  · refine ⟨isValidLengths_of_kraftTotal L 15 hb ?_, ?_⟩
    · rw [← kraft_eq_kraftTotal, kraft_of_le_one 15 hs]
      have : L.count 1 * 2 ^ (15 - 1) ≤ 1 * 2 ^ 14 := Nat.mul_le_mul_right _ h1
      omega
    · simp only [validCodeLengths, Bool.or_eq_true, List.all_eq_true, decide_eq_true_eq]
      exact Or.inr hs

theorem ofLengths_isSome {L : List Nat} {M : Nat} (h : isValidLengths L M = true) :
    ∃ t, HuffmanTable.ofLengths L M = some t :=
  ⟨_, by simp [HuffmanTable.ofLengths, h]; rfl⟩

theorem readDynamicTables_complete' {bs r1 r2 r3 r4 rest : List Bool} {hlit hdist hclen : Nat}
    {vals lens : List Nat} {r : LSBReader}
    (hlitF : DeflateSpec.Field 5 bs hlit r1) (hlitR : hlit + 257 ≤ 286)
    (hdistF : DeflateSpec.Field 5 r1 hdist r2) (hdistR : hdist + 1 ≤ 30)
    (hclenF : DeflateSpec.Field 4 r2 hclen r3) (hfields : DeflateSpec.Fields 3 r3 vals r4)
    (hclc : vals.length = hclen + 4) (hclOK : DeflateSpec.Complete 7 (DeflateSpec.clLengths vals))
    (hruns : DeflateSpec.LengthRuns (DeflateSpec.Code.ofLengths (DeflateSpec.clLengths vals))
      [] r4 lens rest)
    (hcount : lens.length = hlit + 257 + (hdist + 1))
    (hlitOK : DeflateSpec.Policy.strict.codeOK (lens.take (hlit + 257)))
    (hdistOK : DeflateSpec.Policy.strict.codeOK (lens.drop (hlit + 257)))
    (hr : RR r bs) (h256 : (DeflateSpec.Code.ofLengths (lens.take (hlit + 257)) 256).isSome) :
    ∃ lt dt r', readDynamicTables r = .ok (lt, dt, r') ∧ RR r' rest ∧
      TComplete lt (DeflateSpec.Code.ofLengths (lens.take (hlit + 257))) ∧
      TComplete dt (DeflateSpec.Code.ofLengths (lens.drop (hlit + 257))) := by
  obtain ⟨hlitlt, rfl⟩ := hlitF
  obtain ⟨hdistlt, rfl⟩ := hdistF
  obtain ⟨hclenlt, rfl⟩ := hclenF
  obtain ⟨r1', h1, hr1⟩ := RR.readBits_of hlitlt (by rw [← fieldBits_eq]; exact hr)
  obtain ⟨r2', h2, hr2⟩ := RR.readBits_of hdistlt (by rw [← fieldBits_eq]; exact hr1)
  obtain ⟨r3', h3, hr3⟩ := RR.readBits_of hclenlt (by rw [← fieldBits_eq]; exact hr2)
  obtain ⟨r4', h4, hr4⟩ := readCLLengths_complete vals (i := 0)
    (acc := List.replicate 19 0) hfields hr3
  rw [← clLengths_eq, hclc] at h4
  have hcomplete := isCompleteCode_of_complete hclOK
  obtain ⟨clTable, hclTable⟩ := ofLengths_isSome (isValidLengths_of_complete hclOK)
  obtain ⟨r5', h5, hr5⟩ := readCodeLengths_complete (tComplete_ofLengths hclTable) hruns hcount
    (hlit + 257 + (hdist + 1) + 1) hr4 (by simp [hcount])
  have hlt16 := runs_lt16 hruns (by simp)
  have hb : ∀ L, (L = lens.take (hlit + 257) ∨ L = lens.drop (hlit + 257)) → ∀ l ∈ L, l ≤ 15 := by
    intro L hL l hl
    rcases hL with rfl | rfl
    · have := hlt16 l (List.mem_of_mem_take hl); omega
    · have := hlt16 l (List.mem_of_mem_drop hl); omega
  obtain ⟨hvl, hcl⟩ := valid_of_strict_codeOK (hb _ (Or.inl rfl)) hlitOK
  obtain ⟨hvd, hcd⟩ := valid_of_strict_codeOK (hb _ (Or.inr rfl)) hdistOK
  obtain ⟨lt, hlt⟩ := ofLengths_isSome hvl
  obtain ⟨dt, hdt⟩ := ofLengths_isSome hvd
  have h256' : (lens.take (hlit + 257)).getD 256 0 ≠ 0 := by
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h256
    obtain ⟨hs, h0, _⟩ := ofLengths_eq_some hw
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs] using h0
  refine ⟨lt, dt, r5', ?_, hr5, tComplete_ofLengths hlt, tComplete_ofLengths hdt⟩
  have hn : ¬ (286 < hlit + 257 ∨ 30 < hdist + 1) := by omega
  simp only [readDynamicTables, h1, h2, h3, hn, h4, hcomplete, hclTable, h5, h256', hcl, hcd,
    hlt, hdt, ↓reduceIte, Bool.not_true, Bool.false_eq_true]

theorem readDynamicTables_complete {bs rest : List Bool} {lit dist : DeflateSpec.Code}
    {r : LSBReader} (h : DeflateSpec.DynamicHeader .strict bs lit dist rest) (hr : RR r bs)
    (h256 : (lit 256).isSome) :
    ∃ lt dt r', readDynamicTables r = .ok (lt, dt, r') ∧ RR r' rest ∧
      TComplete lt lit ∧ TComplete dt dist ∧ NonEmpty lit := by
  cases h with
  | mk hlitF hlitR hdistF hdistR hclenF hfields hclc hclOK hruns hcount hlitOK hdistOK =>
    obtain ⟨lt, dt, r', h1, h2, h3, h4⟩ := readDynamicTables_complete' hlitF hlitR hdistF hdistR
      hclenF hfields hclc hclOK hruns hcount hlitOK hdistOK hr h256
    exact ⟨lt, dt, r', h1, h2, h3, h4, nonEmpty_ofLengths _⟩

/-! ### Blocks -/

theorem stored_complete {out data : List UInt8} {bs r1 pad r2 r3 r4 rest : List Bool}
    {len nlen : Nat} {r : LSBReader}
    (hf : DeflateSpec.Field 2 bs 0 r1) (hp : r1 = pad ++ r2) (hpad : pad.length < 8)
    (hmod : r2.length % 8 = 0) (hlen : DeflateSpec.Field 16 r2 len r3)
    (hnlen : DeflateSpec.Field 16 r3 nlen r4) (hx : nlen = len ^^^ 0xFFFF)
    (hdl : data.length = len) (h4 : r4 = DeflateSpec.inputBits data ++ rest) (hr : RR r bs) :
    ∃ btype r1 r', r.readBits 2 = some (btype, r1) ∧
      decompressBlockBody btype r1 out = .ok (out ++ data, r') ∧ RR r' rest := by
  obtain ⟨_, rfl⟩ := hf
  obtain ⟨r1', h1, hr1⟩ := RR.readBits_of (n := 2) (v := 0) (by decide)
    (by rw [← fieldBits_eq]; exact hr)
  refine ⟨0, r1', ?_⟩
  obtain ⟨pad', r2', hsplit, hpl, hmod', hra⟩ := hr1.alignToByte
  rw [hp] at hsplit
  have hl := congrArg List.length hsplit
  simp only [List.length_append] at hl
  have hpl' : pad.length = pad'.length := by have := hr1.2; omega
  obtain ⟨rfl, rfl⟩ := List.append_inj hsplit hpl'
  obtain ⟨hlt, rfl⟩ := hlen
  obtain ⟨hnlt, rfl⟩ := hnlen
  subst h4
  rw [fieldBits_eq, fieldBits_eq, inputBits_eq] at hra
  obtain ⟨ra, ha, hra'⟩ := RR.readBits_of hlt hra
  obtain ⟨rb, hb, hrb⟩ := RR.readBits_of hnlt hra'
  obtain ⟨r', hs, hr'⟩ := readStoredBytes_complete data (acc := []) hrb
  have hxor : (len ^^^ nlen) % 65536 = 65535 := (nlen_iff hlt hnlt).mpr hx
  refine ⟨r', h1, ?_, hr'⟩
  rw [hdl] at hs
  simp only [decompressBlockBody, decompressStored, ha, hb, hxor, ne_eq, not_true_eq_false, hs,
    ↓reduceIte, List.nil_append]

theorem decompressBlockBody_complete {out out' : List UInt8} {bs rest : List Bool}
    {r : LSBReader} (h : DeflateSpec.Block .strict out bs out' rest) (hr : RR r bs) :
    ∃ btype r1 r', r.readBits 2 = some (btype, r1) ∧
      decompressBlockBody btype r1 out = .ok (out', r') ∧ RR r' rest := by
  cases h with
  | stored hf hp hpad hmod hlen hnlen hx hdl h4 =>
    exact stored_complete hf hp hpad hmod hlen hnlen hx hdl h4 hr
  | fixed hf hs =>
    obtain ⟨_, rfl⟩ := hf
    obtain ⟨r1', h1, hr1⟩ := RR.readBits_of (n := 2) (v := 1) (by decide) (by rw [← fieldBits_eq]; exact hr)
    obtain ⟨lt, dt, hlt, hdt, _, hlc, _, hdc⟩ := fixed_tables
    obtain ⟨r', h2, hr'⟩ := decodeSymbol_complete hlc hdc
      (by rw [DeflateSpec.fixedLitLenCode]; exact nonEmpty_ofLengths _) hs hr1
    refine ⟨1, r1', r', h1, ?_, hr'⟩
    simp only [decompressBlockBody, hlt, hdt, ↓reduceIte, Nat.one_ne_zero]
    exact h2
  | dynamic hf hdh hs =>
    obtain ⟨_, rfl⟩ := hf
    obtain ⟨r1', h1, hr1⟩ := RR.readBits_of (n := 2) (v := 2) (by decide) (by rw [← fieldBits_eq]; exact hr)
    obtain ⟨lt, dt, r2', h2, hr2, hlc, hdc, hne⟩ :=
      readDynamicTables_complete hdh hr1 (symbols_endOfBlock_isSome hs)
    obtain ⟨r', h3, hr'⟩ := decodeSymbol_complete hlc hdc hne hs hr2
    refine ⟨2, r1', r', h1, ?_, hr'⟩
    simp [decompressBlockBody, h2, h3]

theorem blocks_length {p : DeflateSpec.Policy} {out out' : List UInt8} {bs rest : List Bool}
    (h : DeflateSpec.Blocks p out bs out' rest) : rest.length ≤ bs.length := by
  induction h with
  | last hb => have := block_length hb; simp; omega
  | notLast hb _ ih => have := block_length hb; simp; omega

theorem decompressBlocks_complete {out out' : List UInt8} {bs rest : List Bool}
    (h : DeflateSpec.Blocks .strict out bs out' rest) :
    ∀ (fuel : Nat) {r : LSBReader}, RR r bs → bs.length < rest.length + fuel →
      ∃ r', decompressBlocks fuel r out = .ok (out', r') ∧ RR r' rest := by
  induction h with
  | last hb =>
    intro fuel r hr hf
    obtain ⟨r1, h1, hr1⟩ := hr.readBit_cons
    obtain ⟨btype, r2, r', h2, h3, hr'⟩ := decompressBlockBody_complete hb hr1
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by have := block_length hb; simp at hf; omega⟩
    refine ⟨r', ?_, hr'⟩
    simp [decompressBlocks, h1, h2, h3]
  | notLast hb hbs ih =>
    intro fuel r hr hf
    have := blocks_length hbs
    obtain ⟨r1, h1, hr1⟩ := hr.readBit_cons
    obtain ⟨btype, r2, r3, h2, h3, hr3⟩ := decompressBlockBody_complete hb hr1
    have := block_length hb
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    obtain ⟨r', h4, hr'⟩ := ih f hr3 (by simp at hf; omega)
    refine ⟨r', ?_, hr'⟩
    simp only [decompressBlocks, h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
    exact h4

theorem deflateTake_complete {input out rest : List UInt8}
    (h : DeflateSpec.Stream .strict input out rest) : deflateTake input = .ok (out, rest) := by
  obtain ⟨pad, hpad, hbl⟩ := h
  rw [inputBits_eq, inputBits_eq] at hbl
  obtain ⟨r', h1, hr'⟩ := decompressBlocks_complete hbl (8 * input.length + 1) (RR.init input)
    (by simp; omega)
  have hfuel : ({ buffer := 0, count := 0, input := input, totalRead := 0 } : LSBReader).bitsLeft
      + 1 = 8 * input.length + 1 := by simp [LSBReader.bitsLeft]
  unfold deflateTake
  dsimp only
  rw [hfuel, h1]
  simp only [hr'.tail hpad]

end Silmaril.Proofs.Formats.Compression.DeflateSpec
