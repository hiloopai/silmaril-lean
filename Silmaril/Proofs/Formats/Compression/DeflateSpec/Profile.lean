module

public import Silmaril.Proofs.Formats.Compression.DeflateSpec.History
public import Silmaril.Proofs.Formats.Compression.DeflateSpec.Policy
public import Silmaril.Formats.Compression.Deflate.Profile

/-!
# DEFLATE decoding profiles against `DeflateSpec`

`Deflate.deflateTakeWithHistoryProfile prof` is sound and complete for
`StreamWithHistoryWithin (policyOf prof) prof.window`; the strict profile is
`deflateTakeWithHistory`/`deflateTake`; with no window the `…Within` relations
are the plain ones; with a window of `w` bytes only the last `w` bytes of a
history matter.
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.DeflateSpec

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Deflate

/-! ### The strict profile is the existing decoder -/

set_option maxRecDepth 20000 in
theorem decodeStepW_none (lt dt : HuffmanTable) (r : LSBReader) (out : List UInt8) :
    decodeStepW none lt dt r out = decodeStep lt dt r out := by
  simp only [decodeStepW, decodeStep, withinWindow, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem decodeSymbolsFuelW_none (lt dt : HuffmanTable) : ∀ (fuel : Nat) (r : LSBReader)
    (out : List UInt8), decodeSymbolsFuelW none lt dt fuel r out = decodeSymbolsFuel lt dt fuel r out
  | 0, _, _ => rfl
  | fuel + 1, r, out => by
    rw [decodeSymbolsFuelW, decodeSymbolsFuel, decodeStepW_none]
    rcases decodeStep lt dt r out with e | (⟨o, r'⟩ | ⟨o, r'⟩)
    · rfl
    · rfl
    · exact decodeSymbolsFuelW_none lt dt fuel r' o

theorem readDynamicTablesP_strict (r : LSBReader) :
    readDynamicTablesP .strict r = readDynamicTables r := by
  rfl

theorem decompressBlockBodyP_strict (btype : Nat) (r : LSBReader) (out : List UInt8) :
    decompressBlockBodyP .strict btype r out = decompressBlockBody btype r out := by
  have hw : DecodeProfile.strict.window = none := rfl
  simp only [decompressBlockBodyP, decompressBlockBody, hw,
    decodeSymbolsFuelW_none, readDynamicTablesP_strict, decodeSymbol]
  by_cases h0 : btype = 0
  · subst h0; simp only [↓reduceIte]; rcases decompressStored r with e | ⟨b, r'⟩ <;> rfl
  by_cases h1 : btype = 1
  · subst h1; simp only [↓reduceIte, Nat.one_ne_zero]
    rcases fixedLitLenTable with _ | lt <;> rcases fixedDistTable with _ | dt <;> rfl
  by_cases h2 : btype = 2
  · subst h2; simp only [↓reduceIte, Nat.succ_ne_zero, Nat.reduceEqDiff]
    rcases readDynamicTables r with e | ⟨lt, dt, r'⟩ <;> rfl
  simp only [h0, h1, h2, ↓reduceIte]

theorem decompressBlocksP_strict : ∀ (fuel : Nat) (r : LSBReader) (out : List UInt8),
    decompressBlocksP .strict fuel r out = decompressBlocks fuel r out
  | 0, _, _ => rfl
  | fuel + 1, r, out => by
    simp only [decompressBlocksP, decompressBlocks]
    rcases r.readBit with _ | ⟨bfinal, r1⟩
    · rfl
    · simp only
      rcases r1.readBits 2 with _ | ⟨btype, r2⟩
      · rfl
      · simp only [decompressBlockBodyP_strict]
        rcases decompressBlockBody btype r2 out with e | ⟨o, r3⟩
        · rfl
        · simp only [decompressBlocksP_strict fuel]

theorem deflateTakeWithHistoryProfile_strict (history input : List UInt8) :
    deflateTakeWithHistoryProfile .strict history input =
      deflateTakeWithHistory history input := by
  simp only [deflateTakeWithHistoryProfile, deflateTakeWithHistory, decompressBlocksP_strict]

theorem deflateTakeProfile_strict (input : List UInt8) :
    deflateTakeProfile .strict input = deflateTake input := by
  simp only [deflateTakeProfile, deflateTakeWithHistoryProfile_strict, deflateTakeWithHistory,
    resultWithHistory, deflateTake]
  rcases decompressBlocks _ _ [] with e | ⟨o, r'⟩ <;> rfl

/-! ### Windows -/

theorem withinWindow_iff {w : Option Nat} {d : Nat} :
    withinWindow w d = true ↔ DeflateSpec.WithinWindow w d := by
  cases w <;> simp [withinWindow, DeflateSpec.WithinWindow]

theorem withinWindow_none (d : Nat) : DeflateSpec.WithinWindow none d := by
  simp [DeflateSpec.WithinWindow]

theorem symbolsWithin_forget {w : Option Nat} {lit dist : DeflateSpec.Code} {out bits out' rest}
    (h : DeflateSpec.SymbolsWithin w lit dist out bits out' rest) :
    DeflateSpec.Symbols lit dist out bits out' rest := by
  induction h with
  | endOfBlock h => exact .endOfBlock h
  | literal a b _ ih => exact .literal a b ih
  | reference a b c d e f g _ _ ih => exact .reference a b c d e f g ih

theorem symbolsWithin_of_none {lit dist : DeflateSpec.Code} {out bits out' rest}
    (h : DeflateSpec.Symbols lit dist out bits out' rest) :
    DeflateSpec.SymbolsWithin none lit dist out bits out' rest := by
  induction h with
  | endOfBlock h => exact .endOfBlock h
  | literal a b _ ih => exact .literal a b ih
  | reference a b c d e f g _ ih => exact .reference a b c d e f g (withinWindow_none _) ih

theorem blockWithin_forget {p : DeflateSpec.Policy} {w : Option Nat} {out bits out' rest}
    (h : DeflateSpec.BlockWithin p w out bits out' rest) :
    DeflateSpec.Block p out bits out' rest := by
  cases h with
  | stored a b c d e f g i j => exact .stored a b c d e f g i j
  | fixed a b => exact .fixed a (symbolsWithin_forget b)
  | dynamic a b c => exact .dynamic a b (symbolsWithin_forget c)

theorem blockWithin_of_none {p : DeflateSpec.Policy} {out bits out' rest}
    (h : DeflateSpec.Block p out bits out' rest) :
    DeflateSpec.BlockWithin p none out bits out' rest := by
  cases h with
  | stored a b c d e f g i j => exact .stored a b c d e f g i j
  | fixed a b => exact .fixed a (symbolsWithin_of_none b)
  | dynamic a b c => exact .dynamic a b (symbolsWithin_of_none c)

theorem blocksWithin_forget {p : DeflateSpec.Policy} {w : Option Nat} {out bits out' rest}
    (h : DeflateSpec.BlocksWithin p w out bits out' rest) :
    DeflateSpec.Blocks p out bits out' rest := by
  induction h with
  | last hb => exact .last (blockWithin_forget hb)
  | notLast hb _ ih => exact .notLast (blockWithin_forget hb) ih

theorem blocksWithin_of_none {p : DeflateSpec.Policy} {out bits out' rest}
    (h : DeflateSpec.Blocks p out bits out' rest) :
    DeflateSpec.BlocksWithin p none out bits out' rest := by
  induction h with
  | last hb => exact .last (blockWithin_of_none hb)
  | notLast hb _ ih => exact .notLast (blockWithin_of_none hb) ih

theorem streamWithHistoryWithin_none {p : DeflateSpec.Policy} {history input out rest : List UInt8} :
    DeflateSpec.StreamWithHistoryWithin p none history input out rest ↔
      DeflateSpec.StreamWithHistory p history input out rest :=
  ⟨fun ⟨pad, hp, hb⟩ => ⟨pad, hp, blocksWithin_forget hb⟩,
   fun ⟨pad, hp, hb⟩ => ⟨pad, hp, blocksWithin_of_none hb⟩⟩

theorem streamWithHistoryWithin_forget {p : DeflateSpec.Policy} {w : Option Nat}
    {history input out rest : List UInt8}
    (h : DeflateSpec.StreamWithHistoryWithin p w history input out rest) :
    DeflateSpec.StreamWithHistory p history input out rest :=
  let ⟨pad, hp, hb⟩ := h; ⟨pad, hp, blocksWithin_forget hb⟩

/-- Windows only shrink the accepted streams. -/
theorem symbolsWithin_mono {w w' : Option Nat}
    (hw : ∀ d, DeflateSpec.WithinWindow w d → DeflateSpec.WithinWindow w' d)
    {lit dist : DeflateSpec.Code} {out bits out' rest}
    (h : DeflateSpec.SymbolsWithin w lit dist out bits out' rest) :
    DeflateSpec.SymbolsWithin w' lit dist out bits out' rest := by
  induction h with
  | endOfBlock h => exact .endOfBlock h
  | literal a b _ ih => exact .literal a b ih
  | reference a b c d e f g i _ ih => exact .reference a b c d e f g (hw _ i) ih

theorem blocksWithin_mono {p : DeflateSpec.Policy} {w w' : Option Nat}
    (hw : ∀ d, DeflateSpec.WithinWindow w d → DeflateSpec.WithinWindow w' d)
    {out bits out' rest} (h : DeflateSpec.BlocksWithin p w out bits out' rest) :
    DeflateSpec.BlocksWithin p w' out bits out' rest := by
  have hb : ∀ {out bits out' rest}, DeflateSpec.BlockWithin p w out bits out' rest →
      DeflateSpec.BlockWithin p w' out bits out' rest := by
    intro out bits out' rest h
    cases h with
    | stored a b c d e f g i j => exact .stored a b c d e f g i j
    | fixed a b => exact .fixed a (symbolsWithin_mono hw b)
    | dynamic a b c => exact .dynamic a b (symbolsWithin_mono hw c)
  induction h with
  | last h => exact .last (hb h)
  | notLast h _ ih => exact .notLast (hb h) ih

/-! ### The decoding policy of a profile -/

/-- The `DeflateSpec.Policy` a decoding profile implements. -/
def policyOf (prof : DecodeProfile) : DeflateSpec.Policy where
  maxDistCodes := prof.maxDistCodes
  clCodeOK := if prof.completeCodes then DeflateSpec.Complete 7 else DeflateSpec.PrefixLengths 7
  codeOK := if prof.completeCodes then
      (fun L => DeflateSpec.Complete 15 L ∨ DeflateSpec.SingleCode L)
    else DeflateSpec.PrefixLengths 15

theorem policyOf_strict : policyOf .strict = .strict := rfl

theorem policyOf_rfc : policyOf .rfc = .rfc := rfl

theorem policyOf_windowed (w : Nat) : policyOf (.windowed w) = .strict := rfl

theorem prefixLengths_of_isValid {L : List Nat} {M : Nat} (h : isValidLengths L M = true) :
    DeflateSpec.PrefixLengths M L :=
  ⟨isValidLengths_le L M h, by rw [kraft_eq_kraftTotal]; exact kraftTotal_le L M h⟩

theorem isValid_of_prefixLengths {L : List Nat} {M : Nat} (h : DeflateSpec.PrefixLengths M L) :
    isValidLengths L M = true :=
  isValidLengths_of_kraftTotal L M h.1 (by rw [← kraft_eq_kraftTotal]; exact h.2)

theorem clOK_of_checks {prof : DecodeProfile} {L : List Nat}
    (hc : ¬ (prof.completeCodes && !isCompleteCode L 7) = true) (hv : isValidLengths L 7 = true) :
    (policyOf prof).clCodeOK L := by
  unfold policyOf
  cases hpc : prof.completeCodes
  · exact prefixLengths_of_isValid hv
  · rw [hpc] at hc
    simp only [Bool.true_and, Bool.not_eq_true', Bool.not_eq_false] at hc
    exact complete_of_isCompleteCode hc

theorem codeOK_of_checks {prof : DecodeProfile} {L : List Nat}
    (hc : ¬ (prof.completeCodes && !validCodeLengths L 15) = true)
    (hv : isValidLengths L 15 = true) : (policyOf prof).codeOK L := by
  unfold policyOf
  cases hpc : prof.completeCodes
  · exact prefixLengths_of_isValid hv
  · rw [hpc] at hc
    simp only [Bool.true_and, Bool.not_eq_true', Bool.not_eq_false] at hc
    exact strict_codeOK_of_valid hc hv

theorem checks_of_clOK {prof : DecodeProfile} {L : List Nat} (h : (policyOf prof).clCodeOK L) :
    isValidLengths L 7 = true ∧ (prof.completeCodes && !isCompleteCode L 7) = false := by
  unfold policyOf at h
  cases hpc : prof.completeCodes
  · rw [hpc] at h
    exact ⟨isValid_of_prefixLengths h, rfl⟩
  · rw [hpc] at h
    exact ⟨isValidLengths_of_complete h, by simp [isCompleteCode_of_complete h]⟩

theorem checks_of_codeOK {prof : DecodeProfile} {L : List Nat} (hb : ∀ l ∈ L, l ≤ 15)
    (h : (policyOf prof).codeOK L) :
    isValidLengths L 15 = true ∧ (prof.completeCodes && !validCodeLengths L 15) = false := by
  unfold policyOf at h
  cases hpc : prof.completeCodes
  · rw [hpc] at h
    exact ⟨isValid_of_prefixLengths h, rfl⟩
  · rw [hpc] at h
    obtain ⟨h1, h2⟩ := valid_of_strict_codeOK hb h
    exact ⟨h1, by simp [h2]⟩

/-! ### Soundness -/

/-- What one decoding step means for the spec, with a window. -/
def StepOKW (w : Option Nat) (Cl Cd : DeflateSpec.Code) (out : List UInt8) (bs : List Bool) :
    SymbolStep → Prop
  | .done o r' => o = out ∧ ∃ rest, Cl.Reads bs 256 rest ∧ RR r' rest
  | .more o r' => ∃ rest, RR r' rest ∧ ∀ out' rest',
      DeflateSpec.SymbolsWithin w Cl Cd o rest out' rest' →
      DeflateSpec.SymbolsWithin w Cl Cd out bs out' rest'

theorem decodeStepW_sound {w : Option Nat} {lt dt : HuffmanTable} {Cl Cd : DeflateSpec.Code}
    (hl : TSound lt Cl) (hd : TSound dt Cd) {r : LSBReader} {bs : List Bool}
    {out : List UInt8} {step : SymbolStep}
    (h : decodeStepW w lt dt r out = .ok step) (hr : RR r bs) : StepOKW w Cl Cd out bs step := by
  unfold decodeStepW at h
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
    split at h
    · cases h
    next hwin =>
    cases h
    refine ⟨rest4, hr4, fun out' rest' hsyms => ?_⟩
    have hlc := lengthCode_eq sym
    rw [ite_eq_left ⟨by omega, h3⟩] at hlc
    have hdc := distCode_eq dsym
    rw [ite_eq_left (by omega)] at hdc
    exact .reference hR1 hlc ⟨hxlt, by rw [fieldBits_eq]; exact hrest1⟩ hD hdc
      ⟨hylt, by rw [fieldBits_eq]; exact hrest3⟩
      (by omega) (withinWindow_iff.1 (by simpa using hwin)) (by rw [← copyBack_eq]; exact hsyms)
  · rw [ite_eq_right h3] at h
    cases h

theorem decodeSymbolsFuelW_sound {w : Option Nat} {lt dt : HuffmanTable} {Cl Cd : DeflateSpec.Code}
    (hl : TSound lt Cl) (hd : TSound dt Cd) : ∀ (fuel : Nat) {r r' : LSBReader}
    {bs : List Bool} {out out' : List UInt8},
    decodeSymbolsFuelW w lt dt fuel r out = .ok (out', r') → RR r bs →
    ∃ rest, DeflateSpec.SymbolsWithin w Cl Cd out bs out' rest ∧ RR r' rest := by
  intro fuel
  induction fuel with
  | zero => intro r r' bs out out' h; cases h
  | succ n ih =>
    intro r r' bs out out' h hr
    simp only [decodeSymbolsFuelW] at h
    split at h
    · cases h
    · next o r1 hstep =>
      obtain ⟨rfl, rest, hR, hr1⟩ := decodeStepW_sound hl hd hstep hr
      cases h
      exact ⟨rest, .endOfBlock hR, hr1⟩
    · next o r1 hstep =>
      obtain ⟨rest1, hr1, k⟩ := decodeStepW_sound hl hd hstep hr
      obtain ⟨rest, hs, hr'⟩ := ih h hr1
      exact ⟨rest, k _ _ hs, hr'⟩

theorem readDynamicTablesP_sound {prof : DecodeProfile} {r r' : LSBReader} {bs : List Bool}
    {lt dt : HuffmanTable}
    (h : readDynamicTablesP prof r = .ok (lt, dt, r')) (hr : RR r bs) :
    ∃ lit dist rest, DeflateSpec.DynamicHeader (policyOf prof) bs lit dist rest ∧ RR r' rest ∧
      TSound lt lit ∧ TSound dt dist := by
  unfold readDynamicTablesP at h
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
  split at h
  · next lt' dt' hlt hdt =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨_, _, rest5, ?_, hr5, tSound_ofLengths hlt, tSound_ofLengths hdt⟩
    exact .mk ⟨hlitlt, by rw [fieldBits_eq]⟩ (by omega) ⟨hdistlt, by rw [fieldBits_eq]⟩
      (by show _ ≤ prof.maxDistCodes; omega) ⟨hclenlt, by rw [fieldBits_eq]⟩ hfields (by omega)
      (clOK_of_checks hcomplete (ofLengths_entries hclTable).2.1) hruns (by omega)
      (codeOK_of_checks hvlit (ofLengths_entries hlt).2.1)
      (codeOK_of_checks hvdist (ofLengths_entries hdt).2.1)
  · cases h

theorem decompressBlockBodyP_sound {prof : DecodeProfile} {btype : Nat} {r r' : LSBReader}
    {bs : List Bool} {out out' : List UInt8} (hb : btype < 2 ^ 2)
    (h : decompressBlockBodyP prof btype r out = .ok (out', r')) (hr : RR r bs) :
    ∃ rest, DeflateSpec.BlockWithin (policyOf prof) prof.window out (natBits btype 2 ++ bs)
      out' rest ∧ RR r' rest := by
  have hf : DeflateSpec.Field 2 (natBits btype 2 ++ bs) btype bs := ⟨hb, by rw [fieldBits_eq]⟩
  unfold decompressBlockBodyP at h
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
    obtain ⟨rest, hs, hr'⟩ := decodeSymbolsFuelW_sound hls hds _ h hr
    exact ⟨rest, .fixed hf hs, hr'⟩
  split at h
  · next h2 =>
    subst h2
    split at h
    · cases h
    next lt dt r1 hdyn =>
    obtain ⟨lit, dist, rest1, hdh, hr1, hls, hds⟩ := readDynamicTablesP_sound hdyn hr
    obtain ⟨rest, hs, hr'⟩ := decodeSymbolsFuelW_sound hls hds _ h hr1
    exact ⟨rest, .dynamic hf hdh hs, hr'⟩
  · cases h

theorem decompressBlocksP_sound {prof : DecodeProfile} : ∀ (fuel : Nat) {r r' : LSBReader}
    {bs : List Bool} {out out' : List UInt8},
    decompressBlocksP prof fuel r out = .ok (out', r') → RR r bs →
    ∃ rest, DeflateSpec.BlocksWithin (policyOf prof) prof.window out bs out' rest ∧ RR r' rest := by
  intro fuel
  induction fuel with
  | zero => intro r r' bs out out' h; cases h
  | succ n ih =>
    intro r r' bs out out' h hr
    simp only [decompressBlocksP] at h
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
    obtain ⟨rest1, hblock, hr3⟩ := decompressBlockBodyP_sound hblt hbody hr2
    cases bfinal
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨rest, hbl, hr'⟩ := ih h hr3
      exact ⟨rest, .notLast hblock hbl, hr'⟩
    · simp only [↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rest1, .last hblock, hr3⟩

theorem deflateTakeWithHistoryProfile_sound {prof : DecodeProfile}
    {history input out rest : List UInt8}
    (h : deflateTakeWithHistoryProfile prof history input = .ok (out, rest)) :
    DeflateSpec.StreamWithHistoryWithin (policyOf prof) prof.window history input out rest := by
  unfold deflateTakeWithHistoryProfile resultWithHistory at h
  dsimp only at h
  cases hb : decompressBlocksP prof _ _ history with
  | error e => rw [hb] at h; cases h
  | ok p =>
    obtain ⟨out', r'⟩ := p
    rw [hb] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨bits, hbl, hr'⟩ := decompressBlocksP_sound _ hb (RR.init input)
    obtain ⟨pad, hpad, rfl⟩ := hr'.pad
    obtain ⟨t, rfl⟩ := blocks_prefix (blocksWithin_forget hbl)
    refine ⟨pad, hpad, ?_⟩
    rw [inputBits_eq, inputBits_eq, List.drop_left]
    exact hbl

/-! ### Completeness -/

theorem decodeSymbolsFuelW_complete {w : Option Nat} {lt dt : HuffmanTable}
    {Cl Cd : DeflateSpec.Code}
    (hl : TComplete lt Cl) (hd : TComplete dt Cd) (hne : NonEmpty Cl)
    {out out' : List UInt8} {bs rest : List Bool}
    (h : DeflateSpec.SymbolsWithin w Cl Cd out bs out' rest) :
    ∀ (fuel : Nat) {r : LSBReader}, RR r bs → bs.length < rest.length + fuel →
      ∃ r', decodeSymbolsFuelW w lt dt fuel r out = .ok (out', r') ∧ RR r' rest := by
  induction h with
  | @endOfBlock out bs rest hR =>
    intro fuel r hr hf
    obtain ⟨w', hw, rfl⟩ := hR
    obtain ⟨r', h1, hr'⟩ := hl hw hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by
      have := hne hw; have := List.length_pos_iff.mpr this; simp at hf; omega⟩
    refine ⟨r', ?_, hr'⟩
    simp [decodeSymbolsFuelW, decodeStepW, h1]
  | @literal out bs r1 out' rest v hv hR hsub ih =>
    intro fuel r hr hf
    have := symbols_length (symbolsWithin_forget hsub)
    have hlt := reads_length_lt hne hR
    obtain ⟨w', hw, rfl⟩ := hR
    obtain ⟨r1', h1, hr1⟩ := hl hw hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨r', h2, hr'⟩ := ih f hr1 (by omega)
    refine ⟨r', ?_, hr'⟩
    simp only [decodeSymbolsFuelW, decodeStepW, h1, hv, ↓reduceIte]
    exact h2
  | @reference out bs out' rest sym r1 lenExtra lenBase x r2 dsym r3 distExtra distBase y r4
      hR hlc hx hD hdc hy hle hwin hsub ih =>
    intro fuel r hr hf
    have := symbols_length (symbolsWithin_forget hsub)
    have hlt := reads_length_lt hne hR
    have := field_length hx; have := reads_length hD; have := field_length hy
    obtain ⟨w', hw, rfl⟩ := hR
    obtain ⟨r1', h1, hr1⟩ := hl hw hr
    obtain ⟨hxlt, rfl⟩ := hx
    obtain ⟨r2', h2, hr2⟩ := RR.readBits_of hxlt (by rw [← fieldBits_eq]; exact hr1)
    obtain ⟨w'', hw', rfl⟩ := hD
    obtain ⟨r3', h3, hr3⟩ := hd hw' hr2
    obtain ⟨hylt, rfl⟩ := hy
    obtain ⟨r4', h4, hr4⟩ := RR.readBits_of hylt (by rw [← fieldBits_eq]; exact hr3)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨r', h5, hr'⟩ := ih f hr4 (by simp at *; omega)
    refine ⟨r', ?_, hr'⟩
    have hwb : withinWindow w (distBase + y) = true := withinWindow_iff.2 hwin
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
        simp only [decodeSymbolsFuelW, decodeStepW, h1, hn1, hn2, hs.2, ← hE, ← hB, h2, h3, hn3,
          ← hDE, ← hDB, h4, hn4, hwb, Bool.not_true, Bool.false_eq_true, ↓reduceIte, copyBack_eq]
        exact h5
      · cases hd2
    · cases hl2

theorem readDynamicTablesP_complete' {prof : DecodeProfile} {bs r1 r2 r3 r4 rest : List Bool}
    {hlit hdist hclen : Nat} {vals lens : List Nat} {r : LSBReader}
    (hlitF : DeflateSpec.Field 5 bs hlit r1) (hlitR : hlit + 257 ≤ 286)
    (hdistF : DeflateSpec.Field 5 r1 hdist r2) (hdistR : hdist + 1 ≤ prof.maxDistCodes)
    (hclenF : DeflateSpec.Field 4 r2 hclen r3) (hfields : DeflateSpec.Fields 3 r3 vals r4)
    (hclc : vals.length = hclen + 4)
    (hclOK : (policyOf prof).clCodeOK (DeflateSpec.clLengths vals))
    (hruns : DeflateSpec.LengthRuns (DeflateSpec.Code.ofLengths (DeflateSpec.clLengths vals))
      [] r4 lens rest)
    (hcount : lens.length = hlit + 257 + (hdist + 1))
    (hlitOK : (policyOf prof).codeOK (lens.take (hlit + 257)))
    (hdistOK : (policyOf prof).codeOK (lens.drop (hlit + 257)))
    (hr : RR r bs) (h256 : (DeflateSpec.Code.ofLengths (lens.take (hlit + 257)) 256).isSome) :
    ∃ lt dt r', readDynamicTablesP prof r = .ok (lt, dt, r') ∧ RR r' rest ∧
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
  obtain ⟨hclValid, hclCheck⟩ := checks_of_clOK hclOK
  obtain ⟨clTable, hclTable⟩ := ofLengths_isSome hclValid
  obtain ⟨r5', h5, hr5⟩ := readCodeLengths_complete (tComplete_ofLengths hclTable) hruns hcount
    (hlit + 257 + (hdist + 1) + 1) hr4 (by simp [hcount])
  have hlt16 := runs_lt16 hruns (by simp)
  have hb : ∀ L, (L = lens.take (hlit + 257) ∨ L = lens.drop (hlit + 257)) → ∀ l ∈ L, l ≤ 15 := by
    intro L hL l hl
    rcases hL with rfl | rfl
    · have := hlt16 l (List.mem_of_mem_take hl); omega
    · have := hlt16 l (List.mem_of_mem_drop hl); omega
  obtain ⟨hvl, hcl⟩ := checks_of_codeOK (hb _ (Or.inl rfl)) hlitOK
  obtain ⟨hvd, hcd⟩ := checks_of_codeOK (hb _ (Or.inr rfl)) hdistOK
  obtain ⟨lt, hlt⟩ := ofLengths_isSome hvl
  obtain ⟨dt, hdt⟩ := ofLengths_isSome hvd
  have h256' : (lens.take (hlit + 257)).getD 256 0 ≠ 0 := by
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h256
    obtain ⟨hs, h0, _⟩ := ofLengths_eq_some hw
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs] using h0
  refine ⟨lt, dt, r5', ?_, hr5, tComplete_ofLengths hlt, tComplete_ofLengths hdt⟩
  have hn : ¬ (286 < hlit + 257 ∨ prof.maxDistCodes < hdist + 1) := by omega
  simp only [readDynamicTablesP, h1, h2, h3, hn, h4, hclCheck, hclTable, h5, h256', hcl, hcd,
    hlt, hdt, ↓reduceIte, Bool.false_eq_true]

theorem readDynamicTablesP_complete {prof : DecodeProfile} {bs rest : List Bool}
    {lit dist : DeflateSpec.Code} {r : LSBReader}
    (h : DeflateSpec.DynamicHeader (policyOf prof) bs lit dist rest) (hr : RR r bs)
    (h256 : (lit 256).isSome) :
    ∃ lt dt r', readDynamicTablesP prof r = .ok (lt, dt, r') ∧ RR r' rest ∧
      TComplete lt lit ∧ TComplete dt dist ∧ NonEmpty lit := by
  cases h with
  | mk hlitF hlitR hdistF hdistR hclenF hfields hclc hclOK hruns hcount hlitOK hdistOK =>
    obtain ⟨lt, dt, r', h1, h2, h3, h4⟩ := readDynamicTablesP_complete' hlitF hlitR hdistF hdistR
      hclenF hfields hclc hclOK hruns hcount hlitOK hdistOK hr h256
    exact ⟨lt, dt, r', h1, h2, h3, h4, nonEmpty_ofLengths _⟩

theorem decompressBlockBodyP_zero (prof : DecodeProfile) (r : LSBReader) (out : List UInt8) :
    decompressBlockBodyP prof 0 r out = decompressBlockBody 0 r out := by
  simp only [decompressBlockBodyP, decompressBlockBody, ↓reduceIte]
  rcases decompressStored r with e | ⟨b, r'⟩ <;> rfl

theorem decompressBlockBodyP_complete {prof : DecodeProfile} {out out' : List UInt8}
    {bs rest : List Bool} {r : LSBReader}
    (h : DeflateSpec.BlockWithin (policyOf prof) prof.window out bs out' rest) (hr : RR r bs) :
    ∃ btype r1 r', r.readBits 2 = some (btype, r1) ∧
      decompressBlockBodyP prof btype r1 out = .ok (out', r') ∧ RR r' rest := by
  cases h with
  | stored hf hp hpad hmod hlen hnlen hx hdl h4 =>
    obtain ⟨btype, r1, r', e1, e2, e3⟩ := stored_complete hf hp hpad hmod hlen hnlen hx hdl h4 hr
    obtain ⟨_, rfl⟩ := hf
    have hb : btype = 0 := by
      have := RR.readBits_of (n := 2) (v := 0) (by decide) (by rw [← fieldBits_eq]; exact hr)
      obtain ⟨_, h', _⟩ := this
      rw [h'] at e1; simp only [Option.some.injEq, Prod.mk.injEq] at e1; exact e1.1.symm
    subst hb
    exact ⟨0, r1, r', e1, by rw [decompressBlockBodyP_zero]; exact e2, e3⟩
  | fixed hf hs =>
    obtain ⟨_, rfl⟩ := hf
    obtain ⟨r1', h1, hr1⟩ :=
      RR.readBits_of (n := 2) (v := 1) (by decide) (by rw [← fieldBits_eq]; exact hr)
    obtain ⟨lt, dt, hlt, hdt, _, hlc, _, hdc⟩ := fixed_tables
    obtain ⟨r', h2, hr'⟩ := decodeSymbolsFuelW_complete hlc hdc
      (by rw [DeflateSpec.fixedLitLenCode]; exact nonEmpty_ofLengths _) hs (r1'.bitsLeft + 1) hr1
      (by rw [hr1.1.bitsLeft]; omega)
    refine ⟨1, r1', r', h1, ?_, hr'⟩
    simp only [decompressBlockBodyP, hlt, hdt, ↓reduceIte, Nat.one_ne_zero]
    exact h2
  | dynamic hf hdh hs =>
    obtain ⟨_, rfl⟩ := hf
    obtain ⟨r1', h1, hr1⟩ :=
      RR.readBits_of (n := 2) (v := 2) (by decide) (by rw [← fieldBits_eq]; exact hr)
    obtain ⟨lt, dt, r2', h2, hr2, hlc, hdc, hne⟩ :=
      readDynamicTablesP_complete hdh hr1 (symbols_endOfBlock_isSome (symbolsWithin_forget hs))
    obtain ⟨r', h3, hr'⟩ := decodeSymbolsFuelW_complete hlc hdc hne hs (r2'.bitsLeft + 1) hr2
      (by rw [hr2.1.bitsLeft]; omega)
    refine ⟨2, r1', r', h1, ?_, hr'⟩
    simp [decompressBlockBodyP, h2, h3]

theorem decompressBlocksP_complete {prof : DecodeProfile} {out out' : List UInt8}
    {bs rest : List Bool}
    (h : DeflateSpec.BlocksWithin (policyOf prof) prof.window out bs out' rest) :
    ∀ (fuel : Nat) {r : LSBReader}, RR r bs → bs.length < rest.length + fuel →
      ∃ r', decompressBlocksP prof fuel r out = .ok (out', r') ∧ RR r' rest := by
  induction h with
  | last hb =>
    intro fuel r hr hf
    obtain ⟨r1, h1, hr1⟩ := hr.readBit_cons
    obtain ⟨btype, r2, r', h2, h3, hr'⟩ := decompressBlockBodyP_complete hb hr1
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
      ⟨fuel - 1, by have := block_length (blockWithin_forget hb); simp at hf; omega⟩
    refine ⟨r', ?_, hr'⟩
    simp [decompressBlocksP, h1, h2, h3]
  | notLast hb hbs ih =>
    intro fuel r hr hf
    have := blocks_length (blocksWithin_forget hbs)
    obtain ⟨r1, h1, hr1⟩ := hr.readBit_cons
    obtain ⟨btype, r2, r3, h2, h3, hr3⟩ := decompressBlockBodyP_complete hb hr1
    have := block_length (blockWithin_forget hb)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    obtain ⟨r', h4, hr'⟩ := ih f hr3 (by simp at hf; omega)
    refine ⟨r', ?_, hr'⟩
    simp only [decompressBlocksP, h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
    exact h4

theorem deflateTakeWithHistoryProfile_complete {prof : DecodeProfile}
    {history input out rest : List UInt8}
    (h : DeflateSpec.StreamWithHistoryWithin (policyOf prof) prof.window history input out rest) :
    deflateTakeWithHistoryProfile prof history input = .ok (out, rest) := by
  obtain ⟨pad, hpad, hbl⟩ := h
  rw [inputBits_eq, inputBits_eq] at hbl
  obtain ⟨r', h1, hr'⟩ := decompressBlocksP_complete hbl (8 * input.length + 1) (RR.init input)
    (by simp; omega)
  have hfuel : ({ buffer := 0, count := 0, input := input, totalRead := 0 } : LSBReader).bitsLeft
      + 1 = 8 * input.length + 1 := by simp [LSBReader.bitsLeft]
  unfold deflateTakeWithHistoryProfile resultWithHistory
  dsimp only
  rw [hfuel, h1]
  simp [Except.map, hr'.tail hpad]

theorem deflateTakeWithHistoryProfile_iff {prof : DecodeProfile}
    {history input out rest : List UInt8} :
    deflateTakeWithHistoryProfile prof history input = .ok (out, rest) ↔
      DeflateSpec.StreamWithHistoryWithin (policyOf prof) prof.window history input out rest :=
  ⟨deflateTakeWithHistoryProfile_sound, deflateTakeWithHistoryProfile_complete⟩

/-! ### With a window of `w` bytes, only the last `w` bytes of a history matter -/

theorem symbolsWithin_extend {win : Option Nat} {lit dist : DeflateSpec.Code} (pre : List UInt8)
    {out bits out' rest}
    (h : DeflateSpec.SymbolsWithin win lit dist out bits out' rest) :
    DeflateSpec.SymbolsWithin win lit dist (pre ++ out) bits (pre ++ out') rest := by
  induction h with
  | endOfBlock h => exact .endOfBlock h
  | literal hv hr _ ih => exact .literal hv hr (by simpa using ih)
  | reference h1 h2 h3 h4 h5 h6 h7 h8 _ ih =>
    refine .reference h1 h2 h3 h4 h5 h6 (by simp; omega) h8 ?_
    rwa [copyMatch_append _ _ h7]

theorem symbolsWithin_restrict {W : Nat} {lit dist : DeflateSpec.Code} (pre : List UInt8)
    {out bits out' rest}
    (h : DeflateSpec.SymbolsWithin (some W) lit dist out bits out' rest) :
    ∀ o, out = pre ++ o → W ≤ o.length →
      ∃ o', out' = pre ++ o' ∧ DeflateSpec.SymbolsWithin (some W) lit dist o bits o' rest := by
  induction h with
  | endOfBlock h => intro o ho _; exact ⟨o, ho, .endOfBlock h⟩
  | @literal _ _ _ _ _ v hv hr _ ih =>
    intro o ho hl
    obtain ⟨o', h1, h2⟩ := ih (o ++ [UInt8.ofNat v]) (by simp [ho]) (by simp; omega)
    exact ⟨o', h1, .literal hv hr h2⟩
  | reference h1 h2 h3 h4 h5 h6 h7 h8 _ ih =>
    intro o ho hl
    have hb := h8 W rfl
    subst ho
    rw [copyMatch_append _ _ (by omega)] at ih
    obtain ⟨o', e1, e2⟩ := ih _ rfl (by rw [length_copyMatch]; omega)
    exact ⟨o', e1, .reference h1 h2 h3 h4 h5 h6 (by omega) h8 e2⟩

theorem blockWithin_extend {p : DeflateSpec.Policy} {win : Option Nat} (pre : List UInt8)
    {out bits out' rest} (h : DeflateSpec.BlockWithin p win out bits out' rest) :
    DeflateSpec.BlockWithin p win (pre ++ out) bits (pre ++ out') rest := by
  cases h with
  | stored a b c d e f g i j => rw [← List.append_assoc]; exact .stored a b c d e f g i j
  | fixed a hs => exact .fixed a (symbolsWithin_extend pre hs)
  | dynamic a b hs => exact .dynamic a b (symbolsWithin_extend pre hs)

theorem blockWithin_restrict {p : DeflateSpec.Policy} {W : Nat} (pre : List UInt8)
    {out bits out' rest} (h : DeflateSpec.BlockWithin p (some W) out bits out' rest)
    (o : List UInt8) (ho : out = pre ++ o) (hl : W ≤ o.length) :
    ∃ o', out' = pre ++ o' ∧ DeflateSpec.BlockWithin p (some W) o bits o' rest := by
  cases h with
  | stored a b c d e f g i j => exact ⟨_, by simp [ho], .stored a b c d e f g i j⟩
  | fixed a hs =>
    obtain ⟨o', e1, e2⟩ := symbolsWithin_restrict pre hs o ho hl
    exact ⟨o', e1, .fixed a e2⟩
  | dynamic a b hs =>
    obtain ⟨o', e1, e2⟩ := symbolsWithin_restrict pre hs o ho hl
    exact ⟨o', e1, .dynamic a b e2⟩

theorem blocksWithin_extend {p : DeflateSpec.Policy} {win : Option Nat} (pre : List UInt8)
    {out bits out' rest} (h : DeflateSpec.BlocksWithin p win out bits out' rest) :
    DeflateSpec.BlocksWithin p win (pre ++ out) bits (pre ++ out') rest := by
  induction h with
  | last hb => exact .last (blockWithin_extend pre hb)
  | notLast hb _ ih => exact .notLast (blockWithin_extend pre hb) ih

theorem blocksWithin_restrict {p : DeflateSpec.Policy} {W : Nat} (pre : List UInt8)
    {out bits out' rest} (h : DeflateSpec.BlocksWithin p (some W) out bits out' rest) :
    ∀ o, out = pre ++ o → W ≤ o.length →
      ∃ o', out' = pre ++ o' ∧ DeflateSpec.BlocksWithin p (some W) o bits o' rest := by
  induction h with
  | last hb =>
    intro o ho hl
    obtain ⟨o', e1, e2⟩ := blockWithin_restrict pre hb o ho hl
    exact ⟨o', e1, .last e2⟩
  | notLast hb _ ih =>
    intro o ho hl
    obtain ⟨o1, e1, e2⟩ := blockWithin_restrict pre hb o ho hl
    obtain ⟨t, rfl⟩ := block_prefix (blockWithin_forget e2)
    obtain ⟨o', e3, e4⟩ := ih _ e1 (by simp; omega)
    exact ⟨o', e3, .notLast e2 e4⟩

theorem streamWithHistoryWithin_append {p : DeflateSpec.Policy} {W : Nat} (pre : List UInt8)
    {history input out rest : List UInt8} (hl : W ≤ history.length) :
    DeflateSpec.StreamWithHistoryWithin p (some W) (pre ++ history) input out rest ↔
      DeflateSpec.StreamWithHistoryWithin p (some W) history input out rest := by
  constructor
  · rintro ⟨pad, hpad, hb⟩
    obtain ⟨o', e1, e2⟩ := blocksWithin_restrict pre hb history rfl hl
    rw [List.append_assoc, List.append_cancel_left_eq] at e1
    exact ⟨pad, hpad, e1 ▸ e2⟩
  · rintro ⟨pad, hpad, hb⟩
    exact ⟨pad, hpad, by simpa using blocksWithin_extend pre hb⟩

theorem streamWithHistoryWithin_window {p : DeflateSpec.Policy} {W : Nat}
    {history input out rest : List UInt8} :
    DeflateSpec.StreamWithHistoryWithin p (some W) (history.drop (history.length - W)) input out
        rest ↔
      DeflateSpec.StreamWithHistoryWithin p (some W) history input out rest := by
  by_cases h : history.length ≤ W
  · rw [show history.length - W = 0 by omega, List.drop_zero]
  · conv => rhs; rw [← List.take_append_drop (history.length - W) history]
    exact (streamWithHistoryWithin_append _ (by simp; omega)).symm

end Silmaril.Proofs.Formats.Compression.DeflateSpec
