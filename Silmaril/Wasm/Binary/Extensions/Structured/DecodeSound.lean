module

public import Silmaril.Wasm.Binary.Extensions.Structured.Decode
public import Silmaril.Wasm.Binary.Core.DecodeSound

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.Structured.Decode

open Core Core.Decode

theorem readInstr_readSeq_sound {Leaf : Type} {G : Bytes → Leaf → Prop}
    (reader : Nat → DecodeM Leaf)
    (hreader : ∀ op : UInt8, Sound (fun pre i => G ([op] ++ pre) i) (reader op.toNat))
    (fuel : Nat) :
    (∀ op : UInt8, Sound (fun pre i => Instr Forms.all G ([op] ++ pre) i) (readInstr reader fuel op.toNat)) ∧
    Sound (fun pre (r : List (Wasm.Extensions.Structured.Instr Leaf) × UInt8) =>
      (r.2 = 0x0B ∨ r.2 = 0x05) ∧ ∃ b, pre = b ++ [r.2] ∧ Instrs Forms.all G b r.1) (readSeq reader fuel) := by
  induction fuel with
  | zero =>
    constructor
    · intro op c a c' h
      exact (decodeError_ok h).elim
    · intro c a c' h
      exact (decodeError_ok h).elim
  | succ fuel ih =>
    obtain ⟨hi, hs⟩ := ih
    constructor
    · intro op c a c' h
      simp only [readInstr] at h
      split at h
      · rename_i hop
        have hop : op = 0x02 := UInt8.toNat_inj.mp hop
        subst op
        obtain ⟨t, cm, ht, h⟩ := run_bind_ok h
        obtain ⟨⟨body, term⟩, cn, hseq, h⟩ := run_bind_ok h
        dsimp only at h
        split at h
        · rename_i he
          have he : term = 0x0B := by simpa using he
          subst term
          obtain ⟨rfl, rfl⟩ := run_pure_ok h
          obtain ⟨hbt, bt, hr, hg⟩ := readBlockType_sound ht
          obtain ⟨hbs, bs, hr', _, bodyBytes, rfl, hbody⟩ := hs hseq
          refine ⟨hbs.trans hbt, bt ++ bodyBytes ++ [0x0B], ?_, ?_⟩
          · simp [hr, hr', List.append_assoc]
          · simpa only [List.append_assoc] using Instr.block hg hbody
        · exact (decodeError_ok h).elim
      · rename_i hop
        have hop : op = 0x03 := UInt8.toNat_inj.mp hop
        subst op
        obtain ⟨t, cm, ht, h⟩ := run_bind_ok h
        obtain ⟨⟨body, term⟩, cn, hseq, h⟩ := run_bind_ok h
        dsimp only at h
        split at h
        · rename_i he
          have he : term = 0x0B := by simpa using he
          subst term
          obtain ⟨rfl, rfl⟩ := run_pure_ok h
          obtain ⟨hbt, bt, hr, hg⟩ := readBlockType_sound ht
          obtain ⟨hbs, bs, hr', _, bodyBytes, rfl, hbody⟩ := hs hseq
          refine ⟨hbs.trans hbt, bt ++ bodyBytes ++ [0x0B], ?_, ?_⟩
          · simp [hr, hr', List.append_assoc]
          · simpa only [List.append_assoc] using Instr.loop hg hbody
        · exact (decodeError_ok h).elim
      · rename_i hop
        have hop : op = 0x04 := UInt8.toNat_inj.mp hop
        subst op
        obtain ⟨t, cm, ht, h⟩ := run_bind_ok h
        obtain ⟨⟨thn, term⟩, cn, hseq, h⟩ := run_bind_ok h
        dsimp only at h
        split at h
        · rename_i he
          have he : term = 0x0B := by simpa using he
          subst term
          obtain ⟨rfl, rfl⟩ := run_pure_ok h
          obtain ⟨hbt, bt, hr, hg⟩ := readBlockType_sound ht
          obtain ⟨hbs, bs, hr', _, bodyBytes, rfl, hbody⟩ := hs hseq
          refine ⟨hbs.trans hbt, bt ++ bodyBytes ++ [0x0B], ?_, ?_⟩
          · simp [hr, hr', List.append_assoc]
          · simpa only [List.append_assoc] using Instr.if_ hg hbody
        · rename_i he
          obtain ⟨⟨els, term'⟩, ce, hels, h⟩ := run_bind_ok h
          dsimp only at h
          split at h
          · rename_i he'
            have he' : term' = 0x0B := by simpa using he'
            subst term'
            obtain ⟨rfl, rfl⟩ := run_pure_ok h
            obtain ⟨hbt, bt, hr, hg⟩ := readBlockType_sound ht
            obtain ⟨hbs, bs, hr', hterm, thnBytes, rfl, hthn⟩ := hs hseq
            have hterm : term = 0x05 := hterm.resolve_left (by simpa using he)
            subst term
            obtain ⟨hbe, be, hre, _, elsBytes, rfl, helse⟩ := hs hels
            refine ⟨hbe.trans (hbs.trans hbt), bt ++ thnBytes ++ [0x05] ++ elsBytes ++ [0x0B], ?_, ?_⟩
            · simp [hr, hr', hre, List.append_assoc]
            · simpa only [List.append_assoc] using Instr.ifElse hg hthn helse
          · exact (decodeError_ok h).elim
      · rename_i hop
        have hop : op = 0x1F := UInt8.toNat_inj.mp hop
        subst op
        obtain ⟨t, cm, ht, h⟩ := run_bind_ok h
        obtain ⟨cs, cc, hc, h⟩ := run_bind_ok h
        obtain ⟨⟨body, term⟩, cn, hseq, h⟩ := run_bind_ok h
        dsimp only at h
        split at h
        · rename_i he
          have he : term = 0x0B := by simpa using he
          subst term
          obtain ⟨rfl, rfl⟩ := run_pure_ok h
          obtain ⟨hbt, bt, hr, hg⟩ := readBlockType_sound ht
          obtain ⟨hbc, bc, hrc, hgc⟩ := readVec_sound readCatch_sound hc
          obtain ⟨hbs, bs, hr', _, bodyBytes, rfl, hbody⟩ := hs hseq
          refine ⟨hbs.trans (hbc.trans hbt), bt ++ bc ++ bodyBytes ++ [0x0B], ?_, ?_⟩
          · simp [hr, hrc, hr', List.append_assoc]
          · simpa only [List.append_assoc] using Instr.tryTable hg hgc hbody
        · exact (decodeError_ok h).elim
      · exact sound_map (hreader op) Wasm.Extensions.Structured.Instr.leaf (fun _ _ hg => Instr.leaf hg) h
    · intro c a c' h
      simp only [readSeq] at h
      obtain ⟨b, cm, hb, h⟩ := run_bind_ok h
      obtain ⟨hbbytes, hbrest⟩ := readByte_ok hb
      split at h
      · rename_i hterm
        have hterm : b = 0x0B ∨ b = 0x05 := by simpa using hterm
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        exact ⟨hbbytes, [b], hbrest, hterm, [], rfl, Instrs.nil⟩
      · obtain ⟨i, ci, hi', h⟩ := run_bind_ok h
        obtain ⟨⟨is, term⟩, ce, hseq, h⟩ := run_bind_ok h
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        obtain ⟨hibytes, bi, hirest, hig⟩ := hi b hi'
        obtain ⟨hsbytes, bs, hsrest, hterm, bodyBytes, rfl, hbody⟩ := hs hseq
        refine ⟨hsbytes.trans (hibytes.trans hbbytes), [b] ++ bi ++ (bodyBytes ++ [term]), ?_,
          hterm, [b] ++ bi ++ bodyBytes, ?_, Instrs.cons hig hbody⟩
        · simp [hbrest, hirest, hsrest, List.append_assoc]
        · simp [List.append_assoc]

theorem readExpr_sound {Leaf : Type} {G : Bytes → Leaf → Prop}
    (reader : Nat → DecodeM Leaf)
    (hreader : ∀ op : UInt8, Sound (fun pre i => G ([op] ++ pre) i) (reader op.toNat)) :
    Sound (Expr Forms.all G) (readExpr reader) := by
  intro c a c' h
  obtain ⟨n, cm, hn, h⟩ := run_bind_ok (show (remaining >>= _).run c = _ from h)
  have hc : cm = c := by
    change Except.ok (_, c) = Except.ok (n, cm) at hn
    exact (Prod.mk.inj (Except.ok.inj hn)).2.symm
  subst cm
  obtain ⟨⟨is, term⟩, ce, hseq, h⟩ := run_bind_ok h
  dsimp only at h
  split at h
  · rename_i he
    have he : term = 0x0B := by simpa using he
    subst term
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, _, b, rfl, hg⟩ := (readInstr_readSeq_sound reader hreader (n + 1)).2 hseq
    exact ⟨hb, b ++ [0x0B], hr, Expr.mk hg⟩
  · exact (decodeError_ok h).elim


end Silmaril.Wasm.Binary.Extensions.Structured.Decode
