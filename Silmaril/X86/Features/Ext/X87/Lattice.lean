module

public import Silmaril.X86.Features.Ext.X87.Extension
public import Silmaril.X86.Features.Embed
public import Silmaril.X86.Features.Transport

/-!
# The x87 lane in the extension lattice

The facts the feature-parametric machine needs to use `Fpu.ext` next to other
extensions, so that `step_of_ext`, `run_conservative` and
`FeatureFree.same_behaviour` apply to x87 code:

* `ext_decode_encode`, `ext_decode_of_decode`: the integer decoder rejects
  every x87 encoding, whatever follows it (it rejects the head: an optional
  `64`, an optional REX and the escape byte `D8`–`DF`, or `9B`);
* `float_decode_encode`, `disjoint_float`, `float_disjoint`: no byte string
  decodes both as x87 and as scalar SSE (`X86.Float`), whose encodings all
  pass through `0F`; `pairwiseDisjoint` packages `[floatExt, Fpu.ext]`;
* `missing_requires`: on a processor with the FPU and SSE3 no x87
  instruction raises `featureUD`;
* `step_ext`: in any pairwise-disjoint extension list containing `Fpu.ext`, the
  machine executes the x87 instruction at RIP with `Fpu.exec`.

Larger configurations reuse these: an `Included`/pairwise-disjoint list that
contains `Fpu.ext` is a conservative extension of a smaller one
(`run_conservative`), and a run that never raises `featureUD` behaves the same
on every larger feature set (`FeatureFree.same_behaviour`).
-/

@[expose] public section

namespace Silmaril.X86.Features.Fpu

open Silmaril.X86 (Byte Word)
open Silmaril.X86.Ext (Rex segBytes)

/-! ## The integer decoder rejects the lane -/

private def isBad {α : Type} : Ext.PResult α → Bool
  | .bad => true
  | _ => false

private theorem isBad_iff {α : Type} {r : Ext.PResult α} : isBad r = true ↔ r = .bad := by
  cases r <;> simp [isBad]

/-- Every x87 head (segment override, REX, escape byte) is rejected by the
integer decoder as soon as it reads the escape byte. -/
private theorem heads_bad :
    ∀ fs : Bool, ∀ o : BitVec 3,
      isBad (Ext.parseRaw (segBytes fs ++ [escByte o])) = true ∧
        ∀ w r x b : Bool,
          isBad (Ext.parseRaw (segBytes fs ++ [(⟨w, r, x, b⟩ : Rex).byte, escByte o])) = true := by
  decide +kernel

private theorem wait_bad : Ext.parseRaw [0x9B#8] = .bad := isBad_iff.mp (by decide)

private theorem head_bad (fs : Bool) (rex : Option Rex) (o : BitVec 3) :
    Ext.parseRaw (segBytes fs ++ Ext.rexBytes rex ++ [escByte o]) = .bad := by
  cases rex with
  | none => simpa [Ext.rexBytes] using isBad_iff.mp (heads_bad fs o).1
  | some x =>
    obtain ⟨w, r, xx, b⟩ := x
    simpa [Ext.rexBytes] using isBad_iff.mp ((heads_bad fs o).2 w r xx b)

/-- `Ext.decode` rejects every x87 encoding, whatever follows it. -/
theorem ext_decode_encode (i : Instr) (more : List Byte) : Ext.decode (encode i ++ more) = none := by
  unfold encode
  cases h : toRaw i with
  | wait =>
    unfold Ext.decode
    rw [show Raw.bytes .wait ++ more = [0x9B#8] ++ more from rfl,
      Ext.good_parseRaw.bad wait_bad]
  | esc fs rex o m sib d =>
    unfold Ext.decode
    rw [show Raw.bytes (.esc fs rex o m sib d) ++ more =
        (segBytes fs ++ Ext.rexBytes rex ++ [escByte o]) ++
          (Ext.modrmBytes (some (m, sib, d)) ++ more) by simp [Raw.bytes],
      Ext.good_parseRaw.bad (head_bad fs rex o)]

/-- Bytes the x87 decoder accepts are rejected by the integer decoder. -/
theorem ext_decode_of_decode {bytes : List Byte} {i : Instr} {n : Nat}
    (h : decode bytes = some (i, n)) : Ext.decode bytes = none := by
  rw [(decode_sound h).2]
  exact ext_decode_encode i _

/-! ## Disjointness from scalar SSE (`X86.Float`) -/

/-- A first byte that is neither a mandatory prefix, a REX prefix nor `0F`
ends `X86.Float`'s parse. -/
private theorem float_parse_head (b : Byte) (rest : List Byte)
    (hp : b ≠ 0x66#8 ∧ b ≠ 0xF2#8 ∧ b ≠ 0xF3#8) (hr : b.extractLsb' 4 4 ≠ 0x4#4)
    (h0 : b ≠ 0x0F#8) : _root_.Silmaril.X86.Raw.parse (b :: rest) = none := by
  obtain ⟨h1, h2, h3⟩ := hp
  simp [_root_.Silmaril.X86.Raw.parse, _root_.Silmaril.X86.parsePrefix,
    _root_.Silmaril.X86.parseRex, h1, h2, h3, hr, h0]

/-- A REX prefix followed by a byte other than `0F` ends the parse. -/
private theorem float_parse_rex (b c : Byte) (rest : List Byte)
    (hp : b ≠ 0x66#8 ∧ b ≠ 0xF2#8 ∧ b ≠ 0xF3#8) (hr : b.extractLsb' 4 4 = 0x4#4)
    (h0 : c ≠ 0x0F#8) : _root_.Silmaril.X86.Raw.parse (b :: c :: rest) = none := by
  obtain ⟨h1, h2, h3⟩ := hp
  by_cases hz : b.extractLsb' 0 4 = 0#4 <;>
    simp [_root_.Silmaril.X86.Raw.parse, _root_.Silmaril.X86.parsePrefix,
      _root_.Silmaril.X86.parseRex, h1, h2, h3, hr, hz, h0]

private theorem escByte_facts (o : BitVec 3) :
    (escByte o ≠ 0x66#8 ∧ escByte o ≠ 0xF2#8 ∧ escByte o ≠ 0xF3#8) ∧
      (escByte o).extractLsb' 4 4 ≠ 0x4#4 ∧ escByte o ≠ 0x0F#8 := by
  revert o; decide

private theorem rexByte_facts (x : Rex) :
    (x.byte ≠ 0x66#8 ∧ x.byte ≠ 0xF2#8 ∧ x.byte ≠ 0xF3#8) ∧ x.byte.extractLsb' 4 4 = 0x4#4 := by
  obtain ⟨w, r, xx, b⟩ := x
  revert w r xx b; decide

/-- `X86.Float.decode` rejects every x87 encoding, whatever follows it. -/
theorem float_decode_encode (i : Instr) (more : List Byte) :
    Float.decode (encode i ++ more) = none := by
  have hp : _root_.Silmaril.X86.Raw.parse (encode i ++ more) = none := by
    unfold encode
    cases toRaw i with
    | wait => exact float_parse_head _ _ (by decide) (by decide) (by decide)
    | esc fs rex o m sib d =>
      obtain ⟨he1, he2, he3⟩ := escByte_facts o
      cases fs with
      | true => exact float_parse_head _ _ (by decide) (by decide) (by decide)
      | false =>
        cases rex with
        | none => simpa [Raw.bytes, Ext.rexBytes] using float_parse_head (escByte o) _ he1 he2 he3
        | some x =>
          obtain ⟨hx1, hx2⟩ := rexByte_facts x
          simpa [Raw.bytes, Ext.rexBytes] using float_parse_rex x.byte (escByte o) _ hx1 hx2 he3
  unfold Float.decode
  rw [hp]

theorem float_decode_of_decode {bytes : List Byte} {i : Instr} {n : Nat}
    (h : decode bytes = some (i, n)) : Float.decode bytes = none := by
  rw [(decode_sound h).2]
  exact float_decode_encode i _

theorem disjoint_float : Extension.Disjoint ext floatExt := fun bytes => by
  cases h : decode bytes with
  | none => exact .inl h
  | some p => exact .inr (float_decode_of_decode (i := p.1) (n := p.2) h)

theorem float_disjoint : Extension.Disjoint floatExt ext := fun bytes =>
  (disjoint_float bytes).symm

theorem pairwiseDisjoint : Extension.PairwiseDisjoint [floatExt, ext] := by
  simp [Extension.PairwiseDisjoint, float_disjoint]

/-! ## Features -/

/-- With the FPU and SSE3 (every x86-64 processor since 2005 has both) no x87
instruction is missing a feature; without SSE3 only FISTTP is. -/
theorem missing_requires {F : FeatureSet} (hx : Feature.x87 ∈ F) (h3 : Feature.sse3 ∈ F)
    (i : Instr) : F.missing (ext.requires i) = none :=
  FeatureSet.missing_eq_none_iff.mpr fun f hf => by
    cases i <;> simp only [ext, requires, List.mem_cons,
      List.not_mem_nil, or_false] at hf <;> first | (subst hf; assumption) |
      (rcases hf with rfl | rfl <;> assumption)

theorem missing_requires_of_ne_fisttp {F : FeatureSet} (hx : Feature.x87 ∈ F) {i : Instr}
    (hi : ∀ f m, i ≠ .fisttp f m) : F.missing (ext.requires i) = none :=
  FeatureSet.missing_eq_none_iff.mpr fun f hf => by
    cases i <;> simp only [ext, requires, List.mem_cons,
      List.not_mem_nil, or_false] at hf <;> first | (subst hf; assumption) |
      exact absurd rfl (hi _ _)

/-! ## Stepping -/

/-- An x87 instruction at RIP, in any pairwise-disjoint extension list that
contains `Fpu.ext`, is executed by the lane. -/
theorem step_ext {F : FeatureSet} {exts : List Extension} {exit : Word} {m : MState}
    {i : Instr} {n : Nat} (hd : Extension.PairwiseDisjoint exts) (he : ext ∈ exts)
    (hdec : decode (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) = some (i, n))
    (hperm : m.memory.Permitted .execute m.state.core.rip.toNat n) :
    step F exts exit m = extStep F ext i n m :=
  step_of_ext (ext_decode_of_decode hdec) (extDecode_of_mem hd he (x := i) hdec) hperm

end Silmaril.X86.Features.Fpu
