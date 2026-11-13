module

public import Silmaril.X86.Features.Ext.IntMerged.Agree

/-!
# The merged integer extension

`intMerged` is the one integer extension that both integer lanes embed into:

* `intRest`: the int-ext lane without the forms baseint also has
  (`IntExt.ext.restrict`, by `IntExt.Instr.isBase`): BMI1, BMI2, ADX, MOVBE,
  IMUL imm/one-operand, TEST imm, BSF/BSR, XADD and CMPXCHG.
* `BaseInt.baseIntExt`: ADC/SBB, the 16-bit ALU, SHLD/SHRD and BTx at 16, 32
  and 64 bits, PUSH imm and `repz ret`. It is canonical for the overlap.
* `disjoint_rest_baseInt`: the two never decode the same bytes, so their union
  `intMerged = intRest.union baseIntExt` is an extension
  (`Extension.union`).

The embeddings are the lattice facts: `intExt_embeds` (the whole recovered
int-ext lane, its overlap forms sent to baseint by `toBase?`, which is exact
by `encode_toBase` and `exec_toBase`) and `baseInt_embeds`. With
`run_intExt`, `run_baseInt` and `run_floatExt_intExt`, a run proved with
either lane (or with any sub-family) is the same run with `intMerged`, as long
as the larger list stays pairwise disjoint; `pairwiseDisjoint_merged_float`
supplies that for `[intMerged, floatExt]`.

`ext_decode_none`: the integer decoder `X86.Ext` rejects every encoding
`intMerged` accepts, so `step_of_ext` applies.
-/

@[expose] public section

namespace Silmaril.X86.Features.IntMerged

open Silmaril.X86 (Byte Reg Word fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Sz RM Rex segBytes rexBytes modrmBytes)
open Silmaril.Process (Memory)

/-! ## Agreement, assembled -/

theorem exec_toBase {i : IntExt.Instr} {x : BaseInt.Instr} (h : i.toBase? = some x) (n : Nat)
    (s : State) (m : Memory) : BaseInt.exec x n s m = IntExt.exec i n s m := by
  cases i <;> simp only [IntExt.Instr.toBase?, Option.some.injEq, reduceCtorEq] at h <;> subst h
  · exact exec_carry ..
  · exact exec_carryR ..
  · exact exec_carryI ..
  · exact exec_carryI8 ..
  · exact exec_carryA ..
  · exact exec_pushI ..
  · exact exec_pushI8 ..
  · exact exec_bit ..
  · exact exec_bitI ..
  · exact exec_shd ..

theorem requires_toBase {i : IntExt.Instr} {x : BaseInt.Instr} (h : i.toBase? = some x) :
    IntExt.ext.requires i = BaseInt.baseIntExt.requires x := by
  cases i <;> simp only [IntExt.Instr.toBase?, Option.some.injEq, reduceCtorEq] at h <;> rfl

/-- On the overlap, baseint decodes whatever int-ext decodes, to the
corresponding instruction and with the same length. -/
theorem decode_toBase {bytes : List Byte} {i : IntExt.Instr} {n : Nat} {x : BaseInt.Instr}
    (hd : IntExt.decode bytes = some (i, n)) (h : i.toBase? = some x) :
    BaseInt.decode bytes = some (x, n) := by
  obtain ⟨rfl, rest, rfl⟩ := IntExt.decode_sound hd
  rw [encode_toBase h]
  exact BaseInt.decode_eq_some_iff.mpr ⟨rfl, rest, rfl⟩

/-- And conversely, on the 32/64-bit forms. -/
theorem decode_toIntExt {bytes : List Byte} {x : BaseInt.Instr} {n : Nat} {i : IntExt.Instr}
    (hd : BaseInt.decode bytes = some (x, n)) (h : x.toIntExt? = some i) :
    IntExt.decode bytes = some (i, n) := by
  obtain ⟨rfl, rest, rfl⟩ := BaseInt.decode_eq_some_iff.mp hd
  rw [← encode_toBase (toBase?_toIntExt? h)]
  exact IntExt.decode_encode_append i rest

/-- The overlap forms of int-ext embed into baseint, exactly. -/
theorem overlap_embeds : (IntExt.ext.restrict IntExt.Instr.isBase).Embeds BaseInt.baseIntExt := by
  refine ⟨fun i => i.1.toBase?.get (Option.isSome_iff_ne_none.mp i.2 |> Option.ne_none_iff_isSome.mp),
    fun bytes i n hd => ?_, fun i => ?_, fun i n s m => ?_⟩
  · have h := Option.some_get (Option.ne_none_iff_isSome.mp (Option.isSome_iff_ne_none.mp i.2))
    exact decode_toBase (Extension.restrict_decode_eq_some.mp hd) h.symm
  · exact (requires_toBase (Option.some_get _).symm).symm
  · exact exec_toBase (Option.some_get _).symm n s m

/-- The 32/64-bit forms of baseint embed into int-ext, exactly. -/
theorem wide_embeds :
    (BaseInt.baseIntExt.restrict fun x => x.toIntExt?.isSome).Embeds IntExt.ext := by
  refine ⟨fun x => x.1.toIntExt?.get x.2, fun bytes x n hd => ?_, fun x => ?_, fun x n s m => ?_⟩
  · exact decode_toIntExt (Extension.restrict_decode_eq_some.mp hd) (Option.some_get _).symm
  · exact requires_toBase (toBase?_toIntExt? (Option.some_get _).symm)
  · exact (exec_toBase (toBase?_toIntExt? (Option.some_get _).symm) n s m).symm

/-! ## Int-ext rejects the 16-bit forms and `repz ret` -/

/-- A legacy head with an `66` or `F3` prefix on the one-byte or `0F` map has
no int-ext instruction. -/
theorem ofRaw_eq_none {r : IntExt.Raw}
    (he : ∃ rex, r.enc = .legacy .p66 rex ∨ r.enc = .legacy .pF3 rex)
    (hm : r.map = .one ∨ r.map = .m0F) : IntExt.ofRaw r = none := by
  obtain ⟨fs, enc, map, opc, modrm, imm⟩ := r
  obtain ⟨rex, he | he⟩ := he <;> simp only at he hm <;> subst he <;>
    rcases hm with rfl | rfl <;> rcases modrm with _ | ⟨m, sib, d⟩ <;> cases imm <;> rfl

theorem parse_head {bytes : List Byte} {r : IntExt.Raw} {u : List Byte}
    (h : IntExt.parse bytes = some (r, u)) :
    ∃ v, IntExt.parseHead (IntExt.parseSeg bytes).2 = some (r.enc, r.map, v) := by
  unfold IntExt.parse at h
  split at h
  · cases h
  · rename_i enc map v hh
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · split at h
          · cases h
            exact ⟨_, hh⟩
          · cases h
        · cases h

/-- The legacy bytes of an `Ext.Raw` with an `66` or `F3` prefix read as an
int-ext head, which no int-ext instruction has. -/
theorem guess_eq_none (r : Ext.Raw) (hp : r.pfx = .opsize ∨ r.pfx = .rep)
    (hopc : match r.opc with
      | .one b => IntExt.OpcOk .one b
      | .two b => IntExt.OpcOk .m0F b) (rest : List Byte) :
    IntExt.guess (r.bytes ++ rest) = none := by
  obtain ⟨fs, pfx, rex, opc, modrm, imm⟩ := r
  obtain ⟨p, hpb, hp'⟩ : ∃ p : IntExt.Pfx, pfx.bytes = p.bytes ∧ (p = .p66 ∨ p = .pF3) := by
    rcases hp with h | h <;> simp only at h <;> subst h
    exacts [⟨.p66, rfl, .inl rfl⟩, ⟨.pF3, rfl, .inr rfl⟩]
  obtain ⟨map, b, hob, hok, hm'⟩ : ∃ (map : IntExt.Map) (b : Byte), opc.bytes = map.bytes ++ [b] ∧
      IntExt.OpcOk map b ∧ (map = .one ∨ map = .m0F) := by
    cases opc with
    | one b => exact ⟨.one, b, rfl, hopc, .inl rfl⟩
    | two b => exact ⟨.m0F, b, rfl, hopc, .inr rfl⟩
  have hb : (Ext.Raw.bytes ⟨fs, pfx, rex, opc, modrm, imm⟩) ++ rest =
      segBytes fs ++ ((IntExt.Enc.legacy p rex).bytes map ++ b :: (modrmBytes modrm ++ imm.bytes ++ rest)) := by
    simp [Ext.Raw.bytes, IntExt.Enc.bytes, hpb, hob]
  have hhead := IntExt.parseHead_bytes (.legacy p rex) map b (modrmBytes modrm ++ imm.bytes ++ rest)
    hok (fun _ h => by cases h)
  have hseg := IntExt.parseSeg_bytes fs (.legacy p rex) map b (modrmBytes modrm ++ imm.bytes ++ rest) hok
  rw [hb]
  unfold IntExt.guess
  cases hparse : IntExt.parse (segBytes fs ++ ((IntExt.Enc.legacy p rex).bytes map ++
      b :: (modrmBytes modrm ++ imm.bytes ++ rest))) with
  | none => rfl
  | some ru =>
    obtain ⟨r, u⟩ := ru
    obtain ⟨v, hv⟩ := parse_head hparse
    rw [hseg, hhead] at hv
    simp only [Option.some.injEq, Prod.mk.injEq] at hv
    obtain ⟨he, hm, -⟩ := hv
    refine ofRaw_eq_none ⟨rex, ?_⟩ (hm ▸ hm')
    rcases hp' with rfl | rfl
    · exact .inl he.symm
    · exact .inr he.symm

/-- Int-ext decodes none of the baseint forms outside the overlap. -/
theorem intExt_decode_narrow {x : BaseInt.Instr} (hx : x.toIntExt? = none) (rest : List Byte) :
    IntExt.decode (BaseInt.encode x ++ rest) = none := by
  have hg : IntExt.guess (BaseInt.encode x ++ rest) = none := by
    rcases toIntExt?_eq_none hx with h | ⟨left, dst, src, count, rfl⟩ | ⟨op, dst, src, rfl⟩ | rfl
    · cases x with
      | alu16 op form =>
        refine guess_eq_none _ ?_ ?_ rest <;>
          cases form <;> cases op <;> simp [BaseInt.toRaw, BaseInt.formRaw, Ext.rmRaw, BaseInt.accRaw,
            BaseInt.Op.opRM, BaseInt.Op.opR, BaseInt.Op.opA, IntExt.OpcOk] <;> decide
      | _ => simp [BaseInt.Instr.isAlu16] at h
    · refine guess_eq_none _ ?_ ?_ rest <;>
        cases left <;> cases count <;>
          simp [BaseInt.toRaw, Ext.rmRaw, BaseInt.Width.pfx, BaseInt.shdOpcode, IntExt.OpcOk]
    · refine guess_eq_none _ ?_ ?_ rest <;>
        cases src <;> cases op <;>
          simp [BaseInt.toRaw, Ext.rmRaw, BaseInt.Width.pfx, BaseInt.BtOp.opcode, IntExt.OpcOk]
    · refine guess_eq_none _ ?_ ?_ rest
      · simp [BaseInt.toRaw, BaseInt.accRaw]
      · simp only [BaseInt.toRaw, BaseInt.accRaw, IntExt.OpcOk]; decide
  unfold IntExt.decode IntExt.guessDecode
  rw [hg]

/-! ## The merged extension -/

/-- The int-ext forms outside the overlap. -/
def intRest : Extension := IntExt.ext.restrict fun i => !i.isBase

theorem disjoint_rest_baseInt : intRest.Disjoint BaseInt.baseIntExt := by
  intro bytes
  cases hb : BaseInt.decode bytes with
  | none => exact .inr hb
  | some r =>
    obtain ⟨x, k⟩ := r
    left
    obtain ⟨-, rest, rfl⟩ := BaseInt.decode_eq_some_iff.mp hb
    show Machine.restrictDecode IntExt.byteDecoder _ _ = none
    cases hx : x.toIntExt? with
    | none => exact Machine.restrictDecode_eq_none (intExt_decode_narrow hx rest)
    | some i =>
      have hi := toBase?_toIntExt? hx
      rw [← encode_toBase hi]
      simp [Machine.restrictDecode, IntExt.Instr.isBase, hi]

/-- The merged integer extension. -/
def intMerged : Extension := intRest.union BaseInt.baseIntExt disjoint_rest_baseInt

theorem baseInt_embeds : BaseInt.baseIntExt.Embeds intMerged :=
  Extension.Embeds.union_right _ _ _

theorem intRest_embeds : intRest.Embeds intMerged :=
  Extension.Embeds.union_left _ _ _

/-- The recovered int-ext lane embeds, whole, into the merged extension. -/
theorem intExt_embeds : IntExt.ext.Embeds intMerged := by
  let ι : IntExt.Instr → intMerged.Syntax := fun i =>
    match h : i.toBase? with
    | some x => .inr x
    | none => .inl ⟨i, by simp [IntExt.Instr.isBase, h]⟩
  refine ⟨ι, fun bytes i n hd => ?_, fun i => ?_, fun i n s m => ?_⟩
  · show Machine.unionDecode _ _ bytes = some (ι i, n)
    simp only [ι]
    split
    · rename_i x hx
      refine Machine.unionDecode_inr.mpr ⟨?_, decode_toBase hd hx⟩
      rcases disjoint_rest_baseInt bytes with h | h
      · exact h
      · rw [show BaseInt.baseIntExt.decoder.decode bytes = BaseInt.decode bytes from rfl,
          decode_toBase hd hx] at h
        cases h
    · rename_i hx
      exact Machine.unionDecode_inl.mpr
        (Extension.restrict_decode_eq_some.mpr (by simpa using hd))
  · simp only [ι]
    split
    · rename_i x hx; exact (requires_toBase hx).symm
    · rfl
  · simp only [ι]
    split
    · rename_i x hx; exact exec_toBase hx n s m
    · rfl

/-! ## Disjointness from the scalar SSE extension and the integer decoder -/

/-- The two-byte keys (`BaseInt.floatKey`) int-ext encodings can have: its `0F`
opcodes, and `38` for its `0F 38` forms. -/
def intKey (b : Byte) : Bool :=
  b == 0xBC#8 || b == 0xBD#8 || b == 0xA3#8 || b == 0xAB#8 || b == 0xB3#8 || b == 0xBB#8 ||
    b == 0xBA#8 || b == 0xA4#8 || b == 0xAC#8 || b == 0xA5#8 || b == 0xAD#8 || b == 0xC1#8 ||
    b == 0xB1#8 || b == 0x38#8

theorem floatKey_float_encode (j : Float.Instr) (t : List Byte) :
    ∃ b, BaseInt.floatKey (Float.encode j ++ t) = some b ∧ intKey b = false := by
  refine ⟨_, BaseInt.floatKey_float_raw _ t, ?_⟩
  cases j with
  | arith op => cases op <;> simp [Float.toRaw, Float.raw0F, Float.ArithOp.opcode, intKey]
  | logic op => cases op <;> simp [Float.toRaw, Float.raw0F, Float.LogicOp.opcode, intKey]
  | _ => simp [Float.toRaw, Float.raw0F, intKey]

/-- The key of an int-ext head. -/
def headKey (r : IntExt.Raw) : Option Byte :=
  if r.fs then none
  else
    match r.enc, r.map with
    | .legacy _ _, .m0F => some r.opc
    | .legacy _ _, .m0F38 => some 0x38#8
    | .legacy _ _, .m0F3A => some 0x3A#8
    | _, _ => none

theorem floatKey_intExt_raw {r : IntExt.Raw} (h : r.WF) (t : List Byte) :
    BaseInt.floatKey (r.bytes ++ t) = headKey r := by
  obtain ⟨⟨hm, spec, hs, -, -⟩, -⟩ := h
  have hopc : IntExt.OpcOk r.map r.opc := IntExt.opcOk_of_shape (by simp [hs])
  obtain ⟨fs, enc, map, opc, modrm, imm⟩ := r
  simp only at hopc
  have hx : ∀ x : Rex, x.byte.extractLsb' 4 4 = 4#4 ∧ x.byte ≠ 0x66#8 ∧ x.byte ≠ 0xF2#8 ∧
      x.byte ≠ 0xF3#8 ∧ x.byte ≠ 0x0F#8 := by
    intro x
    have h := Ext.isRex_byte x
    simp only [Ext.isRex, beq_iff_eq] at h
    refine ⟨h, ?_, ?_, ?_, ?_⟩ <;> intro he <;> rw [he] at h <;> exact absurd h (by decide)
  cases fs
  · cases enc with
    | vex v =>
      simp [IntExt.Raw.bytes, IntExt.Enc.bytes, headKey, BaseInt.floatKey, BaseInt.afterPfx,
        BaseInt.afterRex]
    | legacy p rex =>
      cases map <;> simp only [IntExt.OpcOk] at hopc <;> cases p <;> rcases rex with _ | x <;>
        simp_all [IntExt.Raw.bytes, IntExt.Enc.bytes, IntExt.Pfx.bytes, Ext.rexBytes, IntExt.Map.bytes,
          headKey, BaseInt.floatKey, BaseInt.afterPfx, BaseInt.afterRex, Ext.isRex]
  · simp [IntExt.Raw.bytes, segBytes, headKey, BaseInt.floatKey, BaseInt.afterPfx, BaseInt.afterRex]

theorem headKey_toRaw (i : IntExt.Instr) :
    headKey (IntExt.toRaw i) = none ∨ ∃ b, headKey (IntExt.toRaw i) = some b ∧ intKey b = true := by
  unfold headKey
  split
  · exact .inl rfl
  · cases i with
    | scan rev => cases rev <;> simp [IntExt.toRaw, IntExt.legacyRaw, intKey]
    | bit op => cases op <;> simp [IntExt.toRaw, IntExt.legacyRaw, IntExt.BitOp.opcode, intKey]
    | shd right sz dst src count =>
      cases right <;> cases count <;> simp [IntExt.toRaw, IntExt.legacyRaw, IntExt.shdOpcode, intKey]
    | _ => simp [IntExt.toRaw, IntExt.legacyRaw, IntExt.vexRaw, intKey]

/-- No byte string is decoded both by the int-ext lane and by `X86.Float`
(the theorem the int-ext lane's docstring announces). -/
theorem intExt_disjoint_floatExt : IntExt.ext.Disjoint floatExt := by
  intro bytes
  cases hi : IntExt.decode bytes with
  | none => exact .inl hi
  | some r =>
    right
    obtain ⟨i, n⟩ := r
    obtain ⟨-, rest, rfl⟩ := IntExt.decode_sound hi
    cases hf : Float.decode (IntExt.encode i ++ rest) with
    | none => exact hf
    | some r =>
      obtain ⟨j, k⟩ := r
      obtain ⟨-, -, hb⟩ := Float.decode_sound hf
      obtain ⟨b, hkey, hb'⟩ := floatKey_float_encode j ((IntExt.encode i ++ rest).drop k)
      rw [← hb, IntExt.encode, floatKey_intExt_raw (IntExt.toRaw_wf i)] at hkey
      rcases headKey_toRaw i with h | ⟨c, hc, hc'⟩
      · rw [h] at hkey; cases hkey
      · rw [hc] at hkey; cases hkey; rw [hc'] at hb'; cases hb'

theorem disjoint_floatExt : intMerged.Disjoint floatExt :=
  Extension.Disjoint.union _ (intExt_disjoint_floatExt.restrict_left _) BaseInt.disjoint_floatExt

theorem pairwiseDisjoint_merged_float : Extension.PairwiseDisjoint [intMerged, floatExt] :=
  List.pairwise_pair.mpr disjoint_floatExt

/-- The integer decoder rejects every encoding the merged extension accepts. -/
theorem ext_decode_none {bytes : List Byte} {z : intMerged.Syntax} {n : Nat}
    (h : intMerged.decoder.decode bytes = some (z, n)) : Ext.decode bytes = none := by
  cases z with
  | inl i =>
    have hd := Extension.restrict_decode_eq_some.mp (Machine.unionDecode_inl.mp h)
    exact IntExt.base_decode_none_of_decode hd
  | inr x => exact BaseInt.ext_decode_none (Machine.unionDecode_inr.mp h).2

/-! ## Transport -/

/-- A run proved with the int-ext lane is the same run with the merged
extension in its place. -/
theorem run_intExt {F : FeatureSet} {exit : Word} {initial : MState}
    (hdec : ∀ n m, run F [IntExt.ext] exit n initial = some m → Decodes [IntExt.ext] m) (n : Nat) :
    run F [intMerged] exit n initial = run F [IntExt.ext] exit n initial :=
  run_conservative (List.pairwise_singleton _ _)
    (fun _ he => ⟨intMerged, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp he]; exact intExt_embeds⟩) hdec n

/-- A run proved with the baseline-integer lane is the same run with the
merged extension in its place. -/
theorem run_baseInt {F : FeatureSet} {exit : Word} {initial : MState}
    (hdec : ∀ n m, run F [BaseInt.baseIntExt] exit n initial = some m →
      Decodes [BaseInt.baseIntExt] m) (n : Nat) :
    run F [intMerged] exit n initial = run F [BaseInt.baseIntExt] exit n initial :=
  run_conservative (List.pairwise_singleton _ _)
    (fun _ he => ⟨intMerged, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp he]; exact baseInt_embeds⟩) hdec n

/-- With scalar SSE as well: a run proved with either integer lane and
`floatExt` is the same with `[intMerged, floatExt]`. -/
theorem run_floatExt_intExt {F : FeatureSet} {exit : Word} {initial : MState}
    {e : Extension} (he : e = IntExt.ext ∨ e = BaseInt.baseIntExt)
    (hdec : ∀ n m, run F [e, floatExt] exit n initial = some m → Decodes [e, floatExt] m)
    (n : Nat) :
    run F [intMerged, floatExt] exit n initial = run F [e, floatExt] exit n initial := by
  refine run_conservative pairwiseDisjoint_merged_float (fun e' he' => ?_) hdec n
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he'
  rcases he' with rfl | rfl
  · refine ⟨intMerged, List.mem_cons_self .., ?_⟩
    rcases he with rfl | rfl
    · exact intExt_embeds
    · exact baseInt_embeds
  · exact ⟨floatExt, by simp, Extension.Embeds.refl _⟩

end Silmaril.X86.Features.IntMerged
