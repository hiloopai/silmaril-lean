module

public import Silmaril.X86.Features.Ext.SsePacked.Semantics
public import Silmaril.X86.Features.Embed

/-!
# The SSE/SSE2 packed lane as an extension

`SsePacked.ext` packages `Instr`, `byteDecoder`, `Instr.requires` and
`Instr.exec` as a `Features.Extension`.

* **Disjointness** (`disjoint_floatExt`, `pairwiseDisjoint`): no byte string
  is decoded both by this lane and by `floatExt` (`X86.Float`), so the list
  `[floatExt, ext]` is pairwise disjoint and first-match order is irrelevant.
  The proof reads the `X86.Float` encodings with this lane's field parser: the
  `0F`-map ones parse to fields `candidate` rejects (`candidate_float`), the
  `0F 3A` ones (ROUNDSS/SD) to opcode `3A`, which no instruction here has.
* **The integer decoder rejects every encoding** (`ext_decode_encode`):
  `Ext.parseRaw` fails on the prefix, REX, `0F` and opcode bytes of every form
  (`header_bad`, by kernel evaluation over the opcode table), and
  `Ext.good_parseRaw.bad` extends it to every continuation. With
  `step_of_decode` this gives the machine step of every instruction of the lane.
* **Pure forms**: the register forms of the integer, shuffle, move and
  mask-extraction instructions, and the fences and prefetches, are
  `Extension.Pure` (`pure_*`).
-/

@[expose] public section

namespace Silmaril.X86.Features.SsePacked

open Silmaril.Process (Memory)
open Silmaril.X86 (XReg Mem Reg Byte Prefix rexBytes fetchWindow maxInstrLength Word)

/-- The legacy SSE/SSE2 packed and integer SIMD instructions. -/
def ext : Extension where
  name := "SSE/SSE2 packed and integer SIMD (legacy encoding)"
  Syntax := Instr
  decoder := byteDecoder
  requires := Instr.requires
  exec := Instr.exec

@[simp] theorem ext_decode : ext.decoder.decode = decode := rfl

theorem ext_requires (i : Instr) : ext.requires i = i.requires := rfl

theorem ext_exec (i : Instr) (n : Nat) (s : State) (memory : Memory) :
    ext.exec i n s memory = i.exec n s memory := rfl

/-! ## Disjointness from `X86.Float` -/

/-- An `X86.Float` field record read as this lane's fields. -/
def ofFloatRaw (r : X86.Raw) : PRaw := ⟨r.pfx, r.w, r.opc, r.reg, .ofOperand r.rm, r.imm⟩

theorem bytes_ofFloatRaw {r : X86.Raw} (h : r.map = .m0F) : (ofFloatRaw r).bytes = r.bytes := by
  obtain ⟨pfx, w, map, opc, reg, rm, imm⟩ := r
  subst h
  simp [PRaw.bytes, X86.Raw.bytes, PRaw.rex, X86.Raw.rex, ofFloatRaw, X86.OpMap.bytes]

theorem wellFormed_float (i : Float.Instr) (h : (Float.toRaw i).map = .m0F) :
    (ofFloatRaw (Float.toRaw i)).WellFormed := by
  unfold PRaw.WellFormed
  cases i with
  | arith op => cases op <;> rfl
  | logic op => cases op <;> rfl
  | round => cases h
  | _ => rfl

/-- `candidate` rejects the fields of every `0F`-map `X86.Float` instruction. -/
theorem candidate_float (i : Float.Instr) (h : (Float.toRaw i).map = .m0F) :
    candidate (ofFloatRaw (Float.toRaw i)) = none := by
  cases i with
  | movs p | load p | store p | movap p =>
    cases p <;> rfl
  | movToX | movFromX => rfl
  | arith op p _ src =>
    cases op <;> cases p <;> cases src <;> rfl
  | sqrt p _ src | cvtToIntTrunc p _ _ src | cvtToInt p _ _ src | cvtPrec p _ src
  | ucomi p _ src | comi p _ src =>
    cases p <;> cases src <;> rfl
  | cvtFromInt p _ _ src => cases p <;> cases src <;> rfl
  | logic op p _ src => cases op <;> cases p <;> cases src <;> rfl
  | cmp p _ _ src => cases p <;> cases src <;> rfl
  | round => cases h
  | ldmxcsr | stmxcsr => rfl

theorem toRaw_opc_ne_3A (i : Instr) : (toRaw i).opc ≠ 0x3A#8 := by
  cases i with
  | load k | store k => cases k <;> exact ne_of_beq_false rfl
  | movReg k => cases k <;> exact ne_of_beq_false rfl
  | storeNT k => cases k <;> exact ne_of_beq_false rfl
  | movmsk k => cases k <;> exact ne_of_beq_false rfl
  | movHalfLoad high pd | movHalfStore high pd => cases high <;> exact ne_of_beq_false rfl
  | pint op => cases op <;> exact ne_of_beq_false rfl
  | pshiftImm op => cases op <;> exact ne_of_beq_false rfl
  | arithp op => cases op <;> exact ne_of_beq_false rfl
  | logicRip op => cases op <;> exact ne_of_beq_false rfl
  | unpckp high => cases high <;> exact ne_of_beq_false rfl
  | cvtp k => cases k <;> exact ne_of_beq_false rfl
  | approx k => cases k <;> exact ne_of_beq_false rfl
  | _ => exact ne_of_beq_false rfl

/-- No byte string is decoded both by this lane and by `X86.Float`. -/
theorem disjoint_float (bytes : List Byte) : decode bytes = none ∨ Float.decode bytes = none := by
  rcases h1 : decode bytes with _ | ⟨x, n⟩
  · exact Or.inl rfl
  rcases h2 : Float.decode bytes with _ | ⟨i, k⟩
  · exact Or.inr rfl
  exfalso
  obtain ⟨-, -, hx⟩ := decode_sound h1
  obtain ⟨-, -, hi⟩ := Float.decode_sound h2
  have hp : PRaw.parse bytes = some (toRaw x, bytes.drop n) := by
    conv => lhs; rw [hx]
    exact PRaw.parse_bytes _ (toRaw_wellFormed x) _
  by_cases hm : (Float.toRaw i).map = .m0F
  · have hq : PRaw.parse bytes = some (ofFloatRaw (Float.toRaw i), bytes.drop k) := by
      conv => lhs; rw [hi, Float.encode, ← bytes_ofFloatRaw hm]
      exact PRaw.parse_bytes _ (wellFormed_float i hm) _
    rw [hp] at hq
    have heq : toRaw x = ofFloatRaw (Float.toRaw i) := (Prod.mk.inj (Option.some.inj hq)).1
    have := candidate_toRaw x
    rw [heq, candidate_float i hm] at this
    cases this
  · cases i with
    | round p dst src ctrl =>
      rw [hi] at hp
      simp only [Float.encode, Float.toRaw, X86.Raw.bytes, X86.OpMap.bytes, List.cons_append,
        List.nil_append, List.append_assoc] at hp
      exact toRaw_opc_ne_3A x (PRaw.parse_opc hp)
    | arith op => cases op <;> exact hm rfl
    | logic op => cases op <;> exact hm rfl
    | _ => exact hm rfl

theorem disjoint_floatExt : Extension.Disjoint ext floatExt := disjoint_float

theorem disjoint_floatExt' : Extension.Disjoint floatExt ext := fun bytes =>
  (disjoint_float bytes).symm

/-- `[floatExt, ext]` is pairwise disjoint. -/
theorem pairwiseDisjoint : Extension.PairwiseDisjoint [floatExt, ext] := by
  simp only [Extension.PairwiseDisjoint, List.pairwise_cons, List.mem_cons,
    or_false, forall_eq, List.not_mem_nil, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
    implies_true]
  exact disjoint_floatExt'

/-! ## The integer decoder rejects every encoding -/

/-- The prefix, REX, `0F` and opcode bytes. -/
def PRaw.header (r : PRaw) : List Byte := r.pfx.bytes ++ rexBytes r.rex ++ [0x0F#8, r.opc]

theorem PRaw.bytes_eq_header (r : PRaw) :
    r.bytes = r.header ++ (r.rm.bytes (X86.nibbleLo r.reg) ++ r.imm.toList) := by
  simp [PRaw.bytes, PRaw.header]

/-- Every mandatory prefix and opcode of the lane. -/
def opcTable : List (Prefix × Byte) :=
  [(.none, 0x10), (.none, 0x11), (.none, 0x12), (.none, 0x13), (.none, 0x14), (.none, 0x15),
   (.none, 0x16), (.none, 0x17), (.none, 0x18), (.none, 0x28), (.none, 0x29), (.none, 0x2B),
   (.none, 0x50), (.none, 0x51), (.none, 0x52), (.none, 0x53), (.none, 0x54), (.none, 0x55),
   (.none, 0x56), (.none, 0x57), (.none, 0x58), (.none, 0x59), (.none, 0x5A), (.none, 0x5B),
   (.none, 0x5C), (.none, 0x5D), (.none, 0x5E), (.none, 0x5F), (.none, 0xAE), (.none, 0xC2),
   (.none, 0xC6),
   (.pF3, 0x52), (.pF3, 0x53), (.pF3, 0x5B), (.pF3, 0x6F), (.pF3, 0x70), (.pF3, 0x7E),
   (.pF3, 0x7F), (.pF3, 0xE6),
   (.pF2, 0x70), (.pF2, 0xE6),
   (.p66, 0x10), (.p66, 0x11), (.p66, 0x12), (.p66, 0x13), (.p66, 0x14), (.p66, 0x15),
   (.p66, 0x16), (.p66, 0x17), (.p66, 0x28), (.p66, 0x29), (.p66, 0x2B), (.p66, 0x50),
   (.p66, 0x51), (.p66, 0x54), (.p66, 0x55), (.p66, 0x56), (.p66, 0x57), (.p66, 0x58),
   (.p66, 0x59), (.p66, 0x5A), (.p66, 0x5B), (.p66, 0x5C), (.p66, 0x5D), (.p66, 0x5E),
   (.p66, 0x5F), (.p66, 0x60), (.p66, 0x61), (.p66, 0x62), (.p66, 0x63), (.p66, 0x64),
   (.p66, 0x65), (.p66, 0x66), (.p66, 0x67), (.p66, 0x68), (.p66, 0x69), (.p66, 0x6A),
   (.p66, 0x6B), (.p66, 0x6C), (.p66, 0x6D), (.p66, 0x6E), (.p66, 0x6F), (.p66, 0x70),
   (.p66, 0x71), (.p66, 0x72), (.p66, 0x73), (.p66, 0x74), (.p66, 0x75), (.p66, 0x76),
   (.p66, 0x7E), (.p66, 0x7F), (.p66, 0xC2), (.p66, 0xC4), (.p66, 0xC5), (.p66, 0xC6),
   (.p66, 0xD1), (.p66, 0xD2), (.p66, 0xD3), (.p66, 0xD4), (.p66, 0xD5), (.p66, 0xD6),
   (.p66, 0xD7), (.p66, 0xD8), (.p66, 0xD9), (.p66, 0xDA), (.p66, 0xDB), (.p66, 0xDC),
   (.p66, 0xDD), (.p66, 0xDE), (.p66, 0xDF), (.p66, 0xE0), (.p66, 0xE1), (.p66, 0xE2),
   (.p66, 0xE3), (.p66, 0xE4), (.p66, 0xE5), (.p66, 0xE6), (.p66, 0xE7), (.p66, 0xE8),
   (.p66, 0xE9), (.p66, 0xEA), (.p66, 0xEB), (.p66, 0xEC), (.p66, 0xED), (.p66, 0xEE),
   (.p66, 0xEF), (.p66, 0xF1), (.p66, 0xF2), (.p66, 0xF3), (.p66, 0xF4), (.p66, 0xF5),
   (.p66, 0xF6), (.p66, 0xF7), (.p66, 0xF8), (.p66, 0xF9), (.p66, 0xFA), (.p66, 0xFB),
   (.p66, 0xFC), (.p66, 0xFD), (.p66, 0xFE)]

theorem toRaw_mem_opcTable (i : Instr) : ((toRaw i).pfx, (toRaw i).opc) ∈ opcTable := by
  cases i with
  | load k | store k => cases k <;> exact of_decide_eq_true rfl
  | movReg k => cases k <;> exact of_decide_eq_true rfl
  | storeNT k => cases k <;> exact of_decide_eq_true rfl
  | movmsk k => cases k <;> exact of_decide_eq_true rfl
  | movHalfLoad high pd | movHalfStore high pd => cases high <;> cases pd <;> exact of_decide_eq_true rfl
  | pint op => cases op <;> exact of_decide_eq_true rfl
  | pshiftImm op => cases op <;> exact of_decide_eq_true rfl
  | pshuf k => cases k <;> exact of_decide_eq_true rfl
  | arithp op p => cases op <;> cases p <;> exact of_decide_eq_true rfl
  | sqrtp p | cmpp p | shufp p => cases p <;> exact of_decide_eq_true rfl
  | logicRip op p => cases op <;> cases p <;> exact of_decide_eq_true rfl
  | unpckp high p => cases high <;> cases p <;> exact of_decide_eq_true rfl
  | cvtp k => cases k <;> exact of_decide_eq_true rfl
  | approx k => cases k <;> exact of_decide_eq_true rfl
  | _ => exact of_decide_eq_true rfl

def isBad {α : Type} : Ext.PResult α → Bool
  | .bad => true
  | _ => false

theorem isBad_iff {α : Type} {r : Ext.PResult α} : isBad r = true ↔ r = .bad := by
  cases r <;> simp [isBad]

/-- The integer length decoder rejects every header of the lane. -/
theorem header_bad : ∀ p ∈ opcTable, ∀ n : BitVec 4,
    isBad (Ext.parseRaw (p.1.bytes ++ rexBytes n ++ [0x0F#8, p.2])) = true := by
  decide +kernel

/-- The integer decoder rejects every encoding, whatever follows it. -/
theorem ext_decode_encode (i : Instr) (more : List Byte) : Ext.decode (encode i ++ more) = none := by
  have h := isBad_iff.mp (header_bad _ (toRaw_mem_opcTable i) (toRaw i).rex)
  simp only at h
  have hb : encode i ++ more =
      (toRaw i).header ++ ((toRaw i).rm.bytes (X86.nibbleLo (toRaw i).reg) ++ (toRaw i).imm.toList
        ++ more) := by
    rw [encode, PRaw.bytes_eq_header]; simp
  unfold Ext.decode
  rw [hb, PRaw.header, Ext.good_parseRaw.bad h]

theorem ext_decode_of_decode {bytes : List Byte} {i : Instr} {n : Nat}
    (h : decode bytes = some (i, n)) : Ext.decode bytes = none := by
  obtain ⟨-, -, hb⟩ := decode_sound h
  rw [hb]
  exact ext_decode_encode i _

/-- The machine step at an instruction of this lane, for any pairwise disjoint
extension list containing `ext`. -/
theorem step_of_decode {F : FeatureSet} {exts : List Extension} {exit : Word} {m : MState}
    {i : Instr} {n : Nat} (hd : Extension.PairwiseDisjoint exts) (he : ext ∈ exts)
    (hdec : decode (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) = some (i, n))
    (hperm : m.memory.Permitted .execute m.state.core.rip.toNat n) :
    step F exts exit m = extStep F ext i n m :=
  step_of_ext (ext_decode_of_decode hdec) (extDecode_of_mem hd he (x := (i : ext.Syntax)) hdec)
    hperm

/-! ## Pure register forms -/

theorem pure_movReg (k : RegMov) (dst src : XReg) : ext.Pure (Instr.movReg k dst src) :=
  Extension.Pure.of_eq _ (fun s => s.writeXmmLegacy dst.toV (s.xmm src.toV)) (fun _ => rfl)
    (fun _ _ _ => rfl)

theorem pure_pint (op : PIntOp) (dst src : XReg) : ext.Pure (Instr.pint op dst (.reg src)) :=
  Extension.Pure.of_eq _
    (fun s => s.writeXmmLegacy dst.toV (op.eval (s.xmm dst.toV) (s.xmm src.toV)))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem pure_pshiftImm (op : PShiftOp) (dst : XReg) (imm : Byte) :
    ext.Pure (Instr.pshiftImm op dst imm) :=
  Extension.Pure.of_eq _ (fun s => s.writeXmmLegacy dst.toV (op.eval imm (s.xmm dst.toV)))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem pure_pshuf (k : ShufKind) (dst src : XReg) (imm : Byte) :
    ext.Pure (Instr.pshuf k dst (.reg src) imm) :=
  Extension.Pure.of_eq _ (fun s => s.writeXmmLegacy dst.toV (k.eval imm (s.xmm src.toV)))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem pure_unpckp (high : Bool) (p : Float.Precision) (dst src : XReg) :
    ext.Pure (Instr.unpckp high p dst (.reg src)) :=
  Extension.Pure.of_eq _
    (fun s => s.writeXmmLegacy dst.toV (unpack p.width high (s.xmm dst.toV) (s.xmm src.toV)))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem pure_shufp (p : Float.Precision) (dst src : XReg) (imm : Byte) :
    ext.Pure (Instr.shufp p dst (.reg src) imm) :=
  Extension.Pure.of_eq _
    (fun s => s.writeXmmLegacy dst.toV (shufpEval p imm (s.xmm dst.toV) (s.xmm src.toV)))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem pure_movqLoad (dst src : XReg) : ext.Pure (Instr.movqLoad dst (.reg src)) :=
  Extension.Pure.of_eq _
    (fun s => s.writeXmmLegacy dst.toV (((s.xmm src.toV).extractLsb' 0 64).setWidth 128))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem pure_movhlps (dst src : XReg) : ext.Pure (Instr.movhlps dst src) :=
  Extension.Pure.of_eq _
    (fun s => s.writeXmmLegacy dst.toV
      ((s.xmm dst.toV).extractLsb' 64 64 ++ (s.xmm src.toV).extractLsb' 64 64))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem pure_movlhps (dst src : XReg) : ext.Pure (Instr.movlhps dst src) :=
  Extension.Pure.of_eq _
    (fun s => s.writeXmmLegacy dst.toV
      ((s.xmm src.toV).extractLsb' 0 64 ++ (s.xmm dst.toV).extractLsb' 0 64))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem pure_movmsk (k : MskKind) (dst : Reg) (src : XReg) : ext.Pure (Instr.movmsk k dst src) :=
  Extension.Pure.of_eq _
    (fun s => State.writeGpr32 s dst (BitVec.ofNat 32 (signMask k.width (s.xmm src.toV))))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem pure_pextrw (dst : Reg) (src : XReg) (imm : Byte) : ext.Pure (Instr.pextrw dst src imm) :=
  Extension.Pure.of_eq _
    (fun s => State.writeGpr32 s dst ((lane 16 (imm.toNat % 8) (s.xmm src.toV)).setWidth 32))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem pure_pinsrw (dst : XReg) (src : Reg) (imm : Byte) :
    ext.Pure (Instr.pinsrw dst (.reg src) imm) :=
  Extension.Pure.of_eq _
    (fun s => s.writeXmmLegacy dst.toV (ofLanes 16 fun j =>
      if j = imm.toNat % 8 then ((s.core.read src).extractLsb' 0 16).toNat
      else (lane 16 j (s.xmm dst.toV)).toNat))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem pure_fence (k : FenceKind) : ext.Pure (Instr.fence k) :=
  Extension.Pure.of_eq _ id (fun _ => rfl) (fun _ _ _ => rfl)

theorem pure_prefetch (h : PrefetchHint) (a : Addr) : ext.Pure (Instr.prefetch h a) :=
  Extension.Pure.of_eq _ id (fun _ => rfl) (fun _ _ _ => rfl)

end Silmaril.X86.Features.SsePacked
