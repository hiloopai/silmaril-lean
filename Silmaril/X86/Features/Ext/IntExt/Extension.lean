module

public import Silmaril.X86.Features.Ext.IntExt.Semantics
public import Silmaril.X86.Features.Embed

/-!
# Integer extensions: the extension

`ext` packages the lane for the feature-parametric machine.

* `requires` lists the CPUID feature of each form (SDM Vol. 2, the CPUID
  column of each opcode table): `bmi1` for ANDN, BEXTR and the BLS group,
  `bmi2` for BZHI, MULX, PDEP, PEXT, RORX, SARX, SHLX and SHRX, `adx` for
  ADCX/ADOX, `movbe` for MOVBE, and nothing for the baseline forms. None of the
  BMI instructions needs AVX or XCR0 state, although they are VEX-encoded.
* `ext_pure_*`: the register forms are `Extension.Pure` (they retire on every
  state and memory, do not touch memory and advance RIP by their length),
  except the ones that read a flag (ADC/SBB, ADCX/ADOX: chaos on an unknown
  flag) or have an undefined result (BSF/BSR of zero).
* `base_decode_none`: the integer decoder `Ext.decode` rejects every encoding
  of the lane whatever follows it, so `step_of_ext` applies (`step_ext`).
  Most encodings stop `Ext.parseRaw` at the opcode (`0F 38`, `C4`, opcodes the
  integer model lacks); `81 /2`, `81 /3`, `83 /2`, `83 /3`, `F7 /0` and `F7 /5`
  are parsed by the integer length decoder and rejected by its meaning
  function.
* `disjoint_floatExt`: no byte string is decoded both by `ext` and by the
  scalar SSE extension `floatExt`, in either order.
-/

@[expose] public section

namespace Silmaril.X86.Features.IntExt

open Silmaril.X86 (Byte Reg Word fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Sz RM Mem Rex segBytes)
open Silmaril.Process (Memory)

/-- The CPUID features of each form. -/
def Instr.requires : Instr → List Feature
  | .adx .. => [.adx]
  | .movbeLoad .. | .movbeStore .. => [.movbe]
  | .vop op .. =>
    match op with
    | .andn | .bextr => [.bmi1]
    | _ => [.bmi2]
  | .bls .. => [.bmi1]
  | .rorx .. => [.bmi2]
  | _ => []

/-- The integer-extension lane. -/
def ext : Extension where
  name := "int-ext: BMI1, BMI2, ADX, MOVBE and baseline integer forms"
  Syntax := Instr
  decoder := byteDecoder
  requires := Instr.requires
  exec := exec

@[simp] theorem ext_decode : ext.decoder.decode = decode := rfl
@[simp] theorem ext_requires (i : Instr) : ext.requires i = i.requires := rfl
@[simp] theorem ext_exec (i : Instr) (n : Nat) (s : State) (memory : Memory) :
    ext.exec i n s memory = exec i n s memory := rfl

/-! ## Pure register forms -/

theorem ext_pure_vop (op : Vop) (sz : Sz) (dst v r : Reg) :
    ext.Pure (Instr.vop op sz dst v (.reg r) : Instr) :=
  Extension.Pure.of_eq _ (fun s => s.setCore (vopCore op sz dst v (sz.read s.core r) s.core))
    (fun s => vopCore_rip op sz dst v _ s.core) (fun _ _ _ => rfl)

theorem ext_pure_bls (op : BlsOp) (sz : Sz) (dst r : Reg) :
    ext.Pure (Instr.bls op sz dst (.reg r) : Instr) :=
  Extension.Pure.of_eq _ (fun s => s.setCore (blsCore op sz dst (sz.read s.core r) s.core))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem ext_pure_rorx (sz : Sz) (dst r : Reg) (imm : BitVec 8) :
    ext.Pure (Instr.rorx sz dst (.reg r) imm : Instr) :=
  Extension.Pure.of_eq _
    (fun s => s.setCore (sz.write s.core dst ((sz.read s.core r).rotateRight (imm.toNat % sz.bits))))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem ext_pure_imulI (sz : Sz) (dst r : Reg) (imm : BitVec 32) :
    ext.Pure (Instr.imulI sz dst (.reg r) imm : Instr) :=
  Extension.Pure.of_eq _
    (fun s => s.setCore (imul3Core sz dst (sz.read s.core r) (imm.signExtend sz.bits) s.core))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem ext_pure_imulI8 (sz : Sz) (dst r : Reg) (imm : BitVec 8) :
    ext.Pure (Instr.imulI8 sz dst (.reg r) imm : Instr) :=
  Extension.Pure.of_eq _
    (fun s => s.setCore (imul3Core sz dst (sz.read s.core r) (imm.signExtend sz.bits) s.core))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem ext_pure_imul1 (sz : Sz) (r : Reg) : ext.Pure (Instr.imul1 sz (.reg r) : Instr) :=
  Extension.Pure.of_eq _ (fun s => s.setCore (imul1Core sz (sz.read s.core r) s.core))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem ext_pure_testI (sz : Sz) (r : Reg) (imm : BitVec 32) :
    ext.Pure (Instr.testI sz (.reg r) imm : Instr) :=
  Extension.Pure.of_eq _
    (fun s => s.setCore (setFlags s.core
      (Ext.logicFlagsN (sz.read s.core r &&& imm.signExtend sz.bits))))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem ext_pure_xadd (sz : Sz) (dst src : Reg) : ext.Pure (Instr.xadd sz dst src : Instr) :=
  Extension.Pure.of_eq _ (fun s => s.setCore (xaddCore sz dst src s.core))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem ext_pure_cmpxchg (sz : Sz) (dst src : Reg) : ext.Pure (Instr.cmpxchg sz dst src : Instr) :=
  Extension.Pure.of_eq _ (fun s => s.setCore (cmpxchgCore sz dst src s.core))
    (fun s => by simp only [State.setCore, State.rip, cmpxchgCore]; split <;> rfl)
    (fun _ _ _ => rfl)

theorem ext_pure_bitI (op : BitOp) (sz : Sz) (r : Reg) (imm : BitVec 8) :
    ext.Pure (Instr.bitI op sz (.reg r) imm : Instr) := by
  refine Extension.Pure.of_eq _ (fun s =>
    let x := sz.read s.core r
    let k := bitOffset sz imm.toNat
    let fl := bitFlags s.core.flags (x.getLsbD k)
    s.setCore (if op = .bt then setFlags s.core fl else setFlags (sz.write s.core r (op.apply x k)) fl))
    (fun s => by simp only [State.setCore, State.rip]; split <;> rfl) (fun _ _ _ => ?_)
  cases op <;> rfl

theorem ext_pure_bit (op : BitOp) (sz : Sz) (r src : Reg) :
    ext.Pure (Instr.bit op sz (.reg r) src : Instr) :=
  Extension.Pure.of_eq _ (fun s =>
    let x := sz.read s.core r
    let k := bitOffset sz (sz.read s.core src).toNat
    s.setCore (setFlags (if op = .bt then s.core else sz.write s.core r (op.apply x k))
      (bitFlags s.core.flags (x.getLsbD k))))
    (fun s => by simp only [State.setCore, State.rip, setFlags_rip]; split <;> rfl)
    (fun _ _ _ => rfl)

theorem ext_pure_shd (right : Bool) (sz : Sz) (r src : Reg) (count : ShdCount) :
    ext.Pure (Instr.shd right sz (.reg r) src count : Instr) := by
  refine Extension.Pure.of_eq _ (fun s =>
    let k := shdCount sz count s.core
    let x := sz.read s.core r
    let y := sz.read s.core src
    s.setCore (if k = 0 then sz.write s.core r x
      else setFlags (sz.write s.core r (shdValue right x y k)) (shdFlags right x y k)))
    (fun s => by simp only [State.setCore, State.rip]; split <;> rfl) (fun len s mem => ?_)
  by_cases hk : shdCount sz count s.core = 0 <;>
    simp [ext_exec, exec, run, rmw, Ext.readRM, Ext.writeRM, Out.ofOption, hk]

/-! ## The integer decoder rejects the lane -/

private theorem decode_none_of_bad {bytes : List Byte} (h : Ext.parseRaw bytes = .bad) :
    Ext.decode bytes = none := by
  unfold Ext.decode
  rw [h]

/-- A head whose opcode the integer `shape` table lacks. -/
private theorem parseRaw_bad_of_shape {fs : Bool} {pfx : Ext.Pfx} {rex : Option Rex} {opc : Ext.Opc}
    (h : Ext.OpcOk opc) (hs : ∀ w, Ext.shape pfx w opc = none) (rest : List Byte) :
    Ext.parseRaw (segBytes fs ++ pfx.bytes ++ Ext.rexBytes rex ++ opc.bytes ++ rest) = .bad := by
  unfold Ext.parseRaw
  rw [Ext.ByteParser.bind_ok (Ext.pHead_bytes fs pfx rex h rest)]
  simp only [hs]
  rfl

private theorem base_one (fs : Bool) (rex : Option Rex) (opc : Byte) (more : List Byte)
    (h : Ext.OpcOk (.one opc)) (hs : ∀ w, Ext.shape .none w (.one opc) = none) :
    Ext.decode (segBytes fs ++ (Ext.rexBytes rex ++ opc :: more)) = none := by
  apply decode_none_of_bad
  have := parseRaw_bad_of_shape (fs := fs) (rex := rex) h hs more
  simpa [Ext.Pfx.bytes, Ext.Opc.bytes] using this

private theorem base_two (fs : Bool) (pfx : Ext.Pfx) (rex : Option Rex) (opc : Byte)
    (more : List Byte) (hs : ∀ w, Ext.shape pfx w (.two opc) = none) :
    Ext.decode (segBytes fs ++ (pfx.bytes ++ Ext.rexBytes rex ++ 0x0F :: opc :: more)) = none := by
  apply decode_none_of_bad
  have := parseRaw_bad_of_shape (fs := fs) (rex := rex) (opc := .two opc) trivial hs more
  simpa [Ext.Opc.bytes] using this

private theorem base_vex (fs : Bool) (more : List Byte) :
    Ext.decode (segBytes fs ++ (0xC4 :: more)) = none := by
  apply decode_none_of_bad
  have := parseRaw_bad_of_shape (fs := fs) (pfx := .none) (rex := none) (opc := .one 0xC4)
    (by unfold Ext.OpcOk; decide) (fun w => by cases w <;> rfl) more
  simpa [Ext.Pfx.bytes, Ext.Opc.bytes, Ext.rexBytes] using this

/-- The forms that the integer length decoder parses (`81`, `83`, `F7`) but
whose ModRM `reg` digit it gives no meaning. -/
private theorem base_rm {w : Bool} {opc : Byte} {reg : BitVec 3} {op : RM}
    {imm : Ext.Imm} (hs : Ext.shape .none w (.one opc) = some ⟨true, imm.kind⟩)
    (hm : Ext.ofModrm .none w false (.one opc) reg op imm
      (⟨(Ext.encodeRM op).mod, reg, (Ext.encodeRM op).rm⟩, (Ext.encodeRM op).sib,
        (Ext.encodeRM op).disp) = none) (more : List Byte) :
    Ext.decode ((Ext.rmRaw .none w (.one opc) reg false op false imm).bytes ++ more) = none := by
  unfold Ext.decode
  rw [Ext.parseRaw_bytes (Ext.wf_rmRaw hs)]
  simp only [Ext.ofRaw_rmRaw, hm]

private theorem shape_none_one (b : Byte) (w : Bool)
    (h : b = 0x11 ∨ b = 0x13 ∨ b = 0x19 ∨ b = 0x1B ∨ b = 0x15 ∨ b = 0x1D ∨ b = 0x69 ∨
      b = 0x6B ∨ b = 0x68 ∨ b = 0x6A) :
    Ext.OpcOk (.one b) ∧ Ext.shape .none w (.one b) = none := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases w <;>
    exact ⟨by unfold Ext.OpcOk; decide, by decide⟩

private theorem shape_none_two (b : Byte) (w : Bool)
    (h : b = 0xBC ∨ b = 0xBD ∨ b = 0xA3 ∨ b = 0xAB ∨ b = 0xB3 ∨ b = 0xBB ∨ b = 0xBA ∨
      b = 0xA4 ∨ b = 0xA5 ∨ b = 0xAC ∨ b = 0xAD ∨ b = 0xC1 ∨ b = 0xB1) :
    Ext.shape .none w (.two b) = none := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases w <;> decide

private theorem shape_38 (pfx : Ext.Pfx) (w : Bool) (hp : pfx = .none ∨ pfx = .opsize ∨ pfx = .rep) :
    Ext.shape pfx w (.two 0x38) = none := by
  rcases hp with rfl | rfl | rfl <;> cases w <;> decide

private theorem one_ok {b : Byte} (h : b = 0x11 ∨ b = 0x13 ∨ b = 0x19 ∨ b = 0x1B ∨ b = 0x15 ∨
    b = 0x1D ∨ b = 0x69 ∨ b = 0x6B ∨ b = 0x68 ∨ b = 0x6A) (fs : Bool) (rex : Option Rex)
    (more : List Byte) : Ext.decode (segBytes fs ++ (Ext.rexBytes rex ++ b :: more)) = none :=
  base_one fs rex b more (shape_none_one b false h).1 fun w => (shape_none_one b w h).2

private theorem two_ok {b : Byte} (h : b = 0xBC ∨ b = 0xBD ∨ b = 0xA3 ∨ b = 0xAB ∨ b = 0xB3 ∨
    b = 0xBB ∨ b = 0xBA ∨ b = 0xA4 ∨ b = 0xA5 ∨ b = 0xAC ∨ b = 0xAD ∨ b = 0xC1 ∨ b = 0xB1)
    (fs : Bool) (rex : Option Rex) (more : List Byte) :
    Ext.decode (segBytes fs ++ (Ext.rexBytes rex ++ 0x0F :: b :: more)) = none := by
  have := base_two fs .none rex b more fun w => shape_none_two b w h
  simpa [Ext.Pfx.bytes] using this

private theorem m38_ok (pfx : Ext.Pfx) (hp : pfx = .none ∨ pfx = .opsize ∨ pfx = .rep)
    (fs : Bool) (rex : Option Rex) (more : List Byte) :
    Ext.decode (segBytes fs ++ (pfx.bytes ++ Ext.rexBytes rex ++ 0x0F :: 0x38 :: more)) = none :=
  base_two fs pfx rex 0x38 more fun w => shape_38 pfx w hp

/-- The integer decoder rejects every encoding of the lane, whatever follows
it. -/
theorem base_decode_none (i : Instr) (more : List Byte) : Ext.decode (encode i ++ more) = none := by
  cases i with
  | carryI op sz dst imm =>
    have h := base_rm (more := more) (w := sz.w) (opc := 0x81) (reg := op.digit) (op := dst)
      (imm := .i32 imm) (by cases sz <;> rfl)
      (by cases op <;> simp [Ext.ofModrm, CarryOp.digit, AluOp.ofDigit])
    simpa [encode, toRaw, legacyRaw, Raw.bytes, Enc.bytes, Pfx.bytes, Map.bytes, Ext.rmRaw,
      Ext.Raw.bytes, Ext.Pfx.bytes, Ext.Opc.bytes] using h
  | carryI8 op sz dst imm =>
    have h := base_rm (more := more) (w := sz.w) (opc := 0x83) (reg := op.digit) (op := dst)
      (imm := .i8 imm) (by cases sz <;> rfl)
      (by cases op <;> simp [Ext.ofModrm, CarryOp.digit, AluOp.ofDigit])
    simpa [encode, toRaw, legacyRaw, Raw.bytes, Enc.bytes, Pfx.bytes, Map.bytes, Ext.rmRaw,
      Ext.Raw.bytes, Ext.Pfx.bytes, Ext.Opc.bytes] using h
  | imul1 sz src =>
    have h := base_rm (more := more) (w := sz.w) (opc := 0xF7) (reg := 5) (op := src)
      (imm := .none) (by cases sz <;> rfl) (by simp [Ext.ofModrm])
    simpa [encode, toRaw, legacyRaw, Raw.bytes, Enc.bytes, Pfx.bytes, Map.bytes, Ext.rmRaw,
      Ext.Raw.bytes, Ext.Pfx.bytes, Ext.Opc.bytes, Ext.Imm.bytes] using h
  | testI sz dst imm =>
    have h := base_rm (more := X86.imm32Bytes imm ++ more) (w := sz.w) (opc := 0xF7)
      (reg := 0) (op := dst) (imm := .none) (by cases sz <;> rfl) (by simp [Ext.ofModrm])
    simpa [encode, toRaw, legacyRaw, Raw.bytes, Enc.bytes, Pfx.bytes, Map.bytes, Ext.rmRaw,
      Ext.Raw.bytes, Ext.Pfx.bytes, Ext.Opc.bytes, Ext.Imm.bytes] using h
  | carry op =>
    cases op <;>
    simpa [encode, toRaw, legacyRaw, Raw.bytes, Enc.bytes, Pfx.bytes, Map.bytes, CarryOp.opcode]
      using one_ok (by decide) _ _ _
  | carryR op =>
    cases op <;>
    simpa [encode, toRaw, legacyRaw, Raw.bytes, Enc.bytes, Pfx.bytes, Map.bytes, CarryOp.opcodeR]
      using one_ok (by decide) _ _ _
  | carryA op =>
    cases op <;>
    simpa [encode, toRaw, Raw.bytes, Enc.bytes, Pfx.bytes, Map.bytes, CarryOp.opcodeA]
      using one_ok (by decide) false _ _
  | imulI | imulI8 =>
    simpa [encode, toRaw, legacyRaw, Raw.bytes, Enc.bytes, Pfx.bytes, Map.bytes]
      using one_ok (by decide) _ _ _
  | pushI | pushI8 =>
    simpa [encode, toRaw, Raw.bytes, Enc.bytes, Pfx.bytes, Map.bytes]
      using one_ok (by decide) false none _
  | scan rev =>
    cases rev <;>
    simpa [encode, toRaw, legacyRaw, Raw.bytes, Enc.bytes, Pfx.bytes, Map.bytes]
      using two_ok (by decide) _ _ _
  | bit op =>
    cases op <;>
    simpa [encode, toRaw, legacyRaw, Raw.bytes, Enc.bytes, Pfx.bytes, Map.bytes, BitOp.opcode]
      using two_ok (by decide) _ _ _
  | bitI =>
    simpa [encode, toRaw, legacyRaw, Raw.bytes, Enc.bytes, Pfx.bytes, Map.bytes]
      using two_ok (b := 0xBA) (by decide) _ _ _
  | xadd =>
    simpa [encode, toRaw, legacyRaw, Raw.bytes, Enc.bytes, Pfx.bytes, Map.bytes]
      using two_ok (b := 0xC1) (by decide) false _ _
  | cmpxchg =>
    simpa [encode, toRaw, legacyRaw, Raw.bytes, Enc.bytes, Pfx.bytes, Map.bytes]
      using two_ok (b := 0xB1) (by decide) false _ _
  | shd right sz dst src count =>
    cases right <;> cases count <;>
    simpa [encode, toRaw, legacyRaw, Raw.bytes, Enc.bytes, Pfx.bytes, Map.bytes, shdOpcode]
      using two_ok (by decide) _ _ _
  | adx op =>
    cases op
    · simpa [encode, toRaw, legacyRaw, Raw.bytes, Enc.bytes, Pfx.bytes, Map.bytes, Ext.Pfx.bytes]
        using m38_ok .opsize (by decide) _ _ _
    · simpa [encode, toRaw, legacyRaw, Raw.bytes, Enc.bytes, Pfx.bytes, Map.bytes, Ext.Pfx.bytes]
        using m38_ok .rep (by decide) _ _ _
  | movbeLoad | movbeStore =>
    simpa [encode, toRaw, legacyRaw, Raw.bytes, Enc.bytes, Pfx.bytes, Map.bytes, Ext.Pfx.bytes]
      using m38_ok .none (by decide) _ _ _
  | vop | bls | rorx =>
    simpa [encode, toRaw, vexRaw, Raw.bytes, Enc.bytes] using base_vex _ _

/-- The integer decoder rejects every window the lane decodes. -/
theorem base_decode_none_of_decode {bytes : List Byte} {i : Instr} {n : Nat}
    (h : decode bytes = some (i, n)) : Ext.decode bytes = none := by
  obtain ⟨-, rest, rfl⟩ := decode_sound h
  exact base_decode_none i rest

/-- One step of the machine on an instruction of the lane, whichever
extensions precede it in the list, provided they do not decode it. -/
theorem step_ext {F : FeatureSet} {exts : List Extension} {exit : Word} {m : MState}
    {i : Instr} {n : Nat}
    (hdec : decode (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) = some (i, n))
    (hext : extDecode exts (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) =
      some ⟨ext, i, n⟩)
    (hperm : m.memory.Permitted .execute m.state.core.rip.toNat n) :
    step F exts exit m = extStep F ext i n m :=
  step_of_ext (base_decode_none_of_decode hdec) hext hperm

/-- With `ext` alone. -/
theorem step_ext_single {F : FeatureSet} {exit : Word} {m : MState} {i : Instr} {n : Nat}
    (hdec : decode (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) = some (i, n))
    (hperm : m.memory.Permitted .execute m.state.core.rip.toNat n) :
    step F [ext] exit m = extStep F ext i n m :=
  step_ext hdec (by simp [extDecode, hdec]) hperm

end Silmaril.X86.Features.IntExt
