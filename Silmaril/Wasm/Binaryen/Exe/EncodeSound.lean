module

public import Silmaril.Wasm.Binaryen.Exe.Encode
public import Silmaril.Wasm.Binaryen.Exe.MemoryEncodeSound
public import Silmaril.Wasm.Binaryen.Exe.FloatEncodeSound
public import Silmaril.Wasm.Binaryen.Exe.SIMDEncodeSound
public import Silmaril.Wasm.Binaryen.Exe.TableEncodeSound
public import Silmaril.Wasm.Binaryen.Exe.TagEncodeSound
public import Silmaril.Wasm.Binaryen.Exe.GcEncodeSound
import Mathlib.Tactic.Convert

@[expose] public section

/-! # Soundness of the executable encoder

`encodeModule?_sound`: whatever bytes the encoder returns encode the module under
the specification's binary grammar `Binary.Core.Encodes` (`Module Forms.all`,
transcribed from `5.4-binary.modules.spectec`). This is the CERTIFIED piece of
`binaryen-lean`: the output file means exactly the optimised Core 3.0 module.

Milestone E1 is complete: no `sorry`. The proof is bottom-up:

* `encU_sound`/`encS_sound`: minimal LEB128 against `UN`/`SN`, by the same
  well-founded recursion as the encoder;
* `encList_sound`/`encVec_sound`/`encSection_sound`/`encName_sound`: generic over the
  element grammar;
* `encInstr_sound`: one case per profile instruction, `PlainOp` constructors for the
  single-byte opcodes and `Instr.block/loop/if_/ifElse` for the structured ones; the
  recursion through bodies is on a `sizeOf` fuel bound (`encInstr_lt`), as in
  `Instr.mono_lt`;
* `encCode_sound`: the compressed locals flatten back to the declared locals
  (`groupLocals_flatten`);
* `encData_sound`: data segments of kinds `0`, `1` and `2`;
* `encodeModuleWith?_sound`: the `Module.mk` rule, with every absent section
  `Section.empty`, every custom block `Customs.nil`, and tags from `encTagType_sound`; the
  data count section is present exactly when the policy bit holds and there are data
  segments (`dataCntSecIf_sound`); `encodeModule?_sound` and `encodeModule_sound` are
  its two policies; the function and code sections come from the same list
  (`zipFuncs_map`).

The grammar's side conditions that do not hold for every abstract module (`u32`
lengths, the `2^32` locals bound, no data indices without a data count section) are
runtime checks of the encoder, so they appear here as facts extracted from `.ok`.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

/-! ## Types -/

theorem encValType_sound {t : Wasm.ValType} {bs : List UInt8}
    (h : encValType t = .ok bs) : Core.ValType Forms.all bs t := by
  unfold encValType at h
  split at h
  · next it =>
    cases Except.ok.inj h
    cases it
    · exact .num NumType.i32
    · exact .num NumType.i64
  · next ft =>
    cases Except.ok.inj h
    cases ft
    · exact .num NumType.f32
    · exact .num NumType.f64
  · cases Except.ok.inj h
    exact .vec .v128
  · next r =>
    cases Except.ok.inj h
    exact .ref (encRefType_sound r)

theorem encBlockType_sound {bt : Wasm.BlockType} {bs : List UInt8}
    (h : encBlockType bt = .ok bs) : Core.BlockType Forms.all bs bt := by
  unfold encBlockType at h
  split at h
  · cases Except.ok.inj h
    exact .empty
  · exact .value (encValType_sound h)
  · next x =>
    cases Except.ok.inj h
    have hx := x.value.isLt
    have hx' : x.toNat = x.value.val := rfl
    exact .idx x (encS_sound (N := 33) (by simp only [Nat.reduceSub, Int.reducePow]; omega)
      (by simp only [Nat.reduceSub, Int.reducePow, Nat.reducePow] at hx ⊢; omega) (by decide))

theorem encFuncType_sound {ft : Wasm.FuncType} {bs : List UInt8}
    (h : encFuncType ft = .ok bs) : CompType Forms.all bs (.func ft) := by
  unfold encFuncType at h
  obtain ⟨a, ha, h⟩ := bind_ok h
  obtain ⟨b, hb, h⟩ := bind_ok h
  cases Except.ok.inj h
  exact CompType.func (encVec_sound_id (fun _ _ _ hv => encValType_sound hv) ha)
    (encVec_sound_id (fun _ _ _ hv => encValType_sound hv) hb)

theorem encMut_sound (m : Mutability) : Core.Mut [encMut m] m := by
  cases m
  · exact .const
  · exact .var

theorem encFieldType_sound {ft : Wasm.FieldType} {bs : List UInt8}
    (h : encFieldType ft = .ok bs) : Core.FieldType Forms.all bs ft := by
  rcases ft with ⟨m, z⟩
  unfold encFieldType at h
  obtain ⟨a, ha, h⟩ := bind_ok h
  cases Except.ok.inj h
  cases z with
  | val t => exact .mk (.val (encValType_sound ha)) (encMut_sound m)
  | packed p =>
    cases Except.ok.inj (show pure [encPackType p] = Except.ok a from ha)
    exact .mk (.packed (encPackType_sound p)) (encMut_sound m)

theorem encCompType_sound {ct : Wasm.CompositeType} {bs : List UInt8}
    (h : encCompType ct = .ok bs) : CompType Forms.all bs ct := by
  cases ct with
  | func ft => exact encFuncType_sound h
  | struct fs =>
    obtain ⟨a, ha, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact .struct (encVec_sound_id (fun _ _ _ hv => encFieldType_sound hv) ha)
  | array f =>
    obtain ⟨a, ha, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact .array (encFieldType_sound ha)

theorem encSubType_sound {st : Wasm.SubType} {bs : List UInt8}
    (h : encSubType st = .ok bs) : Core.SubType Forms.all bs st := by
  rcases st with ⟨fin, xs, ct⟩
  unfold encSubType at h
  split at h
  · next hc =>
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact .plain (encCompType_sound h)
  · obtain ⟨a, ha, h⟩ := bind_ok h
    obtain ⟨b, hb, h⟩ := bind_ok h
    cases Except.ok.inj h
    have hx : Vec Index a xs := encVec_sound_id (fun x _ b hb => by
      cases Except.ok.inj hb
      exact encIdx_sound x) ha
    cases fin
    · exact .open_ rfl hx (encCompType_sound hb)
    · exact .final rfl hx (encCompType_sound hb)

theorem encRecType_sound {r : Wasm.RecType} {bs : List UInt8}
    (h : encRecType r = .ok bs) : Core.RecType Forms.all bs r := by
  rcases r with ⟨sts⟩
  unfold encRecType at h
  split at h
  · next st e =>
    simp only at e
    subst e
    exact .single (encSubType_sound h)
  · obtain ⟨a, ha, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact .group rfl (encVec_sound_id (fun _ _ _ hv => encSubType_sound hv) ha)

/-! ## Instructions -/

theorem encInstrs_of {is : List Wasm.Instr}
    (H : ∀ i ∈ is, ∀ b, encInstr i = .ok b → Core.Instr Forms.all b i) :
    ∀ {bs : List UInt8}, encInstrs is = .ok bs → Core.Instrs Forms.all bs is := by
  induction is with
  | nil =>
    intro bs h
    simp only [encInstrs] at h
    cases Except.ok.inj h
    exact .nil
  | cons i is ih =>
    intro bs h
    simp only [encInstrs] at h
    obtain ⟨a, ha, h⟩ := bind_ok h
    obtain ⟨b, hb, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact .cons (H i List.mem_cons_self _ ha)
      (ih (fun j hj b hj' => H j (List.mem_cons_of_mem _ hj) b hj') hb)

/-- `encInstr` soundness for instructions of size below a fuel bound. -/
theorem encInstr_lt : ∀ (N : Nat) {i : Wasm.Instr} {bs : List UInt8},
    sizeOf i < N → encInstr i = .ok bs → Core.Instr Forms.all bs i
  | 0, _, _, hN, _ => absurd hN (Nat.not_lt_zero _)
  | N + 1, i, bs, hN, h => by
    have ihs : ∀ {is : List Wasm.Instr} {b : List UInt8}, sizeOf is < sizeOf i →
        encInstrs is = .ok b → Core.Instrs Forms.all b is := fun hs he =>
      encInstrs_of (fun j hj _ hb =>
        encInstr_lt N (by have := List.sizeOf_lt_of_mem hj; omega) hb) he
    unfold encInstr at h
    split at h
    -- unreachable
    · cases Except.ok.inj h; exact .plain .rx00
    -- nop
    · cases Except.ok.inj h; exact .plain .rx01
    -- throw
    · next x => cases Except.ok.inj h; exact .throw (encIdx_sound x)
    -- throw_ref
    · cases Except.ok.inj h; exact .plain .rx0A
    -- block
    · next bt body =>
      obtain ⟨a, ha, h⟩ := bind_ok h
      obtain ⟨b, hb, h⟩ := bind_ok h
      cases Except.ok.inj h
      exact .block (encBlockType_sound ha) (ihs (by simp; omega) hb)
    -- loop
    · next bt body =>
      obtain ⟨a, ha, h⟩ := bind_ok h
      obtain ⟨b, hb, h⟩ := bind_ok h
      cases Except.ok.inj h
      exact .loop (encBlockType_sound ha) (ihs (by simp; omega) hb)
    -- if
    · next bt t e =>
      obtain ⟨a, ha, h⟩ := bind_ok h
      obtain ⟨b, hb, h⟩ := bind_ok h
      obtain ⟨c, hc, h⟩ := bind_ok h
      split at h
      · next he =>
        cases Except.ok.inj h
        obtain rfl : e = [] := List.isEmpty_iff.mp he
        exact .if_ (encBlockType_sound ha) (ihs (by simp; omega) hb)
      · cases Except.ok.inj h
        exact .ifElse (encBlockType_sound ha) (ihs (by simp; omega) hb)
          (ihs (by simp; omega) hc)
    -- try_table
    · next bt cs body =>
      obtain ⟨a, ha, h⟩ := bind_ok h
      obtain ⟨c, hc, h⟩ := bind_ok h
      obtain ⟨b, hb, h⟩ := bind_ok h
      cases Except.ok.inj h
      refine .tryTable (encBlockType_sound ha)
        (encVec_sound_id (fun x _ b hx => ?_) hc) (ihs (by simp; omega) hb)
      cases Except.ok.inj hx
      exact encCatch_sound x
    -- br
    · next l => cases Except.ok.inj h; exact .br (encIdx_sound l)
    -- br_if
    · next l => cases Except.ok.inj h; exact .brIf (encIdx_sound l)
    -- br_table
    · next ls l =>
      obtain ⟨a, ha, h⟩ := bind_ok h
      cases Except.ok.inj h
      refine .brTable (encVec_sound_id (fun x _ b hb => ?_) ha) (encIdx_sound l)
      cases Except.ok.inj hb
      exact encIdx_sound x
    -- return
    · cases Except.ok.inj h; exact .plain .rx0F
    -- call
    · next f => cases Except.ok.inj h; exact .call (encIdx_sound f)
    -- call_indirect
    · next x y =>
      obtain ⟨a, ha, h⟩ := bind_ok h
      cases Except.ok.inj h
      exact .callIndirect (encIdx_sound y) (encTableIdx_sound ha)
    -- tail calls and typed function references
    · next f => cases Except.ok.inj h; exact .returnCall (encIdx_sound f)
    · next x y =>
      cases Except.ok.inj h
      exact .returnCallIndirect (encIdx_sound y) (encIdx_sound x)
    · next x => cases Except.ok.inj h; exact .callRef (encIdx_sound x)
    · next x => cases Except.ok.inj h; exact .returnCallRef (encIdx_sound x)
    -- drop
    · cases Except.ok.inj h; exact .plain .rx1A
    -- select
    · cases Except.ok.inj h; exact .plain .rx1B
    -- reference instructions
    · next ht => cases Except.ok.inj h; exact .refNull (encHeapType_sound ht)
    · cases Except.ok.inj h; exact .plain .rxD1
    · next f => cases Except.ok.inj h; exact .refFunc (encIdx_sound f)
    -- locals and globals
    · next x => cases Except.ok.inj h; exact .localGet (encIdx_sound x)
    · next x => cases Except.ok.inj h; exact .localSet (encIdx_sound x)
    · next x => cases Except.ok.inj h; exact .localTee (encIdx_sound x)
    · next x => cases Except.ok.inj h; exact .globalGet (encIdx_sound x)
    · next x => cases Except.ok.inj h; exact .globalSet (encIdx_sound x)
    -- Table indices are u32s; table.init encodes the element index first.
    · next x => cases Except.ok.inj h; exact .tableGet (encIdx_sound x)
    · next x => cases Except.ok.inj h; exact .tableSet (encIdx_sound x)
    · next x e =>
      cases Except.ok.inj h
      exact .tableInit (by simpa [encU] using encU_sound (by decide : 12 < 2 ^ 32))
        (encIdx_sound e) (encIdx_sound x)
    · next e =>
      cases Except.ok.inj h
      exact .elemDrop (by simpa [encU] using encU_sound (by decide : 13 < 2 ^ 32)) (encIdx_sound e)
    · next dst src =>
      cases Except.ok.inj h
      exact .tableCopy (by simpa [encU] using encU_sound (by decide : 14 < 2 ^ 32))
        (encIdx_sound dst) (encIdx_sound src)
    · next x =>
      cases Except.ok.inj h
      exact .tableGrow (by simpa [encU] using encU_sound (by decide : 15 < 2 ^ 32)) (encIdx_sound x)
    · next x =>
      cases Except.ok.inj h
      exact .tableSize (by simpa [encU] using encU_sound (by decide : 16 < 2 ^ 32)) (encIdx_sound x)
    · next x =>
      cases Except.ok.inj h
      exact .tableFill (by simpa [encU] using encU_sound (by decide : 17 < 2 ^ 32)) (encIdx_sound x)
    -- integer memory instructions
    · obtain ⟨op, hop, h⟩ := bind_ok h
      obtain ⟨a, ha, h⟩ := bind_ok h
      cases Except.ok.inj h
      exact .mem (intLoadOpcode_sound hop) (encMemArg_sound ha)
    · obtain ⟨op, hop, h⟩ := bind_ok h
      obtain ⟨a, ha, h⟩ := bind_ok h
      cases Except.ok.inj h
      exact .mem (intStoreOpcode_sound hop) (encMemArg_sound ha)
    · obtain ⟨a, ha, h⟩ := bind_ok h
      cases Except.ok.inj h
      exact .memorySize (encMemoryIdx_sound ha)
    · obtain ⟨a, ha, h⟩ := bind_ok h
      cases Except.ok.inj h
      exact .memoryGrow (encMemoryIdx_sound ha)
    -- bulk memory (data index precedes the memory index for memory.init)
    · next x d =>
      obtain ⟨a, ha, h⟩ := bind_ok h
      cases Except.ok.inj h
      exact .memoryInit (by simpa [encU] using encU_sound (by decide : 8 < 2 ^ 32))
        (encIdx_sound d) (encMemoryIdx_sound ha)
    · next d =>
      cases Except.ok.inj h
      exact .dataDrop (by simpa [encU] using encU_sound (by decide : 9 < 2 ^ 32)) (encIdx_sound d)
    · obtain ⟨a, ha, h⟩ := bind_ok h
      obtain ⟨b, hb, h⟩ := bind_ok h
      cases Except.ok.inj h
      exact .memoryCopy (by simpa [encU] using encU_sound (by decide : 10 < 2 ^ 32))
        (encMemoryIdx_sound ha) (encMemoryIdx_sound hb)
    · obtain ⟨a, ha, h⟩ := bind_ok h
      cases Except.ok.inj h
      exact .memoryFill (by simpa [encU] using encU_sound (by decide : 11 < 2 ^ 32)) (encMemoryIdx_sound ha)
    -- floating-point memory and numerics
    · next t x a =>
      obtain ⟨b, hb, h⟩ := bind_ok h
      cases Except.ok.inj h
      exact .mem (by cases t <;> constructor) (encMemArg_sound hb)
    · next t x a =>
      obtain ⟨b, hb, h⟩ := bind_ok h
      cases Except.ok.inj h
      exact .mem (by cases t <;> constructor) (encMemArg_sound hb)
    · next t b =>
      cases Except.ok.inj h
      cases t
      · exact .f32Const (encFloatBits_sound _ b)
      · exact .f64Const (encFloatBits_sound _ b)
    · cases Except.ok.inj h; exact .plain (floatUnOpcode_sound _ _)
    · cases Except.ok.inj h; exact .plain (floatBinOpcode_sound _ _)
    · cases Except.ok.inj h; exact .plain (floatRelOpcode_sound _ _)
    -- constants
    · next t b =>
      cases Except.ok.inj h
      cases t
      · exact .i32Const (in_toInt (by decide) b)
      · exact .i64Const (in_toInt (by decide) b)
    -- eqz
    · next t =>
      cases Except.ok.inj h
      cases t
      · exact .plain .rx45
      · exact .plain .rx50
    -- relational
    · next t o =>
      cases Except.ok.inj h
      rcases t with _ | _ <;> rcases o with _ | _ | (_ | _) | (_ | _) | (_ | _) | (_ | _) <;>
        exact .plain (by constructor)
    -- unary
    · next t o =>
      obtain ⟨a, ha, h⟩ := bind_ok h
      cases Except.ok.inj h
      unfold intUnOpcode at ha
      split at ha <;>
        first
        | exact absurd ha throw_ne_ok
        | (cases Except.ok.inj ha; exact .plain (by constructor))
    -- binary
    · next t o =>
      cases Except.ok.inj h
      rcases t with _ | _ <;>
        rcases o with _ | _ | _ | (_ | _) | (_ | _) | _ | _ | _ | _ | (_ | _) | _ | _ <;>
        exact .plain (by constructor)
    -- conversions
    · cases Except.ok.inj h; exact encConvert_sound _
    -- typed select
    · next ts =>
      obtain ⟨a, ha, h⟩ := bind_ok h
      cases Except.ok.inj h
      exact .selectT (encVec_sound_id (fun _ _ _ hv => encValType_sound hv) ha)
    -- references
    · cases Except.ok.inj h; exact .plain .rxD3
    · cases Except.ok.inj h; exact .plain .rxD4
    · next l => cases Except.ok.inj h; exact .brOnNull (encIdx_sound l)
    · next l => cases Except.ok.inj h; exact .brOnNonNull (encIdx_sound l)
    -- structs
    · next x => cases Except.ok.inj h; exact .structNew (u32_byte 0) (encIdx_sound x)
    · next x => cases Except.ok.inj h; exact .structNewDefault (u32_byte 1) (encIdx_sound x)
    · next x i => cases Except.ok.inj h; exact .structGet (u32_byte 2) (encIdx_sound x) (encIdx_sound i)
    · next x i => cases Except.ok.inj h; exact .structGetS (u32_byte 3) (encIdx_sound x) (encIdx_sound i)
    · next x i => cases Except.ok.inj h; exact .structGetU (u32_byte 4) (encIdx_sound x) (encIdx_sound i)
    · next x i => cases Except.ok.inj h; exact .structSet (u32_byte 5) (encIdx_sound x) (encIdx_sound i)
    -- arrays
    · next x => cases Except.ok.inj h; exact .arrayNew (u32_byte 6) (encIdx_sound x)
    · next x => cases Except.ok.inj h; exact .arrayNewDefault (u32_byte 7) (encIdx_sound x)
    · next x n => cases Except.ok.inj h; exact .arrayNewFixed (u32_byte 8) (encIdx_sound x) (encU_sound n.isLt)
    · next x y => cases Except.ok.inj h; exact .arrayNewData (u32_byte 9) (encIdx_sound x) (encIdx_sound y)
    · next x y => cases Except.ok.inj h; exact .arrayNewElem (u32_byte 10) (encIdx_sound x) (encIdx_sound y)
    · next x => cases Except.ok.inj h; exact .arrayGet (u32_byte 11) (encIdx_sound x)
    · next x => cases Except.ok.inj h; exact .arrayGetS (u32_byte 12) (encIdx_sound x)
    · next x => cases Except.ok.inj h; exact .arrayGetU (u32_byte 13) (encIdx_sound x)
    · next x => cases Except.ok.inj h; exact .arraySet (u32_byte 14) (encIdx_sound x)
    · cases Except.ok.inj h; exact .prefixFB .r15 (u32_byte 15)
    · next x => cases Except.ok.inj h; exact .arrayFill (u32_byte 16) (encIdx_sound x)
    · next x y => cases Except.ok.inj h; exact .arrayCopy (u32_byte 17) (encIdx_sound x) (encIdx_sound y)
    · next x y => cases Except.ok.inj h; exact .arrayInitData (u32_byte 18) (encIdx_sound x) (encIdx_sound y)
    · next x y => cases Except.ok.inj h; exact .arrayInitElem (u32_byte 19) (encIdx_sound x) (encIdx_sound y)
    -- casts and tests
    · next ht => cases Except.ok.inj h; exact .refTest (u32_byte 20) (encHeapType_sound ht)
    · next ht => cases Except.ok.inj h; exact .refTestNull (u32_byte 21) (encHeapType_sound ht)
    · next ht => cases Except.ok.inj h; exact .refCast (u32_byte 22) (encHeapType_sound ht)
    · next ht => cases Except.ok.inj h; exact .refCastNull (u32_byte 23) (encHeapType_sound ht)
    -- cast branches
    · next l n₁ h₁ n₂ h₂ =>
      cases Except.ok.inj h
      exact .brOnCast (u32_byte 24) (encCastOp_sound n₁ n₂) (encIdx_sound l)
        (encHeapType_sound h₁) (encHeapType_sound h₂)
    · next l n₁ h₁ n₂ h₂ =>
      cases Except.ok.inj h
      exact .brOnCastFail (u32_byte 25) (encCastOp_sound n₁ n₂) (encIdx_sound l)
        (encHeapType_sound h₁) (encHeapType_sound h₂)
    -- conversions between hierarchies and `i31`
    · cases Except.ok.inj h; exact .prefixFB .r26 (u32_byte 26)
    · cases Except.ok.inj h; exact .prefixFB .r27 (u32_byte 27)
    · cases Except.ok.inj h; exact .prefixFB .r28 (u32_byte 28)
    · cases Except.ok.inj h; exact .prefixFB .r29 (u32_byte 29)
    · cases Except.ok.inj h; exact .prefixFB .r30 (u32_byte 30)
    -- vector constants
    · cases Except.ok.inj h; exact encVecConst_sound _
    -- Stack-only SIMD; every other instruction is rejected by the leaf encoder.
    · exact encSIMDInstr_sound h

theorem encInstr_sound {i : Wasm.Instr} {bs : List UInt8}
    (h : encInstr i = .ok bs) : Core.Instr Forms.all bs i :=
  encInstr_lt (sizeOf i + 1) (Nat.lt_succ_self _) h

theorem encInstrs_sound {is : List Wasm.Instr} {bs : List UInt8}
    (h : encInstrs is = .ok bs) : Core.Instrs Forms.all bs is :=
  encInstrs_of (fun _ _ _ hi => encInstr_sound hi) h

theorem encExpr_sound {e : Wasm.Expr} {bs : List UInt8}
    (h : encExpr e = .ok bs) : Core.Expr Forms.all bs e := by
  unfold encExpr at h
  obtain ⟨a, ha, h⟩ := bind_ok h
  cases Except.ok.inj h
  exact .mk (encInstrs_sound ha)

/-! ## Module fields -/

theorem encImport_sound {i : Wasm.Import} {bs : List UInt8}
    (h : encImport i = .ok bs) : Core.Import Forms.all bs i := by
  unfold encImport at h
  split at h
  · next mn nm x =>
    obtain ⟨a, ha, h⟩ := bind_ok h
    obtain ⟨b, hb, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact .mk (encName_sound ha) (encName_sound hb) (.func (encIdx_sound x))
  · next mn nm tt =>
    obtain ⟨a, ha, h⟩ := bind_ok h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨c, hc, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact .mk (encName_sound ha) (encName_sound hb) (.table (encTableType_sound hc))
  · next mn nm mt =>
    obtain ⟨a, ha, h⟩ := bind_ok h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨c, hc, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact .mk (encName_sound ha) (encName_sound hb) (.memory (encMemory_sound hc))
  · next mn nm gt =>
    obtain ⟨a, ha, h⟩ := bind_ok h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨c, hc, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact .mk (encName_sound ha) (encName_sound hb)
      (.global (.mk (encValType_sound hc) (encMut_sound _)))
  · next mn nm t =>
    obtain ⟨a, ha, h⟩ := bind_ok h
    obtain ⟨b, hb, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact .mk (encName_sound ha) (encName_sound hb) (.tag (encTagType_sound t))

theorem encGlobal_sound {g : Wasm.Global} {bs : List UInt8}
    (h : encGlobal g = .ok bs) : Core.Global Forms.all bs g := by
  unfold encGlobal at h
  obtain ⟨a, ha, h⟩ := bind_ok h
  obtain ⟨b, hb, h⟩ := bind_ok h
  cases Except.ok.inj h
  exact Core.Global.mk (gt := ⟨g.type.mutability, g.type.value⟩)
    (.mk (encValType_sound ha) (encMut_sound _)) (encExpr_sound hb)

theorem encExport_sound {e : Wasm.Export} {bs : List UInt8}
    (h : encExport e = .ok bs) : Core.Export bs e := by
  unfold encExport at h
  split at h
  · next nm x =>
    obtain ⟨a, ha, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact .mk (encName_sound ha) (.func (encIdx_sound x))
  · next nm x =>
    obtain ⟨a, ha, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact .mk (encName_sound ha) (.table (encIdx_sound x))
  · next nm x =>
    obtain ⟨a, ha, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact .mk (encName_sound ha) (.memory (encIdx_sound x))
  · next nm x =>
    obtain ⟨a, ha, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact .mk (encName_sound ha) (.global (encIdx_sound x))
  · next nm x =>
    obtain ⟨a, ha, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact .mk (encName_sound ha) (.tag (encIdx_sound x))

theorem dataBytes_toList (b : ByteArray) : dataBytes b.data.toList = b := by
  cases b; simp [dataBytes]

theorem encData_sound {d : Wasm.Data} {bs : List UInt8} (h : encData d = .ok bs) :
    Core.Data Forms.all bs d := by
  unfold encData at h
  obtain ⟨v, hv, h⟩ := bind_ok h
  have hbv : ByteVec (v ++ d.bytes.data.toList) d.bytes.data.toList :=
    Vec.mk (encU32_sound hv) (seq_byte _)
  obtain ⟨bytes, mode⟩ := d
  have hb := dataBytes_toList bytes
  cases mode with
  | passive =>
    cases Except.ok.inj h
    have := Core.Data.k1 (F := Forms.all) rfl (encU_sound (N := 32) (by decide)) hbv
    rwa [hb] at this
  | active x e =>
    simp only at h
    split at h
    · next hx =>
      obtain ⟨a, ha, h⟩ := bind_ok h
      cases Except.ok.inj h
      have hx0 : x = ⟨0⟩ := by
        cases x with
        | mk v => congr 1; exact Fin.ext hx
      subst hx0
      have := Core.Data.k0 (F := Forms.all) (encU_sound (N := 32) (by decide))
        (encExpr_sound ha) hbv
      rwa [hb] at this
    · obtain ⟨a, ha, h⟩ := bind_ok h
      cases Except.ok.inj h
      have := Core.Data.k2 (F := Forms.all) rfl (encU_sound (N := 32) (by decide))
        (encIdx_sound x) (encExpr_sound ha) hbv
      rwa [hb] at this

theorem dataCntSec_sound {data : List Wasm.Data} {dc s : List UInt8}
    (hdc : encU32 data.length = .ok dc)
    (h : encSection 12 (if data.isEmpty then 0 else 1) dc = .ok s) :
    DataCntSec Forms.all s (if data.isEmpty then none else some data.length) := by
  by_cases he : data.isEmpty = true
  · simp only [he, ite_true] at h ⊢
    simp only [encSection, ite_true] at h
    cases Except.ok.inj h
    exact .absent
  · simp only [he, Bool.false_eq_true, ite_false] at h ⊢
    exact DataCntSec.present (ns := [data.length]) rfl
      (encSection_sound (fun _ => DataCnt.mk (encU32_sound hdc)) (fun h0 => absurd h0 one_ne_zero) h)

/-- The explicit expression forms cover every reference type, including
non-nullable `func` initializers not expressible as function indices. -/
theorem encElemExpressions_sound {e : Wasm.Elem} {bs : List UInt8}
    (h : encElemExpressions e = .ok bs) : Core.Elem Forms.all bs e := by
  rcases e with ⟨rt, init, mode⟩
  unfold encElemExpressions at h
  obtain ⟨v, hv, h⟩ := bind_ok h
  have hV : Vec (Core.Expr Forms.all) v init :=
    encVec_sound_id (fun e _ _ he => encExpr_sound (e := e) he) hv
  cases mode with
  | active x off =>
    obtain ⟨a, ha, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact .k6 rfl (encU_sound (N := 32) (by decide)) (encIdx_sound x)
      (encExpr_sound ha) (encRefType_sound rt) hV
  | passive =>
    cases Except.ok.inj h
    exact .k5 rfl (encU_sound (N := 32) (by decide)) (encRefType_sound rt) hV
  | declarative =>
    cases Except.ok.inj h
    exact .k7 rfl (encU_sound (N := 32) (by decide)) (encRefType_sound rt) hV

theorem encElem_sound {e : Wasm.Elem} {bs : List UInt8} (h : encElem e = .ok bs) :
    Core.Elem Forms.all bs e := by
  rcases e with ⟨rt, init, mode⟩
  unfold encElem at h
  split at h
  · next hrt =>
    simp only at hrt
    subst hrt
    split at h
    · next ys hys =>
      have hi := elemFuncs?_spec hys
      simp only at hi
      subst hi
      obtain ⟨v, hv, h⟩ := bind_ok h
      have hV : Vec Index v ys := encVec_sound_id (fun y _ b hb => by
        cases Except.ok.inj hb
        exact encIdx_sound y) hv
      cases mode with
      | active x off =>
        simp only at h
        split at h
        · next hx =>
          obtain ⟨a, ha, h⟩ := bind_ok h
          cases Except.ok.inj h
          have hx0 : x = ⟨0⟩ := by
            cases x with
            | mk v => congr 1; exact Fin.ext hx
          subst hx0
          exact .k0 (encU_sound (N := 32) (by decide)) (encExpr_sound ha) hV
        · obtain ⟨a, ha, h⟩ := bind_ok h
          cases Except.ok.inj h
          exact .k2 rfl (encU_sound (N := 32) (by decide)) (encIdx_sound x) (encExpr_sound ha)
            .func hV
      | passive =>
        cases Except.ok.inj h
        exact .k1 rfl (encU_sound (N := 32) (by decide)) .func hV
      | declarative =>
        cases Except.ok.inj h
        exact .k3 rfl (encU_sound (N := 32) (by decide)) .func hV
    · exact encElemExpressions_sound h
  · split at h
    · next hrt =>
      simp only at hrt
      subst hrt
      obtain ⟨v, hv, h⟩ := bind_ok h
      have hV : Vec (Core.Expr Forms.all) v init :=
        encVec_sound_id (fun e _ _ he => encExpr_sound (e := e) he) hv
      cases mode with
      | active x off =>
        simp only at h
        split at h
        · next hx =>
          obtain ⟨a, ha, h⟩ := bind_ok h
          cases Except.ok.inj h
          have hx0 : x = ⟨0⟩ := by
            cases x with
            | mk v => congr 1; exact Fin.ext hx
          subst hx0
          exact .k4 rfl (encU_sound (N := 32) (by decide)) (encExpr_sound ha) hV
        · obtain ⟨a, ha, h⟩ := bind_ok h
          cases Except.ok.inj h
          exact .k6 rfl (encU_sound (N := 32) (by decide)) (encIdx_sound x)
            (encExpr_sound ha) (.abs .func) hV
      | passive =>
        cases Except.ok.inj h
        exact .k5 rfl (encU_sound (N := 32) (by decide)) (.abs .func) hV
      | declarative =>
        cases Except.ok.inj h
        exact .k7 rfl (encU_sound (N := 32) (by decide)) (.abs .func) hV
    · exact encElemExpressions_sound h

/-- The locals a group stands for. -/
def localGroup (p : Nat × Wasm.ValType) : List Wasm.ValType := List.replicate p.1 p.2

theorem groupLocals_flatten :
    ∀ ls : List Wasm.ValType, ((groupLocals ls).map localGroup).flatten = ls
  | [] => rfl
  | t :: ts => by
    have ih := groupLocals_flatten ts
    simp only [groupLocals]
    split
    · next n t' rest hg =>
      rw [hg] at ih
      simp only [List.map_cons, List.flatten_cons, localGroup] at ih
      split
      · next he =>
        subst he
        simp only [List.map_cons, List.flatten_cons, localGroup, List.replicate_succ,
          List.cons_append]
        rw [ih]
      · simp only [List.map_cons, List.flatten_cons, localGroup, List.replicate_one,
          List.singleton_append]
        rw [ih]
    · next hg =>
      rw [hg] at ih
      simp only [List.map_nil, List.flatten_nil] at ih
      subst ih
      rfl

theorem encLocals_sound {ls : List Wasm.ValType} {bs : List UInt8}
    (h : encLocals ls = .ok bs) : Vec (Locals Forms.all) bs ((groupLocals ls).map localGroup) := by
  unfold encLocals at h
  refine encVec_sound (fun p _ b hb => ?_) h
  obtain ⟨a, ha, hb⟩ := bind_ok hb
  obtain ⟨c, hc, hb⟩ := bind_ok hb
  cases Except.ok.inj hb
  exact Locals.mk (encU32_sound ha) (encValType_sound hc)

theorem encCode_sound {f : Wasm.Func} {bs : List UInt8}
    (h : encCode f = .ok bs) : Code Forms.all bs (f.locals, f.body) := by
  unfold encCode at h
  split at h
  · next hlen =>
    obtain ⟨l, hl, h⟩ := bind_ok h
    obtain ⟨e, he, h⟩ := bind_ok h
    obtain ⟨n, hn, h⟩ := bind_ok h
    cases Except.ok.inj h
    have hf := Core.Func.mk (encLocals_sound hl) (encExpr_sound he)
      (by rw [groupLocals_flatten]; exact hlen)
    rw [groupLocals_flatten] at hf
    exact Code.mk (encU32_sound hn) rfl hf
  · exact absurd h throw_ne_ok

theorem startSec_sound {st : Option FuncIdx} {b : List UInt8}
    (h : encSection 8 (if st.isSome then 1 else 0) (encStart st) = .ok b) : StartSec b st := by
  cases st with
  | none =>
    exact StartSec.mk (encSection_sound (G := Start) (xs := []) (fun h0 => (h0 rfl).elim)
      (fun _ => rfl) h)
  | some x =>
    exact StartSec.mk (encSection_sound (G := Start) (xs := [x])
      (fun _ => Start.mk (encIdx_sound x)) (fun h0 => by simp at h0) h)

/-- The data count section under the encoder's policy bit: present exactly when `p`. -/
theorem dataCntSecIf_sound {data : List Wasm.Data} {p : Bool} {dc s : List UInt8}
    (hdc : encU32 data.length = .ok dc)
    (h : encSection 12 (if p then 1 else 0) dc = .ok s) :
    DataCntSec Forms.all s (if p then some data.length else none) := by
  cases p
  · simp only [Bool.false_eq_true, ite_false, encSection, ite_true] at h ⊢
    cases Except.ok.inj h
    exact .absent
  · simp only [ite_true] at h ⊢
    exact DataCntSec.present (ns := [data.length]) rfl
      (encSection_sound (fun _ => DataCnt.mk (encU32_sound hdc)) (fun h0 => absurd h0 one_ne_zero) h)

theorem zipFuncs_map :
    ∀ fs : List Wasm.Func, zipFuncs (fs.map fun f => f.type) (fs.map fun f => (f.locals, f.body)) = fs
  | [] => rfl
  | f :: fs => congrArg (List.cons f) (zipFuncs_map fs)

/-! ## Modules -/

/-- **The encoder is sound for the specification's grammar**, under either data count
policy. -/
theorem encodeModuleWith?_sound {dataCount : Bool} {m : Wasm.Module} {bs : List UInt8}
    (h : encodeModuleWith? dataCount m = .ok bs) : Binary.Core.Encodes bs m := by
  unfold encodeModuleWith? at h
  split at h
  · next hdi =>
    obtain ⟨ty, hty, h⟩ := bind_ok h
    obtain ⟨im, him, h⟩ := bind_ok h
    obtain ⟨fn, hfn, h⟩ := bind_ok h
    obtain ⟨me, hme, h⟩ := bind_ok h
    obtain ⟨tg, htg, h⟩ := bind_ok h
    obtain ⟨gl, hgl, h⟩ := bind_ok h
    obtain ⟨ex, hex, h⟩ := bind_ok h
    obtain ⟨co, hco, h⟩ := bind_ok h
    obtain ⟨da, hda, h⟩ := bind_ok h
    obtain ⟨dc, hdc, h⟩ := bind_ok h
    obtain ⟨tb, htb, h⟩ := bind_ok h
    obtain ⟨el, hel, h⟩ := bind_ok h
    obtain ⟨s1, hs1, h⟩ := bind_ok h
    obtain ⟨s2, hs2, h⟩ := bind_ok h
    obtain ⟨s3, hs3, h⟩ := bind_ok h
    obtain ⟨s4, hs4, h⟩ := bind_ok h
    obtain ⟨s5, hs5, h⟩ := bind_ok h
    obtain ⟨s13, hs13, h⟩ := bind_ok h
    obtain ⟨s6, hs6, h⟩ := bind_ok h
    obtain ⟨s7, hs7, h⟩ := bind_ok h
    obtain ⟨s8, hs8, h⟩ := bind_ok h
    obtain ⟨s9, hs9, h⟩ := bind_ok h
    obtain ⟨s12, hs12, h⟩ := bind_ok h
    obtain ⟨s10, hs10, h⟩ := bind_ok h
    obtain ⟨s11, hs11, h⟩ := bind_ok h
    cases Except.ok.inj h
    have nil_of {α : Type} {l : List α} (h0 : l.length = 0) : l = [] :=
      List.eq_nil_of_length_eq_zero h0
    have hTy : TypeSec Forms.all s1 m.types :=
      encSection_sound (fun _ => encVec_sound_id (fun _ _ _ hr => encRecType_sound hr) hty)
        nil_of hs1
    have hIm : ImportSec Forms.all s2 m.imports :=
      encSection_sound (fun _ => encVec_sound_id (fun _ _ _ hi => encImport_sound hi) him)
        nil_of hs2
    have hFn : FuncSec s3 (m.funcs.map fun f => f.type) :=
      encSection_sound
        (fun _ => encVec_sound (g := fun f => f.type)
          (fun f _ b hb => by cases Except.ok.inj hb; exact encIdx_sound f.type) hfn)
        (fun h0 => by simp [nil_of h0]) hs3
    have hTb : TableSec Forms.all s4 m.tables :=
      encSection_sound (fun _ => encVec_sound_id (fun _ _ _ ht =>
        encTableWith_sound (fun _ _ he => encExpr_sound he) ht) htb)
        nil_of hs4
    have hEl : ElemSec Forms.all s9 m.elems :=
      encSection_sound (fun _ => encVec_sound_id (fun _ _ _ he => encElem_sound he) hel)
        nil_of hs9
    have hMe : MemSec Forms.all s5 m.memories :=
      encSection_sound (fun _ => encVec_sound_id (fun _ _ _ hm => encMemory_sound hm) hme)
        nil_of hs5
    have hTg : TagSec Forms.all s13 m.tags :=
      .present rfl (encSection_sound
        (fun _ => encVec_sound_id
          (fun t _ _ ht => by cases Except.ok.inj ht; exact encTagType_sound t) htg)
        nil_of hs13)
    have hGl : GlobalSec Forms.all s6 m.globals :=
      encSection_sound (fun _ => encVec_sound_id (fun _ _ _ hg => encGlobal_sound hg) hgl)
        nil_of hs6
    have hEx : ExportSec s7 m.exports :=
      encSection_sound (fun _ => encVec_sound_id (fun _ _ _ he => encExport_sound he) hex)
        nil_of hs7
    have hCo : CodeSec Forms.all s10 (m.funcs.map fun f => (f.locals, f.body)) :=
      encSection_sound
        (fun _ => encVec_sound (g := fun f => (f.locals, f.body))
          (fun _ _ _ hc => encCode_sound hc) hco)
        (fun h0 => by simp [nil_of h0]) hs10
    have hDa : DataSec Forms.all s11 m.data :=
      encSection_sound (fun _ => encVec_sound_id (fun _ _ _ hd => encData_sound hd) hda)
        nil_of hs11
    have hM := Core.Module.mk (F := Forms.all) Customs.nil hTy Customs.nil hIm Customs.nil hFn
      Customs.nil hTb Customs.nil hMe Customs.nil hTg
      Customs.nil hGl Customs.nil hEx Customs.nil (startSec_sound hs8) Customs.nil
      hEl Customs.nil (dataCntSecIf_sound hdc hs12) Customs.nil hCo Customs.nil hDa
      Customs.nil (fun n hn => by
        split at hn
        · exact (Option.some.inj hn).symm
        · cases hn) (by
        by_cases hd : (dataCount && !m.data.isEmpty) = true
        · exact Or.inl (by simp [hd])
        · exact Or.inr (by simpa [hd, List.isEmpty_iff] using hdi)) (by simp)
    show Core.Module Forms.all _ m
    convert hM using 1
    · simp only [header, magic, version, List.append_nil, List.nil_append, List.append_assoc,
        List.cons_append]
    · rw [zipFuncs_map]
  · exact absurd h throw_ne_ok

/-- The canonical encoder (data count written whenever there are data segments). -/
theorem encodeModule?_sound {m : Wasm.Module} {bs : List UInt8}
    (h : encodeModule? m = .ok bs) : Binary.Core.Encodes bs m :=
  encodeModuleWith?_sound h

/-- The `ByteArray` output form. -/
theorem encodeModule_sound {input : ByteArray} {m : Wasm.Module} {b : ByteArray}
    (h : encodeModule input m = .ok b) : Binary.Core.Encodes b.data.toList m := by
  unfold encodeModule at h
  cases he : encodeModuleWith? (usesDataIdx m || hasDataCountSection input) m with
  | error e => simp [he, Except.map] at h
  | ok bs =>
    simp only [he, Except.map, Except.ok.injEq] at h
    subst h
    simpa using encodeModuleWith?_sound he

/-- **Checked decoding.** If decoding produced `m` and re-encoding `m` gives back the
input bytes, the input encodes `m`: the untrusted decoder is validated per run. -/
theorem decode_checked {m : Wasm.Module} {input : List UInt8}
    (h : encodeModule? m = .ok input) : Binary.Core.Encodes input m :=
  encodeModule?_sound h

end Silmaril.Wasm.Binaryen.Exe
