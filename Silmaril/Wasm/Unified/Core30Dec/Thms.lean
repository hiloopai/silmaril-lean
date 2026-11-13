module

public import Silmaril.Wasm.Unified.Core30.Thms
public import Silmaril.Wasm.Unified.Core30Dec.Defs

/-!
# Core 3.0 is a faithful model: the encoding decodes

* `uncode?_code`, `mapM_uncatch?`: the inverse codes invert.
* `dec_head`: **decoding inverts encoding**: the decoder recovers every Core 3.0 instruction
  from its opcode parameters, immediates, handler table and bodies.
* `eq_of_heads`: hence the instruction-level encoding is injective.

The consequences for the model are in `Silmaril.Wasm.Unified.Core30Faithful`.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Core30

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Unified Silmaril.Wasm.Atlas

theorem uncode?_code {α : Type} [Code α] (a : α) : uncode? (code a) = some a := by
  unfold uncode?
  split
  · next h => exact congrArg some (Code.inj h.choose_spec)
  · next h => exact absurd ⟨a, rfl⟩ h

theorem uncatch?_catchH (c : Catch) : uncatch? (catchH c) = some c := by
  cases c <;> simp [catchH, uncatch?, uncode?_code]

theorem mapM_uncatch? (cs : List Catch) : (cs.map catchH).mapM uncatch? = some cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [uncatch?_catchH, ih]

set_option linter.unusedSimpArgs false in
/-- **Decoding inverts encoding.** -/
theorem dec_head (i : Instr) : ∃ n ps, head i = .named n ps ∧
    dec ps (immsOf i) (hdlOf i) i.bodies = some i := by
  cases i <;> refine ⟨_, _, rfl, ?_⟩ <;>
    simp only [dec, decAt_0, decAt_1, decAt_2, decAt_3, decAt_4, decAt_5, decAt_6, decAt_7, decAt_8, decAt_9, decAt_10, decAt_11, decAt_12, decAt_13, decAt_14, decAt_15, decAt_16, decAt_17, decAt_18, decAt_19, decAt_20, decAt_21, decAt_22, decAt_23, decAt_24, decAt_25, decAt_26, decAt_27, decAt_28, decAt_29, decAt_30, decAt_31, decAt_32, decAt_33, decAt_34, decAt_35, decAt_36, decAt_37, decAt_38, decAt_39, decAt_40, decAt_41, decAt_42, decAt_43, decAt_44, decAt_45, decAt_46, decAt_47, decAt_48, decAt_49, decAt_50, decAt_51, decAt_52, decAt_53, decAt_54, decAt_55, decAt_56, decAt_57, decAt_58, decAt_59, decAt_60, decAt_61, decAt_62, decAt_63, decAt_64, decAt_65, decAt_66, decAt_67, decAt_68, decAt_69, decAt_70, decAt_71, decAt_72, decAt_73, decAt_74, decAt_75, decAt_76, decAt_77, decAt_78, decAt_79, decAt_80, decAt_81, decAt_82, decAt_83, decAt_84, decAt_85, decAt_86, decAt_87, decAt_88, decAt_89, decAt_90, decAt_91, decAt_92, decAt_93, decAt_94, decAt_95, decAt_96, decAt_97, decAt_98, decAt_99, decAt_100, decAt_101, decAt_102, decAt_103, decAt_104, decAt_105, decAt_106, decAt_107, decAt_108, decAt_109, decAt_110, decAt_111, decAt_112, decAt_113] <;>
    simp only [dec_nop, dec_unreachable, dec_drop, dec_select, dec_block, dec_loop, dec_if_, dec_br, dec_brIf, dec_brTable, dec_brOnNull, dec_brOnNonNull, dec_brOnCast, dec_brOnCastFail, dec_call, dec_callRef, dec_callIndirect, dec_return_, dec_returnCall, dec_returnCallRef, dec_returnCallIndirect, dec_throw, dec_throwRef, dec_tryTable, dec_localGet, dec_localSet, dec_localTee, dec_globalGet, dec_globalSet, dec_tableGet, dec_tableSet, dec_tableSize, dec_tableGrow, dec_tableFill, dec_tableCopy, dec_tableInit, dec_elemDrop, dec_intLoad, dec_floatLoad, dec_intStore, dec_floatStore, dec_vecLoad, dec_vecLoadLane, dec_vecStore, dec_vecStoreLane, dec_memorySize, dec_memoryGrow, dec_memoryFill, dec_memoryCopy, dec_memoryInit, dec_dataDrop, dec_refNull, dec_refIsNull, dec_refAsNonNull, dec_refEq, dec_refTest, dec_refCast, dec_refFunc, dec_refI31, dec_i31Get, dec_structNew, dec_structNewDefault, dec_structGet, dec_structSet, dec_arrayNew, dec_arrayNewDefault, dec_arrayNewFixed, dec_arrayNewData, dec_arrayNewElem, dec_arrayGet, dec_arraySet, dec_arrayLen, dec_arrayFill, dec_arrayCopy, dec_arrayInitData, dec_arrayInitElem, dec_externConvertAny, dec_anyConvertExtern, dec_intConst, dec_floatConst, dec_intUnOp, dec_intBinOp, dec_intTestOp, dec_intRelOp, dec_floatUnOp, dec_floatBinOp, dec_floatRelOp, dec_convert, dec_vecConst, dec_vecUnOp, dec_vecBinOp, dec_vecTernOp, dec_vecTestOp, dec_vecIntUnOp, dec_vecFloatUnOp, dec_vecIntBinOp, dec_vecFloatBinOp, dec_vecIntTernOp, dec_vecFloatTernOp, dec_vecAllTrue, dec_vecIntRelOp, dec_vecFloatRelOp, dec_vecShiftOp, dec_vecBitmask, dec_vecSwizzle, dec_vecShuffle, dec_vecExtUnOp, dec_vecExtBinOp, dec_vecExtTernOp, dec_vecNarrow, dec_vecConvert, dec_vecSplat, dec_vecExtractLane, dec_vecReplaceLane,
      immsOf, hdlOf, Instr.bodies, uncode?_code, mapM_uncatch?, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- **The encoding is injective** on heads, immediates, handler tables and bodies. -/
theorem eq_of_heads {i j : Instr} (hh : head j = head i) (hi : immsOf j = immsOf i)
    (hd : hdlOf j = hdlOf i) (hb : j.bodies = i.bodies) : j = i := by
  obtain ⟨n, ps, hn, hdec⟩ := dec_head i
  obtain ⟨n', ps', hn', hdec'⟩ := dec_head j
  rw [hh, hn] at hn'
  obtain ⟨-, rfl⟩ := Opcode.named.inj hn'
  rw [hi, hd, hb, hdec] at hdec'
  exact (Option.some.inj hdec').symm

end Silmaril.Wasm.Unified.Core30
