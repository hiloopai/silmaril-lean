module

public import Silmaril.Wasm.Binary.Core.Modules
public import Silmaril.Raw.Wasm.SpecTec.Wasm.Lime1.Binary
public import Silmaril.Wasm.Lime1.ToCore
-- Split mechanically from the copied `Lime1Core.lean` for build time; declarations unchanged.
-- Hand copy: source namespaces kept, only import lines rewritten.

/-! # Lime1 and Core 3.0 agree on instruction encodings: opcode tables and immediates

Part of `Silmaril.Raw.Wasm.SpecTec.Wasm.Binary.Lime1Core`, split off for build time.
-/

@[expose] public section

open Silmaril.Wasm.Binary

namespace Silmaril.Wasm.Binary.Lime1Core

open Lime1.Binary (TableIdxZero TableZero ZeroPayload)

/-! ## Binary compatibility of instructions -/

mutual
/-- All alignment exponents in an instruction are below `2^6`. -/
def instrAligns : Lime1.Instr → Bool
  | .block _ body | .loop _ body => exprAligns body
  | .if_ _ left right => exprAligns left && exprAligns right
  | .intLoad _ _ a | .floatLoad _ a | .intStore _ _ a | .floatStore _ a => decide
      (a.align.val < 2 ^ 6)
  | _ => true

/-- All alignment exponents in an expression are below `2^6`. -/
def exprAligns : Lime1.Expr → Bool
  | [] => true
  | i :: is => instrAligns i && exprAligns is
end

/-! ## `u32` zero and the table-zero operand -/

theorem u32_zero_padding : ∀ (k N : Nat), 7 * k < N →
    UN N (List.replicate k 0x80 ++ [0x00]) 0
  | 0, N, _ => by simpa using UN.byte (N := N) 0 (by decide) (by simpa using Nat.two_pow_pos N)
  | k + 1, N, h => by
    have := UN.cont (N := N) 0x80 (by decide) (by omega) (u32_zero_padding k (N - 7) (by omega))
    have e : 2 ^ 7 * 0 + ((0x80 : UInt8).toNat - 2 ^ 7) = 0 := by decide
    rw [e] at this
    simpa [List.replicate_succ] using this

theorem un_zero_payload {N : Nat} {b : Bytes} {v : Nat} (h : UN N b v) (hv : v = 0) :
    ZeroPayload b := by
  induction h with
  | byte n _ _ =>
    have : n = 0 := UInt8.toNat_inj.mp (by simpa using hv)
    subst this
    exact .stop
  | cont n h₁ _ _ ih =>
    have hm := ih (by omega)
    have : n = 0x80 := UInt8.toNat_inj.mp (by simp; omega)
    subst this
    exact .more hm

theorem un_length {N : Nat} {b : Bytes} {v : Nat} (h : UN N b v) : b.length ≤ N / 7 + 1 := by
  induction h with
  | byte => simp
  | cont _ _ h₂ _ ih => simp only [List.length_cons]; omega

theorem tableZero_u32 {b : Bytes} (h : TableZero ⟨b.toArray⟩) : U32 b 0 := by
  obtain ⟨hz, hs⟩ := h
  change ZeroPayload b at hz
  obtain ⟨k, rfl⟩ := (ZeroPayload.iff_padding _).mp hz
  simp [ByteArray.size] at hs
  exact u32_zero_padding k 32 (by omega)

theorem u32_tableZero {b : Bytes} (h : U32 b 0) : TableZero ⟨b.toArray⟩ := by
  refine ⟨un_zero_payload h rfl, ?_⟩
  change b.toArray.size ≤ 5
  have := un_length h
  simp only [List.size_toArray]
  omega

theorem tableIdxZero_core {ov : Bool} {bz : Bytes} (h : TableIdxZero ov bz) :
    Core.ReservedIdx (Core.Forms.ofOverlong ov .tableIdxImm) bz (⟨0⟩ : TableIdx) := by
  cases h with
  | literal => exact .zero
  | padded g h =>
    subst g
    exact .idx rfl (tableZero_u32 h)

theorem tableIdxZero_lime1 {ov : Bool} {bz : Bytes}
    (h : Core.ReservedIdx (Core.Forms.ofOverlong ov .tableIdxImm) bz (⟨0⟩ : TableIdx)) :
    TableIdxZero ov bz := by
  cases h with
  | idx g h =>
    have hov : ov = true := by
      cases ov
      · exact absurd g (by decide)
      · rfl
    exact .padded hov (u32_tableZero h)
  | zero => exact .literal

/-- The memory-index immediates are the reserved byte in both restricted grammars. -/
theorem memIdx_reserved {ov : Bool} {k : IndexKind} {b : Bytes} {x : Idx k}
    (h : Core.ReservedIdx (Core.Forms.ofOverlong ov .memIdxImm) b x) :
    b = [0x00] ∧ x = ⟨0⟩ := by
  cases h with
  | idx g _ => cases ov <;> exact absurd g (by decide)
  | zero => exact ⟨rfl, rfl⟩

/-! ## Opcode tables -/

theorem plainOp_core {op : UInt8} {i : Lime1.Instr} (h : Lime1.Binary.PlainOp op i) :
    Core.PlainOp op i.toCore := by
  cases h with
  | rx00 => exact .rx00
  | rx01 => exact .rx01
  | rx1A => exact .rx1A
  | rx1B => exact .rx1B
  | rx0F => exact .rx0F
  | rx45 => exact .rx45
  | rx46 => exact .rx46
  | rx47 => exact .rx47
  | rx48 => exact .rx48
  | rx49 => exact .rx49
  | rx4A => exact .rx4A
  | rx4B => exact .rx4B
  | rx4C => exact .rx4C
  | rx4D => exact .rx4D
  | rx4E => exact .rx4E
  | rx4F => exact .rx4F
  | rx50 => exact .rx50
  | rx51 => exact .rx51
  | rx52 => exact .rx52
  | rx53 => exact .rx53
  | rx54 => exact .rx54
  | rx55 => exact .rx55
  | rx56 => exact .rx56
  | rx57 => exact .rx57
  | rx58 => exact .rx58
  | rx59 => exact .rx59
  | rx5A => exact .rx5A
  | rx5B => exact .rx5B
  | rx5C => exact .rx5C
  | rx5D => exact .rx5D
  | rx5E => exact .rx5E
  | rx5F => exact .rx5F
  | rx60 => exact .rx60
  | rx61 => exact .rx61
  | rx62 => exact .rx62
  | rx63 => exact .rx63
  | rx64 => exact .rx64
  | rx65 => exact .rx65
  | rx66 => exact .rx66
  | rx67 => exact .rx67
  | rx68 => exact .rx68
  | rx69 => exact .rx69
  | rx6A => exact .rx6A
  | rx6B => exact .rx6B
  | rx6C => exact .rx6C
  | rx6D => exact .rx6D
  | rx6E => exact .rx6E
  | rx6F => exact .rx6F
  | rx70 => exact .rx70
  | rx71 => exact .rx71
  | rx72 => exact .rx72
  | rx73 => exact .rx73
  | rx74 => exact .rx74
  | rx75 => exact .rx75
  | rx76 => exact .rx76
  | rx77 => exact .rx77
  | rx78 => exact .rx78
  | rx79 => exact .rx79
  | rx7A => exact .rx7A
  | rx7B => exact .rx7B
  | rxC0 => exact .rxC0
  | rxC1 => exact .rxC1
  | rxC2 => exact .rxC2
  | rxC3 => exact .rxC3
  | rxC4 => exact .rxC4
  | rx7C => exact .rx7C
  | rx7D => exact .rx7D
  | rx7E => exact .rx7E
  | rx7F => exact .rx7F
  | rx80 => exact .rx80
  | rx81 => exact .rx81
  | rx82 => exact .rx82
  | rx83 => exact .rx83
  | rx84 => exact .rx84
  | rx85 => exact .rx85
  | rx86 => exact .rx86
  | rx87 => exact .rx87
  | rx88 => exact .rx88
  | rx89 => exact .rx89
  | rx8A => exact .rx8A
  | rx8B => exact .rx8B
  | rx8C => exact .rx8C
  | rx8D => exact .rx8D
  | rx8E => exact .rx8E
  | rx8F => exact .rx8F
  | rx90 => exact .rx90
  | rx91 => exact .rx91
  | rx92 => exact .rx92
  | rx93 => exact .rx93
  | rx94 => exact .rx94
  | rx95 => exact .rx95
  | rx96 => exact .rx96
  | rx97 => exact .rx97
  | rx98 => exact .rx98
  | rx99 => exact .rx99
  | rx9A => exact .rx9A
  | rx9B => exact .rx9B
  | rx9C => exact .rx9C
  | rx9D => exact .rx9D
  | rx9E => exact .rx9E
  | rx9F => exact .rx9F
  | rxA0 => exact .rxA0
  | rxA1 => exact .rxA1
  | rxA2 => exact .rxA2
  | rxA3 => exact .rxA3
  | rxA4 => exact .rxA4
  | rxA5 => exact .rxA5
  | rxA6 => exact .rxA6
  | rxA7 => exact .rxA7
  | rxA8 => exact .rxA8
  | rxA9 => exact .rxA9
  | rxAA => exact .rxAA
  | rxAB => exact .rxAB
  | rxAC => exact .rxAC
  | rxAD => exact .rxAD
  | rxAE => exact .rxAE
  | rxAF => exact .rxAF
  | rxB0 => exact .rxB0
  | rxB1 => exact .rxB1
  | rxB2 => exact .rxB2
  | rxB3 => exact .rxB3
  | rxB4 => exact .rxB4
  | rxB5 => exact .rxB5
  | rxB6 => exact .rxB6
  | rxB7 => exact .rxB7
  | rxB8 => exact .rxB8
  | rxB9 => exact .rxB9
  | rxBA => exact .rxBA
  | rxBB => exact .rxBB
  | rxBC => exact .rxBC
  | rxBD => exact .rxBD
  | rxBE => exact .rxBE
  | rxBF => exact .rxBF

theorem plainOp_lime1 {op : UInt8} {i : Lime1.Instr} (h : Core.PlainOp op i.toCore) :
    Lime1.Binary.PlainOp op i := by
  cases i with
  | intUnOp t o =>
    rcases o with _ | _ | _ | s
    · cases h <;> constructor
    · cases h <;> constructor
    · cases h <;> constructor
    · cases s <;> cases h <;> constructor
  | _ => cases h <;> constructor

theorem prefixFCOp_core {n : Nat} {i : Lime1.Instr} (h : Lime1.Binary.PrefixFCOp n i) :
    Core.PrefixFCOp n i.toCore := by
  cases h <;> constructor

theorem prefixFCOp_lime1 {n : Nat} {i : Lime1.Instr} (h : Core.PrefixFCOp n i.toCore) :
    Lime1.Binary.PrefixFCOp n i := by
  cases i <;> cases h <;> constructor

/-! ## Immediates -/

theorem valType_core {b : Bytes} {t : Lime1.ValType} (h : V1.Binary.ValType b t) :
    Core.NumType b t := by
  cases h <;> constructor

theorem valType_lime1 {F : Core.Forms} {b : Bytes} {t : Lime1.ValType}
    (h : Core.ValType F b (.num t)) : V1.Binary.ValType b t := by
  cases h with
  | num h => cases h <;> constructor

theorem blockType_core {F : Core.Forms} {bt : Bytes} {t : Lime1.BlockType}
    (h : Lime1.Binary.BlockType bt t) : Core.BlockType F bt t.toCore := by
  cases h with
  | empty => exact .empty
  | value h => exact .value (.num (valType_core h))
  | idx i h => exact .idx i h

theorem blockType_lime1 {F : Core.Forms} {bt : Bytes} {t : Lime1.BlockType}
    (h : Core.BlockType F bt t.toCore) : Lime1.Binary.BlockType bt t := by
  cases t with
  | empty =>
    cases h with
    | empty => exact .empty
  | value t => cases h with
    | value h => exact .value (valType_lime1 h)
  | typeIdx i => cases h with
    | idx _ h => exact .idx i h

theorem memarg_core {ov : Bool} {b : Bytes} {a : Lime1.MemArg} (h : V1.Binary.Memarg b a)
    (ha : a.align.val < 2 ^ 6) :
    Core.Memarg (Core.Forms.ofOverlong ov) b (⟨0⟩, a.toCore) := by
  cases h with
  | mk hn ho => exact .mem0 hn ha (.u32 ho)

theorem memarg_lime1 {ov : Bool} {b : Bytes} {p : MemIdx × Wasm.MemArg}
    (h : Core.Memarg (Core.Forms.ofOverlong ov) b p) {a : Lime1.MemArg}
    (hp : p = (⟨0⟩, a.toCore)) : V1.Binary.Memarg b a := by
  cases h with
  | mem0 hn _ hm =>
    obtain ⟨al, o⟩ := a
    simp only [V1.MemArg.toCore, Prod.mk.injEq, Wasm.MemArg.mk.injEq, true_and] at hp
    obtain ⟨rfl, rfl⟩ := hp
    cases hm with
    | u64 g _ => cases ov <;> exact absurd g (by decide)
    | u32 h => exact .mk hn h
  | memIdx g => cases ov <;> exact absurd g (by decide)

theorem loadPackToCore_eq_iff {p : Option (Lime1.PackSize × Signedness)}
    {q : Option (Wasm.PackSize × Signedness)} :
    Lime1.loadPackToCore p = q ↔ Lime1.loadPackOfCore? q = some p := by
  rcases p with _ | ⟨n, s⟩ <;> rcases q with _ | ⟨n', s'⟩ <;> (try cases n) <;> (try cases n') <;>
    simp [Lime1.loadPackToCore, Lime1.loadPackOfCore?, V1.PackSize.toCore,
      V1.PackSize.ofCore?, eq_comm]

theorem packSize_toCore_eq_iff {p : Lime1.PackSize} {q : Wasm.PackSize} :
    p.toCore = q ↔ V1.PackSize.ofCore? q = some p := by
  cases p <;> cases q <;> simp [V1.PackSize.toCore, V1.PackSize.ofCore?]

theorem mem_core {ov : Bool} {op : UInt8} {b : Bytes} {mk : Lime1.MemArg → Lime1.Instr}
    {a : Lime1.MemArg} (h : Lime1.Binary.MemOp op mk) (hm : V1.Binary.Memarg b a)
    (ha : instrAligns (mk a) = true) :
    Core.Instr (Core.Forms.ofOverlong ov) ([op] ++ b) (mk a).toCore := by
  have hal : a.align.val < 2 ^ 6 := by cases h <;> simpa [instrAligns] using ha
  have hm' := memarg_core (ov := ov) hm hal
  cases h with
  | rx28 => exact Core.Instr.mem .rx28 hm'
  | rx29 => exact Core.Instr.mem .rx29 hm'
  | rx2A => exact Core.Instr.mem .rx2A hm'
  | rx2B => exact Core.Instr.mem .rx2B hm'
  | rx2C => exact Core.Instr.mem .rx2C hm'
  | rx2D => exact Core.Instr.mem .rx2D hm'
  | rx2E => exact Core.Instr.mem .rx2E hm'
  | rx2F => exact Core.Instr.mem .rx2F hm'
  | rx30 => exact Core.Instr.mem .rx30 hm'
  | rx31 => exact Core.Instr.mem .rx31 hm'
  | rx32 => exact Core.Instr.mem .rx32 hm'
  | rx33 => exact Core.Instr.mem .rx33 hm'
  | rx34 => exact Core.Instr.mem .rx34 hm'
  | rx35 => exact Core.Instr.mem .rx35 hm'
  | rx36 => exact Core.Instr.mem .rx36 hm'
  | rx37 => exact Core.Instr.mem .rx37 hm'
  | rx38 => exact Core.Instr.mem .rx38 hm'
  | rx39 => exact Core.Instr.mem .rx39 hm'
  | rx3A => exact Core.Instr.mem .rx3A hm'
  | rx3B => exact Core.Instr.mem .rx3B hm'
  | rx3C => exact Core.Instr.mem .rx3C hm'
  | rx3D => exact Core.Instr.mem .rx3D hm'
  | rx3E => exact Core.Instr.mem .rx3E hm'

theorem mem_lime1 {ov : Bool} {op : UInt8} {b : Bytes} {mk : MemIdx → Wasm.MemArg → Wasm.Instr}
    {x : MemIdx} {ao : Wasm.MemArg} {i : Lime1.Instr} (h : Core.MemOp op mk)
    (hm : Core.Memarg (Core.Forms.ofOverlong ov) b (x, ao)) (hc : mk x ao = i.toCore) :
    Lime1.Binary.Instr ov ([op] ++ b) i := by
  replace hc := hc.symm
  cases h with
  | rx28 =>
    cases i <;> simp [Lime1.Instr.toCore, loadPackToCore_eq_iff, Lime1.loadPackOfCore?] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx28 (memarg_lime1 hm rfl)
  | rx29 =>
    cases i <;> simp [Lime1.Instr.toCore, loadPackToCore_eq_iff, Lime1.loadPackOfCore?] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx29 (memarg_lime1 hm rfl)
  | rx2A =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx2A (memarg_lime1 hm rfl)
  | rx2B =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx2B (memarg_lime1 hm rfl)
  | rx2C =>
    cases i <;> simp [Lime1.Instr.toCore, loadPackToCore_eq_iff, Lime1.loadPackOfCore?,
        V1.PackSize.ofCore?] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx2C (memarg_lime1 hm rfl)
  | rx2D =>
    cases i <;> simp [Lime1.Instr.toCore, loadPackToCore_eq_iff, Lime1.loadPackOfCore?,
        V1.PackSize.ofCore?] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx2D (memarg_lime1 hm rfl)
  | rx2E =>
    cases i <;> simp [Lime1.Instr.toCore, loadPackToCore_eq_iff, Lime1.loadPackOfCore?,
        V1.PackSize.ofCore?] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx2E (memarg_lime1 hm rfl)
  | rx2F =>
    cases i <;> simp [Lime1.Instr.toCore, loadPackToCore_eq_iff, Lime1.loadPackOfCore?,
        V1.PackSize.ofCore?] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx2F (memarg_lime1 hm rfl)
  | rx30 =>
    cases i <;> simp [Lime1.Instr.toCore, loadPackToCore_eq_iff, Lime1.loadPackOfCore?,
        V1.PackSize.ofCore?] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx30 (memarg_lime1 hm rfl)
  | rx31 =>
    cases i <;> simp [Lime1.Instr.toCore, loadPackToCore_eq_iff, Lime1.loadPackOfCore?,
        V1.PackSize.ofCore?] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx31 (memarg_lime1 hm rfl)
  | rx32 =>
    cases i <;> simp [Lime1.Instr.toCore, loadPackToCore_eq_iff, Lime1.loadPackOfCore?,
        V1.PackSize.ofCore?] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx32 (memarg_lime1 hm rfl)
  | rx33 =>
    cases i <;> simp [Lime1.Instr.toCore, loadPackToCore_eq_iff, Lime1.loadPackOfCore?,
        V1.PackSize.ofCore?] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx33 (memarg_lime1 hm rfl)
  | rx34 =>
    cases i <;> simp [Lime1.Instr.toCore, loadPackToCore_eq_iff, Lime1.loadPackOfCore?,
        V1.PackSize.ofCore?] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx34 (memarg_lime1 hm rfl)
  | rx35 =>
    cases i <;> simp [Lime1.Instr.toCore, loadPackToCore_eq_iff, Lime1.loadPackOfCore?,
        V1.PackSize.ofCore?] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx35 (memarg_lime1 hm rfl)
  | rx36 =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx36 (memarg_lime1 hm rfl)
  | rx37 =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx37 (memarg_lime1 hm rfl)
  | rx38 =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx38 (memarg_lime1 hm rfl)
  | rx39 =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx39 (memarg_lime1 hm rfl)
  | rx3A =>
    cases i <;> simp [Lime1.Instr.toCore, packSize_toCore_eq_iff, V1.PackSize.ofCore?] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx3A (memarg_lime1 hm rfl)
  | rx3B =>
    cases i <;> simp [Lime1.Instr.toCore, packSize_toCore_eq_iff, V1.PackSize.ofCore?] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx3B (memarg_lime1 hm rfl)
  | rx3C =>
    cases i <;> simp [Lime1.Instr.toCore, packSize_toCore_eq_iff, V1.PackSize.ofCore?] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx3C (memarg_lime1 hm rfl)
  | rx3D =>
    cases i <;> simp [Lime1.Instr.toCore, packSize_toCore_eq_iff, V1.PackSize.ofCore?] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx3D (memarg_lime1 hm rfl)
  | rx3E =>
    cases i <;> simp [Lime1.Instr.toCore, packSize_toCore_eq_iff, V1.PackSize.ofCore?] at hc
    casesm* _ ∧ _
    subst_vars
    exact .mem .rx3E (memarg_lime1 hm rfl)

end Silmaril.Wasm.Binary.Lime1Core
