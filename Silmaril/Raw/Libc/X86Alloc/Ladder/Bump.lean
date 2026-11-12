module

public import Silmaril.Libc.X86Alloc.Ladder.Bump.Defs
public import Silmaril.Raw.Libc.X86Alloc.Steps
public import Silmaril.X86.Sep.Alloc.Thms

/-! # Proofs: rung 02 (`bump`) meets its reference model -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.Bump

open Silmaril.X86 (Word Byte Reg)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Insn
open Silmaril.Libc.X86Alloc.Ladder.Bump
open Silmaril.Raw.Libc.X86Alloc.Frame
open Silmaril.Raw.Libc.X86Alloc.Steps

theorem post_fail (u : Nat) (n : Word) (hu : u ≤ size) (hfail : ¬ n.toNat ≤ size - u)
    (v : Word) (hv : v = 0) :
    (wordPt usedAddr (BitVec.ofNat 64 u) ∗ blockAny (arena + u) (size - u) ∗ strue) ⊢ₛ
      (mallocSpecF iface).post (u, n) v := by
  subst hv
  have hm : ref.malloc u n.toNat = 0 := by simp [ref, hfail]
  show _ ⊢ₛ (⌜(0 : Word) = ref.malloc u n.toNat⌝ ∗ sor (⌜(0 : Word) = 0⌝ ∗
    (⌜u ≤ size⌝ ∗ wordPt usedAddr (BitVec.ofNat 64 u) ∗ blockAny (arena + u) (size - u) ∗ strue))
    _)
  exact spure_sep_intro hm.symm (entails_trans (spure_sep_intro rfl (spure_sep_intro hu
    (entails_refl _))) (sor_intro_left _ _))

theorem post_ok (u : Nat) (n : Word) (hu : u ≤ size) (hok : n.toNat ≤ size - u) (w v : Word)
    (hw : w = BitVec.ofNat 64 (u + n.toNat)) (hv : v = BitVec.ofNat 64 (arena + u)) :
    (wordPt usedAddr w ∗ blockAny (arena + u) (size - u) ∗ strue) ⊢ₛ
      (mallocSpecF iface).post (u, n) v := by
  subst hw hv
  have hu' : u ≤ 4096 := hu
  have hok' : n.toNat ≤ 4096 - u := hok
  have hvn : (BitVec.ofNat 64 (arena + u)).toNat = arena + u := by
    simp only [BitVec.toNat_ofNat, arena]; omega
  have hv0 : BitVec.ofNat 64 (arena + u) ≠ 0 := by
    intro e; have := congrArg BitVec.toNat e; rw [hvn] at this; simp at this
  have hm : ref.malloc u n.toNat = BitVec.ofNat 64 (arena + u) := by simp [ref, hok]
  have hsplit : blockAny (arena + u) (size - u) = (blockAny (arena + u) n.toNat ∗
      blockAny (arena + (u + n.toNat)) (size - (u + n.toNat))) := by
    rw [show size - u = n.toNat + (size - (u + n.toNat)) by simp only [size]; omega, blockAny_add,
      Nat.add_assoc]
  show _ ⊢ₛ (⌜_ = ref.malloc u n.toNat⌝ ∗ sor _
    ((⌜BitVec.ofNat 64 (arena + u) ≠ 0 ∧ (BitVec.ofNat 64 (arena + u)).toNat % 1 = 0⌝ ∗ emp ∗
      blockAny (BitVec.ofNat 64 (arena + u)).toNat n.toNat) ∗
      (⌜u + n.toNat ≤ size⌝ ∗ wordPt usedAddr (BitVec.ofNat 64 (u + n.toNat)) ∗
        blockAny (arena + (u + n.toNat)) (size - (u + n.toNat)) ∗ strue)))
  refine spure_sep_intro hm.symm (entails_trans ?_ (sor_intro_right _ _))
  rw [hvn, emp_sep, hsplit]
  refine entails_trans ?_ (entails_of_eq (show (⌜BitVec.ofNat 64 (arena + u) ≠ 0 ∧
    (arena + u) % 1 = 0⌝ ∗ ⌜u + n.toNat ≤ size⌝ ∗ (blockAny (arena + u) n.toNat ∗
      wordPt usedAddr (BitVec.ofNat 64 (u + n.toNat)) ∗
      blockAny (arena + (u + n.toNat)) (size - (u + n.toNat)) ∗ strue)) = _ by ac_rfl))
  exact spure_sep_intro ⟨hv0, Nat.mod_one _⟩ (spure_sep_intro (by simp only [size]; omega)
    (entails_of_eq (by ac_rfl)))

/-! ## The listing, decoded once (kernel evaluation) -/

theorem d0 : Silmaril.X86.Ext.decode ((code.drop 0).take 7) = some (.load .q .rax (ripMem 0x1d51), 7) := by
  decide +kernel
theorem d7 : Silmaril.X86.Ext.decode ((code.drop 7).take 5) = some (.movI32 .rdx 0x1000, 5) := by
  decide +kernel
theorem d12 : Silmaril.X86.Ext.decode ((code.drop 12).take 3) = some (.alu .q .sub (.reg .rdx) .rax, 3) := by
  decide +kernel
theorem d15 : Silmaril.X86.Ext.decode ((code.drop 15).take 3) = some (.alu .q .cmp (.reg .rdx) .rdi, 3) := by
  decide +kernel
theorem d18 : Silmaril.X86.Ext.decode ((code.drop 18).take 2) = some (.jcc8 .b 0x14, 2) := by
  decide +kernel
theorem d20 : Silmaril.X86.Ext.decode ((code.drop 20).take 3) = some (.alu .q .add (.reg .rdi) .rax, 3) := by
  decide +kernel
theorem d23 : Silmaril.X86.Ext.decode ((code.drop 23).take 6) = some (.aluA .q .add 0x4030a0, 6) := by
  decide +kernel
theorem d29 : Silmaril.X86.Ext.decode ((code.drop 29).take 7) = some (.mov .q (.mem (ripMem 0x1d34)) .rdi, 7) := by
  decide +kernel
theorem d40 : Silmaril.X86.Ext.decode ((code.drop 40).take 2) = some (.alu .d .xor (.reg .rax) .rax, 2) := by
  decide +kernel
theorem r36 : (code.drop 36).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem r42 : (code.drop 42).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem r48 : (code.drop 48).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem hlen : code.length = 64 := by decide +kernel
theorem fit (o k : Nat) (h : o + k ≤ 64 := by decide) : o + k ≤ code.length := hlen ▸ h

theorem malloc_sat :
    (mallocSpecF iface).Sat Silmaril.X86.Open.isa layout.C layout.mallocAt := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine satWith_of_St rfl (fun x => x.2) (fun _ => rfl) fun x sp ret f fl _ hsp hdi => ?_
  obtain ⟨u, n⟩ := x
  change Nat at u
  dsimp only at hdi ⊢
  change SPEC _ (codePt 0x401330 code) (St _ f fl (wordPt sp.toNat ret ∗ (⌜u ≤ size⌝ ∗ _))) _
  rw [St_pure]
  refine SPEC.spure fun hu => ?_
  have hu' : u ≤ 4096 := hu
  have hu64 : u < 2 ^ 64 := by omega
  refine SPEC.mem (M' := wordPt usedAddr (BitVec.ofNat 64 u) ∗ wordPt sp.toNat ret ∗
    blockAny (arena + u) (size - u) ∗ strue) (by dsimp only; ac_rfl) ?_
  refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 0) (k := 7)
    (pc := 0x401330) (pc' := 0x401337) rfl (fit 0 7) (dst := .rax) (by decide) (disp := 0x1d51)
    d0 (by decide) (by decide)) ?_
  refine SPEC.trans (c_movI32 E (b := 0x401330) (code := code) (o := 7) (k := 5) (pc := 0x401337)
    (pc' := 0x40133c) (by decide) (fit 7 5) (r := .rdx) (imm := 0x1000) (by decide) d7
    (by decide)) ?_
  refine SPEC.trans (c_alu E (b := 0x401330) (code := code) (o := 12) (k := 3) (pc := 0x40133c)
    (by decide) (fit 12 3) (op := .sub) (by decide) (r := .rdx) (q := .rax) (by decide)
    (by decide) (by decide) d12) ?_
  refine SPEC.trans (c_cmp E (b := 0x401330) (code := code) (o := 15) (k := 3)
    (pc := 0x40133c + 3#64) (by decide) (fit 15 3) (r := .rdx) (q := .rdi) (by decide) (by decide)
    (by decide) d15) ?_
  have hsub : (Silmaril.X86.Ext.AluOp.resultN .sub (BitVec.setWidth 64 (0x1000 : BitVec 32))
      (BitVec.ofNat 64 u)).toNat = 4096 - u := by
    show (BitVec.setWidth 64 (0x1000 : BitVec 32) - BitVec.ofNat 64 u).toNat = _
    have hle : BitVec.ofNat 64 u ≤ 4096#64 := by
      rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu64]; exact hu'
    rw [show BitVec.setWidth 64 (0x1000 : BitVec 32) = 4096#64 by decide +kernel,
      BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu64]
  have hs : size = 4096 := rfl
  by_cases hok : n.toNat ≤ size - u
  · refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 18) (k := 2)
      (pc := 0x40133c + 3#64 + 3#64) (pc' := 0x401344) (by decide) (fit 18 2) (c := .b)
      (rel := 0x14) ?_ d18 (by decide)) ?_
    · rw [eval_b_cmp]
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hdi, hsub]
      simp only [Option.some.injEq, decide_eq_false_iff_not]; omega
    refine SPEC.trans (c_alu E (b := 0x401330) (code := code) (o := 20) (k := 3) (pc := 0x401344)
      (by decide) (fit 20 3) (op := .add) (by decide) (r := .rdi) (q := .rax) (by decide)
      (by decide) (by decide) d20) ?_
    refine SPEC.trans (c_aluA E (b := 0x401330) (code := code) (o := 23) (k := 6)
      (pc := 0x401344 + 3#64) (by decide) (fit 23 6) (op := .add) (by decide) (imm := 0x4030a0)
      d23) ?_
    refine SPEC.trans (c_storeRip E (b := 0x401330) (code := code) (o := 29) (k := 7)
      (pc := 0x401344 + 3#64 + 6#64) (pc' := 0x401354) (by decide) (fit 29 7) (src := .rdi)
      (by decide) (disp := 0x1d34) (wordPt_blockAny _ _) d29 (by decide) (by decide)) ?_
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ wordPt usedAddr _ ∗
      blockAny (arena + u) (size - u) ∗ strue) (by ac_rfl) ?_
    refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 36)
      (k := 1) (pc := 0x401354) (by decide) (fit 36 1)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp]) r36) ?_
    refine St_post rfl (by simp only [Function.update_self]) (post_ok u n hu hok _ _ ?_ ?_)
    · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hdi,
        Silmaril.X86.Ext.AluOp.resultN]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu64]
      omega
    · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Silmaril.X86.Ext.AluOp.resultN]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu64,
        show (BitVec.signExtend 64 (0x4030a0 : BitVec 32)).toNat = arena by decide +kernel]
      simp only [arena]; omega
  · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 18) (k := 2)
      (pc := 0x40133c + 3#64 + 3#64) (pc' := 0x401358) (by decide) (fit 18 2) (c := .b)
      (rel := 0x14) ?_ d18 (by decide)) ?_
    · rw [eval_b_cmp]
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hdi, hsub]
      simp only [Option.some.injEq, decide_eq_true_eq]; omega
    refine SPEC.trans (c_xor32 E (b := 0x401330) (code := code) (o := 40) (k := 2)
      (pc := 0x401358) (by decide) (fit 40 2) (r := .rax) (by decide) d40) ?_
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ wordPt usedAddr (BitVec.ofNat 64 u) ∗
      blockAny (arena + u) (size - u) ∗ strue) (by ac_rfl) ?_
    refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 42)
      (k := 1) (pc := 0x401358 + 2#64) (by decide) (fit 42 1)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp]) r42) ?_
    exact St_post rfl (by simp only [Function.update_self]) (post_fail u n hu hok _
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]))

theorem free_sat :
    (freeSpecF iface).Sat Silmaril.X86.Open.isa layout.C layout.freeAt := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine satWith_of_St rfl (fun x => x.p) (fun _ => rfl) fun x sp ret f fl _ hsp _ => ?_
  refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 48) (k := 1)
    rfl (fit 48 1) hsp r48) ?_
  refine St_post rfl (by simp [Function.update]) ?_
  rcases x with ⟨s, p, _ | n⟩
  · show (iface.mmS s ∗ ⌜p = 0⌝) ⊢ₛ iface.mmS s
    rw [sep_comm]; exact spure_sep_elim fun _ => entails_refl _
  · change Nat at s
    show ((⌜s ≤ size⌝ ∗ wordPt usedAddr (BitVec.ofNat 64 s) ∗ blockAny (arena + s) (size - s) ∗
      strue) ∗ emp ∗ blockAny p.toNat n) ⊢ₛ
      (⌜s ≤ size⌝ ∗ wordPt usedAddr (BitVec.ofNat 64 s) ∗ blockAny (arena + s) (size - s) ∗ strue)
    refine entails_trans (entails_of_eq (show _ = ((⌜s ≤ size⌝ ∗ wordPt usedAddr (BitVec.ofNat 64 s) ∗
      blockAny (arena + s) (size - s)) ∗ (strue ∗ emp ∗ blockAny p.toNat n)) by ac_rfl))
      (entails_trans (sep_mono_right _ (entails_strue _)) (entails_of_eq (by ac_rfl)))

/-- **The loaded image establishes the allocator's state** at `used = 0`. -/
theorem init : layout.Init ⊢ₛ iface.mmS (0 : Nat) := by
  show bytesPt usedAddr (List.replicate (arena + size - usedAddr) 0) ⊢ₛ
    (⌜0 ≤ size⌝ ∗ wordPt usedAddr (BitVec.ofNat 64 0) ∗ blockAny (arena + 0) (size - 0) ∗ strue)
  have hw : Silmaril.Machine.LittleEndian.encodeWords [BitVec.ofNat 64 0] =
      List.replicate 8 (0 : Byte) := by decide
  rw [show arena + size - usedAddr = 8 + (16 + 4096) from rfl, List.replicate_add,
    List.replicate_add, bytesPt, bytesAt_append, bytesAt_append, wordPt, hw]
  simp only [List.length_replicate]
  refine spure_sep_intro (Nat.zero_le _) (sep_mono (entails_refl _) ?_)
  refine entails_trans (entails_of_eq (sep_comm _ _)) (sep_mono ?_ (entails_strue _))
  refine entails_trans (bytesPt_blockAny _ _) (entails_of_eq ?_)
  rw [List.length_replicate]
  congr 1

end Silmaril.Raw.Libc.X86Alloc.Ladder.Bump
