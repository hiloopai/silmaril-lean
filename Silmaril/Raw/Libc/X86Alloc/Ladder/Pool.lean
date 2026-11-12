module

public import Silmaril.Libc.X86Alloc.Ladder.Pool.Defs
public import Silmaril.Raw.Libc.X86Alloc.Steps
public import Silmaril.X86.Sep.Alloc.Thms

/-! # Proofs: rung 04 (`pool`) meets its LIFO reference model -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.Pool

open Silmaril.X86 (Word Byte Reg)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Insn
open Silmaril.Libc.X86Alloc.Ladder.Pool
open Silmaril.Raw.Libc.X86Alloc.Frame
open Silmaril.Raw.Libc.X86Alloc.Steps

/-- Fold the allocator state. -/
theorem fold (ps : List Word) (k : Nat) (h : Word) (hk : k ≤ 64) :
    (wordPt headAddr h ∗ flist ps h ∗ wordPt nextAddr (BitVec.ofNat 64 k) ∗
      blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue) ⊢ₛ iface.mmS (ps, k) :=
  sexists_intro h (spure_sep_intro hk (entails_refl _))

/-- A failing call. -/
theorem post_fail (s : List Word × Nat) (n : Word) (hm : ref.malloc s n.toNat = 0) {M : SProp}
    (hM : M ⊢ₛ iface.mmS s) (v : Word) (hv : v = 0) :
    M ⊢ₛ (mallocSpecF iface).post (s, n) v := by
  subst hv
  show M ⊢ₛ (⌜(0 : Word) = ref.malloc s n.toNat⌝ ∗ sor (⌜(0 : Word) = 0⌝ ∗ iface.mmS s) _)
  exact spure_sep_intro hm.symm (entails_trans (spure_sep_intro rfl hM) (sor_intro_left _ _))

/-- A 64-byte block from its first word and the rest. -/
theorem block64 (p : Word) (q : Word) (n : Nat) (hn : n ≤ 64) :
    (wordPt p.toNat q ∗ blockAny (p.toNat + 8) 56) ⊢ₛ
      (blockAny p.toNat n ∗ blockAny (p.toNat + n) (64 - n)) := by
  refine entails_trans (sep_mono_left _ (wordPt_blockAny _ _)) (entails_of_eq ?_)
  rw [← blockAny_add, ← blockAny_add, Nat.add_sub_cancel' hn]

/-- Popping the free list. -/
theorem post_pop (p q : Word) (ps : List Word) (k : Nat) (n : Word) (hk : k ≤ 64)
    (hn : ¬ 64 < n.toNat) (hp : p ≠ 0 ∧ p.toNat % 16 = 0) (v : Word) (hv : v = p) :
    (wordPt headAddr q ∗ wordPt p.toNat q ∗ blockAny (p.toNat + 8) 56 ∗ flist ps q ∗
      wordPt nextAddr (BitVec.ofNat 64 k) ∗ blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue) ⊢ₛ
      (mallocSpecF iface).post ((p :: ps, k), n) v := by
  rw [hv]
  have hm : ref.malloc (p :: ps, k) n.toNat = p := by simp [ref, hn]
  have hn' : n.toNat ≤ 64 := by omega
  show _ ⊢ₛ (⌜p = ref.malloc (p :: ps, k) n.toNat⌝ ∗ sor _
    ((⌜p ≠ 0 ∧ p.toNat % 16 = 0⌝ ∗ (⌜n.toNat ≤ 64 ∧ p ≠ 0 ∧ p.toNat % 16 = 0⌝ ∗
      blockAny (p.toNat + n.toNat) (64 - n.toNat)) ∗ blockAny p.toNat n.toNat) ∗
      iface.mmS (ps, k)))
  refine spure_sep_intro hm.symm (entails_trans ?_ (sor_intro_right _ _))
  refine entails_trans (entails_of_eq (show _ = ((wordPt p.toNat q ∗ blockAny (p.toNat + 8) 56) ∗
    (wordPt headAddr q ∗ flist ps q ∗ wordPt nextAddr (BitVec.ofNat 64 k) ∗
      blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue)) by ac_rfl))
    (sep_mono (block64 p q _ hn') (fold ps k q hk) |> entails_trans <| ?_)
  refine entails_trans ?_ (entails_of_eq (show (⌜p ≠ 0 ∧ p.toNat % 16 = 0⌝ ∗
    ⌜n.toNat ≤ 64 ∧ p ≠ 0 ∧ p.toNat % 16 = 0⌝ ∗ ((blockAny p.toNat n.toNat ∗
      blockAny (p.toNat + n.toNat) (64 - n.toNat)) ∗ iface.mmS (ps, k))) = _ by ac_rfl))
  exact spure_sep_intro hp (spure_sep_intro ⟨hn', hp⟩ (entails_refl _))

/-- Handing out a never-used block. -/
theorem post_bump (k : Nat) (n : Word) (hk : ¬ 63 < k) (hn : ¬ 64 < n.toNat) (w v : Word)
    (hw : w = BitVec.ofNat 64 (k + 1)) (hv : v = BitVec.ofNat 64 (pool + 64 * k)) :
    (wordPt nextAddr w ∗ wordPt headAddr 0 ∗ blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue) ⊢ₛ
      (mallocSpecF iface).post (([], k), n) v := by
  subst hw hv
  have hn' : n.toNat ≤ 64 := by omega
  have hvn : (BitVec.ofNat 64 (pool + 64 * k)).toNat = pool + 64 * k := by
    simp only [BitVec.toNat_ofNat, pool]; omega
  have hv0 : BitVec.ofNat 64 (pool + 64 * k) ≠ 0 := by
    intro e; have := congrArg BitVec.toNat e; rw [hvn] at this; simp at this
  have hm : ref.malloc ([], k) n.toNat = BitVec.ofNat 64 (pool + 64 * k) := by
    simp [ref, hn, show k < 64 by omega]
  have hsplit : blockAny (pool + 64 * k) (64 * (64 - k)) = (blockAny (pool + 64 * k) n.toNat ∗
      blockAny (pool + 64 * k + n.toNat) (64 - n.toNat) ∗
      blockAny (pool + 64 * (k + 1)) (64 * (64 - (k + 1)))) := by
    rw [show 64 * (64 - k) = n.toNat + ((64 - n.toNat) + 64 * (64 - (k + 1))) by omega,
      blockAny_add, blockAny_add,
      show pool + 64 * k + n.toNat + (64 - n.toNat) = pool + 64 * (k + 1) by omega]
  show _ ⊢ₛ (⌜_ = ref.malloc ([], k) n.toNat⌝ ∗ sor _
    ((⌜BitVec.ofNat 64 (pool + 64 * k) ≠ 0 ∧ (BitVec.ofNat 64 (pool + 64 * k)).toNat % 16 = 0⌝ ∗
      (⌜n.toNat ≤ 64 ∧ BitVec.ofNat 64 (pool + 64 * k) ≠ 0 ∧
        (BitVec.ofNat 64 (pool + 64 * k)).toNat % 16 = 0⌝ ∗
      blockAny ((BitVec.ofNat 64 (pool + 64 * k)).toNat + n.toNat) (64 - n.toNat)) ∗
      blockAny (BitVec.ofNat 64 (pool + 64 * k)).toNat n.toNat) ∗
      iface.mmS ([], k + 1)))
  refine spure_sep_intro hm.symm (entails_trans ?_ (sor_intro_right _ _))
  rw [hvn, hsplit]
  have hal : (pool + 64 * k) % 16 = 0 := by simp only [pool]; omega
  refine entails_trans ?_ (entails_of_eq (show (⌜BitVec.ofNat 64 (pool + 64 * k) ≠ 0 ∧
    (pool + 64 * k) % 16 = 0⌝ ∗ ⌜n.toNat ≤ 64 ∧ BitVec.ofNat 64 (pool + 64 * k) ≠ 0 ∧
      (pool + 64 * k) % 16 = 0⌝ ∗ ((blockAny (pool + 64 * k) n.toNat ∗
      blockAny (pool + 64 * k + n.toNat) (64 - n.toNat)) ∗ iface.mmS ([], k + 1))) = _ by ac_rfl))
  refine spure_sep_intro ⟨hv0, hal⟩ (spure_sep_intro ⟨hn', hv0, hal⟩ ?_)
  refine entails_trans ?_ (sep_mono_right _ (fold [] (k + 1) 0 (by omega)))
  refine entails_trans (entails_of_eq (show _ = ((blockAny (pool + 64 * k) n.toNat ∗
      blockAny (pool + 64 * k + n.toNat) (64 - n.toNat)) ∗ (wordPt headAddr 0 ∗
      wordPt nextAddr (BitVec.ofNat 64 (k + 1)) ∗
      blockAny (pool + 64 * (k + 1)) (64 * (64 - (k + 1))) ∗ strue)) by ac_rfl))
    (sep_mono_right _ (sep_mono_right _ (spure_sep_intro rfl (entails_refl _))))

/-! ## The listing, decoded once (kernel evaluation) -/

theorem d0 : Silmaril.X86.Ext.decode ((code.drop 0).take 4) = some (.aluI8 .q .cmp (.reg .rdi) 0x40, 4) := by
  decide +kernel
theorem d4 : Silmaril.X86.Ext.decode ((code.drop 4).take 2) = some (.jcc8 .a 0x4a, 2) := by
  decide +kernel
theorem d6 : Silmaril.X86.Ext.decode ((code.drop 6).take 7) = some (.load .q .rax (ripMem 0x1d93), 7) := by
  decide +kernel
theorem d13 : Silmaril.X86.Ext.decode ((code.drop 13).take 3) = some (.test .q (.reg .rax) .rax, 3) := by
  decide +kernel
theorem d16 : Silmaril.X86.Ext.decode ((code.drop 16).take 2) = some (.jcc8 .e 0x0e, 2) := by
  decide +kernel
theorem d18 : Silmaril.X86.Ext.decode ((code.drop 18).take 3) = some (.load .q .rdx (Silmaril.X86.Sep.Insn.memAt .rax 0), 3) := by
  decide +kernel
theorem d21 : Silmaril.X86.Ext.decode ((code.drop 21).take 7) = some (.mov .q (.mem (ripMem 0x1d84)) .rdx, 7) := by
  decide +kernel
theorem d32 : Silmaril.X86.Ext.decode ((code.drop 32).take 7) = some (.load .q .rdx (ripMem 0x1d71), 7) := by
  decide +kernel
theorem d39 : Silmaril.X86.Ext.decode ((code.drop 39).take 4) = some (.aluI8 .q .cmp (.reg .rdx) 0x3f, 4) := by
  decide +kernel
theorem d43 : Silmaril.X86.Ext.decode ((code.drop 43).take 2) = some (.jcc8 .a 0x25, 2) := by
  decide +kernel
theorem d45 : Silmaril.X86.Ext.decode ((code.drop 45).take 3) = some (.mov .q (.reg .rax) .rdx, 3) := by
  decide +kernel
theorem d48 : Silmaril.X86.Ext.decode ((code.drop 48).take 4) = some (.aluI8 .q .add (.reg .rdx) 0x01, 4) := by
  decide +kernel
theorem d52 : Silmaril.X86.Ext.decode ((code.drop 52).take 4) = some (.shift .q .shl (.reg .rax) (.imm 6), 4) := by
  decide +kernel
theorem d56 : Silmaril.X86.Ext.decode ((code.drop 56).take 7) = some (.mov .q (.mem (ripMem 0x1d59)) .rdx, 7) := by
  decide +kernel
theorem d63 : Silmaril.X86.Ext.decode ((code.drop 63).take 6) = some (.aluA .q .add 0x4030e0, 6) := by
  decide +kernel
theorem d80 : Silmaril.X86.Ext.decode ((code.drop 80).take 2) = some (.alu .d .xor (.reg .rax) .rax, 2) := by
  decide +kernel
theorem d96 : Silmaril.X86.Ext.decode ((code.drop 96).take 3) = some (.test .q (.reg .rdi) .rdi, 3) := by
  decide +kernel
theorem d99 : Silmaril.X86.Ext.decode ((code.drop 99).take 2) = some (.jcc8 .e 0x11, 2) := by
  decide +kernel
theorem d101 : Silmaril.X86.Ext.decode ((code.drop 101).take 7) = some (.load .q .rax (ripMem 0x1d34), 7) := by
  decide +kernel
theorem d108 : Silmaril.X86.Ext.decode ((code.drop 108).take 7) = some (.mov .q (.mem (ripMem 0x1d2d)) .rdi, 7) := by
  decide +kernel
theorem d115 : Silmaril.X86.Ext.decode ((code.drop 115).take 3) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rdi 0)) .rax, 3) := by
  decide +kernel
theorem r28 : (code.drop 28).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem r69 : (code.drop 69).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem r82 : (code.drop 82).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem r118 : (code.drop 118).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem hlen : code.length = 128 := by decide +kernel

/-! ## The paths of `malloc` after its branches -/

section Paths

variable {sp ret : Word} {fl : Silmaril.X86.Flags}


theorem fit (o k : Nat) (h : o + k ≤ 128 := by decide) : o + k ≤ code.length := hlen ▸ h

/-- `xor %eax, %eax; ret`: a request above the block size. -/
theorem path_big (f : Reg → Word) (hrsp : f .rsp = sp) (ps : List Word) (k : Nat) (h : Word)
    (n : Word) (hk : k ≤ 64) (hbig : 64 < n.toNat) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x401380 f fl (wordPt sp.toNat ret ∗ (wordPt headAddr h ∗
      flist ps h ∗ wordPt nextAddr (BitVec.ofNat 64 k) ∗ blockAny (pool + 64 * k) (64 * (64 - k)) ∗
      strue))) ((mallocSpecF iface).SysVPost ((ps, k), n) sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine SPEC.trans (c_xor32 E (b := 0x401330) (code := code) (o := 80) (k := 2) (pc := 0x401380) (by decide) (fit 80 2)
    (r := .rax) (by decide) d80) ?_
  refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 82) (k := 1) (pc := 0x401380 + 2#64)
    (by decide) (fit 82 1) (by simp only [Function.update_of_ne (show Reg.rsp ≠ .rax by decide), hrsp]) r82) ?_
  exact St_post rfl (by simp only [Function.update_self])
    (post_fail _ n (by simp [ref, hbig]) (fold ps k h hk) _
      (by simp only [Function.update_of_ne (show Reg.rax ≠ .rsp by decide), Function.update_self]))

/-- `ret` with `rax = head = 0`: the pool is exhausted. -/
theorem path_full (f : Reg → Word) (hrsp : f .rsp = sp) (hrax : f .rax = 0) (k : Nat) (n : Word)
    (hk : k ≤ 64) (hfull : 63 < k) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x401382 f fl (wordPt sp.toNat ret ∗ (wordPt headAddr 0 ∗
      flist [] 0 ∗ wordPt nextAddr (BitVec.ofNat 64 k) ∗ blockAny (pool + 64 * k) (64 * (64 - k)) ∗
      strue))) ((mallocSpecF iface).SysVPost (([], k), n) sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 82) (k := 1) (pc := 0x401382)
    (by decide) (fit 82 1) hrsp r82) ?_
  exact St_post rfl (by simp only [Function.update_self])
    (post_fail _ n (by simp [ref]; omega) (fold [] k 0 hk) _
      (by simp only [Function.update_of_ne (show Reg.rax ≠ .rsp by decide), hrax]))

/-- Handing out block `next`. -/
theorem path_bump (f : Reg → Word) (hrsp : f .rsp = sp) (k : Nat) (hrdx : f .rdx = BitVec.ofNat 64 k)
    (n : Word) (hfull : ¬ 63 < k) (hbig : ¬ 64 < n.toNat) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x40135d f fl (wordPt nextAddr (BitVec.ofNat 64 k) ∗
      wordPt headAddr 0 ∗ wordPt sp.toNat ret ∗ blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue))
      ((mallocSpecF iface).SysVPost (([], k), n) sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hk' : k < 2 ^ 64 := by omega
  refine SPEC.trans (c_movQ E (b := 0x401330) (code := code) (o := 45) (k := 3) (pc := 0x40135d) (by decide) (fit 45 3)
    (r := .rax) (q := .rdx) (by decide) (by decide) (by decide) d45) ?_
  refine SPEC.trans (c_aluI8 E (b := 0x401330) (code := code) (o := 48) (k := 4) (pc := 0x40135d + 3#64) (by decide)
    (fit 48 4) (op := .add) (by decide) (r := .rdx) (imm := 0x01) (by decide) d48) ?_
  refine SPEC.trans (c_shl E (b := 0x401330) (code := code) (o := 52) (k := 4) (pc := 0x40135d + 3#64 + 4#64) (by decide)
    (fit 52 4) (r := .rax) (c := 6) (by decide) (by decide) d52) ?_
  refine SPEC.trans (c_storeRip E (b := 0x401330) (code := code) (o := 56) (k := 7) (pc := 0x40135d + 3#64 + 4#64 + 4#64)
    (pc' := 0x40136f) (by decide) (fit 56 7) (src := .rdx) (by decide) (disp := 0x1d59)
    (wordPt_blockAny _ _) d56 (by decide) (by decide)) ?_
  refine SPEC.trans (c_aluA E (b := 0x401330) (code := code) (o := 63) (k := 6) (pc := 0x40136f) (by decide) (fit 63 6)
    (op := .add) (by decide) (imm := 0x4030e0) d63) ?_
  refine SPEC.mem (M' := wordPt sp.toNat ret ∗ wordPt nextAddr _ ∗ wordPt headAddr 0 ∗
    blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue) (by ac_rfl) ?_
  refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 69) (k := 1) (pc := 0x40136f + 6#64)
    (by decide) (fit 69 1) (by simp [Function.update, hrsp]) r69) ?_
  refine St_post rfl (by simp only [Function.update_self]) (post_bump k n hfull hbig _ _ ?_ ?_)
  · simp only [Function.update_of_ne (show Reg.rdx ≠ .rax by decide), Function.update_self,
      Silmaril.X86.Ext.AluOp.resultN, hrdx]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk',
      show (BitVec.signExtend 64 (0x01 : BitVec 8)).toNat = 1 by decide +kernel, BitVec.toNat_ofNat]
  · simp only [Function.update_of_ne (show Reg.rax ≠ .rsp by decide), Function.update_self,
      Function.update_of_ne (show Reg.rax ≠ .rdx by decide), Silmaril.X86.Ext.AluOp.resultN,
      Silmaril.X86.Ext.ShiftOp.result, hrdx]
    have h64 : 64 * k < 2 ^ 64 := by omega
    have h1 : (BitVec.ofNat 64 k <<< ((6 : BitVec 8).toNat % 64)).toNat = 64 * k := by
      rw [BitVec.toNat_shiftLeft, show (6 : BitVec 8).toNat % 64 = 6 from rfl, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hk', Nat.shiftLeft_eq, show (2 : Nat) ^ 6 = 64 from rfl, Nat.mul_comm,
        Nat.mod_eq_of_lt h64]
    have h2 : (BitVec.signExtend 64 (0x4030e0 : BitVec 32)).toNat = pool := by decide +kernel
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, h1, h2, BitVec.toNat_ofNat]
    simp only [pool]
    omega

/-- Popping the free list. -/
theorem path_pop (f : Reg → Word) (hrsp : f .rsp = sp) (h q : Word) (hrax : f .rax = h)
    (ps : List Word) (k : Nat) (n : Word) (hk : k ≤ 64) (hbig : ¬ 64 < n.toNat)
    (hp : h ≠ 0 ∧ h.toNat % 16 = 0) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x401342 f fl (wordPt h.toNat q ∗ wordPt headAddr h ∗
      wordPt sp.toNat ret ∗ wordPt nextAddr (BitVec.ofNat 64 k) ∗
      blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue ∗ blockAny (h.toNat + 8) 56 ∗ flist ps q))
      ((mallocSpecF iface).SysVPost ((h :: ps, k), n) sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 18) (k := 3) (pc := 0x401342) (pc' := 0x401345)
    (by decide) (fit 18 3) (base := .rax) (dst := .rdx) (by decide) (by decide) (by decide)
    (disp := 0) d18 (by decide) (by simp [hrax])) ?_
  refine SPEC.mem (M' := wordPt headAddr h ∗ wordPt h.toNat q ∗ wordPt sp.toNat ret ∗
    wordPt nextAddr (BitVec.ofNat 64 k) ∗ blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue ∗
    blockAny (h.toNat + 8) 56 ∗ flist ps q) (by ac_rfl) ?_
  refine SPEC.trans (c_storeRip E (b := 0x401330) (code := code) (o := 21) (k := 7) (pc := 0x401345) (pc' := 0x40134c)
    (by decide) (fit 21 7) (src := .rdx) (by decide) (disp := 0x1d84) (wordPt_blockAny _ _)
    d21 (by decide) (by decide)) ?_
  refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (wordPt headAddr q ∗ wordPt h.toNat q ∗
    blockAny (h.toNat + 8) 56 ∗ flist ps q ∗ wordPt nextAddr (BitVec.ofNat 64 k) ∗
    blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue))
    (by simp only [Function.update_self]; ac_rfl) ?_
  refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 28) (k := 1) (pc := 0x40134c)
    (by decide) (fit 28 1) (by simp only [Function.update_of_ne (show Reg.rsp ≠ .rdx by decide), hrsp])
    r28) ?_
  exact St_post rfl (by simp only [Function.update_self])
    (post_pop h q ps k n hk hbig hp _ (by
      simp only [Function.update_of_ne (show Reg.rax ≠ .rsp by decide),
        Function.update_of_ne (show Reg.rax ≠ .rdx by decide), hrax]))

end Paths

theorem malloc_sat :
    (mallocSpecF iface).Sat Silmaril.X86.Open.isa layout.C layout.mallocAt := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine satWith_of_St rfl (fun x => x.2) (fun _ => rfl) fun x sp ret f fl _ hsp hdi => ?_
  obtain ⟨⟨ps, k⟩, n⟩ := x
  change SPEC _ (codePt 0x401330 code) (St _ f fl (wordPt sp.toNat ret ∗ sexists _)) _
  rw [St_ex]
  refine SPEC.sexists fun h => ?_
  rw [St_pure]
  refine SPEC.spure fun hk => ?_
  dsimp only at hdi hk ⊢
  refine SPEC.trans (c_cmpI8 E (b := 0x401330) (code := code) (o := 0) (k := 4) (pc := 0x401330)
    rfl (fit 0 4) (r := .rdi) (imm := 0x40) (by decide) d0) ?_
  have h64 : (BitVec.signExtend 64 (0x40 : BitVec 8)).toNat = 64 := by decide +kernel
  by_cases hbig : 64 < n.toNat
  · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 4) (k := 2)
      (pc := 0x401330 + 4#64) (pc' := 0x401380) (by decide) (fit 4 2) (c := .a) (rel := 0x4a) ?_
      d4 (by decide)) ?_
    · rw [eval_a_cmp, hdi, h64]; simp [hbig]
    exact path_big _ (by simp only [hsp]) ps k h n hk hbig
  refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 4) (k := 2)
    (pc := 0x401330 + 4#64) (pc' := 0x401336) (by decide) (fit 4 2) (c := .a) (rel := 0x4a) ?_ d4
    (by decide)) ?_
  · rw [eval_a_cmp, hdi, h64]; simp [hbig]
  refine SPEC.mem (M' := wordPt headAddr h ∗ wordPt sp.toNat ret ∗ flist ps h ∗
    wordPt nextAddr (BitVec.ofNat 64 k) ∗ blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue)
    (by ac_rfl) ?_
  refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 6) (k := 7) (pc := 0x401336)
    (pc' := 0x40133d) (by decide) (fit 6 7) (dst := .rax) (by decide) (disp := 0x1d93) d6
    (by decide) (by decide)) ?_
  refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 13) (k := 3) (pc := 0x40133d)
    (by decide) (fit 13 3) (r := .rax) (by decide) d13) ?_
  cases ps with
  | nil =>
    refine SPEC.mem (M' := wordPt headAddr h ∗ (⌜h = 0⌝ ∗ (wordPt sp.toNat ret ∗
      wordPt nextAddr (BitVec.ofNat 64 k) ∗ blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue)))
      (by simp only [flist]; ac_rfl) ?_
    rw [St_pure]
    refine SPEC.spure fun h0 => ?_
    subst h0
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 16) (k := 2)
      (pc := 0x40133d + 3#64) (pc' := 0x401350) (by decide) (fit 16 2) (c := .e) (rel := 0x0e) ?_
      d16 (by decide)) ?_
    · rw [eval_e_test, Function.update_self]; rfl
    refine SPEC.mem (M' := wordPt nextAddr (BitVec.ofNat 64 k) ∗ wordPt headAddr 0 ∗
      wordPt sp.toNat ret ∗ blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue) (by ac_rfl) ?_
    refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 32) (k := 7)
      (pc := 0x401350) (pc' := 0x401357) (by decide) (fit 32 7) (dst := .rdx) (by decide)
      (disp := 0x1d71) d32 (by decide) (by decide)) ?_
    refine SPEC.trans (c_cmpI8 E (b := 0x401330) (code := code) (o := 39) (k := 4)
      (pc := 0x401357) (by decide) (fit 39 4) (r := .rdx) (imm := 0x3f) (by decide) d39) ?_
    have hk' : k < 2 ^ 64 := by omega
    have h63 : (BitVec.signExtend 64 (0x3f : BitVec 8)).toNat = 63 := by decide +kernel
    have hrdx : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk']
    by_cases hfull : 63 < k
    · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 43) (k := 2)
        (pc := 0x401357 + 4#64) (pc' := 0x401382) (by decide) (fit 43 2) (c := .a) (rel := 0x25)
        ?_ d43 (by decide)) ?_
      · rw [eval_a_cmp, Function.update_self, hrdx, h63]; simp [hfull]
      refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (wordPt headAddr 0 ∗ flist [] 0 ∗
        wordPt nextAddr (BitVec.ofNat 64 k) ∗ blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue))
        (by simp only [flist, show ((0 : Word) = 0) = True from eq_self _, spure_true_emp,
          emp_sep]; ac_rfl) ?_
      exact path_full _ (by simp [Function.update, hsp]) (by simp [Function.update]) k n hk hfull
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 43) (k := 2)
      (pc := 0x401357 + 4#64) (pc' := 0x40135d) (by decide) (fit 43 2) (c := .a) (rel := 0x25) ?_
      d43 (by decide)) ?_
    · rw [eval_a_cmp, Function.update_self, hrdx, h63]; simp [hfull]
    exact path_bump _ (by simp [Function.update, hsp]) k (by simp [Function.update]) n hfull hbig
  | cons p ps =>
    refine SPEC.mem (M' := wordPt headAddr h ∗ (⌜h = p ∧ p ≠ 0 ∧ p.toNat % 16 = 0⌝ ∗
      ((wordPt sp.toNat ret ∗ wordPt nextAddr (BitVec.ofNat 64 k) ∗
        blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue) ∗
        sexists fun q => wordPt p.toNat q ∗ blockAny (p.toNat + 8) 56 ∗ flist ps q)))
      (by simp only [flist]; ac_rfl) ?_
    rw [St_pure]
    refine SPEC.spure fun ⟨hhp, hp0, hp16⟩ => ?_
    subst hhp
    refine SPEC.mem (M' := (wordPt headAddr h ∗ wordPt sp.toNat ret ∗
      wordPt nextAddr (BitVec.ofNat 64 k) ∗ blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue) ∗
      sexists fun q => wordPt h.toNat q ∗ blockAny (h.toNat + 8) 56 ∗ flist ps q)
      (by ac_rfl) ?_
    rw [St_ex]
    refine SPEC.sexists fun q => ?_
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 16) (k := 2)
      (pc := 0x40133d + 3#64) (pc' := 0x401342) (by decide) (fit 16 2) (c := .e) (rel := 0x0e) ?_
      d16 (by decide)) ?_
    · rw [eval_e_test, Function.update_self]; simpa using hp0
    refine SPEC.mem (M' := wordPt h.toNat q ∗ wordPt headAddr h ∗ wordPt sp.toNat ret ∗
      wordPt nextAddr (BitVec.ofNat 64 k) ∗ blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue ∗
      blockAny (h.toNat + 8) 56 ∗ flist ps q) (by ac_rfl) ?_
    exact path_pop _ (by simp [Function.update, hsp]) h q (by simp [Function.update]) ps k n hk
      hbig ⟨hp0, hp16⟩

theorem blk_eq (p : Nat) (n : Nat) (hn : n ≤ 64) :
    (blockAny p n ∗ blockAny (p + n) (64 - n)) = (blockAny p 8 ∗ blockAny (p + 8) 56) := by
  rw [← blockAny_add, ← blockAny_add, Nat.add_sub_cancel' hn]

/-- Pushing a block. -/
theorem post_push (p h : Word) (fl : List Word) (k : Nat) (hk : k ≤ 64)
    (hp : p ≠ 0 ∧ p.toNat % 16 = 0) (w : Word) (hw : w = h) :
    (wordPt p.toNat w ∗ wordPt headAddr p ∗ blockAny (p.toNat + 8) 56 ∗ flist fl h ∗
      wordPt nextAddr (BitVec.ofNat 64 k) ∗ blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue) ⊢ₛ
      iface.mmS (p :: fl, k) := by
  subst hw
  refine entails_trans ?_ (fold (p :: fl) k p hk)
  refine entails_trans (entails_of_eq (show _ = (wordPt headAddr p ∗ (wordPt p.toNat w ∗
    blockAny (p.toNat + 8) 56 ∗ flist fl w) ∗ wordPt nextAddr (BitVec.ofNat 64 k) ∗
    blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue) by ac_rfl)) ?_
  refine sep_mono_right _ (sep_mono_left _ ?_)
  exact spure_sep_intro ⟨rfl, hp⟩ (sexists_intro w (entails_refl _))

theorem free_sat :
    (freeSpecF iface).Sat Silmaril.X86.Open.isa layout.C layout.freeAt := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine satWith_of_St rfl (fun x => x.p) (fun _ => rfl) fun x sp ret f fl _ hsp hdi => ?_
  rcases x with ⟨⟨fs, k⟩, p, _ | n⟩
  · -- free(NULL)
    change SPEC _ (codePt 0x401330 code) (St _ f fl (wordPt sp.toNat ret ∗
      (iface.mmS (fs, k) ∗ ⌜p = 0⌝))) _
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜p = 0⌝ ∗ iface.mmS (fs, k))) (by ac_rfl) ?_
    rw [St_pure]
    refine SPEC.spure fun hp => ?_
    dsimp only at hdi
    subst hp
    refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 96) (k := 3) (pc := 0x401390)
      rfl (fit 96 3) (r := .rdi) (by decide) d96) ?_
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 99) (k := 2)
      (pc := 0x401390 + 3#64) (pc' := 0x4013a6) (by decide) (fit 99 2) (c := .e) (rel := 0x11) ?_
      d99 (by decide)) ?_
    · rw [eval_e_test, hdi]; rfl
    refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 118)
      (k := 1) (pc := 0x4013a6) (by decide) (fit 118 1) hsp r118) ?_
    exact St_post rfl (by simp only [Function.update_self]) (entails_refl _)
  · -- free(p) of a block of requested size n
    change SPEC _ (codePt 0x401330 code) (St _ f fl (wordPt sp.toNat ret ∗
      (iface.mmS (fs, k) ∗ (⌜n ≤ 64 ∧ p ≠ 0 ∧ p.toNat % 16 = 0⌝ ∗
        blockAny (p.toNat + n) (64 - n)) ∗ blockAny p.toNat n))) _
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜n ≤ 64 ∧ p ≠ 0 ∧ p.toNat % 16 = 0⌝ ∗
      (iface.mmS (fs, k) ∗ blockAny (p.toNat + n) (64 - n) ∗ blockAny p.toNat n))) (by ac_rfl) ?_
    rw [St_pure]
    refine SPEC.spure fun ⟨hn, hp0, hp16⟩ => ?_
    dsimp only at hdi
    refine SPEC.mem (M' := (wordPt sp.toNat ret ∗ blockAny p.toNat 8 ∗ blockAny (p.toNat + 8) 56) ∗
      iface.mmS (fs, k)) (by rw [← blk_eq _ _ hn]; ac_rfl) ?_
    change SPEC _ _ (St _ f fl (_ ∗ sexists _)) _
    rw [St_ex]
    refine SPEC.sexists fun h => ?_
    refine SPEC.mem (M' := wordPt headAddr h ∗ (⌜k ≤ 64⌝ ∗ (wordPt sp.toNat ret ∗
      blockAny p.toNat 8 ∗ blockAny (p.toNat + 8) 56 ∗ flist fs h ∗
      wordPt nextAddr (BitVec.ofNat 64 k) ∗ blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue)))
      (by dsimp only; ac_rfl) ?_
    rw [St_pure]
    refine SPEC.spure fun hk => ?_
    refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 96) (k := 3) (pc := 0x401390)
      rfl (fit 96 3) (r := .rdi) (by decide) d96) ?_
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 99) (k := 2)
      (pc := 0x401390 + 3#64) (pc' := 0x401395) (by decide) (fit 99 2) (c := .e) (rel := 0x11) ?_
      d99 (by decide)) ?_
    · rw [eval_e_test, hdi]; simpa using hp0
    refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 101) (k := 7)
      (pc := 0x401395) (pc' := 0x40139c) (by decide) (fit 101 7) (dst := .rax) (by decide)
      (disp := 0x1d34) d101 (by decide) (by decide)) ?_
    refine SPEC.trans (c_storeRip E (b := 0x401330) (code := code) (o := 108) (k := 7)
      (pc := 0x40139c) (pc' := 0x4013a3) (by decide) (fit 108 7) (src := .rdi) (by decide)
      (disp := 0x1d2d) (wordPt_blockAny _ _) d108 (by decide) (by decide)) ?_
    refine SPEC.mem (M' := blockAny p.toNat 8 ∗ wordPt headAddr _ ∗ wordPt sp.toNat ret ∗
      blockAny (p.toNat + 8) 56 ∗ flist fs h ∗ wordPt nextAddr (BitVec.ofNat 64 k) ∗
      blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue) (by ac_rfl) ?_
    refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 115) (k := 3)
      (pc := 0x4013a3) (pc' := 0x4013a6) (by decide) (fit 115 3) (base := .rdi) (src := .rax)
      (by decide) (by decide) (by decide) (disp := 0) (entails_refl _) d115 (by decide)
      (by simp [Function.update, hdi])) ?_
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (wordPt p.toNat _ ∗ wordPt headAddr p ∗
      blockAny (p.toNat + 8) 56 ∗ flist fs h ∗ wordPt nextAddr (BitVec.ofNat 64 k) ∗
      blockAny (pool + 64 * k) (64 * (64 - k)) ∗ strue))
      (by simp only [Function.update_of_ne (show Reg.rdi ≠ .rax by decide), hdi]; ac_rfl) ?_
    refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 118)
      (k := 1) (pc := 0x4013a6) (by decide) (fit 118 1) (by simp [Function.update, hsp]) r118) ?_
    exact St_post rfl (by simp only [Function.update_self])
      (post_push p h fs k hk ⟨hp0, hp16⟩ _ (by simp [Function.update]))

/-- **The loaded image establishes the allocator's state** `([], 0)`. -/
theorem init : layout.Init ⊢ₛ iface.mmS (([] : List Word), (0 : Nat)) := by
  unfold Layout.Init
  dsimp only [layout]
  have hw : Silmaril.Machine.LittleEndian.encodeWords [BitVec.ofNat 64 0] =
      List.replicate 8 (0 : Byte) := by decide
  rw [show pool + 4096 - nextAddr = 8 + (8 + (8 + 4096)) from rfl, List.replicate_add,
    List.replicate_add, List.replicate_add, bytesPt, bytesAt_append, bytesAt_append,
    bytesAt_append]
  simp only [List.length_replicate]
  refine sexists_intro (0 : Word) (spure_sep_intro (Nat.zero_le _) ?_)
  have e1 : bytesAt RW nextAddr (List.replicate 8 0) = wordPt nextAddr (BitVec.ofNat 64 0) := by
    rw [wordPt, hw]; rfl
  have e2 : bytesAt RW (nextAddr + 8) (List.replicate 8 0) = wordPt headAddr 0 := by
    rw [wordPt, show (0 : Word) = BitVec.ofNat 64 0 from rfl, hw]; rfl
  rw [e1, e2]
  have e3 : bytesAt RW (nextAddr + 8 + 8 + 8) (List.replicate 4096 0) ⊢ₛ
      blockAny (pool + 64 * 0) (64 * (64 - 0)) := by
    refine entails_trans (bytesPt_blockAny _ _) (entails_of_eq ?_)
    rw [List.length_replicate]
  have e4 : (wordPt nextAddr (BitVec.ofNat 64 0) ∗ wordPt headAddr 0 ∗
      bytesAt RW (nextAddr + 8 + 8) (List.replicate 8 0) ∗
      bytesAt RW (nextAddr + 8 + 8 + 8) (List.replicate 4096 0)) =
      (wordPt headAddr 0 ∗ wordPt nextAddr (BitVec.ofNat 64 0) ∗
        bytesAt RW (nextAddr + 8 + 8 + 8) (List.replicate 4096 0) ∗
        bytesAt RW (nextAddr + 8 + 8) (List.replicate 8 0)) := by ac_rfl
  rw [e4]
  refine sep_mono_right _ (spure_sep_intro rfl (sep_mono_right _ (sep_mono e3 (entails_strue _))))

theorem sim : ref.Sim cap α Inv where
  avail s n hI ha := by
    obtain ⟨fs, k⟩ := s
    obtain ⟨hk, hfs⟩ := hI
    obtain ⟨hn, hc⟩ := ha
    have hn' : ¬ 64 < n := by omega
    cases fs with
    | cons p ps =>
      simp only [ref, hn', ite_false]
      exact hfs p List.mem_cons_self
    | nil =>
      have hk' : k < 64 := by simp [α] at hc; omega
      simp only [ref, hn', ite_false, hk', ite_true]
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat, pool] at this
      rw [show (0 : Word).toNat = 0 from rfl] at this
      omega
  alloc s n hI hm := by
    obtain ⟨fs, k⟩ := s
    obtain ⟨hk, hfs⟩ := hI
    have hn : ¬ 64 < n := by intro hc; exact hm (by simp only [ref, hc, ite_true])
    cases fs with
    | cons p ps =>
      refine ⟨⟨hk, fun q hq => hfs q (List.mem_cons_of_mem _ hq)⟩, ?_⟩
      show ps.length + (64 - k) = (p :: ps).length + (64 - k) - 1
      simp
    | nil =>
      have hk' : k < 64 := by
        by_contra hc; exact hm (by simp only [ref, hn, ite_false, hc, ite_false])
      refine ⟨⟨by show k + 1 ≤ 64; omega, fun q hq => absurd hq List.not_mem_nil⟩, ?_⟩
      show 0 + (64 - (k + 1)) = 0 + (64 - k) - 1
      omega
  dealloc s p _ hI hp := by
    obtain ⟨fs, k⟩ := s
    obtain ⟨hk, hfs⟩ := hI
    refine ⟨⟨hk, fun q hq => ?_⟩, ?_⟩
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact hp
      · exact hfs q hq
    · show (p :: fs).length + (64 - k) = fs.length + (64 - k) + 1
      simp; omega

end Silmaril.Raw.Libc.X86Alloc.Ladder.Pool
