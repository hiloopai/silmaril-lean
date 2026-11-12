module

public import Silmaril.Raw.Libc.X86Alloc.Insn
public import Silmaril.X86.Sep.SysV.Thms

/-!
# Proofs: the canonical frame of a leaf function

A leaf System V function (stack budget `0`, no callee-saved register touched) is proved on one
**canonical assertion** `St pc f fl M`: `rip ↦ pc`, the ten registers `frameRegs` with values
`f`, the flags `fl`, and a memory part `M`. Every instruction of the ladder is a `SPEC` from one
canonical assertion to the next (`c_*` lemmas): the register file is updated with
`Function.update`, so steps compose by `SPEC.trans` without re-arranging `∗`.

* `satWith_of_St`: a one-argument spec from canonical runs (entry: `SysVPre` is a family of
  canonical assertions, one per value of the unknown registers and flags).
* `post_of_St`: the canonical assertion after `ret` gives `SysVPost`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Frame

open Silmaril.X86 (State MState Word Byte Reg Flags Insn)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Insn (ne_nil_of_dec)
open Silmaril.Libc.X86Alloc.Insn
open Silmaril.Raw.Libc.X86Alloc.Insn

instance : Std.Associative (α := SProp) sep := ⟨sep_assoc⟩
instance : Std.Commutative (α := SProp) sep := ⟨sep_comm⟩

variable {σ : Type} {I : Isa σ}

/-- The registers of the canonical frame: the nine caller-saved registers and `rsp`. -/
def frameRegs : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp]

/-- Registers holding the values of `f`. -/
def regsPt : List Reg → (Reg → Word) → SProp
  | [], _ => emp
  | r :: rs, f => regPt r (f r) ∗ regsPt rs f

/-- **The canonical assertion**: `rip`, the frame registers, the flags and the memory part. -/
def St (pc : Word) (f : Reg → Word) (fl : Flags) (M : SProp) : SProp :=
  ripPt pc ∗ regsPt frameRegs f ∗ flagsPt fl ∗ M

/-- A register file from ten values. -/
def regFile (rax rcx rdx rsi rdi r8 r9 r10 r11 rsp : Word) : Reg → Word
  | .rax => rax | .rcx => rcx | .rdx => rdx | .rsi => rsi | .rdi => rdi
  | .r8 => r8 | .r9 => r9 | .r10 => r10 | .r11 => r11 | .rsp => rsp | _ => 0

theorem regsPt_erase : ∀ (rs : List Reg) (f : Reg → Word) {r : Reg}, r ∈ rs →
    regsPt rs f = (regPt r (f r) ∗ regsPt (rs.erase r) f)
  | [], _, _, h => absurd h (List.not_mem_nil)
  | q :: rs, f, r, h => by
    by_cases e : q = r
    · subst e; simp [regsPt, List.erase_cons_head]
    · have hr : r ∈ rs := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm e
        · exact h
      rw [List.erase_cons_tail (by simpa using e)]
      simp only [regsPt]
      rw [regsPt_erase rs f hr, sep_left_comm]

theorem regsPt_update_notin : ∀ (rs : List Reg) (f : Reg → Word) {r : Reg} (v : Word),
    r ∉ rs → regsPt rs (Function.update f r v) = regsPt rs f
  | [], _, _, _, _ => rfl
  | q :: rs, f, r, v, h => by
    have hq : q ≠ r := fun e => h (e ▸ List.mem_cons_self)
    have hr : r ∉ rs := fun hm => h (List.mem_cons_of_mem _ hm)
    simp only [regsPt, Function.update_of_ne hq, regsPt_update_notin rs f v hr]

theorem regsPt_frame_update (f : Reg → Word) {r : Reg} (hr : r ∈ frameRegs) (v : Word) :
    regsPt frameRegs (Function.update f r v) = (regPt r v ∗ regsPt (frameRegs.erase r) f) := by
  rw [regsPt_erase _ _ hr, Function.update_self,
    regsPt_update_notin _ _ _ ((List.Nodup.not_mem_erase (by decide)))]

theorem flagsPt_flagsAny (fl : Flags) : flagsPt fl ⊢ₛ flagsAny := sexists_intro fl (entails_refl _)

theorem regPt_regAny (r : Reg) (v : Word) : regPt r v ⊢ₛ regAny r := sexists_intro v (entails_refl _)

/-! ## From an instruction triple to a step of the whole code -/

/-- An instruction triple on its own bytes, framed by the rest of the code `D`. -/
theorem spec_of_triple {C c D P Q : SProp} (hC : C = (c ∗ D)) (h : Triple I (c ∗ P) (c ∗ Q)) :
    SPEC I C P Q := by
  refine Triple.conseq (entails_of_eq ?_) (Triple.frame h D) (entails_of_eq ?_)
  · rw [hC]; ac_rfl
  · rw [hC]; ac_rfl

/-- The bytes of a code region at an offset. -/
theorem codePt_split (b : Nat) (code : List Byte) (o k : Nat) (hfit : o + k ≤ code.length) :
    codePt b code = (codePt (b + o) ((code.drop o).take k) ∗
      (codePt b (code.take o) ∗ codePt (b + o + k) (code.drop (o + k)))) := by
  have e : code = code.take o ++ ((code.drop o).take k ++ code.drop (o + k)) := by
    rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have h1 : (code.take o).length = o := by simp; omega
  have h2 : ((code.drop o).take k).length = k := by simp; omega
  conv_lhs => rw [e]
  simp only [codePt, bytesAt_append, h1, h2]
  ac_rfl

/-- **A step of the whole code** from an instruction triple on its bytes at offset `o`. -/
theorem c_step {b : Nat} {code : List Byte} {o k : Nat} {pc : Word} (hpc : pc.toNat = b + o)
    (hfit : o + k ≤ code.length) {P Q Pin Pout R : SProp}
    (h : Triple I (codePt pc.toNat ((code.drop o).take k) ∗ Pin)
      (codePt pc.toNat ((code.drop o).take k) ∗ Pout))
    (hpre : P ⊢ₛ (Pin ∗ R)) (hpost : (Pout ∗ R) ⊢ₛ Q) : SPEC I (codePt b code) P Q := by
  have hC := codePt_split b code o k hfit
  rw [← hpc] at hC
  refine SPEC.conseq hpre (spec_of_triple hC ?_) hpost
  refine Triple.conseq (entails_of_eq ?_) (Triple.frame h R) (entails_of_eq ?_) <;> ac_rfl


/-! ## Canonical instruction steps -/

section Steps

variable (E : Silmaril.X86.Open.isa.Extends I) {b : Nat} {code : List Byte} {o k : Nat}
  {pc pc' : Word} (hpc : pc.toNat = b + o) (hfit : o + k ≤ code.length)

include E hpc hfit

omit E hpc in
theorem bytes_len : ((code.drop o).take k).length = k := by simp; omega

/-- `reg1_step` on the canonical frame. -/
theorem c_reg1 {i : Silmaril.X86.Ext.Instr} {r : Reg} (hr : r ∈ frameRegs) {f : Reg → Word}
    {fl f' : Flags} {a' : Word} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (i, k)) (hnr : i ≠ .ret)
    (hnext : pc + BitVec.ofNat 64 k = pc')
    (hx : ∀ (s : State) (mem : Silmaril.Process.Memory), s.read r = f r → ∃ s' : State,
      Silmaril.X86.Ext.exec i s mem = .ok s' mem ∧ s'.rip = s.rip + BitVec.ofNat 64 i.length ∧
      s'.read r = a' ∧ (∀ q, q ≠ r → s'.read q = s.read q) ∧ s'.flags = f') :
    SPEC I (codePt b code) (St pc f fl M) (St pc' (Function.update f r a') f' M) := by
  subst hnext
  have hl := bytes_len hfit
  refine c_step hpc hfit (R := regsPt (frameRegs.erase r) f ∗ M)
    (reg1_step E (by simpa only [hl] using hdec) hnr (congrArg (fun x => pc + BitVec.ofNat 64 x) hl) hx) ?_ ?_
  · refine entails_trans (entails_of_eq ?_)
      (sep_mono_left _ (sep_mono_right _ (sep_mono_right _ (flagsPt_flagsAny fl))))
    rw [St, regsPt_erase _ _ hr]; ac_rfl
  · refine entails_of_eq ?_
    rw [St, regsPt_frame_update _ hr]; ac_rfl

/-- `reg2_step` on the canonical frame: `r` written, `q` read. -/
theorem c_reg2 {i : Silmaril.X86.Ext.Instr} {r q : Reg} (hr : r ∈ frameRegs)
    (hq : q ∈ frameRegs) (hrq : r ≠ q) {f : Reg → Word} {fl f' : Flags} {a' : Word} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (i, k)) (hnr : i ≠ .ret)
    (hnext : pc + BitVec.ofNat 64 k = pc')
    (hx : ∀ (s : State) (mem : Silmaril.Process.Memory), s.read r = f r → s.read q = f q →
      ∃ s' : State,
      Silmaril.X86.Ext.exec i s mem = .ok s' mem ∧ s'.rip = s.rip + BitVec.ofNat 64 i.length ∧
      s'.read r = a' ∧ (∀ t, t ≠ r → s'.read t = s.read t) ∧ s'.flags = f') :
    SPEC I (codePt b code) (St pc f fl M) (St pc' (Function.update f r a') f' M) := by
  subst hnext
  have hl := bytes_len hfit
  have hq' : q ∈ frameRegs.erase r := List.mem_erase_of_ne (Ne.symm hrq) |>.2 hq
  refine c_step hpc hfit (R := regsPt ((frameRegs.erase r).erase q) f ∗ M)
    (reg2_step E hrq (by simpa only [hl] using hdec) hnr (congrArg (fun x => pc + BitVec.ofNat 64 x) hl) hx) ?_ ?_
  · refine entails_trans (entails_of_eq ?_) (sep_mono_left _ (sep_mono_right _ (sep_mono_right _
      (sep_mono_right _ (flagsPt_flagsAny fl)))))
    rw [St, regsPt_erase _ _ hr, regsPt_erase _ _ hq']; ac_rfl
  · refine entails_of_eq ?_
    rw [St, regsPt_frame_update _ hr, regsPt_erase _ _ hq']; ac_rfl

/-- `mov2_step` on the canonical frame (flags kept). -/
theorem c_mov2 {i : Silmaril.X86.Ext.Instr} {r q : Reg} (hr : r ∈ frameRegs)
    (hq : q ∈ frameRegs) (hrq : r ≠ q) {f : Reg → Word} {fl : Flags} {a' : Word} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (i, k)) (hnr : i ≠ .ret)
    (hnext : pc + BitVec.ofNat 64 k = pc')
    (hx : ∀ (s : State) (mem : Silmaril.Process.Memory), s.read r = f r → s.read q = f q →
      ∃ s' : State,
      Silmaril.X86.Ext.exec i s mem = .ok s' mem ∧ s'.rip = s.rip + BitVec.ofNat 64 i.length ∧
      s'.read r = a' ∧ (∀ t, t ≠ r → s'.read t = s.read t) ∧ s'.flags = s.flags) :
    SPEC I (codePt b code) (St pc f fl M) (St pc' (Function.update f r a') fl M) := by
  subst hnext
  have hl := bytes_len hfit
  have hq' : q ∈ frameRegs.erase r := List.mem_erase_of_ne (Ne.symm hrq) |>.2 hq
  refine c_step hpc hfit (R := regsPt ((frameRegs.erase r).erase q) f ∗ flagsPt fl ∗ M)
    (mov2_step E hrq (by simpa only [hl] using hdec) hnr (congrArg (fun x => pc + BitVec.ofNat 64 x) hl) hx) ?_ ?_
  · refine entails_of_eq ?_
    rw [St, regsPt_erase _ _ hr, regsPt_erase _ _ hq']; ac_rfl
  · refine entails_of_eq ?_
    rw [St, regsPt_frame_update _ hr, regsPt_erase _ _ hq']; ac_rfl

/-- `mov $imm32, %r32` on the canonical frame. -/
theorem c_movI32 {r : Reg} (hr : r ∈ frameRegs) {imm : BitVec 32} {f : Reg → Word}
    {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.movI32 r imm, k))
    (hnext : pc + BitVec.ofNat 64 k = pc') :
    SPEC I (codePt b code) (St pc f fl M)
      (St pc' (Function.update f r (imm.setWidth 64)) fl M) := by
  subst hnext
  have hl := bytes_len hfit
  refine c_step hpc hfit (R := regsPt (frameRegs.erase r) f ∗ flagsPt fl ∗ M)
    (Silmaril.X86.Sep.Insn.movI32_step E (by simpa only [hl] using hdec) (congrArg (fun x => pc + BitVec.ofNat 64 x) hl))
    ?_ ?_
  · refine entails_trans (entails_of_eq ?_)
      (sep_mono_left _ (sep_mono_right _ (regPt_regAny r (f r))))
    rw [St, regsPt_erase _ _ hr]; ac_rfl
  · refine entails_of_eq ?_
    rw [St, regsPt_frame_update _ hr]; ac_rfl

/-- `mov disp(%rip), %dst` on the canonical frame: the word is the first memory atom. -/
theorem c_loadRip {dst : Reg} (hr : dst ∈ frameRegs) {disp : BitVec 32} {a : Nat} {w : Word}
    {f : Reg → Word} {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) =
      some (.load .q dst (ripMem disp), k))
    (hnext : pc + BitVec.ofNat 64 k = pc') (ha : (pc' + disp.signExtend 64).toNat = a) :
    SPEC I (codePt b code) (St pc f fl (wordPt a w ∗ M))
      (St pc' (Function.update f dst w) fl (wordPt a w ∗ M)) := by
  subst hnext
  have hl := bytes_len hfit
  refine c_step hpc hfit (R := regsPt (frameRegs.erase dst) f ∗ flagsPt fl ∗ M)
    (loadRip_step E (w := w) (dst := dst) ha (by simpa only [hl] using hdec) (congrArg (fun x => pc + BitVec.ofNat 64 x) hl)) ?_ ?_
  · refine entails_trans (entails_of_eq ?_)
      (sep_mono_left _ (sep_mono_right _ (sep_mono_right _ (regPt_regAny dst (f dst)))))
    rw [St, regsPt_erase _ _ hr]; ac_rfl
  · refine entails_of_eq ?_
    rw [St, regsPt_frame_update _ hr]; ac_rfl

/-- `mov %src, disp(%rip)` on the canonical frame, into the first memory atom `B`
(eight writable bytes). -/
theorem c_storeRip {src : Reg} (hr : src ∈ frameRegs) {disp : BitVec 32} {a : Nat}
    {f : Reg → Word} {fl : Flags} {B M : SProp} (hB : B ⊢ₛ blockAny a 8)
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) =
      some (.mov .q (.mem (ripMem disp)) src, k))
    (hnext : pc + BitVec.ofNat 64 k = pc') (ha : (pc' + disp.signExtend 64).toNat = a) :
    SPEC I (codePt b code) (St pc f fl (B ∗ M)) (St pc' f fl (wordPt a (f src) ∗ M)) := by
  subst hnext
  have hl := bytes_len hfit
  refine c_step hpc hfit (R := regsPt (frameRegs.erase src) f ∗ flagsPt fl ∗ M)
    (storeRip_step E (v := f src) (src := src) ha (by simpa only [hl] using hdec) (congrArg (fun x => pc + BitVec.ofNat 64 x) hl)) ?_ ?_
  · refine entails_trans (entails_of_eq ?_)
      (sep_mono_left _ (sep_mono_right _ (sep_mono_right _ hB)))
    rw [St, regsPt_erase _ _ hr]; ac_rfl
  · refine entails_of_eq ?_
    rw [St, regsPt_erase _ _ hr]; ac_rfl

/-- `mov disp(%base), %dst` on the canonical frame: the word is the first memory atom. -/
theorem c_loadQ {base dst : Reg} (hb : base ∈ frameRegs) (hr : dst ∈ frameRegs)
    (hne : dst ≠ base) {disp : BitVec 32} {a : Nat} {w : Word}
    {f : Reg → Word} {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) =
      some (.load .q dst (Silmaril.X86.Sep.Insn.memAt base disp), k))
    (hnext : pc + BitVec.ofNat 64 k = pc') (ha : (f base + disp.signExtend 64).toNat = a) :
    SPEC I (codePt b code) (St pc f fl (wordPt a w ∗ M))
      (St pc' (Function.update f dst w) fl (wordPt a w ∗ M)) := by
  subst hnext
  have hl := bytes_len hfit
  have hb' : base ∈ frameRegs.erase dst := List.mem_erase_of_ne (Ne.symm hne) |>.2 hb
  refine c_step hpc hfit (R := regsPt ((frameRegs.erase dst).erase base) f ∗ flagsPt fl ∗ M)
    (Silmaril.X86.Sep.Insn.loadQ_step E (w := w) (b := f base) ha hne (by simpa only [hl] using hdec)
      (congrArg (fun x => pc + BitVec.ofNat 64 x) hl)) ?_ ?_
  · refine entails_trans (entails_of_eq ?_)
      (sep_mono_left _ (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
        (regPt_regAny dst (f dst))))))
    rw [St, regsPt_erase _ _ hr, regsPt_erase _ _ hb']; ac_rfl
  · refine entails_of_eq ?_
    rw [St, regsPt_frame_update _ hr, regsPt_erase _ _ hb']; ac_rfl

/-- `mov disp(%r), %r` on the canonical frame: the word is the first memory atom. -/
theorem c_loadSelf {r : Reg} (hr : r ∈ frameRegs) {disp : BitVec 32} {a : Nat} {w : Word}
    {f : Reg → Word} {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) =
      some (.load .q r (Silmaril.X86.Sep.Insn.memAt r disp), k))
    (hnext : pc + BitVec.ofNat 64 k = pc') (ha : (f r + disp.signExtend 64).toNat = a) :
    SPEC I (codePt b code) (St pc f fl (wordPt a w ∗ M))
      (St pc' (Function.update f r w) fl (wordPt a w ∗ M)) := by
  subst hnext
  have hl := bytes_len hfit
  refine c_step hpc hfit (R := regsPt (frameRegs.erase r) f ∗ flagsPt fl ∗ M)
    (loadSelf_step E (w := w) (b := f r) ha (by simpa only [hl] using hdec)
      (congrArg (fun x => pc + BitVec.ofNat 64 x) hl)) ?_ ?_
  · refine entails_of_eq ?_
    rw [St, regsPt_erase _ _ hr]; ac_rfl
  · refine entails_of_eq ?_
    rw [St, regsPt_frame_update _ hr]; ac_rfl

/-- `mov %src, disp(%base)` on the canonical frame, into the first memory atom `B`. -/
theorem c_storeQ {base src : Reg} (hb : base ∈ frameRegs) (hr : src ∈ frameRegs)
    (hne : src ≠ base) {disp : BitVec 32} {a : Nat}
    {f : Reg → Word} {fl : Flags} {B M : SProp} (hB : B ⊢ₛ blockAny a 8)
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) =
      some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt base disp)) src, k))
    (hnext : pc + BitVec.ofNat 64 k = pc') (ha : (f base + disp.signExtend 64).toNat = a) :
    SPEC I (codePt b code) (St pc f fl (B ∗ M)) (St pc' f fl (wordPt a (f src) ∗ M)) := by
  subst hnext
  have hl := bytes_len hfit
  have hb' : base ∈ frameRegs.erase src := List.mem_erase_of_ne (Ne.symm hne) |>.2 hb
  refine c_step hpc hfit (R := regsPt ((frameRegs.erase src).erase base) f ∗ flagsPt fl ∗ M)
    (Silmaril.X86.Sep.Insn.storeQ_step E (v := f src) (b := f base) ha (by simpa only [hl] using hdec)
      (congrArg (fun x => pc + BitVec.ofNat 64 x) hl)) ?_ ?_
  · refine entails_trans (entails_of_eq ?_)
      (sep_mono_left _ (sep_mono_right _ (sep_mono_right _ (sep_mono_right _ hB))))
    rw [St, regsPt_erase _ _ hr, regsPt_erase _ _ hb']; ac_rfl
  · refine entails_of_eq ?_
    rw [St, regsPt_erase _ _ hr, regsPt_erase _ _ hb']; ac_rfl

/-- A taken `jcc rel8` on the canonical frame. -/
theorem c_jcc_taken {c : Silmaril.X86.Ext.Cond} {rel : BitVec 8} {f : Reg → Word} {fl : Flags}
    {M : SProp} (hev : c.eval fl = some true)
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.jcc8 c rel, k))
    (hnext : pc + BitVec.ofNat 64 k + rel.signExtend 64 = pc') :
    SPEC I (codePt b code) (St pc f fl M) (St pc' f fl M) := by
  subst hnext
  have hl := bytes_len hfit
  refine c_step hpc hfit (R := regsPt frameRegs f ∗ M)
    (Silmaril.X86.Sep.Insn.jcc8_taken E hev (by simpa only [hl] using hdec) (congrArg (fun x => pc + BitVec.ofNat 64 x + rel.signExtend 64) hl))
    (entails_of_eq ?_) (entails_of_eq ?_) <;> (rw [St]; ac_rfl)

/-- A `jcc rel8` that falls through, on the canonical frame. -/
theorem c_jcc_not {c : Silmaril.X86.Ext.Cond} {rel : BitVec 8} {f : Reg → Word} {fl : Flags}
    {M : SProp} (hev : c.eval fl = some false)
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.jcc8 c rel, k))
    (hnext : pc + BitVec.ofNat 64 k = pc') :
    SPEC I (codePt b code) (St pc f fl M) (St pc' f fl M) := by
  subst hnext
  have hl := bytes_len hfit
  refine c_step hpc hfit (R := regsPt frameRegs f ∗ M)
    (Silmaril.X86.Sep.Insn.jcc8_not_taken E hev (by simpa only [hl] using hdec)
      (congrArg (fun x => pc + BitVec.ofNat 64 x) hl))
    (entails_of_eq ?_) (entails_of_eq ?_) <;> (rw [St]; ac_rfl)

/-- `ret` on the canonical frame: the return slot is the first memory atom. -/
theorem c_ret {f : Reg → Word} {fl : Flags} {ret : Word} {M : SProp}
    (hcode : (code.drop o).take k = Insn.encode .ret) :
    SPEC I (codePt b code) (St pc f fl (wordPt (f .rsp).toNat ret ∗ M))
      (St ret (Function.update f .rsp (f .rsp + 8#64)) fl (wordPt (f .rsp).toNat ret ∗ M)) := by
  have hr : Reg.rsp ∈ frameRegs := by decide
  refine c_step hpc hfit (R := regsPt (frameRegs.erase .rsp) f ∗ flagsPt fl ∗ M)
    (hcode ▸ ret_step E pc (f .rsp) ret) ?_ ?_
  · refine entails_of_eq ?_
    rw [St, regsPt_erase _ _ hr]; ac_rfl
  · refine entails_of_eq ?_
    rw [St, regsPt_frame_update _ hr]; ac_rfl

end Steps

/-! ## Entry and exit -/

/-- The System V entry of a one-argument leaf function is a family of canonical assertions. -/
theorem entry_St {S : FnSpec} (hstack : S.stack = 0) {x : S.Arg} {a : Word}
    (hargs : S.args x = [a]) (entry sp ret : Word) :
    S.SysVPre x entry sp ret ⊢ₛ sexists fun (f : Reg → Word) => sexists fun (fl : Flags) =>
      ⌜f .rsp = sp ∧ f .rdi = a⌝ ∗ St entry f fl (wordPt sp.toNat ret ∗ S.pre x) := by
  unfold FnSpec.SysVPre FnSpec.SysVEntry SysVRegs
  rw [hargs, hstack]
  simp only [regsWith, regsAny, argRegs, scratchRegs, regAny, flagsAny, blockAny,
    sep_emp, sexists_sep, sep_sexists]
  refine sexists_elim fun fl => sexists_elim fun r11 => sexists_elim fun r10 =>
    sexists_elim fun rax => sexists_elim fun r9 => sexists_elim fun r8 =>
    sexists_elim fun rcx => sexists_elim fun rdx => sexists_elim fun rsi => ?_
  refine sexists_intro (regFile rax rcx rdx rsi a r8 r9 r10 r11 sp)
    (sexists_intro fl (spure_sep_intro ⟨rfl, rfl⟩ (entails_of_eq ?_)))
  simp only [St, regsPt, frameRegs, regFile, sep_emp]
  ac_rfl

/-- After `ret`, the canonical assertion gives the System V postcondition. -/
theorem St_post {S : FnSpec} (hstack : S.stack = 0) {x : S.Arg} {sp ret r0 : Word}
    {f : Reg → Word} {fl : Flags} {M : SProp} (hrsp : f .rsp = sp + 8#64)
    (hM : M ⊢ₛ S.post x (f .rax)) :
    St ret f fl (wordPt sp.toNat r0 ∗ M) ⊢ₛ S.SysVPost x sp ret := by
  unfold FnSpec.SysVPost FnSpec.SysVExit SysVRet
  rw [hstack]
  refine sexists_intro (f .rax) ?_
  simp only [St, regsPt, frameRegs, regsAny, regsWith, clobberedRegs, Nat.sub_zero, Nat.zero_add,
    sep_emp, hrsp]
  refine entails_trans (entails_of_eq (show _ = ((ripPt ret ∗ regPt .rsp (sp + 8#64) ∗
      (regPt .rax (f .rax) ∗ regPt .rcx (f .rcx) ∗ regPt .rdx (f .rdx) ∗ regPt .rsi (f .rsi) ∗
        regPt .rdi (f .rdi) ∗ regPt .r8 (f .r8) ∗ regPt .r9 (f .r9) ∗ regPt .r10 (f .r10) ∗
        regPt .r11 (f .r11)) ∗ flagsPt fl ∗ wordPt sp.toNat r0) ∗ M) by ac_rfl)) ?_
  refine sep_mono (sep_mono_right _ (sep_mono_right _ (sep_mono (sep_mono_right _ ?_)
    (sep_mono (flagsPt_flagsAny fl) (wordPt_blockAny _ _))))) hM
  exact sep_mono (regPt_regAny _ _) (sep_mono (regPt_regAny _ _) (sep_mono (regPt_regAny _ _)
    (sep_mono (regPt_regAny _ _) (sep_mono (regPt_regAny _ _) (sep_mono (regPt_regAny _ _)
    (sep_mono (regPt_regAny _ _) (regPt_regAny _ _)))))))

/-- **A one-argument leaf spec from canonical runs.** -/
theorem satWith_of_St {S : FnSpec} {A : Word → Prop} {C : SProp} {entry : Word}
    (hstack : S.stack = 0) (arg : S.Arg → Word) (hargs : ∀ x, S.args x = [arg x])
    (h : ∀ x sp ret (f : Reg → Word) (fl : Flags), A sp → f .rsp = sp → f .rdi = arg x →
      SPEC I C (St entry f fl (wordPt sp.toNat ret ∗ S.pre x)) (S.SysVPost x sp ret)) :
    S.SatWith I A C entry := by
  intro x sp ret hA _
  refine SPEC.conseq (entry_St hstack (hargs x) entry sp ret) ?_ (entails_refl _)
  exact SPEC.sexists fun f => SPEC.sexists fun fl =>
    SPEC.spure fun ⟨h1, h2⟩ => h x sp ret f fl hA h1 h2

/-! ## Derived steps for the ALU forms gcc emits -/

section Alu

open Silmaril.X86.Ext (Sz ShiftOp)

variable (E : Silmaril.X86.Open.isa.Extends I) {b : Nat} {code : List Byte} {o k : Nat}
  {pc : Word} (hpc : pc.toNat = b + o) (hfit : o + k ≤ code.length)

include E hpc hfit

/-- `op %q, %r` (64-bit, not `cmp`). -/
theorem c_alu {op : Silmaril.X86.AluOp} (hop : op ≠ .cmp) {r q : Reg} (hr : r ∈ frameRegs)
    (hq : q ∈ frameRegs) (hrq : r ≠ q) {f : Reg → Word} {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.alu .q op (.reg r) q, k)) :
    SPEC I (codePt b code) (St pc f fl M)
      (St (pc + BitVec.ofNat 64 k) (Function.update f r (Silmaril.X86.Ext.AluOp.resultN op (f r) (f q)))
        (Silmaril.X86.Ext.AluOp.flagsN op (f r) (f q)) M) :=
  c_reg2 E hpc hfit hr hq hrq hdec (by simp) rfl fun s mem h1 h2 =>
    ⟨_, by simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.retire, hop]; rfl, rfl, by simp [Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
        Silmaril.X86.Ext.writeRM, hop, h1, h2],
      fun t ht => by simp [Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
        Silmaril.X86.Ext.writeRM, hop, ht],
      by simp [Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, hop,
        h1, h2]⟩

/-- `cmp %q, %r` (64-bit). -/
theorem c_cmp {r q : Reg} (hr : r ∈ frameRegs) (hq : q ∈ frameRegs) (hrq : r ≠ q)
    {f : Reg → Word} {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) =
      some (.alu .q .cmp (.reg r) q, k)) :
    SPEC I (codePt b code) (St pc f fl M)
      (St (pc + BitVec.ofNat 64 k) f (Silmaril.X86.Ext.AluOp.flagsN .cmp (f r) (f q)) M) := by
  have := c_reg2 E hpc hfit hr hq hrq hdec (by simp) rfl (f := f) (fl := fl) (M := M)
    (a' := f r) (f' := Silmaril.X86.Ext.AluOp.flagsN .cmp (f r) (f q)) fun s mem h1 h2 =>
    ⟨_, rfl, rfl, by simp [h1], fun t _ => rfl, by
      simp [Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM, h1, h2]⟩
  rwa [Function.update_eq_self] at this

/-- `op $imm32, %rax` (64-bit accumulator form, not `cmp`). -/
theorem c_aluA {op : Silmaril.X86.AluOp} (hop : op ≠ .cmp) {imm : BitVec 32}
    {f : Reg → Word} {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.aluA .q op imm, k)) :
    SPEC I (codePt b code) (St pc f fl M)
      (St (pc + BitVec.ofNat 64 k)
        (Function.update f .rax (Silmaril.X86.Ext.AluOp.resultN op (f .rax) (imm.signExtend 64)))
        (Silmaril.X86.Ext.AluOp.flagsN op (f .rax) (imm.signExtend 64)) M) :=
  c_reg1 E hpc hfit (by decide) hdec (by simp) rfl fun s mem h1 =>
    ⟨_, by simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.retire, hop]; rfl, rfl, by simp [Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
        Silmaril.X86.Ext.writeRM, hop, h1],
      fun t ht => by simp [Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
        Silmaril.X86.Ext.writeRM, hop, ht],
      by simp [Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, hop,
        h1]⟩

/-- `op $imm8, %r` (64-bit, not `cmp`). -/
theorem c_aluI8 {op : Silmaril.X86.AluOp} (hop : op ≠ .cmp) {r : Reg} (hr : r ∈ frameRegs)
    {imm : BitVec 8} {f : Reg → Word} {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.aluI8 .q op (.reg r) imm, k)) :
    SPEC I (codePt b code) (St pc f fl M)
      (St (pc + BitVec.ofNat 64 k)
        (Function.update f r (Silmaril.X86.Ext.AluOp.resultN op (f r) (imm.signExtend 64)))
        (Silmaril.X86.Ext.AluOp.flagsN op (f r) (imm.signExtend 64)) M) :=
  c_reg1 E hpc hfit hr hdec (by simp) rfl fun s mem h1 =>
    ⟨_, by simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.retire, hop]; rfl, rfl, by simp [Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
        Silmaril.X86.Ext.writeRM, hop, h1],
      fun t ht => by simp [Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
        Silmaril.X86.Ext.writeRM, hop, ht],
      by simp [Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, hop,
        h1]⟩

/-- `cmp $imm8, %r` (64-bit). -/
theorem c_cmpI8 {r : Reg} (hr : r ∈ frameRegs) {imm : BitVec 8} {f : Reg → Word} {fl : Flags}
    {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) =
      some (.aluI8 .q .cmp (.reg r) imm, k)) :
    SPEC I (codePt b code) (St pc f fl M)
      (St (pc + BitVec.ofNat 64 k) f (Silmaril.X86.Ext.AluOp.flagsN .cmp (f r) (imm.signExtend 64)) M) := by
  have := c_reg1 E hpc hfit hr hdec (by simp) rfl (f := f) (fl := fl) (M := M)
    (a' := f r) (f' := Silmaril.X86.Ext.AluOp.flagsN .cmp (f r) (imm.signExtend 64)) fun s mem h1 =>
    ⟨_, rfl, rfl, by simp [h1], fun t _ => rfl, by
      simp [Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM, h1]⟩
  rwa [Function.update_eq_self] at this

/-- `test %r, %r` (64-bit). -/
theorem c_test {r : Reg} (hr : r ∈ frameRegs) {f : Reg → Word} {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.test .q (.reg r) r, k)) :
    SPEC I (codePt b code) (St pc f fl M)
      (St (pc + BitVec.ofNat 64 k) f (Silmaril.X86.Ext.logicFlagsN (f r &&& f r)) M) := by
  have := c_reg1 E hpc hfit hr hdec (by simp) rfl (f := f) (fl := fl) (M := M)
    (a' := f r) (f' := Silmaril.X86.Ext.logicFlagsN (f r &&& f r)) fun s mem h1 =>
    ⟨_, rfl, rfl, by simp [h1], fun t _ => rfl, by
      simp only [Silmaril.X86.Ext.readRM, Sz.read_q, h1]; rfl⟩
  rwa [Function.update_eq_self] at this

/-- `xor %r32, %r32`: zero the register. -/
theorem c_xor32 {r : Reg} (hr : r ∈ frameRegs) {f : Reg → Word} {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.alu .d .xor (.reg r) r, k)) :
    SPEC I (codePt b code) (St pc f fl M)
      (St (pc + BitVec.ofNat 64 k) (Function.update f r 0)
        (Silmaril.X86.Ext.AluOp.flagsN .xor ((f r).setWidth 32) ((f r).setWidth 32)) M) :=
  c_reg1 E hpc hfit hr hdec (by simp) rfl fun s mem h1 =>
    ⟨_, rfl, rfl, by
        show (Sz.d.write s r (Sz.d.read s r ^^^ Sz.d.read s r)).read r = 0
        rw [BitVec.xor_self]; simp [Sz.write],
      fun t ht => by simp [Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
        Silmaril.X86.Ext.writeRM, Sz.write, ht],
      by simp [Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM,
        Sz.read, h1]⟩

/-- `shl $c, %r` (64-bit). -/
theorem c_shl {r : Reg} (hr : r ∈ frameRegs) {c : BitVec 8} (hc : c.toNat % 64 ≠ 0)
    {f : Reg → Word} {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) =
      some (.shift .q .shl (.reg r) (.imm c), k)) :
    SPEC I (codePt b code) (St pc f fl M)
      (St (pc + BitVec.ofNat 64 k) (Function.update f r (ShiftOp.shl.result (f r) (c.toNat % 64)))
        (ShiftOp.shl.flags (f r) (c.toNat % 64) fl) M) := by
  refine c_reg1 E hpc hfit hr hdec (by simp) rfl (f := f) (fl := fl) fun s mem h1 =>
    ⟨_, rfl, rfl, by simp [Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM,
        Silmaril.X86.Ext.Count.raw, h1],
      fun t ht => by simp [Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, ht], ?_⟩
  simp only [Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, Sz.read_q, h1, Option.map_some]
  simp [ShiftOp.flags, hc, Silmaril.X86.Ext.Count.raw]; rfl

/-- `mov %q, %r` (64-bit). -/
theorem c_movQ {r q : Reg} (hr : r ∈ frameRegs) (hq : q ∈ frameRegs) (hrq : r ≠ q)
    {f : Reg → Word} {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.mov .q (.reg r) q, k)) :
    SPEC I (codePt b code) (St pc f fl M)
      (St (pc + BitVec.ofNat 64 k) (Function.update f r (f q)) fl M) :=
  c_mov2 E hpc hfit hr hq hrq hdec (by simp) rfl fun s mem h1 h2 =>
    ⟨_, rfl, rfl, by simp [Silmaril.X86.Ext.writeRM, h2],
      fun t ht => by simp [Silmaril.X86.Ext.writeRM, ht], rfl⟩

end Alu

end Silmaril.Raw.Libc.X86Alloc.Frame
