module

public import Silmaril.Proofs.X86.Sep.JmpBuf.Setjmp
public import Silmaril.X86.Safe.Exc.Thms
public import Silmaril.X86.Sep.Ind.Thms
public import Silmaril.X86.Open9.Thms

/-!
# Proofs: `longjmp` as an exceptional-exit triple

* `longjmp_head`: `movl %esi, %eax; testl %eax, %eax; jnz 1f; movl $1, %eax` leaves
  `rax = retVal v` (both branches).
* `longjmp_body`: the head and the seven loads of the `jmp_buf`, a total triple on the open
  machine, up to `jmp *56(%rdi)`.
* `longjmp_triple`: on every machine `I` with `Open9.isa.Extends I`, `longjmp` takes the
  exceptional exit to the continuation in the `jmp_buf`, for every normal postcondition `Q`
  and every index; the `jmp` goes through `Sep.Ind.jmpM_progress`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Sep.JmpBuf

open Silmaril.X86 (State MState Word Byte Reg Insn)
open Silmaril.X86.Ext (rip_advance)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.JmpBuf
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep.Ind (encJmpM ea wordAt jmpM_progress)
open Silmaril.Proofs.X86.Sep.Insn
open Silmaril.X86.Sep.Insn (memAt testFlags)
open Silmaril.X86.Safe

/-! ## Listing chunks -/

def lj0 : List Byte := [0x89, 0xf0]
def lj1 : List Byte := [0x85, 0xc0]
def lj2 : List Byte := [0x75, 0x05]
def lj3 : List Byte := [0xb8, 0x01, 0x00, 0x00, 0x00]
def lj4 : List Byte := [0x48, 0x8b, 0x1f]
def lj5 : List Byte := [0x48, 0x8b, 0x6f, 0x08]
def lj6 : List Byte := [0x4c, 0x8b, 0x67, 0x10]
def lj7 : List Byte := [0x4c, 0x8b, 0x6f, 0x18]
def lj8 : List Byte := [0x4c, 0x8b, 0x77, 0x20]
def lj9 : List Byte := [0x4c, 0x8b, 0x7f, 0x28]
def lj10 : List Byte := [0x48, 0x8b, 0x67, 0x30]
def lj11 : List Byte := encJmpM .rdi 0x38#8

theorem longjmpBytes_eq :
    longjmpBytes = lj0 ++ lj1 ++ lj2 ++ lj3 ++ lj4 ++ lj5 ++ lj6 ++ lj7 ++ lj8 ++ lj9 ++ lj10 ++
      lj11 := by decide

/-! ## The returned value -/

theorem zext_low (v : Word) : ((v.setWidth 32).setWidth 64).setWidth 32 = v.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := (v.setWidth 32).isLt
  simp only [BitVec.toNat_setWidth] at this
  rw [Nat.mod_eq_of_lt (by omega : v.toNat % 2 ^ 32 < 2 ^ 64), Nat.mod_mod]

theorem low_of_zext {v : Word} (hz : (v.setWidth 32).setWidth 64 = 0) :
    (((v.setWidth 32).setWidth 64).setWidth 32 == 0#32) = true := by
  rw [hz]; rfl

theorem low_of_zext_ne {v : Word} (hz : ¬ (v.setWidth 32).setWidth 64 = 0) :
    (((v.setWidth 32).setWidth 64).setWidth 32 == 0#32) = false := by
  rw [zext_low]
  cases h : (v.setWidth 32 == 0#32)
  · rfl
  · exfalso; apply hz
    rw [beq_iff_eq] at h
    rw [h]; rfl

theorem retVal_of_zero {v : Word} (hz : (v.setWidth 32).setWidth 64 = 0) : retVal v = 1 := by
  simp [retVal, hz]

theorem retVal_of_ne {v : Word} (hz : ¬ (v.setWidth 32).setWidth 64 = 0) :
    retVal v = (v.setWidth 32).setWidth 64 := by
  unfold retVal
  split
  · contradiction
  · rfl

/-- `longjmp(b, v)` never makes `setjmp` return `0`. -/
theorem retVal_ne_zero (v : Word) : retVal v ≠ 0 := by
  unfold retVal
  split
  · decide
  · assumption

theorem jne_target (l : Word) :
    l + BitVec.ofNat 64 4 + BitVec.ofNat 64 lj2.length + (5#8).signExtend 64 =
      l + BitVec.ofNat 64 11 := by
  rw [show (5#8 : BitVec 8).signExtend 64 = BitVec.ofNat 64 5 by decide,
    rip_advance l (show 4 + lj2.length = 6 by decide), rip_advance l (show 6 + 5 = 11 by rfl)]

theorem longjmp_head {l v : Word} :
    Triple Silmaril.X86.Open.isa
      (codePt l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat
      64 4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ ripPt l ∗ regPt .rsi v ∗
      regAny .rax ∗ flagsAny)
      (codePt l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat
      64 4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ ripPt (l + BitVec.ofNat 64
      11) ∗ regPt .rsi v ∗ regPt .rax (retVal v) ∗ flagsAny) := by
  by_cases hz : ((v.setWidth 32).setWidth 64) = 0
  · have hev : Silmaril.X86.Ext.Cond.ne.eval (testFlags ((v.setWidth 32).setWidth 64)) = some false := by
      rw [eval_ne_testFlags, low_of_zext hz]; rfl
    have h : Triple Silmaril.X86.Open.isa
        (codePt l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat
        64 4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ ripPt l ∗ regPt .rsi v ∗
        regAny .rax ∗ flagsAny)
        (codePt l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat
        64 4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ ripPt (l + BitVec.ofNat 64
        11) ∗ regPt .rsi v ∗ regPt .rax ((1#32).setWidth 64) ∗ flagsPt (testFlags ((v.setWidth
        32).setWidth 64))) := by
      refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
        (Triple.frame (movD_step (pc := l) (pc' := (l + BitVec.ofNat 64 2)) (bytes := lj0) (dst := .rax)
            (src := .rsi) (v := v) (by decide) (by decide) rfl)
          (codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat 64 4).toNat lj2 ∗
           codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ flagsAny)) (entails_refl _)) ?_
      refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
        (Triple.frame (testSelf_step (pc := (l + BitVec.ofNat 64 2)) (pc' := (l + BitVec.ofNat 64 4))
            (bytes := lj1) (r := .rax) (v := ((v.setWidth 32).setWidth 64)) (by decide)
            (rip_advance l (by decide)))
          (codePt l.toNat lj0 ∗ regPt .rsi v ∗ codePt (l + BitVec.ofNat 64 4).toNat lj2 ∗ codePt
           (l + BitVec.ofNat 64 6).toNat lj3)) (entails_refl _)) ?_
      refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
        (Triple.frame (jcc8_not_taken (pc := (l + BitVec.ofNat 64 4)) (pc' := (l + BitVec.ofNat 64 6))
            (bytes := lj2) (c := .ne) (rel := 5#8) (f := testFlags ((v.setWidth 32).setWidth
            64)) hev (by decide) (rip_advance l (by decide)))
          (codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ regPt .rax ((v.setWidth 32).setWidth 64) ∗
           codePt l.toNat lj0 ∗ regPt .rsi v ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3)) (entails_refl _)) ?_
      refine Triple.pre (entails_trans (entails_of_eq (by ac_rfl))
        (sep_mono_left (codePt (l + BitVec.ofNat 64 4).toNat lj2 ∗ ripPt (l + BitVec.ofNat 64 6) ∗ flagsPt
          (testFlags ((v.setWidth 32).setWidth 64)) ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗
          codePt l.toNat lj0 ∗ regPt .rsi v ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3)
          (show regPt .rax ((v.setWidth 32).setWidth 64) ⊢ₛ regAny .rax from fun _ hp => ⟨_, hp⟩))) ?_
      refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
        (Triple.frame (movI32_step (pc := (l + BitVec.ofNat 64 6)) (pc' := (l + BitVec.ofNat 64 11)) (bytes
            := lj3) (r := .rax) (imm := 1#32) (by decide) (rip_advance l (by decide)))
          (codePt (l + BitVec.ofNat 64 4).toNat lj2 ∗ flagsPt (testFlags ((v.setWidth
           32).setWidth 64)) ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt l.toNat lj0 ∗
           regPt .rsi v)) (entails_refl _)) ?_
      exact Triple.post (Triple.refl _) (entails_of_eq (by ac_rfl))
    refine Triple.post h (entails_trans (entails_of_eq (by ac_rfl))
      (entails_trans (sep_mono_left (codePt l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat
        64 4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ ripPt (l + BitVec.ofNat 64
        11) ∗ regPt .rsi v)
        (sep_mono (show regPt .rax ((1#32).setWidth 64) ⊢ₛ regPt .rax (retVal v) from entails_of_eq (by rw [retVal_of_zero hz]; rfl))
          (show flagsPt (testFlags ((v.setWidth 32).setWidth 64)) ⊢ₛ flagsAny from fun _ hp => ⟨_, hp⟩)))
        (entails_of_eq (by ac_rfl))))
  · have hev : Silmaril.X86.Ext.Cond.ne.eval (testFlags ((v.setWidth 32).setWidth 64)) = some true := by
      rw [eval_ne_testFlags, low_of_zext_ne hz]; rfl
    have h : Triple Silmaril.X86.Open.isa
        (codePt l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat
        64 4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ ripPt l ∗ regPt .rsi v ∗
        regAny .rax ∗ flagsAny)
        (codePt l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat
        64 4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ ripPt (l + BitVec.ofNat 64
        11) ∗ regPt .rsi v ∗ regPt .rax ((v.setWidth 32).setWidth 64) ∗ flagsPt (testFlags
        ((v.setWidth 32).setWidth 64))) := by
      refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
        (Triple.frame (movD_step (pc := l) (pc' := (l + BitVec.ofNat 64 2)) (bytes := lj0) (dst := .rax)
            (src := .rsi) (v := v) (by decide) (by decide) rfl)
          (codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat 64 4).toNat lj2 ∗
           codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ flagsAny)) (entails_refl _)) ?_
      refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
        (Triple.frame (testSelf_step (pc := (l + BitVec.ofNat 64 2)) (pc' := (l + BitVec.ofNat 64 4))
            (bytes := lj1) (r := .rax) (v := ((v.setWidth 32).setWidth 64)) (by decide)
            (rip_advance l (by decide)))
          (codePt l.toNat lj0 ∗ regPt .rsi v ∗ codePt (l + BitVec.ofNat 64 4).toNat lj2 ∗ codePt
           (l + BitVec.ofNat 64 6).toNat lj3)) (entails_refl _)) ?_
      refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
        (Triple.frame (jcc8_taken (pc := (l + BitVec.ofNat 64 4)) (pc' := (l + BitVec.ofNat 64 11)) (bytes
            := lj2) (c := .ne) (rel := 5#8) (f := testFlags ((v.setWidth 32).setWidth 64)) hev
            (by decide) (jne_target l))
          (codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ regPt .rax ((v.setWidth 32).setWidth 64) ∗
           codePt l.toNat lj0 ∗ regPt .rsi v ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3)) (entails_refl _)) ?_
      exact Triple.post (Triple.refl _) (entails_of_eq (by ac_rfl))
    refine Triple.post h (entails_trans (entails_of_eq (by ac_rfl))
      (entails_trans (sep_mono_left (codePt l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat
        64 4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ ripPt (l + BitVec.ofNat 64
        11) ∗ regPt .rsi v)
        (sep_mono (show regPt .rax ((v.setWidth 32).setWidth 64) ⊢ₛ regPt .rax (retVal v) from entails_of_eq (by rw [retVal_of_ne hz]))
          (show flagsPt (testFlags ((v.setWidth 32).setWidth 64)) ⊢ₛ flagsAny from fun _ hp => ⟨_, hp⟩)))
        (entails_of_eq (by ac_rfl))))

theorem longjmp_body {l bw v c0 c1 c2 c3 c4 c5 ksp kret : Word}
    (hb : bw.toNat + 64 < 2 ^ 64) :
    Triple Silmaril.X86.Open.isa
      (codePt l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat
      64 4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ codePt (l + BitVec.ofNat 64
      11).toNat lj4 ∗ codePt (l + BitVec.ofNat 64 14).toNat lj5 ∗ codePt (l + BitVec.ofNat 64
      18).toNat lj6 ∗ codePt (l + BitVec.ofNat 64 22).toNat lj7 ∗ codePt (l + BitVec.ofNat 64
      26).toNat lj8 ∗ codePt (l + BitVec.ofNat 64 30).toNat lj9 ∗ codePt (l + BitVec.ofNat 64
      34).toNat lj10 ∗ codePt (l + BitVec.ofNat 64 38).toNat lj11 ∗ ripPt l ∗ regPt .rdi bw ∗
      regPt .rsi v ∗ regAny .rax ∗ flagsAny ∗ regAny .rbx ∗ regAny .rbp ∗ regAny .r12 ∗ regAny
      .r13 ∗ regAny .r14 ∗ regAny .r15 ∗ regAny .rsp ∗ wordPt bw.toNat c0 ∗ wordPt (bw.toNat +
      8) c1 ∗ wordPt (bw.toNat + 16) c2 ∗ wordPt (bw.toNat + 24) c3 ∗ wordPt (bw.toNat + 32) c4
      ∗ wordPt (bw.toNat + 40) c5 ∗ wordPt (bw.toNat + 48) ksp ∗ wordPt (bw.toNat + 56) kret)
      (codePt l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat
      64 4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ codePt (l + BitVec.ofNat 64
      11).toNat lj4 ∗ codePt (l + BitVec.ofNat 64 14).toNat lj5 ∗ codePt (l + BitVec.ofNat 64
      18).toNat lj6 ∗ codePt (l + BitVec.ofNat 64 22).toNat lj7 ∗ codePt (l + BitVec.ofNat 64
      26).toNat lj8 ∗ codePt (l + BitVec.ofNat 64 30).toNat lj9 ∗ codePt (l + BitVec.ofNat 64
      34).toNat lj10 ∗ codePt (l + BitVec.ofNat 64 38).toNat lj11 ∗ ripPt (l + BitVec.ofNat 64
      38) ∗ regPt .rdi bw ∗ regPt .rsi v ∗ regPt .rax (retVal v) ∗ flagsAny ∗ regPt .rbx c0 ∗
      regPt .rbp c1 ∗ regPt .r12 c2 ∗ regPt .r13 c3 ∗ regPt .r14 c4 ∗ regPt .r15 c5 ∗ regPt .rsp
      ksp ∗ wordPt bw.toNat c0 ∗ wordPt (bw.toNat + 8) c1 ∗ wordPt (bw.toNat + 16) c2 ∗ wordPt
      (bw.toNat + 24) c3 ∗ wordPt (bw.toNat + 32) c4 ∗ wordPt (bw.toNat + 40) c5 ∗ wordPt
      (bw.toNat + 48) ksp ∗ wordPt (bw.toNat + 56) kret) := by
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (longjmp_head (l := l) (v := v))
      (codePt (l + BitVec.ofNat 64 11).toNat lj4 ∗ codePt (l + BitVec.ofNat 64 14).toNat lj5 ∗
       codePt (l + BitVec.ofNat 64 18).toNat lj6 ∗ codePt (l + BitVec.ofNat 64 22).toNat lj7 ∗
       codePt (l + BitVec.ofNat 64 26).toNat lj8 ∗ codePt (l + BitVec.ofNat 64 30).toNat lj9 ∗
       codePt (l + BitVec.ofNat 64 34).toNat lj10 ∗ codePt (l + BitVec.ofNat 64 38).toNat lj11 ∗
       regPt .rdi bw ∗ regAny .rbx ∗ regAny .rbp ∗ regAny .r12 ∗ regAny .r13 ∗ regAny .r14 ∗
       regAny .r15 ∗ regAny .rsp ∗ wordPt bw.toNat c0 ∗ wordPt (bw.toNat + 8) c1 ∗ wordPt
       (bw.toNat + 16) c2 ∗ wordPt (bw.toNat + 24) c3 ∗ wordPt (bw.toNat + 32) c4 ∗ wordPt
       (bw.toNat + 40) c5 ∗ wordPt (bw.toNat + 48) ksp ∗ wordPt (bw.toNat + 56) kret)) (entails_refl _)) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (loadQ_step (pc := (l + BitVec.ofNat 64 11)) (pc' := (l + BitVec.ofNat 64 14)) (bytes :=
        lj4) (base := .rdi) (dst := .rbx) (disp := 0#32) (a := bw.toNat) (ea_zero bw) (by
        decide) (by decide) (rip_advance l (by decide)))
      (codePt l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat
       64 4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ regPt .rsi v ∗ regPt .rax
       (retVal v) ∗ flagsAny ∗ codePt (l + BitVec.ofNat 64 14).toNat lj5 ∗ codePt (l +
       BitVec.ofNat 64 18).toNat lj6 ∗ codePt (l + BitVec.ofNat 64 22).toNat lj7 ∗ codePt (l +
       BitVec.ofNat 64 26).toNat lj8 ∗ codePt (l + BitVec.ofNat 64 30).toNat lj9 ∗ codePt (l +
       BitVec.ofNat 64 34).toNat lj10 ∗ codePt (l + BitVec.ofNat 64 38).toNat lj11 ∗ regAny .rbp
       ∗ regAny .r12 ∗ regAny .r13 ∗ regAny .r14 ∗ regAny .r15 ∗ regAny .rsp ∗ wordPt (bw.toNat
       + 8) c1 ∗ wordPt (bw.toNat + 16) c2 ∗ wordPt (bw.toNat + 24) c3 ∗ wordPt (bw.toNat + 32)
       c4 ∗ wordPt (bw.toNat + 40) c5 ∗ wordPt (bw.toNat + 48) ksp ∗ wordPt (bw.toNat + 56) kret)) (entails_refl _)) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (loadQ_step (pc := (l + BitVec.ofNat 64 14)) (pc' := (l + BitVec.ofNat 64 18)) (bytes :=
        lj5) (base := .rdi) (dst := .rbp) (disp := 8#32) (a := bw.toNat + 8) (ea_add bw (by
        decide) (by omega)) (by decide) (by decide) (rip_advance l (by decide)))
      (codePt (l + BitVec.ofNat 64 11).toNat lj4 ∗ wordPt bw.toNat c0 ∗ regPt .rbx c0 ∗ codePt
       l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat 64
       4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ regPt .rsi v ∗ regPt .rax
       (retVal v) ∗ flagsAny ∗ codePt (l + BitVec.ofNat 64 18).toNat lj6 ∗ codePt (l +
       BitVec.ofNat 64 22).toNat lj7 ∗ codePt (l + BitVec.ofNat 64 26).toNat lj8 ∗ codePt (l +
       BitVec.ofNat 64 30).toNat lj9 ∗ codePt (l + BitVec.ofNat 64 34).toNat lj10 ∗ codePt (l +
       BitVec.ofNat 64 38).toNat lj11 ∗ regAny .r12 ∗ regAny .r13 ∗ regAny .r14 ∗ regAny .r15 ∗
       regAny .rsp ∗ wordPt (bw.toNat + 16) c2 ∗ wordPt (bw.toNat + 24) c3 ∗ wordPt (bw.toNat +
       32) c4 ∗ wordPt (bw.toNat + 40) c5 ∗ wordPt (bw.toNat + 48) ksp ∗ wordPt (bw.toNat + 56)
       kret)) (entails_refl _)) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (loadQ_step (pc := (l + BitVec.ofNat 64 18)) (pc' := (l + BitVec.ofNat 64 22)) (bytes :=
        lj6) (base := .rdi) (dst := .r12) (disp := 16#32) (a := bw.toNat + 16) (ea_add bw (by
        decide) (by omega)) (by decide) (by decide) (rip_advance l (by decide)))
      (codePt (l + BitVec.ofNat 64 14).toNat lj5 ∗ wordPt (bw.toNat + 8) c1 ∗ regPt .rbp c1 ∗
       codePt (l + BitVec.ofNat 64 11).toNat lj4 ∗ wordPt bw.toNat c0 ∗ regPt .rbx c0 ∗ codePt
       l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat 64
       4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ regPt .rsi v ∗ regPt .rax
       (retVal v) ∗ flagsAny ∗ codePt (l + BitVec.ofNat 64 22).toNat lj7 ∗ codePt (l +
       BitVec.ofNat 64 26).toNat lj8 ∗ codePt (l + BitVec.ofNat 64 30).toNat lj9 ∗ codePt (l +
       BitVec.ofNat 64 34).toNat lj10 ∗ codePt (l + BitVec.ofNat 64 38).toNat lj11 ∗ regAny .r13
       ∗ regAny .r14 ∗ regAny .r15 ∗ regAny .rsp ∗ wordPt (bw.toNat + 24) c3 ∗ wordPt (bw.toNat
       + 32) c4 ∗ wordPt (bw.toNat + 40) c5 ∗ wordPt (bw.toNat + 48) ksp ∗ wordPt (bw.toNat +
       56) kret)) (entails_refl _)) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (loadQ_step (pc := (l + BitVec.ofNat 64 22)) (pc' := (l + BitVec.ofNat 64 26)) (bytes :=
        lj7) (base := .rdi) (dst := .r13) (disp := 24#32) (a := bw.toNat + 24) (ea_add bw (by
        decide) (by omega)) (by decide) (by decide) (rip_advance l (by decide)))
      (codePt (l + BitVec.ofNat 64 18).toNat lj6 ∗ wordPt (bw.toNat + 16) c2 ∗ regPt .r12 c2 ∗
       codePt (l + BitVec.ofNat 64 14).toNat lj5 ∗ wordPt (bw.toNat + 8) c1 ∗ regPt .rbp c1 ∗
       codePt (l + BitVec.ofNat 64 11).toNat lj4 ∗ wordPt bw.toNat c0 ∗ regPt .rbx c0 ∗ codePt
       l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat 64
       4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ regPt .rsi v ∗ regPt .rax
       (retVal v) ∗ flagsAny ∗ codePt (l + BitVec.ofNat 64 26).toNat lj8 ∗ codePt (l +
       BitVec.ofNat 64 30).toNat lj9 ∗ codePt (l + BitVec.ofNat 64 34).toNat lj10 ∗ codePt (l +
       BitVec.ofNat 64 38).toNat lj11 ∗ regAny .r14 ∗ regAny .r15 ∗ regAny .rsp ∗ wordPt
       (bw.toNat + 32) c4 ∗ wordPt (bw.toNat + 40) c5 ∗ wordPt (bw.toNat + 48) ksp ∗ wordPt
       (bw.toNat + 56) kret)) (entails_refl _)) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (loadQ_step (pc := (l + BitVec.ofNat 64 26)) (pc' := (l + BitVec.ofNat 64 30)) (bytes :=
        lj8) (base := .rdi) (dst := .r14) (disp := 32#32) (a := bw.toNat + 32) (ea_add bw (by
        decide) (by omega)) (by decide) (by decide) (rip_advance l (by decide)))
      (codePt (l + BitVec.ofNat 64 22).toNat lj7 ∗ wordPt (bw.toNat + 24) c3 ∗ regPt .r13 c3 ∗
       codePt (l + BitVec.ofNat 64 18).toNat lj6 ∗ wordPt (bw.toNat + 16) c2 ∗ regPt .r12 c2 ∗
       codePt (l + BitVec.ofNat 64 14).toNat lj5 ∗ wordPt (bw.toNat + 8) c1 ∗ regPt .rbp c1 ∗
       codePt (l + BitVec.ofNat 64 11).toNat lj4 ∗ wordPt bw.toNat c0 ∗ regPt .rbx c0 ∗ codePt
       l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat 64
       4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ regPt .rsi v ∗ regPt .rax
       (retVal v) ∗ flagsAny ∗ codePt (l + BitVec.ofNat 64 30).toNat lj9 ∗ codePt (l +
       BitVec.ofNat 64 34).toNat lj10 ∗ codePt (l + BitVec.ofNat 64 38).toNat lj11 ∗ regAny .r15
       ∗ regAny .rsp ∗ wordPt (bw.toNat + 40) c5 ∗ wordPt (bw.toNat + 48) ksp ∗ wordPt (bw.toNat
       + 56) kret)) (entails_refl _)) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (loadQ_step (pc := (l + BitVec.ofNat 64 30)) (pc' := (l + BitVec.ofNat 64 34)) (bytes :=
        lj9) (base := .rdi) (dst := .r15) (disp := 40#32) (a := bw.toNat + 40) (ea_add bw (by
        decide) (by omega)) (by decide) (by decide) (rip_advance l (by decide)))
      (codePt (l + BitVec.ofNat 64 26).toNat lj8 ∗ wordPt (bw.toNat + 32) c4 ∗ regPt .r14 c4 ∗
       codePt (l + BitVec.ofNat 64 22).toNat lj7 ∗ wordPt (bw.toNat + 24) c3 ∗ regPt .r13 c3 ∗
       codePt (l + BitVec.ofNat 64 18).toNat lj6 ∗ wordPt (bw.toNat + 16) c2 ∗ regPt .r12 c2 ∗
       codePt (l + BitVec.ofNat 64 14).toNat lj5 ∗ wordPt (bw.toNat + 8) c1 ∗ regPt .rbp c1 ∗
       codePt (l + BitVec.ofNat 64 11).toNat lj4 ∗ wordPt bw.toNat c0 ∗ regPt .rbx c0 ∗ codePt
       l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat 64
       4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ regPt .rsi v ∗ regPt .rax
       (retVal v) ∗ flagsAny ∗ codePt (l + BitVec.ofNat 64 34).toNat lj10 ∗ codePt (l +
       BitVec.ofNat 64 38).toNat lj11 ∗ regAny .rsp ∗ wordPt (bw.toNat + 48) ksp ∗ wordPt
       (bw.toNat + 56) kret)) (entails_refl _)) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (loadQ_step (pc := (l + BitVec.ofNat 64 34)) (pc' := (l + BitVec.ofNat 64 38)) (bytes :=
        lj10) (base := .rdi) (dst := .rsp) (disp := 48#32) (a := bw.toNat + 48) (ea_add bw (by
        decide) (by omega)) (by decide) (by decide) (rip_advance l (by decide)))
      (codePt (l + BitVec.ofNat 64 30).toNat lj9 ∗ wordPt (bw.toNat + 40) c5 ∗ regPt .r15 c5 ∗
       codePt (l + BitVec.ofNat 64 26).toNat lj8 ∗ wordPt (bw.toNat + 32) c4 ∗ regPt .r14 c4 ∗
       codePt (l + BitVec.ofNat 64 22).toNat lj7 ∗ wordPt (bw.toNat + 24) c3 ∗ regPt .r13 c3 ∗
       codePt (l + BitVec.ofNat 64 18).toNat lj6 ∗ wordPt (bw.toNat + 16) c2 ∗ regPt .r12 c2 ∗
       codePt (l + BitVec.ofNat 64 14).toNat lj5 ∗ wordPt (bw.toNat + 8) c1 ∗ regPt .rbp c1 ∗
       codePt (l + BitVec.ofNat 64 11).toNat lj4 ∗ wordPt bw.toNat c0 ∗ regPt .rbx c0 ∗ codePt
       l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat 64
       4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ regPt .rsi v ∗ regPt .rax
       (retVal v) ∗ flagsAny ∗ codePt (l + BitVec.ofNat 64 38).toNat lj11 ∗ wordPt (bw.toNat +
       56) kret)) (entails_refl _)) ?_
  exact Triple.post (Triple.refl _) (entails_of_eq (by ac_rfl))

theorem lj11_eq : lj11 = [0xff, 0x67, 0x38] := by decide

theorem longjmp_code {l : Word} (hl : l.toNat + 41 < 2 ^ 64) :
    codePt l.toNat longjmpBytes =
      (codePt l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat
      64 4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ codePt (l + BitVec.ofNat 64
      11).toNat lj4 ∗ codePt (l + BitVec.ofNat 64 14).toNat lj5 ∗ codePt (l + BitVec.ofNat 64
      18).toNat lj6 ∗ codePt (l + BitVec.ofNat 64 22).toNat lj7 ∗ codePt (l + BitVec.ofNat 64
      26).toNat lj8 ∗ codePt (l + BitVec.ofNat 64 30).toNat lj9 ∗ codePt (l + BitVec.ofNat 64
      34).toNat lj10 ∗ codePt (l + BitVec.ofNat 64 38).toNat lj11) := by
  have t := fun k (h : k ≤ 41) => Silmaril.X86.Ext.toNat_add_ofNat (x := l) (k := k) (by omega)
  rw [t 2 (by omega), t 4 (by omega), t 6 (by omega), t 11 (by omega), t 14 (by omega),
    t 18 (by omega), t 22 (by omega), t 26 (by omega), t 30 (by omega), t 34 (by omega),
    t 38 (by omega), longjmpBytes_eq]
  simp only [codePt, bytesAt_append, List.append_assoc, lj0, lj1, lj2, lj3, lj4, lj5, lj6, lj7,
    lj8, lj9, lj10, lj11_eq, List.length_cons, List.length_nil, Nat.add_assoc, Nat.reduceAdd]

theorem ea_38 (bw : Word) (hb : bw.toNat + 64 < 2 ^ 64) : (ea bw 0x38#8).toNat = bw.toNat + 56 := by
  rw [ea, show (0x38#8 : BitVec 8).signExtend 64 = BitVec.ofNat 64 56 by decide]
  exact Silmaril.X86.Ext.toNat_add_ofNat (by omega)

/-- **`longjmp` as an exceptional-only two-exit triple.** Called with
`rdi = bw`, a `jmp_buf` holding the continuation `k`, and `rsi = v`, it restores `k`'s
callee-saved registers and stack pointer and jumps to `k.ret` with `rax = retVal v` (`v` as an
`int`, `1` if it is `0`). The normal exit is never taken, so `Q` is arbitrary. The payload
returns the code and the `jmp_buf`; the precondition owns every register `AtCont` mentions. -/
theorem longjmp_triple {σ : Type} {I : Isa σ} (E : Silmaril.X86.Open9.isa.Extends I)
    {l bw v c0 c1 c2 c3 c4 c5 ksp kret : Word}
    (hl : l.toNat + 41 < 2 ^ 64) (hb : bw.toNat + 64 < 2 ^ 64) (Q : SProp) (n : Nat) :
    STripleX I n
      (codePt l.toNat longjmpBytes ∗ ripPt l ∗ regPt .rdi bw ∗ regPt .rsi v ∗ regAny .rax ∗
        flagsAny ∗ regsAny calleeSavedRegs ∗ regAny .rsp ∗
        regsAny [.rcx, .rdx, .r8, .r9, .r10, .r11] ∗
        jbPt bw.toNat ⟨[c0, c1, c2, c3, c4, c5], ksp, kret⟩)
      Q ⟨[c0, c1, c2, c3, c4, c5], ksp, kret⟩
      (fun v' => ⌜v' = retVal v⌝ ∗ codePt l.toNat longjmpBytes ∗
        jbPt bw.toNat ⟨[c0, c1, c2, c3, c4, c5], ksp, kret⟩) := by
  cases n with
  | zero => exact STripleX.zero _ _ _ _
  | succ n =>
  rw [longjmp_code hl, jbPt_words, regsAny_calleeSaved]
  simp only [regsAny, regsWith, sep_emp]
  have hbody := Triple.frame (longjmp_body (l := l) (bw := bw) (v := v) (c0 := c0) (c1 := c1)
    (c2 := c2) (c3 := c3) (c4 := c4) (c5 := c5) (ksp := ksp) (kret := kret) hb)
    (regAny .rcx ∗ regAny .rdx ∗ regAny .r8 ∗ regAny .r9 ∗ regAny .r10 ∗ regAny .r11)
  refine STripleX.triple_seq
    ((Triple.pre (entails_of_eq (by ac_rfl)) hbody).lift (Silmaril.X86.Open9.extendsOpen.trans E)) ?_
  have hj := jmpM_progress E (need := RW) (fun q h => h.1) .rdi 0x38#8
    (l + BitVec.ofNat 64 38) bw kret
  rw [ea_38 bw hb, show encJmpM .rdi 0x38#8 = lj11 from rfl,
    show wordAt RW (bw.toNat + 56) kret = wordPt (bw.toNat + 56) kret from rfl] at hj
  refine STripleX.progress_seq (Progress.conseq (entails_of_eq (by ac_rfl))
    (Progress.frame hj
      (codePt l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat
       64 4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ codePt (l + BitVec.ofNat 64
       11).toNat lj4 ∗ codePt (l + BitVec.ofNat 64 14).toNat lj5 ∗ codePt (l + BitVec.ofNat 64
       18).toNat lj6 ∗ codePt (l + BitVec.ofNat 64 22).toNat lj7 ∗ codePt (l + BitVec.ofNat 64
       26).toNat lj8 ∗ codePt (l + BitVec.ofNat 64 30).toNat lj9 ∗ codePt (l + BitVec.ofNat 64
       34).toNat lj10 ∗ regPt .rsi v ∗ regPt .rax (retVal v) ∗ flagsAny ∗ regPt .rbx c0 ∗ regPt
       .rbp c1 ∗ regPt .r12 c2 ∗ regPt .r13 c3 ∗ regPt .r14 c4 ∗ regPt .r15 c5 ∗ regPt .rsp ksp
       ∗ wordPt bw.toNat c0 ∗ wordPt (bw.toNat + 8) c1 ∗ wordPt (bw.toNat + 16) c2 ∗ wordPt
       (bw.toNat + 24) c3 ∗ wordPt (bw.toNat + 32) c4 ∗ wordPt (bw.toNat + 40) c5 ∗ wordPt
       (bw.toNat + 48) ksp ∗ regAny .rcx ∗ regAny .rdx ∗ regAny .r8 ∗ regAny .r9 ∗ regAny .r10 ∗
       regAny .r11))
    (entails_refl _)) ?_
  refine STripleX.throw ?_ Q
  refine sexists_intro (retVal v) ?_
  refine spure_sep_intro (retVal_ne_zero v) ?_
  rw [sep_left_comm (AtCont _ (retVal v)) (⌜retVal v = retVal v⌝)]
  refine spure_sep_intro rfl ?_
  simp only [AtCont, clobberedRegs, regsAny, regsWith, calleeSavedRegs, sep_emp]
  exact entails_trans (entails_of_eq (by ac_rfl))
    (entails_trans (sep_mono_left
      (codePt (l + BitVec.ofNat 64 38).toNat lj11 ∗ ripPt kret ∗ wordPt (bw.toNat + 56) kret ∗
       codePt l.toNat lj0 ∗ codePt (l + BitVec.ofNat 64 2).toNat lj1 ∗ codePt (l + BitVec.ofNat
       64 4).toNat lj2 ∗ codePt (l + BitVec.ofNat 64 6).toNat lj3 ∗ codePt (l + BitVec.ofNat 64
       11).toNat lj4 ∗ codePt (l + BitVec.ofNat 64 14).toNat lj5 ∗ codePt (l + BitVec.ofNat 64
       18).toNat lj6 ∗ codePt (l + BitVec.ofNat 64 22).toNat lj7 ∗ codePt (l + BitVec.ofNat 64
       26).toNat lj8 ∗ codePt (l + BitVec.ofNat 64 30).toNat lj9 ∗ codePt (l + BitVec.ofNat 64
       34).toNat lj10 ∗ regPt .rax (retVal v) ∗ flagsAny ∗ regPt .rbx c0 ∗ regPt .rbp c1 ∗ regPt
       .r12 c2 ∗ regPt .r13 c3 ∗ regPt .r14 c4 ∗ regPt .r15 c5 ∗ regPt .rsp ksp ∗ wordPt
       bw.toNat c0 ∗ wordPt (bw.toNat + 8) c1 ∗ wordPt (bw.toNat + 16) c2 ∗ wordPt (bw.toNat +
       24) c3 ∗ wordPt (bw.toNat + 32) c4 ∗ wordPt (bw.toNat + 40) c5 ∗ wordPt (bw.toNat + 48)
       ksp ∗ regAny .rcx ∗ regAny .rdx ∗ regAny .r8 ∗ regAny .r9 ∗ regAny .r10 ∗ regAny .r11)
      (show regPt .rsi v ∗ regPt .rdi bw ⊢ₛ regAny .rsi ∗ regAny .rdi from
        sep_mono (fun _ hp => ⟨_, hp⟩) (fun _ hp => ⟨_, hp⟩)))
      (entails_of_eq (by ac_rfl)))

end Silmaril.Proofs.X86.Sep.JmpBuf
