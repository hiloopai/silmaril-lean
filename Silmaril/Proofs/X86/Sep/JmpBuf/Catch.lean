module

public import Silmaril.Proofs.X86.Sep.JmpBuf.Longjmp
public import Silmaril.X86.Sep.JmpBuf.Catch.Defs

/-!
# Proofs: the catch test (`catch → throw2 → throw1 → longjmp`)

The program and its pre- and postcondition are in `Sep/JmpBuf/Catch/Defs.lean`.

* `throw1_x`, `throw2_x`: two-exit triples of the callees, built by `xcall_rule` from
  `longjmp_triple`. Their normal postcondition is `sfalse`: they never return normally.
* `region_x`: the protected region of `catch`, from the first return of `setjmp`.
* `handler`: the handler, from every exceptional state.
* `catch_test`: **`catch` returns `-1`**, an ordinary `STriple` at every index on every
  machine `I` with `Open9.isa.Extends I`, through `catch_rule`.

The framed sequential compositions are each `Triple.trans` (or `STripleX.triple_seq`) of a
framed instruction triple; the frames and rearrangements are closed by `ac_rfl`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Sep.JmpBuf.CatchTest

open Silmaril.X86 (State MState Word Byte Reg Insn)
open Silmaril.X86.Ext (rip_advance toNat_add_ofNat)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.JmpBuf
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Safe
open Silmaril.Proofs.X86.Sep.JmpBuf
open Silmaril.Proofs.X86.Sep.Insn
open Silmaril.X86.Sep.Insn (testFlags)
open Silmaril.X86.Sep.JmpBuf.CatchTest

/-- The assertion that holds of no fragment. -/
def sfalse : SProp := fun _ => False

theorem sep_sfalse (P : SProp) : (P ∗ sfalse) ⊢ₛ sfalse := by
  rintro _ ⟨_, _, _, _, _, h⟩; exact h

theorem sfalse_sep (P : SProp) : (sfalse ∗ P) ⊢ₛ sfalse := by
  rintro _ ⟨_, _, _, _, h, _⟩; exact h

/-- The payload of the test: `rax = 1`, and garbage. -/
def Ew : Word → SProp := fun v => ⌜v = 1⌝ ∗ strue

theorem Ew_frame (v : Word) (R : SProp) : (Ew v ∗ R) ⊢ₛ Ew v := by
  unfold Ew
  rw [sep_assoc]
  exact sep_mono_right _ (entails_strue _)

theorem pt_any {r : Reg} {v : Word} : regPt r v ⊢ₛ regAny r := fun _ hp => ⟨_, hp⟩

/-! ## Code -/


theorem call_target (e : Word) {rel : BitVec 32} {a r c : Nat}
    (hr : rel.signExtend 64 = BitVec.ofNat 64 r) (h : a + 5 + r = c) :
    e + BitVec.ofNat 64 a + 5#64 + rel.signExtend 64 = e + BitVec.ofNat 64 c := by
  rw [hr, show (5#64 : Word) = BitVec.ofNat 64 5 from rfl, rip_advance e rfl, rip_advance e h]

theorem ret_addr (e : Word) (a : Nat) :
    e + BitVec.ofNat 64 a + 5#64 = e + BitVec.ofNat 64 (a + 5) := by
  rw [show (5#64 : Word) = BitVec.ofNat 64 5 from rfl, rip_advance e rfl]

theorem sub8 {s : Word} (h : 8 ≤ s.toNat) : (s - 8#64).toNat = s.toNat - 8 := by
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

variable {σ : Type} {I : Isa σ} (E : Silmaril.X86.Open9.isa.Extends I)
  {e jb c0 c1 c2 c3 c4 c5 ksp kret : Word}

include E

local notation "EO" => Silmaril.X86.Open9.extendsOpen.trans E

local notation "OTH" => regsAny [Reg.rcx, Reg.rdx, Reg.r8, Reg.r9, Reg.r10, Reg.r11]

/-! ## `throw1` -/

/-- **`throw1`**: `mov $0, %esi; call longjmp`, entered with return address `ra` at `s`. -/
theorem throw1_x (n : Nat) (s ra : Word) (h8 : 8 ≤ s.toNat) (he : e.toNat + 122 < 2 ^ 64)
    (hb : jb.toNat + 64 < 2 ^ 64) :
    STripleX I n
      (ripPt (e + BitVec.ofNat 64 27) ∗ regPt .rsp s ∗ wordPt s.toNat ra ∗
        (codePt (e + BitVec.ofNat 64 27).toNat t1Mov ∗ codePt (e + BitVec.ofNat 64 32).toNat (Insn.encode (.call 0x2c#32)) ∗
          codePt (e + BitVec.ofNat 64 81).toNat longjmpBytes ∗ blockAny (s.toNat - 8) 8 ∗
          regPt .rdi jb ∗ regAny .rsi ∗ regAny .rax ∗ flagsAny ∗ regsAny calleeSavedRegs ∗ OTH ∗
          jbPt jb.toNat (⟨[c0, c1, c2, c3, c4, c5], ksp, kret⟩ : Cont)))
      sfalse (⟨[c0, c1, c2, c3, c4, c5], ksp, kret⟩ : Cont) Ew := by
  have hl : (e + BitVec.ofNat 64 81).toNat + 41 < 2 ^ 64 := by
    rw [toNat_add_ofNat (by omega)]; omega
  have LJ := STripleX.frameF (longjmp_triple E (l := e + BitVec.ofNat 64 81) (bw := jb)
    (v := (0#32).setWidth 64) (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (c4 := c4) (c5 := c5)
    (ksp := ksp) (kret := kret) hl hb sfalse n)
    (wordPt (s.toNat - 8) (e + BitVec.ofNat 64 32 + 5#64) ∗ wordPt s.toNat ra)
  have hS : STripleX I n
      (ripPt (e + BitVec.ofNat 64 81) ∗ regPt .rsp (s - 8#64) ∗
        wordPt (s.toNat - 8) (e + BitVec.ofNat 64 32 + 5#64) ∗
        (codePt (e + BitVec.ofNat 64 81).toNat longjmpBytes ∗ regPt .rdi jb ∗
          regPt .rsi ((0#32).setWidth 64) ∗ regAny .rax ∗ flagsAny ∗ regsAny calleeSavedRegs ∗
          OTH ∗ jbPt jb.toNat (⟨[c0, c1, c2, c3, c4, c5], ksp, kret⟩ : Cont) ∗ wordPt s.toNat ra))
      sfalse (⟨[c0, c1, c2, c3, c4, c5], ksp, kret⟩ : Cont) Ew :=
    STripleX.pre (sep_mono_right _ (sep_mono_left _ pt_any))
      (STripleX.conseq (entails_of_eq (by ac_rfl)) LJ (sfalse_sep _)
        (fun _ => spure_sep_elim fun hv => spure_sep_intro (by rw [hv]; decide)
          (entails_strue _)))
  have X := STripleX.frameF (xcall_rule EO (pc := e + BitVec.ofNat 64 32) (s := s)
    (rel := 0x2c#32) h8 (call_target e (r := 44) (by decide) (by rfl)) hS)
    (codePt (e + BitVec.ofNat 64 27).toNat t1Mov)
  have M := (movI32_step (pc := e + BitVec.ofNat 64 27) (pc' := e + BitVec.ofNat 64 32)
    (bytes := t1Mov) (r := .rsi) (imm := 0#32) (by decide) (rip_advance e (by decide))).lift EO
  refine STripleX.triple_seq (Triple.conseq (entails_of_eq (by ac_rfl)) (Triple.frame M
      (regPt .rsp s ∗ wordPt s.toNat ra ∗ codePt (e + BitVec.ofNat 64 32).toNat (Insn.encode (.call 0x2c#32)) ∗
        codePt (e + BitVec.ofNat 64 81).toNat longjmpBytes ∗ blockAny (s.toNat - 8) 8 ∗
        regPt .rdi jb ∗ regAny .rax ∗ flagsAny ∗ regsAny calleeSavedRegs ∗ OTH ∗
        jbPt jb.toNat (⟨[c0, c1, c2, c3, c4, c5], ksp, kret⟩ : Cont))) (entails_refl _)) ?_
  exact STripleX.conseq (entails_of_eq (by ac_rfl)) X
    (entails_trans (sep_mono_left _ (sep_sfalse _)) (sfalse_sep _))
    (fun v => Ew_frame v _)

/-! ## `throw2` -/

/-- **`throw2`**: `call throw1`, entered with return address `ra` at `s`. -/
theorem throw2_x (n : Nat) (s ra : Word) (h16 : 16 ≤ s.toNat) (he : e.toNat + 122 < 2 ^ 64)
    (hb : jb.toNat + 64 < 2 ^ 64) :
    STripleX I n
      (ripPt (e + BitVec.ofNat 64 21) ∗ regPt .rsp s ∗ wordPt s.toNat ra ∗
        (codePt (e + BitVec.ofNat 64 21).toNat (Insn.encode (.call 0x01#32)) ∗
          codePt (e + BitVec.ofNat 64 27).toNat t1Mov ∗
          codePt (e + BitVec.ofNat 64 32).toNat (Insn.encode (.call 0x2c#32)) ∗
          codePt (e + BitVec.ofNat 64 81).toNat longjmpBytes ∗ blockAny (s.toNat - 8) 8 ∗
          blockAny (s.toNat - 16) 8 ∗
          regPt .rdi jb ∗ regAny .rsi ∗ regAny .rax ∗ flagsAny ∗ regsAny calleeSavedRegs ∗ OTH ∗
          jbPt jb.toNat (⟨[c0, c1, c2, c3, c4, c5], ksp, kret⟩ : Cont)))
      sfalse (⟨[c0, c1, c2, c3, c4, c5], ksp, kret⟩ : Cont) Ew := by
  have T1 := throw1_x E (e := e) (jb := jb) (c0 := c0) (c1 := c1) (c2 := c2)
    (c3 := c3) (c4 := c4) (c5 := c5) (ksp := ksp) (kret := kret) n (s - 8#64)
    (e + BitVec.ofNat 64 21 + 5#64) (by rw [sub8 (by omega)]; omega) he hb
  rw [sub8 (by omega), show s.toNat - 8 - 8 = s.toNat - 16 by omega] at T1
  have X := STripleX.frameF (xcall_rule EO (pc := e + BitVec.ofNat 64 21) (s := s)
    (rel := 0x01#32) (by omega) (call_target e (r := 1) (by decide) (by rfl)) T1)
    (wordPt s.toNat ra)
  exact STripleX.conseq (entails_of_eq (by ac_rfl)) X
    (entails_trans (sep_mono_left _ (sep_sfalse _)) (sfalse_sep _)) (fun v => Ew_frame v _)

/-! ## The protected region of `catch` -/

/-- **The protected region**: after the first return of `setjmp` (`rax = 0`, at `e + 5`),
`test; jne` falls through and `call throw2` never returns normally. -/
theorem region_x (n : Nat) (s : Word) (h24 : 24 ≤ s.toNat) (he : e.toNat + 122 < 2 ^ 64)
    (hb : jb.toNat + 64 < 2 ^ 64) :
    STripleX I n
      (ripPt (e + BitVec.ofNat 64 5) ∗ regPt .rsp s ∗ regPt .rax 0 ∗ flagsAny ∗
        codePt (e + BitVec.ofNat 64 5).toNat cTest ∗ codePt (e + BitVec.ofNat 64 7).toNat cJne ∗
        codePt (e + BitVec.ofNat 64 9).toNat (Insn.encode (.call 0x07#32)) ∗ (codePt (e + BitVec.ofNat 64 21).toNat (Insn.encode (.call 0x01#32)) ∗
          codePt (e + BitVec.ofNat 64 27).toNat t1Mov ∗
          codePt (e + BitVec.ofNat 64 32).toNat (Insn.encode (.call 0x2c#32)) ∗
          codePt (e + BitVec.ofNat 64 81).toNat longjmpBytes) ∗
        blockAny (s.toNat - 8) 8 ∗ blockAny (s.toNat - 16) 8 ∗ blockAny (s.toNat - 24) 8 ∗
        regPt .rdi jb ∗ regAny .rsi ∗ regsAny calleeSavedRegs ∗ OTH ∗
        jbPt jb.toNat (⟨[c0, c1, c2, c3, c4, c5], ksp, kret⟩ : Cont))
      sfalse (⟨[c0, c1, c2, c3, c4, c5], ksp, kret⟩ : Cont)
      (fun v => Ew v ∗ (codePt (e + BitVec.ofNat 64 5).toNat cTest ∗ codePt (e + BitVec.ofNat 64 7).toNat cJne)) := by
  have T2 := throw2_x E (e := e) (jb := jb) (c0 := c0) (c1 := c1) (c2 := c2)
    (c3 := c3) (c4 := c4) (c5 := c5) (ksp := ksp) (kret := kret) n (s - 8#64)
    (e + BitVec.ofNat 64 9 + 5#64) (by rw [sub8 (by omega)]; omega) he hb
  rw [sub8 (by omega), show s.toNat - 8 - 8 = s.toNat - 16 by omega,
    show s.toNat - 8 - 16 = s.toNat - 24 by omega] at T2
  have X := STripleX.frameG (xcall_rule EO (pc := e + BitVec.ofNat 64 9) (s := s)
    (rel := 0x07#32) (by omega) (call_target e (r := 7) (by decide) (by rfl)) T2)
    (codePt (e + BitVec.ofNat 64 5).toNat cTest ∗ codePt (e + BitVec.ofNat 64 7).toNat cJne)
  have TS := testSelf_step (pc := e + BitVec.ofNat 64 5) (pc' := e + BitVec.ofNat 64 7)
    (bytes := cTest) (r := .rax) (v := 0) (by decide) (rip_advance e (by decide))
  have JN := jcc8_not_taken (pc := e + BitVec.ofNat 64 7) (pc' := e + BitVec.ofNat 64 9)
    (bytes := cJne) (c := .ne) (rel := 0x06#8) (f := testFlags 0) (by rfl) (by decide)
    (rip_advance e (by decide))
  have T : Triple Silmaril.X86.Open.isa
      (ripPt (e + BitVec.ofNat 64 5) ∗ regPt .rax 0 ∗ flagsAny ∗
        codePt (e + BitVec.ofNat 64 5).toNat cTest ∗ codePt (e + BitVec.ofNat 64 7).toNat cJne)
      (ripPt (e + BitVec.ofNat 64 9) ∗ regAny .rax ∗ flagsAny ∗
        codePt (e + BitVec.ofNat 64 5).toNat cTest ∗ codePt (e + BitVec.ofNat 64 7).toNat cJne) :=
    Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
        (Triple.frame TS (codePt (e + BitVec.ofNat 64 7).toNat cJne)) (entails_refl _))
      (Triple.conseq (entails_of_eq (by ac_rfl))
        (Triple.frame JN (codePt (e + BitVec.ofNat 64 5).toNat cTest ∗ regPt .rax 0))
        (entails_trans (entails_of_eq (by ac_rfl))
          (entails_trans (sep_mono_left
            (ripPt (e + BitVec.ofNat 64 9) ∗ codePt (e + BitVec.ofNat 64 5).toNat cTest ∗
              codePt (e + BitVec.ofNat 64 7).toNat cJne)
            (show (regPt .rax 0 ∗ flagsPt (testFlags 0)) ⊢ₛ (regAny .rax ∗ flagsAny) from
              sep_mono pt_any (fun _ hp => ⟨_, hp⟩)))
            (entails_of_eq (by ac_rfl)))))
  refine STripleX.triple_seq (Triple.conseq (entails_of_eq (by ac_rfl)) (Triple.frame (T.lift EO)
      (regPt .rsp s ∗ codePt (e + BitVec.ofNat 64 9).toNat (Insn.encode (.call 0x07#32)) ∗
        (codePt (e + BitVec.ofNat 64 21).toNat (Insn.encode (.call 0x01#32)) ∗
          codePt (e + BitVec.ofNat 64 27).toNat t1Mov ∗
          codePt (e + BitVec.ofNat 64 32).toNat (Insn.encode (.call 0x2c#32)) ∗
          codePt (e + BitVec.ofNat 64 81).toNat longjmpBytes) ∗ blockAny (s.toNat - 8) 8 ∗ blockAny (s.toNat - 16) 8 ∗
        blockAny (s.toNat - 24) 8 ∗ regPt .rdi jb ∗ regAny .rsi ∗ regsAny calleeSavedRegs ∗ OTH ∗
        jbPt jb.toNat (⟨[c0, c1, c2, c3, c4, c5], ksp, kret⟩ : Cont))) (entails_refl _)) ?_
  exact STripleX.conseq (entails_of_eq (by ac_rfl)) X
    (entails_trans (sep_mono_left _ (sep_sfalse _)) (sfalse_sep _))
    (fun v => sep_mono_left _ (Ew_frame v _))

/-! ## The handler -/

omit E in
/-- The handler's straight-line run: `test` (on `1`), `jne` taken, `mov $-1, %eax`, `ret`. -/
theorem handler_run (s r : Word) :
    Triple Silmaril.X86.Open.isa
      (ripPt (e + BitVec.ofNat 64 5) ∗ regPt .rsp s ∗ regPt .rax 1 ∗ flagsAny ∗
        (codePt (e + BitVec.ofNat 64 5).toNat cTest ∗ codePt (e + BitVec.ofNat 64 7).toNat cJne ∗
          codePt (e + BitVec.ofNat 64 15).toNat cMov ∗
          codePt (e + BitVec.ofNat 64 20).toNat (Insn.encode .ret) ∗ wordPt s.toNat r))
      (ripPt r ∗ regPt .rsp (s + 8#64) ∗ regPt .rax 0xFFFFFFFF#64 ∗ flagsAny ∗
        (codePt (e + BitVec.ofNat 64 5).toNat cTest ∗ codePt (e + BitVec.ofNat 64 7).toNat cJne ∗
          codePt (e + BitVec.ofNat 64 15).toNat cMov ∗
          codePt (e + BitVec.ofNat 64 20).toNat (Insn.encode .ret) ∗ wordPt s.toNat r)) := by
  have TS := testSelf_step (pc := e + BitVec.ofNat 64 5) (pc' := e + BitVec.ofNat 64 7)
    (bytes := cTest) (r := .rax) (v := 1) (by decide) (rip_advance e (by decide))
  have JT := jcc8_taken (pc := e + BitVec.ofNat 64 7) (pc' := e + BitVec.ofNat 64 15)
    (bytes := cJne) (c := .ne) (rel := 0x06#8) (f := testFlags 1) (by rfl) (by decide)
    (by rw [show (0x06#8 : BitVec 8).signExtend 64 = BitVec.ofNat 64 6 by decide,
      rip_advance e (show 7 + cJne.length = 9 by decide), rip_advance e (show 9 + 6 = 15 by rfl)])
  have MV := movI32_step (pc := e + BitVec.ofNat 64 15) (pc' := e + BitVec.ofNat 64 20)
    (bytes := cMov) (r := .rax) (imm := 0xffffffff#32) (by decide) (rip_advance e (by decide))
  rw [show ((0xffffffff#32 : BitVec 32).setWidth 64) = 0xFFFFFFFF#64 by decide] at MV
  have RT := Silmaril.Proofs.X86.Sep.ret_step (e + BitVec.ofNat 64 20) s r
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl)) (Triple.frame TS
    (regPt .rsp s ∗ codePt (e + BitVec.ofNat 64 7).toNat cJne ∗
      codePt (e + BitVec.ofNat 64 15).toNat cMov ∗
      codePt (e + BitVec.ofNat 64 20).toNat (Insn.encode .ret) ∗ wordPt s.toNat r))
    (entails_refl _)) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl)) (Triple.frame JT
    (regPt .rsp s ∗ regPt .rax 1 ∗ codePt (e + BitVec.ofNat 64 5).toNat cTest ∗
      codePt (e + BitVec.ofNat 64 15).toNat cMov ∗
      codePt (e + BitVec.ofNat 64 20).toNat (Insn.encode .ret) ∗ wordPt s.toNat r))
    (entails_refl _)) ?_
  refine Triple.pre (entails_trans (entails_of_eq (by ac_rfl)) (sep_mono_left
    (ripPt (e + BitVec.ofNat 64 15) ∗ regPt .rsp s ∗ codePt (e + BitVec.ofNat 64 5).toNat cTest ∗
      codePt (e + BitVec.ofNat 64 7).toNat cJne ∗ codePt (e + BitVec.ofNat 64 15).toNat cMov ∗
      codePt (e + BitVec.ofNat 64 20).toNat (Insn.encode .ret) ∗ wordPt s.toNat r)
    (show (regPt .rax 1 ∗ flagsPt (testFlags 1)) ⊢ₛ (regAny .rax ∗ flagsAny) from
      sep_mono pt_any (fun _ hp => ⟨_, hp⟩)))) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl)) (Triple.frame MV
    (regPt .rsp s ∗ flagsAny ∗ codePt (e + BitVec.ofNat 64 5).toNat cTest ∗
      codePt (e + BitVec.ofNat 64 7).toNat cJne ∗
      codePt (e + BitVec.ofNat 64 20).toNat (Insn.encode .ret) ∗ wordPt s.toNat r))
    (entails_refl _)) ?_
  exact Triple.conseq (entails_of_eq (by ac_rfl)) (Triple.frame RT
    (regPt .rax 0xFFFFFFFF#64 ∗ flagsAny ∗ codePt (e + BitVec.ofNat 64 5).toNat cTest ∗
      codePt (e + BitVec.ofNat 64 7).toNat cJne ∗ codePt (e + BitVec.ofNat 64 15).toNat cMov))
    (entails_of_eq (by ac_rfl))

/-- **The handler**, from every exceptional state of the region (survivor frame: the
handler's code and `catch`'s return slot). -/
theorem handler (n : Nat) (s r : Word) (v : Word) :
    STriple I n
      (AtCont (⟨[c0, c1, c2, c3, c4, c5], s, e + BitVec.ofNat 64 5⟩ : Cont) v ∗
        (Ew v ∗ (codePt (e + BitVec.ofNat 64 5).toNat cTest ∗ codePt (e + BitVec.ofNat 64 7).toNat cJne ∗
          codePt (e + BitVec.ofNat 64 15).toNat cMov ∗
          codePt (e + BitVec.ofNat 64 20).toNat (Insn.encode .ret) ∗ wordPt s.toNat r)))
      (catchPost s r c0 c1 c2 c3 c4 c5) := by
  unfold AtCont Ew catchPost
  refine STriple.conseq (entails_of_eq (by ac_rfl : _ = (⌜v = 1⌝ ∗
      ((ripPt (e + BitVec.ofNat 64 5) ∗ regPt .rsp s ∗ regPt .rax v ∗ flagsAny ∗ (codePt (e + BitVec.ofNat 64 5).toNat cTest ∗ codePt (e + BitVec.ofNat 64 7).toNat cJne ∗
          codePt (e + BitVec.ofNat 64 15).toNat cMov ∗
          codePt (e + BitVec.ofNat 64 20).toNat (Insn.encode .ret) ∗ wordPt s.toNat r)) ∗
        (regsWith calleeSavedRegs [c0, c1, c2, c3, c4, c5] ∗ regsAny clobberedRegs ∗ strue)))))
    (STriple.spure_pre fun hv => ?_) (entails_refl _)
  subst hv
  refine STriple.of_triple (Triple.conseq (entails_refl _) (Triple.frame
    ((handler_run (e := e) s r).lift EO)
    (regsWith calleeSavedRegs [c0, c1, c2, c3, c4, c5] ∗ regsAny clobberedRegs ∗ strue)) ?_)
  exact entails_trans (entails_of_eq (by ac_rfl : _ =
      ((ripPt r ∗ regPt .rsp (s + 8#64) ∗ regPt .rax 0xFFFFFFFF#64 ∗ regsWith calleeSavedRegs [c0, c1, c2, c3, c4, c5]) ∗
        (flagsAny ∗ (codePt (e + BitVec.ofNat 64 5).toNat cTest ∗ codePt (e + BitVec.ofNat 64 7).toNat cJne ∗
          codePt (e + BitVec.ofNat 64 15).toNat cMov ∗
          codePt (e + BitVec.ofNat 64 20).toNat (Insn.encode .ret) ∗ wordPt s.toNat r) ∗ regsAny clobberedRegs ∗ strue))))
    (sep_mono_right _ (entails_strue _))


/-! ## `catch` returns `-1` -/

/-- **The catch test.** `catch` calls `setjmp`, then `throw2`, which calls `throw1`,
which calls `longjmp(jb, 0)`; `setjmp` returns again with `1` and `catch` returns `-1`
(`eax = 0xffffffff`) to `r` with `rsp = s + 8` and the callee-saved registers unchanged. Proved
at every index on every machine `I` with `Open9.isa.Extends I` (so `Open9.isa` and `Str9.isa`),
through `catch_rule`: the exceptional exit of `throw2` is sealed inside `catch`. -/
theorem catch_test (n : Nat) {s r : Word} (h24 : 24 ≤ s.toNat) (he : e.toNat + 122 < 2 ^ 64)
    (hb : jb.toNat + 64 < 2 ^ 64) :
    STriple I n (catchPre e s r jb c0 c1 c2 c3 c4 c5) (catchPost s r c0 c1 c2 c3 c4 c5) := by
  -- the region with its survivor frame, sealed by the handler
  have RG := STripleX.frameG (region_x E (e := e) (jb := jb) (c0 := c0) (c1 := c1)
    (c2 := c2) (c3 := c3) (c4 := c4) (c5 := c5) (ksp := s) (kret := (e + BitVec.ofNat 64 5)) n s h24 he hb)
    (codePt (e + BitVec.ofNat 64 15).toNat cMov ∗ codePt (e + BitVec.ofNat 64 20).toNat (Insn.encode .ret) ∗ wordPt s.toNat r)
  have RG' := STripleX.frameF RG
    (codePt e.toNat (Insn.encode (.call 0x21#32)) ∗ codePt (e + BitVec.ofNat 64 38).toNat setjmpBytes)
  have CR := catch_rule RG' (fun v _ => STriple.conseq (entails_of_eq (by ac_rfl))
    (handler E (e := e) (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (c4 := c4)
      (c5 := c5) n s r v) (entails_refl _))
  -- `call setjmp` and `setjmp`
  have CT := Silmaril.X86.Sep.call_step EO e s 0x21#32 (by omega)
  rw [show e + 5#64 + (0x21#32 : BitVec 32).signExtend 64 = (e + BitVec.ofNat 64 38) by
    rw [show (0x21#32 : BitVec 32).signExtend 64 = BitVec.ofNat 64 33 by decide]
    exact rip_advance e rfl] at CT
  have SJ := Triple.lift EO <| setjmp_triple (e := (e + BitVec.ofNat 64 38)) (sp := s - 8#64) (ret := e + 5#64) (bw := jb)
    (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (c4 := c4) (c5 := c5)
    (by rw [toNat_add_ofNat (by omega)]; omega) hb
  rw [sub8 (by omega), saved, BitVec.sub_add_cancel] at SJ
  have S1 := Triple.trans (Triple.conseq (entails_refl _) (Triple.frame CT
      (codePt (e + BitVec.ofNat 64 38).toNat setjmpBytes ∗ regPt .rdi jb ∗ regsWith calleeSavedRegs [c0, c1, c2, c3, c4, c5] ∗ regAny .rdx ∗ regAny .rax ∗
        flagsAny ∗ jbAny jb.toNat)) (entails_refl _))
    (Triple.conseq (entails_of_eq (by ac_rfl)) (Triple.frame SJ
      (codePt e.toNat (Insn.encode (.call 0x21#32)))) (entails_refl _))
  unfold catchPre
  simp only [regsAny, regsWith, calleeSavedRegs, sep_emp] at RG CR S1 ⊢
  refine STriple.triple_seq (Triple.conseq (entails_of_eq (by ac_rfl)) (Triple.frame S1
      (codePt (e + BitVec.ofNat 64 5).toNat cTest ∗ codePt (e + BitVec.ofNat 64 7).toNat cJne ∗
        codePt (e + BitVec.ofNat 64 9).toNat (Insn.encode (.call 0x07#32)) ∗ codePt (e + BitVec.ofNat 64 15).toNat cMov ∗
        codePt (e + BitVec.ofNat 64 20).toNat (Insn.encode .ret) ∗
        codePt (e + BitVec.ofNat 64 21).toNat (Insn.encode (.call 0x01#32)) ∗ codePt (e + BitVec.ofNat 64 27).toNat t1Mov ∗
        codePt (e + BitVec.ofNat 64 32).toNat (Insn.encode (.call 0x2c#32)) ∗
        codePt (e + BitVec.ofNat 64 81).toNat longjmpBytes ∗ wordPt s.toNat r ∗ blockAny (s.toNat - 16) 8 ∗
        blockAny (s.toNat - 24) 8 ∗ regAny .rsi ∗ regAny .rcx ∗ regAny .r8 ∗ regAny .r9 ∗
        regAny .r10 ∗ regAny .r11)) (entails_refl _)) ?_
  refine STriple.conseq ?_ CR (sor_elim (entails_trans (sep_mono_left _ (sfalse_sep _))
    (entails_trans (sfalse_sep _) (fun _ h => h.elim))) ?_)
  · refine entails_trans (entails_of_eq (by ac_rfl : _ =
      ((wordPt (s.toNat - 8) (e + BitVec.ofNat 64 5) ∗ regPt .rdx (e + BitVec.ofNat 64 5) ∗ regPt .rbx c0 ∗ regPt .rbp c1 ∗
        regPt .r12 c2 ∗ regPt .r13 c3 ∗ regPt .r14 c4 ∗ regPt .r15 c5) ∗
      (codePt (e + BitVec.ofNat 64 38).toNat setjmpBytes ∗ ripPt (e + BitVec.ofNat 64 5) ∗ regPt .rsp s ∗ regPt .rdi jb ∗
        regPt .rax 0 ∗ flagsAny ∗ jbPt jb.toNat (⟨[c0, c1, c2, c3, c4, c5], s, (e + BitVec.ofNat 64 5)⟩ : Cont) ∗
        codePt e.toNat (Insn.encode (.call 0x21#32)) ∗
        codePt (e + BitVec.ofNat 64 5).toNat cTest ∗ codePt (e + BitVec.ofNat 64 7).toNat cJne ∗
        codePt (e + BitVec.ofNat 64 9).toNat (Insn.encode (.call 0x07#32)) ∗ codePt (e + BitVec.ofNat 64 15).toNat cMov ∗
        codePt (e + BitVec.ofNat 64 20).toNat (Insn.encode .ret) ∗
        codePt (e + BitVec.ofNat 64 21).toNat (Insn.encode (.call 0x01#32)) ∗ codePt (e + BitVec.ofNat 64 27).toNat t1Mov ∗
        codePt (e + BitVec.ofNat 64 32).toNat (Insn.encode (.call 0x2c#32)) ∗
        codePt (e + BitVec.ofNat 64 81).toNat longjmpBytes ∗ wordPt s.toNat r ∗ blockAny (s.toNat - 16) 8 ∗
        blockAny (s.toNat - 24) 8 ∗ regAny .rsi ∗ regAny .rcx ∗ regAny .r8 ∗ regAny .r9 ∗
        regAny .r10 ∗ regAny .r11)))) ?_
    refine entails_trans (sep_mono_left _ (sep_mono (wordPt_blockAny _ _)
      (sep_mono pt_any (sep_mono pt_any (sep_mono pt_any (sep_mono pt_any (sep_mono pt_any
        (sep_mono pt_any pt_any)))))))) ?_
    exact entails_of_eq (by ac_rfl)
  · unfold catchPost
    rw [sep_assoc]
    exact strue_absorb _

omit E in
/-- **The catch test on `Open9`** (the machine whose `jmp *56(%rdi)` is the `Ext9` form). -/
theorem catch_test_open9 (n : Nat) {s r : Word} (h24 : 24 ≤ s.toNat)
    (he : e.toNat + 122 < 2 ^ 64) (hb : jb.toNat + 64 < 2 ^ 64) :
    STriple Silmaril.X86.Open9.isa n (catchPre e s r jb c0 c1 c2 c3 c4 c5)
      (catchPost s r c0 c1 c2 c3 c4 c5) :=
  catch_test (Isa.Extends.refl _) n h24 he hb

end Silmaril.Proofs.X86.Sep.JmpBuf.CatchTest
