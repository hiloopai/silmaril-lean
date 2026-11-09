module

public import Silmaril.X86.Sep.JmpBuf.Defs
public import Silmaril.Proofs.X86.Sep.Insn
public import Silmaril.Proofs.X86.Sep.Call

/-!
# Proofs: `setjmp` as a total triple on the open machine

* `setjmp_split`: the twelve instructions of `setjmpBytes`, each an instruction triple of
  `Proofs/X86/Sep/Insn.lean` framed with the rest, composed with `Triple.trans` (the frames
  and rearrangements are closed by `ac_rfl`).
* `setjmp_code`, `jbAny_split`, `jbPt_words`: the code and the `jmp_buf` as their pieces.
* `setjmp_triple`: the whole function.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Sep.JmpBuf

open Silmaril.X86 (State MState Word Byte Reg Insn)
open Silmaril.X86.Ext (rip_advance)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.JmpBuf
open Silmaril.Proofs.X86.Sep.Insn

/-! ## Listing chunks -/

def sj0 : List Byte := [0x48, 0x89, 0x1f]
def sj1 : List Byte := [0x48, 0x89, 0x6f, 0x08]
def sj2 : List Byte := [0x4c, 0x89, 0x67, 0x10]
def sj3 : List Byte := [0x4c, 0x89, 0x6f, 0x18]
def sj4 : List Byte := [0x4c, 0x89, 0x77, 0x20]
def sj5 : List Byte := [0x4c, 0x89, 0x7f, 0x28]
def sj6 : List Byte := [0x48, 0x8d, 0x54, 0x24, 0x08]
def sj7 : List Byte := [0x48, 0x89, 0x57, 0x30]
def sj8 : List Byte := [0x48, 0x8b, 0x14, 0x24]
def sj9 : List Byte := [0x48, 0x89, 0x57, 0x38]
def sj10 : List Byte := [0x31, 0xc0]
def sj11 : List Byte := Insn.encode .ret

theorem setjmpBytes_eq :
    setjmpBytes = sj0 ++ sj1 ++ sj2 ++ sj3 ++ sj4 ++ sj5 ++ sj6 ++ sj7 ++ sj8 ++ sj9 ++ sj10 ++
      sj11 := by decide

/-! ## Addresses -/

theorem ea_zero (b : Word) : (b + (0#32).signExtend 64).toNat = b.toNat := by
  simp

theorem ea_add (b : Word) {d : BitVec 32} {k : Nat} (hd : d.signExtend 64 = BitVec.ofNat 64 k)
    (hk : b.toNat + k < 2 ^ 64) : (b + d.signExtend 64).toNat = b.toNat + k := by
  rw [hd]; exact Silmaril.X86.Ext.toNat_add_ofNat hk

theorem setjmp_split {e sp ret bw c0 c1 c2 c3 c4 c5 : Word}
    (hb : bw.toNat + 64 < 2 ^ 64) :
    Triple Silmaril.X86.Open.isa
      (codePt e.toNat sj0 ∗ codePt (e + BitVec.ofNat 64 3).toNat sj1 ∗
      codePt (e + BitVec.ofNat 64 7).toNat sj2 ∗ codePt (e + BitVec.ofNat 64 11).toNat sj3 ∗
      codePt (e + BitVec.ofNat 64 15).toNat sj4 ∗ codePt (e + BitVec.ofNat 64 19).toNat sj5 ∗
      codePt (e + BitVec.ofNat 64 23).toNat sj6 ∗ codePt (e + BitVec.ofNat 64 28).toNat sj7 ∗
      codePt (e + BitVec.ofNat 64 32).toNat sj8 ∗ codePt (e + BitVec.ofNat 64 36).toNat sj9 ∗
      codePt (e + BitVec.ofNat 64 40).toNat sj10 ∗ codePt (e + BitVec.ofNat 64 42).toNat sj11 ∗
      ripPt e ∗ regPt .rsp sp ∗ wordPt sp.toNat ret ∗ regPt .rdi bw ∗ regPt .rbx c0 ∗
      regPt .rbp c1 ∗ regPt .r12 c2 ∗ regPt .r13 c3 ∗ regPt .r14 c4 ∗ regPt .r15 c5 ∗
      regAny .rdx ∗ regAny .rax ∗ flagsAny ∗ blockAny bw.toNat 8 ∗ blockAny (bw.toNat + 8) 8 ∗
      blockAny (bw.toNat + 16) 8 ∗ blockAny (bw.toNat + 24) 8 ∗ blockAny (bw.toNat + 32) 8 ∗
      blockAny (bw.toNat + 40) 8 ∗ blockAny (bw.toNat + 48) 8 ∗ blockAny (bw.toNat + 56) 8)
      (codePt e.toNat sj0 ∗ codePt (e + BitVec.ofNat 64 3).toNat sj1 ∗
      codePt (e + BitVec.ofNat 64 7).toNat sj2 ∗ codePt (e + BitVec.ofNat 64 11).toNat sj3 ∗
      codePt (e + BitVec.ofNat 64 15).toNat sj4 ∗ codePt (e + BitVec.ofNat 64 19).toNat sj5 ∗
      codePt (e + BitVec.ofNat 64 23).toNat sj6 ∗ codePt (e + BitVec.ofNat 64 28).toNat sj7 ∗
      codePt (e + BitVec.ofNat 64 32).toNat sj8 ∗ codePt (e + BitVec.ofNat 64 36).toNat sj9 ∗
      codePt (e + BitVec.ofNat 64 40).toNat sj10 ∗ codePt (e + BitVec.ofNat 64 42).toNat sj11 ∗
      ripPt ret ∗ regPt .rsp (sp + 8#64) ∗ wordPt sp.toNat ret ∗ regPt .rdi bw ∗ regPt .rbx c0 ∗
      regPt .rbp c1 ∗ regPt .r12 c2 ∗ regPt .r13 c3 ∗ regPt .r14 c4 ∗ regPt .r15 c5 ∗
      regPt .rdx ret ∗ regPt .rax 0 ∗ flagsAny ∗ wordPt bw.toNat c0 ∗ wordPt (bw.toNat + 8) c1 ∗
      wordPt (bw.toNat + 16) c2 ∗ wordPt (bw.toNat + 24) c3 ∗ wordPt (bw.toNat + 32) c4 ∗
      wordPt (bw.toNat + 40) c5 ∗ wordPt (bw.toNat + 48) (sp + (8#32).signExtend 64) ∗
      wordPt (bw.toNat + 56) ret) := by
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (storeQ_step (pc := e) (pc' := (e + BitVec.ofNat 64 3)) (bytes := sj0) (base := .rdi)
        (src := .rbx) (disp := 0#32) (a := bw.toNat) (ea_zero bw) (by decide) rfl)
      (codePt (e + BitVec.ofNat 64 3).toNat sj1 ∗ codePt (e + BitVec.ofNat 64 7).toNat sj2 ∗
       codePt (e + BitVec.ofNat 64 11).toNat sj3 ∗ codePt (e + BitVec.ofNat 64 15).toNat sj4 ∗
       codePt (e + BitVec.ofNat 64 19).toNat sj5 ∗ codePt (e + BitVec.ofNat 64 23).toNat sj6 ∗
       codePt (e + BitVec.ofNat 64 28).toNat sj7 ∗ codePt (e + BitVec.ofNat 64 32).toNat sj8 ∗
       codePt (e + BitVec.ofNat 64 36).toNat sj9 ∗ codePt (e + BitVec.ofNat 64 40).toNat sj10 ∗
       codePt (e + BitVec.ofNat 64 42).toNat sj11 ∗ regPt .rsp sp ∗ wordPt sp.toNat ret ∗ regPt
       .rbp c1 ∗ regPt .r12 c2 ∗ regPt .r13 c3 ∗ regPt .r14 c4 ∗ regPt .r15 c5 ∗ regAny .rdx ∗
       regAny .rax ∗ flagsAny ∗ blockAny (bw.toNat + 8) 8 ∗ blockAny (bw.toNat + 16) 8 ∗
       blockAny (bw.toNat + 24) 8 ∗ blockAny (bw.toNat + 32) 8 ∗ blockAny (bw.toNat + 40) 8 ∗
       blockAny (bw.toNat + 48) 8 ∗ blockAny (bw.toNat + 56) 8)) (entails_refl _)) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (storeQ_step (pc := (e + BitVec.ofNat 64 3)) (pc' := (e + BitVec.ofNat 64 7)) (bytes :=
        sj1) (base := .rdi) (src := .rbp) (disp := 8#32) (a := bw.toNat + 8) (ea_add bw (by
        decide) (by omega)) (by decide) (rip_advance e (by decide)))
      (codePt e.toNat sj0 ∗ regPt .rbx c0 ∗ wordPt bw.toNat c0 ∗ codePt (e + BitVec.ofNat 64
       7).toNat sj2 ∗ codePt (e + BitVec.ofNat 64 11).toNat sj3 ∗ codePt (e + BitVec.ofNat 64
       15).toNat sj4 ∗ codePt (e + BitVec.ofNat 64 19).toNat sj5 ∗ codePt (e + BitVec.ofNat 64
       23).toNat sj6 ∗ codePt (e + BitVec.ofNat 64 28).toNat sj7 ∗ codePt (e + BitVec.ofNat 64
       32).toNat sj8 ∗ codePt (e + BitVec.ofNat 64 36).toNat sj9 ∗ codePt (e + BitVec.ofNat 64
       40).toNat sj10 ∗ codePt (e + BitVec.ofNat 64 42).toNat sj11 ∗ regPt .rsp sp ∗ wordPt
       sp.toNat ret ∗ regPt .r12 c2 ∗ regPt .r13 c3 ∗ regPt .r14 c4 ∗ regPt .r15 c5 ∗ regAny
       .rdx ∗ regAny .rax ∗ flagsAny ∗ blockAny (bw.toNat + 16) 8 ∗ blockAny (bw.toNat + 24) 8 ∗
       blockAny (bw.toNat + 32) 8 ∗ blockAny (bw.toNat + 40) 8 ∗ blockAny (bw.toNat + 48) 8 ∗
       blockAny (bw.toNat + 56) 8)) (entails_refl _)) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (storeQ_step (pc := (e + BitVec.ofNat 64 7)) (pc' := (e + BitVec.ofNat 64 11)) (bytes :=
        sj2) (base := .rdi) (src := .r12) (disp := 16#32) (a := bw.toNat + 16) (ea_add bw (by
        decide) (by omega)) (by decide) (rip_advance e (by decide)))
      (codePt (e + BitVec.ofNat 64 3).toNat sj1 ∗ regPt .rbp c1 ∗ wordPt (bw.toNat + 8) c1 ∗
       codePt e.toNat sj0 ∗ regPt .rbx c0 ∗ wordPt bw.toNat c0 ∗ codePt (e + BitVec.ofNat 64
       11).toNat sj3 ∗ codePt (e + BitVec.ofNat 64 15).toNat sj4 ∗ codePt (e + BitVec.ofNat 64
       19).toNat sj5 ∗ codePt (e + BitVec.ofNat 64 23).toNat sj6 ∗ codePt (e + BitVec.ofNat 64
       28).toNat sj7 ∗ codePt (e + BitVec.ofNat 64 32).toNat sj8 ∗ codePt (e + BitVec.ofNat 64
       36).toNat sj9 ∗ codePt (e + BitVec.ofNat 64 40).toNat sj10 ∗ codePt (e + BitVec.ofNat 64
       42).toNat sj11 ∗ regPt .rsp sp ∗ wordPt sp.toNat ret ∗ regPt .r13 c3 ∗ regPt .r14 c4 ∗
       regPt .r15 c5 ∗ regAny .rdx ∗ regAny .rax ∗ flagsAny ∗ blockAny (bw.toNat + 24) 8 ∗
       blockAny (bw.toNat + 32) 8 ∗ blockAny (bw.toNat + 40) 8 ∗ blockAny (bw.toNat + 48) 8 ∗
       blockAny (bw.toNat + 56) 8)) (entails_refl _)) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (storeQ_step (pc := (e + BitVec.ofNat 64 11)) (pc' := (e + BitVec.ofNat 64 15)) (bytes :=
        sj3) (base := .rdi) (src := .r13) (disp := 24#32) (a := bw.toNat + 24) (ea_add bw (by
        decide) (by omega)) (by decide) (rip_advance e (by decide)))
      (codePt (e + BitVec.ofNat 64 7).toNat sj2 ∗ regPt .r12 c2 ∗ wordPt (bw.toNat + 16) c2 ∗
       codePt (e + BitVec.ofNat 64 3).toNat sj1 ∗ regPt .rbp c1 ∗ wordPt (bw.toNat + 8) c1 ∗
       codePt e.toNat sj0 ∗ regPt .rbx c0 ∗ wordPt bw.toNat c0 ∗ codePt (e + BitVec.ofNat 64
       15).toNat sj4 ∗ codePt (e + BitVec.ofNat 64 19).toNat sj5 ∗ codePt (e + BitVec.ofNat 64
       23).toNat sj6 ∗ codePt (e + BitVec.ofNat 64 28).toNat sj7 ∗ codePt (e + BitVec.ofNat 64
       32).toNat sj8 ∗ codePt (e + BitVec.ofNat 64 36).toNat sj9 ∗ codePt (e + BitVec.ofNat 64
       40).toNat sj10 ∗ codePt (e + BitVec.ofNat 64 42).toNat sj11 ∗ regPt .rsp sp ∗ wordPt
       sp.toNat ret ∗ regPt .r14 c4 ∗ regPt .r15 c5 ∗ regAny .rdx ∗ regAny .rax ∗ flagsAny ∗
       blockAny (bw.toNat + 32) 8 ∗ blockAny (bw.toNat + 40) 8 ∗ blockAny (bw.toNat + 48) 8 ∗
       blockAny (bw.toNat + 56) 8)) (entails_refl _)) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (storeQ_step (pc := (e + BitVec.ofNat 64 15)) (pc' := (e + BitVec.ofNat 64 19)) (bytes :=
        sj4) (base := .rdi) (src := .r14) (disp := 32#32) (a := bw.toNat + 32) (ea_add bw (by
        decide) (by omega)) (by decide) (rip_advance e (by decide)))
      (codePt (e + BitVec.ofNat 64 11).toNat sj3 ∗ regPt .r13 c3 ∗ wordPt (bw.toNat + 24) c3 ∗
       codePt (e + BitVec.ofNat 64 7).toNat sj2 ∗ regPt .r12 c2 ∗ wordPt (bw.toNat + 16) c2 ∗
       codePt (e + BitVec.ofNat 64 3).toNat sj1 ∗ regPt .rbp c1 ∗ wordPt (bw.toNat + 8) c1 ∗
       codePt e.toNat sj0 ∗ regPt .rbx c0 ∗ wordPt bw.toNat c0 ∗ codePt (e + BitVec.ofNat 64
       19).toNat sj5 ∗ codePt (e + BitVec.ofNat 64 23).toNat sj6 ∗ codePt (e + BitVec.ofNat 64
       28).toNat sj7 ∗ codePt (e + BitVec.ofNat 64 32).toNat sj8 ∗ codePt (e + BitVec.ofNat 64
       36).toNat sj9 ∗ codePt (e + BitVec.ofNat 64 40).toNat sj10 ∗ codePt (e + BitVec.ofNat 64
       42).toNat sj11 ∗ regPt .rsp sp ∗ wordPt sp.toNat ret ∗ regPt .r15 c5 ∗ regAny .rdx ∗
       regAny .rax ∗ flagsAny ∗ blockAny (bw.toNat + 40) 8 ∗ blockAny (bw.toNat + 48) 8 ∗
       blockAny (bw.toNat + 56) 8)) (entails_refl _)) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (storeQ_step (pc := (e + BitVec.ofNat 64 19)) (pc' := (e + BitVec.ofNat 64 23)) (bytes :=
        sj5) (base := .rdi) (src := .r15) (disp := 40#32) (a := bw.toNat + 40) (ea_add bw (by
        decide) (by omega)) (by decide) (rip_advance e (by decide)))
      (codePt (e + BitVec.ofNat 64 15).toNat sj4 ∗ regPt .r14 c4 ∗ wordPt (bw.toNat + 32) c4 ∗
       codePt (e + BitVec.ofNat 64 11).toNat sj3 ∗ regPt .r13 c3 ∗ wordPt (bw.toNat + 24) c3 ∗
       codePt (e + BitVec.ofNat 64 7).toNat sj2 ∗ regPt .r12 c2 ∗ wordPt (bw.toNat + 16) c2 ∗
       codePt (e + BitVec.ofNat 64 3).toNat sj1 ∗ regPt .rbp c1 ∗ wordPt (bw.toNat + 8) c1 ∗
       codePt e.toNat sj0 ∗ regPt .rbx c0 ∗ wordPt bw.toNat c0 ∗ codePt (e + BitVec.ofNat 64
       23).toNat sj6 ∗ codePt (e + BitVec.ofNat 64 28).toNat sj7 ∗ codePt (e + BitVec.ofNat 64
       32).toNat sj8 ∗ codePt (e + BitVec.ofNat 64 36).toNat sj9 ∗ codePt (e + BitVec.ofNat 64
       40).toNat sj10 ∗ codePt (e + BitVec.ofNat 64 42).toNat sj11 ∗ regPt .rsp sp ∗ wordPt
       sp.toNat ret ∗ regAny .rdx ∗ regAny .rax ∗ flagsAny ∗ blockAny (bw.toNat + 48) 8 ∗
       blockAny (bw.toNat + 56) 8)) (entails_refl _)) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (leaQ_step (pc := (e + BitVec.ofNat 64 23)) (pc' := (e + BitVec.ofNat 64 28)) (bytes :=
        sj6) (base := .rsp) (dst := .rdx) (disp := 8#32) (by decide) (by decide) (rip_advance e
        (by decide)))
      (codePt (e + BitVec.ofNat 64 19).toNat sj5 ∗ regPt .rdi bw ∗ regPt .r15 c5 ∗ wordPt
       (bw.toNat + 40) c5 ∗ codePt (e + BitVec.ofNat 64 15).toNat sj4 ∗ regPt .r14 c4 ∗ wordPt
       (bw.toNat + 32) c4 ∗ codePt (e + BitVec.ofNat 64 11).toNat sj3 ∗ regPt .r13 c3 ∗ wordPt
       (bw.toNat + 24) c3 ∗ codePt (e + BitVec.ofNat 64 7).toNat sj2 ∗ regPt .r12 c2 ∗ wordPt
       (bw.toNat + 16) c2 ∗ codePt (e + BitVec.ofNat 64 3).toNat sj1 ∗ regPt .rbp c1 ∗ wordPt
       (bw.toNat + 8) c1 ∗ codePt e.toNat sj0 ∗ regPt .rbx c0 ∗ wordPt bw.toNat c0 ∗ codePt (e +
       BitVec.ofNat 64 28).toNat sj7 ∗ codePt (e + BitVec.ofNat 64 32).toNat sj8 ∗ codePt (e +
       BitVec.ofNat 64 36).toNat sj9 ∗ codePt (e + BitVec.ofNat 64 40).toNat sj10 ∗ codePt (e +
       BitVec.ofNat 64 42).toNat sj11 ∗ wordPt sp.toNat ret ∗ regAny .rax ∗ flagsAny ∗ blockAny
       (bw.toNat + 48) 8 ∗ blockAny (bw.toNat + 56) 8)) (entails_refl _)) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (storeQ_step (pc := (e + BitVec.ofNat 64 28)) (pc' := (e + BitVec.ofNat 64 32)) (bytes :=
        sj7) (base := .rdi) (src := .rdx) (disp := 48#32) (a := bw.toNat + 48) (ea_add bw (by
        decide) (by omega)) (by decide) (rip_advance e (by decide)))
      (codePt (e + BitVec.ofNat 64 23).toNat sj6 ∗ regPt .rsp sp ∗ codePt (e + BitVec.ofNat 64
       19).toNat sj5 ∗ regPt .r15 c5 ∗ wordPt (bw.toNat + 40) c5 ∗ codePt (e + BitVec.ofNat 64
       15).toNat sj4 ∗ regPt .r14 c4 ∗ wordPt (bw.toNat + 32) c4 ∗ codePt (e + BitVec.ofNat 64
       11).toNat sj3 ∗ regPt .r13 c3 ∗ wordPt (bw.toNat + 24) c3 ∗ codePt (e + BitVec.ofNat 64
       7).toNat sj2 ∗ regPt .r12 c2 ∗ wordPt (bw.toNat + 16) c2 ∗ codePt (e + BitVec.ofNat 64
       3).toNat sj1 ∗ regPt .rbp c1 ∗ wordPt (bw.toNat + 8) c1 ∗ codePt e.toNat sj0 ∗ regPt .rbx
       c0 ∗ wordPt bw.toNat c0 ∗ codePt (e + BitVec.ofNat 64 32).toNat sj8 ∗ codePt (e +
       BitVec.ofNat 64 36).toNat sj9 ∗ codePt (e + BitVec.ofNat 64 40).toNat sj10 ∗ codePt (e +
       BitVec.ofNat 64 42).toNat sj11 ∗ wordPt sp.toNat ret ∗ regAny .rax ∗ flagsAny ∗ blockAny
       (bw.toNat + 56) 8)) (entails_refl _)) ?_
  refine Triple.pre (entails_trans (entails_of_eq (by ac_rfl))
    (sep_mono_left (codePt (e + BitVec.ofNat 64 28).toNat sj7 ∗ ripPt (e + BitVec.ofNat 64 32) ∗ regPt .rdi bw
      ∗ wordPt (bw.toNat + 48) (sp + (8#32).signExtend 64) ∗ codePt (e + BitVec.ofNat 64
      23).toNat sj6 ∗ regPt .rsp sp ∗ codePt (e + BitVec.ofNat 64 19).toNat sj5 ∗ regPt .r15 c5
      ∗ wordPt (bw.toNat + 40) c5 ∗ codePt (e + BitVec.ofNat 64 15).toNat sj4 ∗ regPt .r14 c4 ∗
      wordPt (bw.toNat + 32) c4 ∗ codePt (e + BitVec.ofNat 64 11).toNat sj3 ∗ regPt .r13 c3 ∗
      wordPt (bw.toNat + 24) c3 ∗ codePt (e + BitVec.ofNat 64 7).toNat sj2 ∗ regPt .r12 c2 ∗
      wordPt (bw.toNat + 16) c2 ∗ codePt (e + BitVec.ofNat 64 3).toNat sj1 ∗ regPt .rbp c1 ∗
      wordPt (bw.toNat + 8) c1 ∗ codePt e.toNat sj0 ∗ regPt .rbx c0 ∗ wordPt bw.toNat c0 ∗
      codePt (e + BitVec.ofNat 64 32).toNat sj8 ∗ codePt (e + BitVec.ofNat 64 36).toNat sj9 ∗
      codePt (e + BitVec.ofNat 64 40).toNat sj10 ∗ codePt (e + BitVec.ofNat 64 42).toNat sj11 ∗
      wordPt sp.toNat ret ∗ regAny .rax ∗ flagsAny ∗ blockAny (bw.toNat + 56) 8)
      (show regPt .rdx (sp + (8#32).signExtend 64) ⊢ₛ regAny .rdx from fun _ hp => ⟨_, hp⟩))) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (loadQ_step (pc := (e + BitVec.ofNat 64 32)) (pc' := (e + BitVec.ofNat 64 36)) (bytes :=
        sj8) (base := .rsp) (dst := .rdx) (disp := 0#32) (a := sp.toNat) (ea_zero sp) (by
        decide) (by decide) (rip_advance e (by decide)))
      (codePt (e + BitVec.ofNat 64 28).toNat sj7 ∗ regPt .rdi bw ∗ wordPt (bw.toNat + 48) (sp +
       (8#32).signExtend 64) ∗ codePt (e + BitVec.ofNat 64 23).toNat sj6 ∗ codePt (e +
       BitVec.ofNat 64 19).toNat sj5 ∗ regPt .r15 c5 ∗ wordPt (bw.toNat + 40) c5 ∗ codePt (e +
       BitVec.ofNat 64 15).toNat sj4 ∗ regPt .r14 c4 ∗ wordPt (bw.toNat + 32) c4 ∗ codePt (e +
       BitVec.ofNat 64 11).toNat sj3 ∗ regPt .r13 c3 ∗ wordPt (bw.toNat + 24) c3 ∗ codePt (e +
       BitVec.ofNat 64 7).toNat sj2 ∗ regPt .r12 c2 ∗ wordPt (bw.toNat + 16) c2 ∗ codePt (e +
       BitVec.ofNat 64 3).toNat sj1 ∗ regPt .rbp c1 ∗ wordPt (bw.toNat + 8) c1 ∗ codePt e.toNat
       sj0 ∗ regPt .rbx c0 ∗ wordPt bw.toNat c0 ∗ codePt (e + BitVec.ofNat 64 36).toNat sj9 ∗
       codePt (e + BitVec.ofNat 64 40).toNat sj10 ∗ codePt (e + BitVec.ofNat 64 42).toNat sj11 ∗
       regAny .rax ∗ flagsAny ∗ blockAny (bw.toNat + 56) 8)) (entails_refl _)) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (storeQ_step (pc := (e + BitVec.ofNat 64 36)) (pc' := (e + BitVec.ofNat 64 40)) (bytes :=
        sj9) (base := .rdi) (src := .rdx) (disp := 56#32) (a := bw.toNat + 56) (ea_add bw (by
        decide) (by omega)) (by decide) (rip_advance e (by decide)))
      (codePt (e + BitVec.ofNat 64 32).toNat sj8 ∗ regPt .rsp sp ∗ wordPt sp.toNat ret ∗ codePt
       (e + BitVec.ofNat 64 28).toNat sj7 ∗ wordPt (bw.toNat + 48) (sp + (8#32).signExtend 64) ∗
       codePt (e + BitVec.ofNat 64 23).toNat sj6 ∗ codePt (e + BitVec.ofNat 64 19).toNat sj5 ∗
       regPt .r15 c5 ∗ wordPt (bw.toNat + 40) c5 ∗ codePt (e + BitVec.ofNat 64 15).toNat sj4 ∗
       regPt .r14 c4 ∗ wordPt (bw.toNat + 32) c4 ∗ codePt (e + BitVec.ofNat 64 11).toNat sj3 ∗
       regPt .r13 c3 ∗ wordPt (bw.toNat + 24) c3 ∗ codePt (e + BitVec.ofNat 64 7).toNat sj2 ∗
       regPt .r12 c2 ∗ wordPt (bw.toNat + 16) c2 ∗ codePt (e + BitVec.ofNat 64 3).toNat sj1 ∗
       regPt .rbp c1 ∗ wordPt (bw.toNat + 8) c1 ∗ codePt e.toNat sj0 ∗ regPt .rbx c0 ∗ wordPt
       bw.toNat c0 ∗ codePt (e + BitVec.ofNat 64 40).toNat sj10 ∗ codePt (e + BitVec.ofNat 64
       42).toNat sj11 ∗ regAny .rax ∗ flagsAny)) (entails_refl _)) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (xorSelf_any (pc := (e + BitVec.ofNat 64 40)) (pc' := (e + BitVec.ofNat 64 42)) (bytes :=
        sj10) (r := .rax) (by decide) (rip_advance e (by decide)))
      (codePt (e + BitVec.ofNat 64 36).toNat sj9 ∗ regPt .rdi bw ∗ regPt .rdx ret ∗ wordPt
       (bw.toNat + 56) ret ∗ codePt (e + BitVec.ofNat 64 32).toNat sj8 ∗ regPt .rsp sp ∗ wordPt
       sp.toNat ret ∗ codePt (e + BitVec.ofNat 64 28).toNat sj7 ∗ wordPt (bw.toNat + 48) (sp +
       (8#32).signExtend 64) ∗ codePt (e + BitVec.ofNat 64 23).toNat sj6 ∗ codePt (e +
       BitVec.ofNat 64 19).toNat sj5 ∗ regPt .r15 c5 ∗ wordPt (bw.toNat + 40) c5 ∗ codePt (e +
       BitVec.ofNat 64 15).toNat sj4 ∗ regPt .r14 c4 ∗ wordPt (bw.toNat + 32) c4 ∗ codePt (e +
       BitVec.ofNat 64 11).toNat sj3 ∗ regPt .r13 c3 ∗ wordPt (bw.toNat + 24) c3 ∗ codePt (e +
       BitVec.ofNat 64 7).toNat sj2 ∗ regPt .r12 c2 ∗ wordPt (bw.toNat + 16) c2 ∗ codePt (e +
       BitVec.ofNat 64 3).toNat sj1 ∗ regPt .rbp c1 ∗ wordPt (bw.toNat + 8) c1 ∗ codePt e.toNat
       sj0 ∗ regPt .rbx c0 ∗ wordPt bw.toNat c0 ∗ codePt (e + BitVec.ofNat 64 42).toNat sj11)) (entails_refl _)) ?_
  refine Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame (Silmaril.Proofs.X86.Sep.ret_step (e + BitVec.ofNat 64 42) sp ret)
      (codePt (e + BitVec.ofNat 64 40).toNat sj10 ∗ regPt .rax 0 ∗ flagsAny ∗ codePt (e +
       BitVec.ofNat 64 36).toNat sj9 ∗ regPt .rdi bw ∗ regPt .rdx ret ∗ wordPt (bw.toNat + 56)
       ret ∗ codePt (e + BitVec.ofNat 64 32).toNat sj8 ∗ codePt (e + BitVec.ofNat 64 28).toNat
       sj7 ∗ wordPt (bw.toNat + 48) (sp + (8#32).signExtend 64) ∗ codePt (e + BitVec.ofNat 64
       23).toNat sj6 ∗ codePt (e + BitVec.ofNat 64 19).toNat sj5 ∗ regPt .r15 c5 ∗ wordPt
       (bw.toNat + 40) c5 ∗ codePt (e + BitVec.ofNat 64 15).toNat sj4 ∗ regPt .r14 c4 ∗ wordPt
       (bw.toNat + 32) c4 ∗ codePt (e + BitVec.ofNat 64 11).toNat sj3 ∗ regPt .r13 c3 ∗ wordPt
       (bw.toNat + 24) c3 ∗ codePt (e + BitVec.ofNat 64 7).toNat sj2 ∗ regPt .r12 c2 ∗ wordPt
       (bw.toNat + 16) c2 ∗ codePt (e + BitVec.ofNat 64 3).toNat sj1 ∗ regPt .rbp c1 ∗ wordPt
       (bw.toNat + 8) c1 ∗ codePt e.toNat sj0 ∗ regPt .rbx c0 ∗ wordPt bw.toNat c0)) (entails_refl _)) ?_
  exact Triple.post (Triple.refl _) (entails_of_eq (by ac_rfl))

/-! ## Splitting the assertions -/

theorem setjmp_code {e : Word} (he : e.toNat + 43 < 2 ^ 64) :
    codePt e.toNat setjmpBytes =
      (codePt e.toNat sj0 ∗ codePt (e + BitVec.ofNat 64 3).toNat sj1 ∗
      codePt (e + BitVec.ofNat 64 7).toNat sj2 ∗ codePt (e + BitVec.ofNat 64 11).toNat sj3 ∗
      codePt (e + BitVec.ofNat 64 15).toNat sj4 ∗ codePt (e + BitVec.ofNat 64 19).toNat sj5 ∗
      codePt (e + BitVec.ofNat 64 23).toNat sj6 ∗ codePt (e + BitVec.ofNat 64 28).toNat sj7 ∗
      codePt (e + BitVec.ofNat 64 32).toNat sj8 ∗ codePt (e + BitVec.ofNat 64 36).toNat sj9 ∗
      codePt (e + BitVec.ofNat 64 40).toNat sj10 ∗ codePt (e + BitVec.ofNat 64 42).toNat sj11) := by
  have t := fun k (h : k ≤ 43) => Silmaril.X86.Ext.toNat_add_ofNat (x := e) (k := k) (by omega)
  rw [t 3 (by omega), t 7 (by omega), t 11 (by omega), t 15 (by omega), t 19 (by omega),
    t 23 (by omega), t 28 (by omega), t 32 (by omega), t 36 (by omega), t 40 (by omega),
    t 42 (by omega), setjmpBytes_eq]
  simp only [codePt, bytesAt_append, List.append_assoc, sj0, sj1, sj2, sj3, sj4, sj5, sj6, sj7,
    sj8, sj9, sj10, List.length_cons, List.length_nil, Nat.add_assoc, Nat.reduceAdd]

/-- The 64 bytes of a `jmp_buf` as eight blocks. -/
theorem jbAny_split (b : Nat) :
    jbAny b = (blockAny b 8 ∗ blockAny (b + 8) 8 ∗ blockAny (b + 16) 8 ∗ blockAny (b + 24) 8 ∗
      blockAny (b + 32) 8 ∗ blockAny (b + 40) 8 ∗ blockAny (b + 48) 8 ∗ blockAny (b + 56) 8) := by
  rw [jbAny]
  conv_lhs => rw [show (64 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + (8 + 8)))))) from rfl]
  rw [blockAny_add, blockAny_add, blockAny_add, blockAny_add, blockAny_add, blockAny_add,
    blockAny_add]

theorem bytesPt_encodeWords_cons (a : Nat) (w : Word) (ws : List Word) :
    bytesPt a (Silmaril.Machine.LittleEndian.encodeWords (w :: ws)) =
      (wordPt a w ∗ bytesPt (a + 8) (Silmaril.Machine.LittleEndian.encodeWords ws)) := by
  rw [show w :: ws = [w] ++ ws from rfl, Silmaril.Machine.LittleEndian.encodeWords_append,
    bytesPt, bytesAt_append, Silmaril.X86.length_encodeWords_singleton]
  rfl

/-- **A `jmp_buf` holding `k` is eight words.** -/
theorem jbPt_words (b : Nat) (c0 c1 c2 c3 c4 c5 sp ret : Word) :
    jbPt b ⟨[c0, c1, c2, c3, c4, c5], sp, ret⟩ =
      (wordPt b c0 ∗ wordPt (b + 8) c1 ∗ wordPt (b + 16) c2 ∗ wordPt (b + 24) c3 ∗
        wordPt (b + 32) c4 ∗ wordPt (b + 40) c5 ∗ wordPt (b + 48) sp ∗ wordPt (b + 56) ret) := by
  simp only [jbPt, enc, words, List.cons_append, List.nil_append, bytesPt_encodeWords_cons,
    Nat.add_assoc, Nat.reduceAdd]
  rw [show bytesPt (b + 64) (Silmaril.Machine.LittleEndian.encodeWords []) = emp from rfl,
    sep_emp]

theorem regsWith_calleeSaved (c0 c1 c2 c3 c4 c5 : Word) :
    regsWith calleeSavedRegs [c0, c1, c2, c3, c4, c5] =
      (regPt .rbx c0 ∗ regPt .rbp c1 ∗ regPt .r12 c2 ∗ regPt .r13 c3 ∗ regPt .r14 c4 ∗
        regPt .r15 c5) := by
  simp only [regsWith, calleeSavedRegs, sep_emp]

theorem regsAny_calleeSaved :
    regsAny calleeSavedRegs =
      (regAny .rbx ∗ regAny .rbp ∗ regAny .r12 ∗ regAny .r13 ∗ regAny .r14 ∗ regAny .r15) := by
  simp only [regsAny, regsWith, calleeSavedRegs, sep_emp]

/-! ## `setjmp` -/

/-- **`setjmp` as a total triple on the open machine.** Called with
`rdi = bw` (an owned `jmp_buf`) and return address `ret` at `sp`, it saves the callee-saved
registers, `sp + 8` and `ret` into the `jmp_buf` and returns `0`. Its postcondition mentions
its own `sp` and `ret`, which `FnSpec` cannot express, so it is a raw triple. -/
theorem setjmp_triple {e sp ret bw c0 c1 c2 c3 c4 c5 : Word}
    (he : e.toNat + 43 < 2 ^ 64) (hb : bw.toNat + 64 < 2 ^ 64) :
    Triple Silmaril.X86.Open.isa
      (codePt e.toNat setjmpBytes ∗ ripPt e ∗ regPt .rsp sp ∗ wordPt sp.toNat ret ∗
        regPt .rdi bw ∗ regsWith calleeSavedRegs [c0, c1, c2, c3, c4, c5] ∗ regAny .rdx ∗
        regAny .rax ∗ flagsAny ∗ jbAny bw.toNat)
      (codePt e.toNat setjmpBytes ∗ ripPt ret ∗ regPt .rsp (sp + 8#64) ∗ wordPt sp.toNat ret ∗
        regPt .rdi bw ∗ regsWith calleeSavedRegs [c0, c1, c2, c3, c4, c5] ∗ regPt .rdx ret ∗
        regPt .rax 0 ∗ flagsAny ∗ jbPt bw.toNat (saved [c0, c1, c2, c3, c4, c5] sp ret)) := by
  have h := setjmp_split (e := e) (sp := sp) (ret := ret) (c0 := c0) (c1 := c1) (c2 := c2)
    (c3 := c3) (c4 := c4) (c5 := c5) hb
  rw [show (8#32 : BitVec 32).signExtend 64 = 8#64 by decide] at h
  rw [setjmp_code he, jbAny_split, saved, jbPt_words, regsWith_calleeSaved]
  exact Triple.conseq (entails_of_eq (by ac_rfl)) h (entails_of_eq (by ac_rfl))

end Silmaril.Proofs.X86.Sep.JmpBuf
