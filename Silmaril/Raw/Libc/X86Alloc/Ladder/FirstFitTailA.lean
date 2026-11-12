module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitMalloc
public import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitPost

/-!
# Proofs: rung 05 (first-fit) `malloc` — the "too small" exits of the walk (offset 104)

The block `b` under inspection is too small: `rsi` moves to its next slot; if its next pointer is
null the list is exhausted and `malloc` returns `NULL` (`tailA_end`), else the walk continues
with the next block, a strictly shorter tail (`tailA_next`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitMalloc

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Insn
open Silmaril.Libc.X86Alloc.Ladder.FirstFit
open Silmaril.Raw.Libc.X86Alloc.Frame
open Silmaril.Raw.Libc.X86Alloc.Steps
open Silmaril.Raw.Libc.X86Alloc.Whole
open Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitPost

theorem hlen : mcode.length = 128 := by decide +kernel
theorem fit (o k : Nat) (h : o + k ≤ 128 := by decide) : o + k ≤ mcode.length := hlen ▸ h

/-- Weaken the memory part of a postcondition's canonical assertion. -/
theorem St_mono {pc : Word} {f : Reg → Word} {fl : Flags} {M M' : SProp} (h : M ⊢ₛ M') :
    St pc f fl M ⊢ₛ St pc f fl M' :=
  sep_mono_right _ (sep_mono_right _ (sep_mono_right _ h))

/-- **The postconditions of `malloc`'s exits**, generic in the spec `S` (at argument `x`) that
the walk is proved against: the request too big, the list empty, the list exhausted, a block served
whole, a block split. Each is the memory at that exit entailing `S.post x v`. -/
structure Exits (S : Silmaril.X86.Sep.FnSpec) (x : S.Arg) (n : Word) (fl0 : List Block) : Prop where
  big : 4096 < n.toNat → ∀ h, (wordPt flAddr.toNat h ∗ hdrSeg fl0 h ∗ strue) ⊢ₛ S.post x 0
  empty : fl0 = [] → (wordPt flAddr.toNat 0 ∗ strue) ⊢ₛ S.post x 0
  exh : n.toNat ≤ 4096 → ∀ (passed : List Block) (b : Block), passed ++ [b] = fl0 →
    (∀ c ∈ passed, c.size < roundUp 16 n.toNat) → b.size < roundUp 16 n.toNat → b.WF →
    (plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
      wordPt (b.addr + 8#64).toNat 0 ∗ blockAny (b.addr.toNat + 16) b.size ∗ strue) ⊢ₛ S.post x 0
  whole : n.toNat ≤ 4096 → ∀ (passed rest : List Block) (b : Block) (nxt : Word),
    passed ++ b :: rest = fl0 →
    (∀ c ∈ passed, c.size < roundUp 16 n.toNat) → b.WF → roundUp 16 n.toNat ≤ b.size → ¬ roundUp 16 n.toNat + 32 ≤ b.size →
    ∀ v, v = b.addr + 16#64 →
    (plistO flAddr passed ∗ wordPt (lastSlot flAddr passed).toNat nxt ∗
      wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ wordPt (b.addr + 8#64).toNat nxt ∗
      blockAny (b.addr.toNat + 16) b.size ∗ hdrSeg rest nxt ∗ strue) ⊢ₛ S.post x v
  split : n.toNat ≤ 4096 → ∀ (passed rest : List Block) (b : Block) (nxt : Word),
    passed ++ b :: rest = fl0 →
    (∀ c ∈ passed, c.size < roundUp 16 n.toNat) → b.WF → roundUp 16 n.toNat + 32 ≤ b.size →
    ∀ v, v = b.addr + 16#64 →
    (plistO flAddr passed ∗ wordPt (lastSlot flAddr passed).toNat (rem b (roundUp 16 n.toNat)).addr ∗
      wordPt b.addr.toNat (BitVec.ofNat 64 (roundUp 16 n.toNat)) ∗ wordPt (b.addr + 8#64).toNat nxt ∗
      blockAny (b.addr.toNat + 16) (roundUp 16 n.toNat) ∗
      wordPt (rem b (roundUp 16 n.toNat)).addr.toNat (BitVec.ofNat 64 (rem b (roundUp 16 n.toNat)).size) ∗
      wordPt ((rem b (roundUp 16 n.toNat)).addr + 8#64).toNat nxt ∗
      blockAny ((rem b (roundUp 16 n.toNat)).addr.toNat + 16) (rem b (roundUp 16 n.toNat)).size ∗
      hdrSeg rest nxt ∗ strue) ⊢ₛ S.post x v

/-- **The list exhausted.** -/
theorem tailA_end (S : Silmaril.X86.Sep.FnSpec) (hS : S.stack = 0) (x : S.Arg) (fl0 passed : List Block)
    (b : Block) (n sp ret : Word) (hE : Exits S x n fl0) (f : Reg → Word)
    (fl : Flags) (hrcx : f .rcx = 0) (hrsp : f .rsp = sp) (hn4 : n.toNat ≤ 4096)
    (hfl : passed ++ [b] = fl0)
    (hsmall : ∀ c ∈ passed, c.size < roundUp 16 n.toNat) (hb : b.size < roundUp 16 n.toNat)
    (hWF : b.WF) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 mcode) (St 0x401398 f fl (wordPt sp.toNat ret ∗
      plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
      wordPt (b.addr + 8#64).toNat 0 ∗ blockAny (b.addr.toNat + 16) b.size ∗ strue))
      (S.SysVPost x sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine SPEC.trans (c_lea E (b := 0x401330) (code := mcode) (o := 104) (k := 4) (pc := 0x401398)
    (by decide) (fit 104 4) (dst := .rsi) (by decide) d104
    (a := f .rax + 8#64) (fun s hregs next => by
      rw [Silmaril.X86.Sep.Insn.memAt_addr, hregs .rax (by decide)]; rfl)) ?_
  refine SPEC.trans (c_test E (b := 0x401330) (code := mcode) (o := 108) (k := 3)
    (pc := 0x401398 + 4#64) (by decide) (fit 108 3) (r := .rcx) (by decide) d108) ?_
  refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := mcode) (o := 111) (k := 2)
    (pc := 0x401398 + 4#64 + 3#64) (pc' := 0x401390) (by decide) (fit 111 2) (c := .e)
    (rel := 0xef) ?_ d111 (by decide)) ?_
  · rw [eval_e_test]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx]; rfl
  refine SPEC.trans (c_xor32 E (b := 0x401330) (code := mcode) (o := 96) (k := 2) (pc := 0x401390)
    (by decide) (fit 96 2) (r := .rax) (by decide) d96) ?_
  refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := mcode) (o := 98) (k := 1)
    (pc := 0x401390 + 2#64) (by decide) (fit 98 1)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]) r98) ?_
  refine St_post hS (by simp only [Function.update_self]) ?_
  have hv : (Function.update (Function.update (Function.update f .rsi (f .rax + 8#64)) .rax 0)
      .rsp (sp + 8#64)) .rax = 0 := by
    simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
  rw [hv]
  exact hE.exh hn4 passed b hfl hsmall hb hWF

/-- **The walk continues** with the next block. -/
theorem tailA_next (need : Nat) (fl0 passed rest : List Block) (b c : Block) (sp ret : Word)
    (f : Reg → Word) (fl : Flags) (hrax : f .rax = b.addr) (hrcx : f .rcx = c.addr)
    (hrsp : f .rsp = sp) (hrdi : f .rdi = BitVec.ofNat 64 need)
    (hsmall : ∀ d ∈ passed, d.size < need) (hb : b.size < need)
    (hfl : passed ++ b :: c :: rest = fl0) (hWF : b.WF) (hc0 : c.addr ≠ 0) (Q : SProp) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 mcode) (St 0x401398 f fl (wordPt sp.toNat ret ∗
      plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
      wordPt (b.addr + 8#64).toNat c.addr ∗ blockAny (b.addr.toNat + 16) b.size ∗
      hdrSeg (c :: rest) c.addr ∗ strue))
      (sor Q (sexists fun y => ⌜μ y < μ ⟨passed, b, c :: rest⟩⌝ ∗ Inv need sp ret fl0 y)) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine SPEC.trans (c_lea E (b := 0x401330) (code := mcode) (o := 104) (k := 4) (pc := 0x401398)
    (by decide) (fit 104 4) (dst := .rsi) (by decide) d104
    (a := f .rax + 8#64) (fun s hregs next => by
      rw [Silmaril.X86.Sep.Insn.memAt_addr, hregs .rax (by decide)]; rfl)) ?_
  refine SPEC.trans (c_test E (b := 0x401330) (code := mcode) (o := 108) (k := 3)
    (pc := 0x401398 + 4#64) (by decide) (fit 108 3) (r := .rcx) (by decide) d108) ?_
  refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := mcode) (o := 111) (k := 2)
    (pc := 0x401398 + 4#64 + 3#64) (pc' := 0x4013a1) (by decide) (fit 111 2) (c := .e)
    (rel := 0xef) ?_ d111 (by decide)) ?_
  · rw [eval_e_test]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx]
    simpa using hc0
  refine SPEC.trans (c_movQ E (b := 0x401330) (code := mcode) (o := 113) (k := 3) (pc := 0x4013a1)
    (by decide) (fit 113 3) (r := .rax) (q := .rcx) (by decide) (by decide) (by decide) d113) ?_
  refine SPEC.conseq (entails_refl _) (c_jmp8 E (b := 0x401330) (code := mcode) (o := 116) (k := 2)
    (pc := 0x4013a1 + 3#64) (by decide) (fit 116 2) (pc' := 0x401352) d116 (by decide)) ?_
  refine entails_trans ?_ (sor_intro_right _ _)
  refine sexists_intro ⟨passed ++ [b], c, rest⟩ (spure_sep_intro (by simp [μ]) ?_)
  refine sexists_intro _ (sexists_intro _ (spure_sep_intro ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ (St_mono ?_)))
  · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx]
  · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax, lastSlot_snoc]
  · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdi]
  · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]
  · intro d hd
    rcases List.mem_append.1 hd with h | h
    · exact hsmall d h
    · rw [List.mem_singleton] at h; rw [h]; exact hb
  · simpa using hfl
  · rw [← plist_snoc]
    refine entails_trans ?_ (entails_of_eq (show (wordPt sp.toNat ret ∗ (plist flAddr passed b.addr ∗
      ⌜b.WF⌝ ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ blockAny (b.addr.toNat + 16) b.size ∗
      wordPt (b.addr + 8#64).toNat c.addr) ∗ hdrSeg (c :: rest) c.addr ∗ strue) = _ from rfl))
    refine entails_trans ?_ (sep_mono_right _ (sep_mono_left _ (sep_mono_right _
      (spure_sep_intro hWF (entails_refl _)))))
    exact entails_of_eq (by ac_rfl)

end Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitMalloc
