module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryDecF

/-!
# Proofs: rung 08 (boundary tags) — `malloc`: the request, the walk's invariant, failures

`need n` is the block size `malloc(n)` looks for (`max 32 (round16 n + 16)`). `LInv` is the state
at the walk's head `0x401371` for the split `x = (l1, y, l2)` of the free list: `rax` at the
block `y` under inspection; the measure is `l2.length`. `malloc_entry` runs from the entry to the
walk (or to a failure), given the loop's result.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Insn
open Silmaril.Libc.X86Alloc.Ladder.Boundary
open Silmaril.Raw.Libc.X86Alloc.Frame
open Silmaril.Raw.Libc.X86Alloc.Steps
open Silmaril.Raw.Libc.X86Alloc.Whole
open Silmaril.Raw.Libc.X86Alloc.MemStep

/-! ## Words -/

theorem toNat_wd {x : Nat} (h : x < 2 ^ 64) : (wd x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem wd_add (x y : Nat) : wd x + wd y = wd (x + y) := (BitVec.ofNat_add x y).symm

theorem wd_ne_zero {x : Nat} (h0 : 0 < x) (h : x < 2 ^ 64) : wd x ≠ 0 := by
  intro e; have := congrArg BitVec.toNat e; rw [toNat_wd h] at this; simp at this; omega

/-- Adding a negative displacement `-d`. -/
theorem wd_sub {x d : Nat} (hd : d ≤ x) (hd1 : d ≤ 2 ^ 64) :
    wd x + wd (2 ^ 64 - d) = wd (x - d) := by
  rw [wd_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have : x + (2 ^ 64 - d) = (x - d) + 2 ^ 64 := by omega
  rw [this, Nat.add_mod_right]

theorem eval_b_wd {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    Silmaril.X86.Ext.Cond.b.eval (Silmaril.X86.Ext.AluOp.flagsN .cmp (wd x) (wd y)) =
      some (decide (x < y)) := by
  rw [eval_b_cmp, toNat_wd hx, toNat_wd hy]

theorem eval_e_wd {x : Nat} (hx : x < 2 ^ 64) :
    Silmaril.X86.Ext.Cond.e.eval (Silmaril.X86.Ext.logicFlagsN (wd x &&& wd x)) =
      some (decide (x = 0)) := by
  rw [eval_e_test]
  by_cases h : x = 0
  · subst h; rfl
  · simp only [h, decide_false]
    have := wd_ne_zero (Nat.pos_of_ne_zero h) hx
    simpa using this

theorem eval_ne_test (x : Word) :
    Silmaril.X86.Ext.Cond.ne.eval (Silmaril.X86.Ext.logicFlagsN (x &&& x)) = some (x != 0) := by
  simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.isZeroN,
    Silmaril.X86.Ext.kNot, bne]

theorem eval_ne_wd {x : Nat} (hx : x < 2 ^ 64) :
    Silmaril.X86.Ext.Cond.ne.eval (Silmaril.X86.Ext.logicFlagsN (wd x &&& wd x)) =
      some (decide (x ≠ 0)) := by
  rw [eval_ne_test]
  by_cases h : x = 0
  · subst h; rfl
  · simp only [h, ne_eq, not_false_eq_true, decide_true]
    have := wd_ne_zero (Nat.pos_of_ne_zero h) hx
    simpa using this

/-- An address `v + d` from a register holding `v`. -/
theorem addr_reg {f : Reg → Word} {r : Reg} (hr : r ∈ frameRegs) {v : Word} (hf : f r = v)
    {d : BitVec 32} {a : Nat} (ha : (v + d.signExtend 64).toNat = a) :
    ∀ s : Silmaril.X86.State, (∀ q ∈ frameRegs, s.read q = f q) → ∀ next,
      ((Silmaril.X86.Sep.Insn.memAt r d).addr s next).toNat = a := by
  intro s hregs next
  rw [Silmaril.X86.Sep.Insn.memAt_addr, hregs r hr, hf, ha]

/-- An address `v + u + d` from registers holding `v` and `u`. -/
theorem addr_idx {f : Reg → Word} {r q : Reg} (hr : r ∈ frameRegs) (hq : q ∈ frameRegs)
    (hne : q ≠ .rsp) {v u : Word} (hf : f r = v) (hg : f q = u) {d : BitVec 32} {a : Nat}
    (ha : (v + u + d.signExtend 64).toNat = a) :
    ∀ s : Silmaril.X86.State, (∀ q ∈ frameRegs, s.read q = f q) → ∀ next,
      ((idx r q hne d).addr s next).toNat = a := by
  intro s hregs next
  rw [idx_addr, hregs r hr, hregs q hq, hf, hg, ha]

/-! ## The request -/

/-- The block size `malloc(n)` looks for. -/
def need (n : Nat) : Nat := max 32 ((n + 15) / 16 * 16 + 16)

theorem need_facts {n : Nat} (h : n ≤ 4096) :
    need n % 16 = 0 ∧ 32 ≤ need n ∧ n + 16 ≤ need n ∧ need n ≤ 4112 := by
  unfold need; omega

/-- The postcondition of `malloc`. -/
abbrev MQ (nw sp ret : Word) : SProp := (mallocSpec iface).SysVPost nw sp ret

theorem mm_of {fs : List (Nat × Nat)} (hw : WF fs) : mmOf fs ⊢ₛ mm :=
  sexists_intro fs (spure_sep_intro hw (entails_refl _))

theorem post_fail {fs : List (Nat × Nat)} (hw : WF fs) (nw : Word) :
    mmOf fs ⊢ₛ (mallocSpec iface).post nw 0 := by
  show mmOf fs ⊢ₛ (mm ∗ sor ⌜(0 : Word) = 0⌝ (iface.Fresh 0 nw.toNat))
  refine entails_trans (entails_of_eq (sep_emp _).symm) (sep_mono (mm_of hw) ?_)
  refine entails_trans ?_ (sor_intro_left _ _)
  rw [eq_self, spure_true_emp]; exact entails_refl _

/-- `ret` with `rax = 0`: `malloc` fails, the state unchanged. -/
theorem ret_fail {o : Nat} {pc : Word} (hpc : pc.toNat = 0x401330 + o) (hfit : o + 1 ≤ code.length)
    (hr : (code.drop o).take 1 = Silmaril.X86.Insn.encode .ret) (f : Reg → Word) (fl : Flags)
    {nw sp ret : Word} (hrsp : f .rsp = sp) (hrax : f .rax = 0) {fs : List (Nat × Nat)}
    (hw : WF fs) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St pc f fl (wordPt sp.toNat ret ∗ mmOf fs))
      (MQ nw sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine SPEC.conseq (entails_refl _) (c_retAt E hpc hfit hrsp hr) ?_
  refine St_post rfl (by simp only [Function.update_self]) ?_
  rw [Function.update_of_ne (by decide), hrax]
  exact post_fail hw nw

/-! ## The walk -/

/-- A split of the free list at the block under inspection. -/
structure Ix where
  l1 : List (Nat × Nat)
  y : Nat × Nat
  l2 : List (Nat × Nat)

/-- **The state at the walk's head `0x401371`.** -/
def LInv (n : Nat) (sp ret : Word) (fs : List (Nat × Nat)) (x : Ix) : SProp :=
  sexists fun (f : Reg → Word) => sexists fun (fl : Flags) =>
    ⌜f .rax = wd x.y.1 ∧ f .rdx = wd (need n) ∧ f .rsp = sp ∧ n ≤ 4096 ∧ WF fs ∧
      x.l1 ++ x.y :: x.l2 = fs⌝ ∗
    St 0x401371 f fl (wordPt sp.toNat ret ∗ mmOf fs)

/-- The walk's measure. -/
def μ (x : Ix) : Nat := x.l2.length

/-- From the head of the free list to the walk (`0x401355`). -/
theorem walk_entry (nw sp ret : Word) (f : Reg → Word) (fl : Flags) (hrsp : f .rsp = sp)
    (hrdx : f .rdx = wd (need nw.toNat)) (hn : nw.toNat ≤ 4096) (fs : List (Nat × Nat))
    (hw : WF fs)
    (hloop : ∀ x, SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (LInv nw.toNat sp ret fs x)
      (MQ nw sp ret)) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x401355 f fl (wordPt sp.toNat ret ∗ mmOf fs))
      (MQ nw sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hg := hw.1
  refine SPEC.mem (M' := wordPt flistA (wd (hdOr fs 0)) ∗ (wordPt sp.toNat ret ∗
    blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT fs) ∗ tblPt firstA (firstT fs) ∗ dll fs 0 0))
    (by simp only [mmOf]; ac_rfl) ?_
  refine SPEC.trans (c_loadRip E (b := 0x401330) (code := code) (o := 37) (k := 7)
    (pc := 0x401355) (pc' := 0x40135c) (by decide) (fit 37 7) (dst := .rax) (by decide)
    (disp := 0x1d44) d37 (by decide) (by decide)) ?_
  refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 44) (k := 3) (pc := 0x40135c)
    (by decide) (fit 44 3) (r := .rax) (by decide) d44) ?_
  have hh : hdOr fs 0 < 2 ^ 64 := by
    cases fs with
    | nil => simp [hdOr]
    | cons y l =>
      have := good_lt hg ⟨y, List.mem_cons_self, rfl⟩; have := heap_eq; simp only [hdOr]; omega
  have hmm : (wordPt flistA (wd (hdOr fs 0)) ∗ (wordPt sp.toNat ret ∗
      blockAny (flistA + 8) 24 ∗ tblPt lastA (lastT fs) ∗ tblPt firstA (firstT fs) ∗ dll fs 0 0)) =
      (wordPt sp.toNat ret ∗ mmOf fs) := by simp only [mmOf]; ac_rfl
  cases fs with
  | nil =>
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 47) (k := 2)
      (pc := 0x40135c + BitVec.ofNat 64 3) (pc' := 0x401361) (by decide) (fit 47 2) (c := .ne)
      (rel := 0x10) ?_ d47 (by decide)) ?_
    · simp only [Function.update_self]; rw [eval_ne_wd hh]; rfl
    rw [hmm]
    exact ret_fail (o := 49) (by decide) (fit 49 1) r49 _ _
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp])
      (by simp only [Function.update_self]; rfl) hw
  | cons y l2 =>
    have hy := good_lt hg ⟨y, List.mem_cons_self, rfl⟩
    have hH := heap_eq
    have hyv : hdOr (y :: l2) 0 = y.1 := rfl
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 47) (k := 2)
      (pc := 0x40135c + BitVec.ofNat 64 3) (pc' := 0x401371) (by decide) (fit 47 2) (c := .ne)
      (rel := 0x10) ?_ d47 (by decide)) ?_
    · simp only [Function.update_self]; rw [eval_ne_wd hh, hyv]; simp; omega
    rw [hmm]
    refine SPEC.conseq ?_ (hloop ⟨[], y, l2⟩) (entails_refl _)
    refine sexists_intro _ (sexists_intro _ (spure_sep_intro ⟨?_, ?_, ?_, hn, hw, rfl⟩
      (entails_refl _)))
    · simp only [Function.update_self]; rfl
    · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx]
    · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]

theorem toNat_rdi (nw : Word) (hn : nw.toNat ≤ 4096) :
    Silmaril.X86.Ext.AluOp.resultN .and
      (Silmaril.X86.Ext.AluOp.resultN .add nw (BitVec.signExtend 64 (0xf : BitVec 8)))
      (BitVec.signExtend 64 (0xf0 : BitVec 8)) = wd ((nw.toNat + 15) / 16 * 16) := by
  show (nw + BitVec.signExtend 64 (0xf : BitVec 8)) &&& BitVec.signExtend 64 (0xf0 : BitVec 8) = _
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.signExtend 64 (0xf0 : BitVec 8)).toNat = 2 ^ 64 - 16 by
    decide +kernel, nat_and_mask16 _ (BitVec.isLt _), BitVec.toNat_add,
    show (BitVec.signExtend 64 (0xf : BitVec 8)).toNat = 15 by decide +kernel,
    Nat.mod_eq_of_lt (by omega), toNat_wd (by omega)]

/-- **From the entry of `malloc` to the walk or a failure.** -/
theorem malloc_entry (nw sp ret : Word) (f : Reg → Word) (fl : Flags) (hrsp : f .rsp = sp)
    (hrdi : f .rdi = nw) (fs : List (Nat × Nat)) (hw : WF fs)
    (hloop : nw.toNat ≤ 4096 → ∀ x, SPEC Silmaril.X86.Open.isa (codePt 0x401330 code)
      (LInv nw.toNat sp ret fs x) (MQ nw sp ret)) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x401330 f fl (wordPt sp.toNat ret ∗ mmOf fs))
      (MQ nw sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine SPEC.trans (c_cmpI E (b := 0x401330) (code := code) (o := 0) (k := 7) (pc := 0x401330)
    rfl (fit 0 7) (r := .rdi) (imm := 0x1000) (by decide) d0) ?_
  have e4096 : (BitVec.signExtend 64 (0x1000 : BitVec 32)).toNat = 4096 := by decide +kernel
  by_cases hbig : 4096 < nw.toNat
  · refine SPEC.trans (c_jcc32_taken E (b := 0x401330) (code := code) (o := 7) (k := 6)
      (pc := 0x401330 + BitVec.ofNat 64 7) (pc' := 0x401418) (by decide) (fit 7 6) (c := .a)
      (rel := 0xdb) (by rw [eval_a_cmp, hrdi, e4096]; simp [hbig]) d7 (by decide)) ?_
    refine SPEC.trans (c_xor32 E (b := 0x401330) (code := code) (o := 232) (k := 2)
      (pc := 0x401418) (by decide) (fit 232 2) (r := .rax) (by decide) d232) ?_
    exact ret_fail (o := 234) (by decide) (fit 234 1) r234 _ _
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp])
      (by simp only [Function.update_self]) hw
  have hn : nw.toNat ≤ 4096 := by omega
  refine SPEC.trans (c_jcc32_not E (b := 0x401330) (code := code) (o := 7) (k := 6)
    (pc := 0x401330 + BitVec.ofNat 64 7) (by decide) (fit 7 6) (c := .a)
    (rel := 0xdb) (by rw [eval_a_cmp, hrdi, e4096]; simp [hbig]) d7) ?_
  refine SPEC.trans (c_aluI8 E (b := 0x401330) (code := code) (o := 13) (k := 4)
    (pc := 0x40133d) (by decide) (fit 13 4) (op := .add) (by decide) (r := .rdi) (by decide)
    (imm := 0xf) d13) ?_
  refine SPEC.trans (c_movI32 E (b := 0x401330) (code := code) (o := 17) (k := 5)
    (pc := 0x40133d + BitVec.ofNat 64 4) (pc' := 0x401346) (by decide) (fit 17 5) (r := .rax)
    (by decide) d17 (by decide)) ?_
  refine SPEC.trans (c_aluI8 E (b := 0x401330) (code := code) (o := 22) (k := 4)
    (pc := 0x401346) (by decide) (fit 22 4) (op := .and) (by decide) (r := .rdi) (by decide)
    (imm := 0xf0) d22) ?_
  have hr16 := toNat_rdi nw hn
  set r16 := (nw.toNat + 15) / 16 * 16 with hr16def
  refine SPEC.trans (c_lea E (b := 0x401330) (code := code) (o := 26) (k := 4)
    (pc := 0x401346 + BitVec.ofNat 64 4) (by decide) (fit 26 4) (dst := .rdx) (by decide) d26
    (a := wd (r16 + 16)) (fun st hregs next => by
      rw [Silmaril.X86.Sep.Insn.memAt_addr, hregs .rdi (by decide)]
      simp only [Function.update_self, Function.update_apply, reduceCtorEq, ↓reduceIte, hrdi]
      rw [hr16, show BitVec.signExtend 64 (0x10 : BitVec 32) = wd 16 by decide +kernel, wd_add]))
    ?_
  refine SPEC.trans (c_cmp E (b := 0x401330) (code := code) (o := 30) (k := 3)
    (pc := 0x401346 + BitVec.ofNat 64 4 + BitVec.ofNat 64 4) (by decide) (fit 30 3) (r := .rdx)
    (q := .rax) (by decide) (by decide) (by decide) d30) ?_
  have e32 : ((0x20 : BitVec 32).setWidth 64) = wd 32 := by decide +kernel
  refine SPEC.trans (c_cmov E (b := 0x401330) (code := code) (o := 33) (k := 4)
    (pc := 0x401346 + BitVec.ofNat 64 4 + BitVec.ofNat 64 4 + BitVec.ofNat 64 3) (by decide)
    (fit 33 4) (c := .b) (dst := .rdx) (src := .rax) (by decide) (by decide)
    (t := decide (r16 + 16 < 32)) (by
      simp only [Function.update_self, Function.update_apply, reduceCtorEq, ↓reduceIte]
      rw [e32, eval_b_wd (by omega) (by omega)]) d33) ?_
  refine walk_entry nw sp ret _ _
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]) ?_ hn fs hw (hloop hn)
  simp only [Function.update_self, Function.update_apply, reduceCtorEq, ↓reduceIte]
  rw [e32]
  unfold need
  by_cases h : r16 + 16 < 32
  · simp only [h, decide_true, ite_true]; congr 1; omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]; congr 1; omega

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary
