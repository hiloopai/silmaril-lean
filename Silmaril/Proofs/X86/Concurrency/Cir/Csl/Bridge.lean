module

public import Silmaril.X86.Concurrency.Cir.Csl.Defs
public import Silmaril.X86.Concurrency.Cir.Litmus.Thms

/-!
# CSL over CIR: the axiomatic-to-buffered bridge needs ownership

The CIR-native machines run a `local` block as **one** step:
it reads all its input cells at once. The axiomatic models see a block as its
memory actions, one load per input cell (`Lab.acts`), so another thread's writes may land
between them. `MP+block`: thread 0 stores `1` to `x` then to `y`; thread 1 runs a block that
reads `x` then `y` into `rax`, `rbx`. Axiomatic SC (hence TSO and XL) allows `rax = 0`,
`rbx = 1` (checked by the axiomatic enumerator, `check`), but no run of the XL store-buffer machine
reaches it (`not_reach`: the invariant `Inv` says `y = 1` in memory only after `x = 1`, as
both stores are write-back and flush in order). So the bridge from axiomatic behaviours to
the buffered machine holds at best for programs whose blocks do not race, which is what
`Task.cirXlOpAx`'s CSL hypothesis ensures.

Stated in `Silmaril.X86.Concurrency.Cir.Csl.Thms` (`cirXlOpAx_needs_csl`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.Bridge

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Lit (x y shell)
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.MemoryModel.Axiomatic (Exec)

/-- A block reading `x` then `y` into `rax`, `rbx`. -/
def getXY : Block where
  name := "getxy"
  ins := [(x, 4), (y, 4)]
  outs := []
  rin := []
  rout := [.rax, .rbx]
  spec := fun i o => o = i
  dec := fun _ _ => inferInstance

/-- Thread 0's first store. -/
abbrev sx : Stmt := .store .rlx 4 .wb (.lit x) (.lit 1)
/-- Thread 0's second store. -/
abbrev sy : Stmt := .store .rlx 4 .wb (.lit y) (.lit 1)

/-- Thread 1's final registers. -/
def R (vx vy : Nat) : Regs := Regs.zero.setMany [.rax, .rbx] [vx, vy]

/-- Thread 0's progress, buffer and memory. -/
def T0 (C : OCfg) : Prop :=
  ((C.ts 0).1 = .seq sx sy ∧ C.buf 0 = [] ∧ C.mem x = some 0 ∧ C.mem y = some 0) ∨
  (((C.ts 0).1 = .seq .skip sy ∨ (C.ts 0).1 = sy) ∧ C.mem y = some 0 ∧
    ((C.buf 0 = [.st x 1 false] ∧ C.mem x = some 0) ∨ (C.buf 0 = [] ∧ C.mem x = some 1))) ∨
  ((C.ts 0).1 = .skip ∧
    ((C.buf 0 = [.st x 1 false, .st y 1 false] ∧ C.mem x = some 0 ∧ C.mem y = some 0) ∨
     (C.buf 0 = [.st y 1 false] ∧ C.mem x = some 1 ∧ C.mem y = some 0) ∨
     (C.buf 0 = [] ∧ C.mem x = some 1 ∧ C.mem y = some 1)))

/-- **The invariant**: memory never shows `y = 1` before `x = 1`, and thread 1's block
never read `x = 0`, `y = 1`. -/
def Inv (C : OCfg) : Prop :=
  (C.ts 0).2 = Regs.zero ∧ C.buf 1 = [] ∧ T0 C ∧
  (C.ts 1 = (.local getXY, Regs.zero) ∨
    ∃ vx vy, C.ts 1 = (.skip, R vx vy) ∧ vx ≤ 1 ∧ vy ≤ 1 ∧ ¬ (vx = 0 ∧ vy = 1))

theorem t0_xy (C : OCfg) (h : T0 C) :
    (C.mem x = some 0 ∨ C.mem x = some 1) ∧ (C.mem y = some 0 ∨ C.mem y = some 1) ∧
    ¬ (C.mem x = some 0 ∧ C.mem y = some 1) := by
  rcases h with ⟨-, -, hx, hy⟩ | ⟨-, hy, ⟨-, hx⟩ | ⟨-, hx⟩⟩ |
    ⟨-, ⟨-, hx, hy⟩ | ⟨-, hx, hy⟩ | ⟨-, hx, hy⟩⟩ <;> simp [hx, hy]

theorem lx (rs : Regs) : ((Expr.lit x).eval rs).toNat = x := rfl
theorem ly (rs : Regs) : ((Expr.lit y).eval rs).toNat = y := rfl
theorem l1 (rs : Regs) : ((Expr.lit 1).eval rs).toNat % 2 ^ (8 * 4) = 1 := rfl

/-- Thread 1's steps. -/
theorem t1_tau {s' rs'} (h : TStep (.local getXY) Regs.zero none s' rs') : False := by
  cases h

theorem t0_none {C : OCfg} (h0 : T0 C) {s' rs'} (h : TStep (C.ts 0).1 Regs.zero none s' rs') :
    (C.ts 0).1 = .seq .skip sy ∧ s' = sy ∧ rs' = Regs.zero := by
  rcases h0 with ⟨e, -⟩ | ⟨e | e, -⟩ | ⟨e, -⟩ <;> rw [e] at h ⊢
  · cases h with | seq h => cases h
  · cases h with
    | seq h => cases h
    | seqSkip => exact ⟨rfl, rfl, rfl⟩
  · cases h
  · cases h


theorem upd0 {α} (f : Nat → α) (v : α) : upd f 0 v 0 = v := rfl
theorem upd0' {α} (f : Nat → α) (v : α) : upd f 0 v 1 = f 1 := rfl
theorem upd1 {α} (f : Nat → α) (v : α) : upd f 1 v 1 = v := rfl
theorem upd1' {α} (f : Nat → α) (v : α) : upd f 1 v 0 = f 0 := rfl

theorem hxy : (x = y) = False := by decide
theorem hyx : (y = x) = False := by decide

theorem step_inv {C C' : OCfg} (hI : Inv C) (h : OStep .xl 2 C C') : Inv C' := by
  obtain ⟨hr0, hb1, h0, h1⟩ := hI
  cases h with
  | @tau t s' rs' ht hs =>
    obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
    · rw [hr0] at hs
      obtain ⟨e, rfl, rfl⟩ := t0_none h0 hs
      refine ⟨rfl, hb1, ?_, h1⟩
      rcases h0 with ⟨e', -⟩ | ⟨-, hy, hb⟩ | ⟨e', -⟩
      · rw [e] at e'; cases e'
      · exact Or.inr (Or.inl ⟨Or.inr rfl, hy, hb⟩)
      · rw [e] at e'; cases e'
    · rcases h1 with e | ⟨vx, vy, e, -, -, -⟩ <;> rw [e] at hs
      · exact (t1_tau hs).elim
      · cases hs
  | @buffered t l s' rs' ht hs hm hd hc hok =>
    obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
    · rw [hr0] at hs
      rcases h0 with ⟨e, hb0, hx, hy⟩ | ⟨e | e, hy, hb⟩ | ⟨e, -⟩ <;> rw [e] at hs
      · cases hs with
        | seq h =>
          cases h
          refine ⟨rfl, hb1, Or.inr (Or.inl ⟨Or.inl rfl, hy, Or.inl ⟨?_, hx⟩⟩), h1⟩
          show C.buf 0 ++ _ = _
          rw [hb0, lx, l1]; rfl
      · cases hs with | seq h => cases h
      · cases hs
        refine ⟨rfl, hb1, Or.inr (Or.inr ⟨rfl, ?_⟩), h1⟩
        show (C.buf 0 ++ _ = _ ∧ _) ∨ _
        rw [ly, l1]
        rcases hb with ⟨hb, hx⟩ | ⟨hb, hx⟩ <;> rw [hb]
        · exact Or.inl ⟨rfl, hx, hy⟩
        · exact Or.inr (Or.inl ⟨rfl, hx, hy⟩)
      · cases hs
    · rcases h1 with e | ⟨vx, vy, e, -, -, -⟩ <;> rw [e] at hs
      · cases hs with
        | @blk _ _ ivs rvs ovs hspec hi hr ho =>
          match ivs, ovs, hi, ho with
          | [a, b], [], _, _ =>
            simp only [getXY, List.append_nil] at hspec
            subst hspec
            have ha := hok (x, a) (by simp [Lab.reads, getXY, cellVals])
            have hb := hok (y, b) (by simp [Lab.reads, getXY, cellVals])
            simp only [hb1, view, newest, Option.none_or] at ha hb
            obtain ⟨hx, hy, hn⟩ := t0_xy C h0
            refine ⟨hr0, ?_, h0, Or.inr ⟨a, b, rfl, ?_, ?_, ?_⟩⟩
            · show C.buf 1 ++ _ = []
              rw [hb1]; rfl
            · rcases hx with h | h <;> rw [h] at ha <;> cases ha <;> decide
            · rcases hy with h | h <;> rw [h] at hb <;> cases hb <;> decide
            · rintro ⟨rfl, rfl⟩; exact hn ⟨ha, hb⟩
      · cases hs
  | @drained t l s' rs' ht hs hm hd he hc hok =>
    exfalso
    obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
    · rw [hr0] at hs
      rcases h0 with ⟨e, -⟩ | ⟨e | e, -⟩ | ⟨e, -⟩ <;> rw [e] at hs
      · cases hs with | seq h => cases h; cases hd
      · cases hs with | seq h => cases h
      · cases hs; cases hd
      · cases hs
    · rcases h1 with e | ⟨vx, vy, e, -, -, -⟩ <;> rw [e] at hs
      · cases hs; cases hd
      · cases hs
  | @flush t pre e post ht hb hp hmod =>
    obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
    · have hm : ∀ z, e.apply C.mem z = (e.val z).or (C.mem z) := by
        intro z; cases e with
        | st a v w => by_cases h : z = a <;> simp [Ent.apply, Ent.val, h, eq_comm]
        | bar => rfl
      refine ⟨hr0, hb1, ?_, h1⟩
      simp only [T0]
      show (_ ∧ upd C.buf 0 (pre ++ post) 0 = [] ∧ _) ∨ _
      rw [upd0, hm x, hm y]
      rcases h0 with ⟨e0, hb0, hx, hy⟩ | ⟨e0, hy, ⟨hb0, hx⟩ | ⟨hb0, hx⟩⟩ |
        ⟨e0, ⟨hb0, hx, hy⟩ | ⟨hb0, hx, hy⟩ | ⟨hb0, hx, hy⟩⟩ <;> rw [hb0] at hb
      · simp at hb
      · rcases pre with _ | ⟨p, pre⟩
        · simp only [List.nil_append, List.cons.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          exact Or.inr (Or.inl ⟨e0, by simp [Ent.val, hxy, hy], Or.inr ⟨rfl, by simp [Ent.val]⟩⟩)
        · simp at hb
      · simp at hb
      · rcases pre with _ | ⟨p, _ | ⟨p2, pre⟩⟩
        · simp only [List.nil_append, List.cons.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          exact Or.inr (Or.inr ⟨e0, Or.inr (Or.inl ⟨rfl, by simp [Ent.val],
            by simp [Ent.val, hxy, hy]⟩)⟩)
        · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hb
          obtain ⟨rfl, rfl, rfl⟩ := hb
          simp [Ent.passes] at hp
        · simp at hb
      · rcases pre with _ | ⟨p, pre⟩
        · simp only [List.nil_append, List.cons.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          exact Or.inr (Or.inr ⟨e0, Or.inr (Or.inr ⟨rfl, by simp [Ent.val, hyx, hx],
            by simp [Ent.val]⟩)⟩)
        · simp at hb
      · simp at hb
    · rw [hb1] at hb; simp at hb


theorem reach_inv {C C' : OCfg} (h : OReach .xl 2 C C') (hI : Inv C) : Inv C' := by
  induction h with
  | refl => exact hI
  | step s _ ih => exact ih (step_inv hI s)

/-- `MP+block` as a CIR litmus test. -/
def mpBlk : CTest :=
  ⟨shell "MP+block" "a local block reads x then y while another thread writes x then y"
      (.and (.atom (.reg 1 .rax 32 0)) (.atom (.reg 1 .rbx 32 1))) .allowed,
    [⟨.seq sx sy, false⟩, ⟨.local getXY, false⟩]⟩

/-- The program. -/
abbrev P : Prog := mpBlk.prog

theorem check : mpBlk.check = true := by decide +kernel

theorem uniform : P.uniformB = true := by decide +kernel

theorem threads_ok :
    (P.threads.all fun th => th.body.threadFree && th.body.posSizes && !th.spawned) = true := by
  decide +kernel

theorem init_inv : Inv (progInit P).toO := by
  refine ⟨rfl, rfl, Or.inl ⟨rfl, rfl, ?_, ?_⟩, Or.inl rfl⟩ <;> decide +kernel

/-- Axiomatic SC allows the torn block read. -/
theorem behav_sc : ∃ f, Behav P Exec.Sc f ∧
    (f.regs 1 .rax).toNat % 2 ^ 32 = 0 ∧ (f.regs 1 .rbx).toNat % 2 ^ 32 = 1 := by
  obtain ⟨f, hf, hw⟩ := (verdicts_of_check check).allowed .sc rfl
  simp only [mpBlk, shell, Silmaril.X86.MemoryModel.Litmus.Test.witness,
    Silmaril.X86.MemoryModel.Litmus.Cond.eval, Silmaril.X86.MemoryModel.Litmus.Atom.eval,
    Bool.and_eq_true, beq_iff_eq] at hw
  exact ⟨f, hf, hw⟩

/-- The XL store-buffer machine never finishes with the torn read. -/
theorem not_reach (f : Silmaril.X86.MemoryModel.Litmus.Final)
    (h0 : (f.regs 1 .rax).toNat % 2 ^ 32 = 0) (h1 : (f.regs 1 .rbx).toNat % 2 ^ 32 = 1) :
    ¬ ∃ C : OCfg, OReach .xl P.threads.length (progInit P).toO C ∧
      (∀ t < P.threads.length, (C.ts t).1 = .skip ∧ f.regs t = (C.ts t).2) := by
  rintro ⟨C, hr, hfin⟩
  obtain ⟨-, -, -, e | ⟨vx, vy, e, hvx, hvy, hn⟩⟩ := reach_inv hr init_inv
  · have := (hfin 1 (by decide)).1; rw [e] at this; cases this
  · have hf := (hfin 1 (by decide)).2
    rw [e] at hf
    rw [hf] at h0 h1
    have ex : R vx vy .rax = BitVec.ofNat 64 vx := rfl
    have ey : R vx vy .rbx = BitVec.ofNat 64 vy := rfl
    simp only [ex, ey] at h0 h1
    simp only [BitVec.toNat_ofNat] at h0 h1
    omega

/-- `LD+nt`: `r0 = x; y :=nt 1 ∥ y := 2; mfence; x := 1` with `r0 = 1` and final
`y = 2`. XL's `ppoXl` drops the order from the load to the later weak store, so axiomatic XL
allows it while TSO and SC forbid it (`ldNt_check`). The XL store-buffer machine forbids it
(an argument, not proved here: thread 0's store enters its buffer after its load, which saw
`x = 1`, so after thread 1's `y := 2` had been flushed by its `mfence`). Not uniform (the store
is non-temporal), so `Task.cirXlOpAx` does not claim it. -/
def ldNt : CTest :=
  ⟨{ shell "LD+nt" "a load then a non-temporal store, against store; mfence; store"
      (.and (.atom (.reg 0 .rax 32 1)) (.atom (.mem y 4 2))) .forbidden with xl := .allowed },
    [Lit.th [Lit.ld .rax x, .store .rlx 4 .nt (.lit y) (.lit 1)],
      Lit.th [Lit.st y 2, Lit.mf, Lit.st x 1]]⟩

theorem ldNt_check : ldNt.check = true := by decide +kernel

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.Bridge
