module

public import Silmaril.Proofs.X86.Bir9.Instr

/-!
# Lemmas for the symbolic instruction table

`symStep σ i len` (in `Silmaril.X86.Bir9.Defs`) gives the Bir9 statements and the new
symbolic state for one `LInstr`. This module proves the facts about its helpers
(`Src8.sym`, `countSym`, `hiByte`, `setHiByte`) that `symStep_sound` (`Sound.lean`) uses.
-/

@[expose] public section

namespace Silmaril.X86.Bir9

open Silmaril.X86 (Reg Word State Flags AluOp Byte pushWord popWord wordOfBytes?)
open Silmaril.X86.Ext
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)

variable {σ : SState} {env : Env} {s : State} {mem : Memory}

theorem Rel.regs_wf (h : Rel σ env s mem) {n : Nat} (hn : σ.n ≤ n) (r : Reg) : (σ.regs r).wf n :=
  E.wf_mono hn (h.wf.1 r)

theorem Rel.flags_wf (h : Rel σ env s mem) {n : Nat} (hn : σ.n ≤ n) : σ.flags.wf n :=
  F.wf_mono hn h.wf.2.1

theorem Rel.regs_den (h : Rel σ env s mem) {env1 : Env} (hx : env.Ext env1) (r : Reg) :
    (σ.regs r).den env1 = s.read r := by
  rw [E.den_ext hx (wf_lift h (h.wf.1 r)), h.regs]

theorem Rel.flags_den (h : Rel σ env s mem) {env1 : Env} (hx : env.Ext env1) :
    σ.flags.den env1 = s.flags := by
  rw [F.den_ext hx (h.len ▸ h.wf.2.1), h.flags]

theorem one_setWidth (sz : Sz) : (1#64).setWidth sz.bits = 1#sz.bits := by cases sz <;> rfl

theorem Src8.sym_den (h : Rel σ env s mem) {env1 : Env} (hx : env.Ext env1) (src : Src8) :
    ((src.sym σ).den env1).setWidth 8 = src.read s := by
  cases src with
  | reg r => simp [Src8.sym, Src8.read, h.regs_den hx]
  | imm b => simp [Src8.sym, Src8.read, E.den]

theorem Src8.sym_wf (h : Rel σ env s mem) {n : Nat} (hn : σ.n ≤ n) (src : Src8) :
    (src.sym σ).wf n := by
  cases src <;> simp [Src8.sym, E.wf, h.regs_wf hn]

theorem countSym_den (h : Rel σ env s mem) {env1 : Env} (hx : env.Ext env1) (c : Count) :
    ((countSym σ c).den env1).setWidth 8 = c.raw s := by
  cases c with
  | cl => simp [countSym, Count.raw, h.regs_den hx]
  | one => rfl
  | imm b => simp [countSym, Count.raw, E.den]

theorem countSym_wf (h : Rel σ env s mem) {n : Nat} (hn : σ.n ≤ n) (c : Count) :
    (countSym σ c).wf n := by
  cases c <;> simp [countSym, E.wf, h.regs_wf hn]

/-! ## The table -/

theorem hiByte_den (env : Env) (a : E) : ((hiByte a).den env).setWidth 8 = ((a.den env) >>> 8).setWidth 8 := by
  simp [hiByte, E.den, ShiftOp.result]

theorem setHiByte_den (env : Env) (old new : E) :
    (setHiByte old new).den env =
      (old.den env &&& ~~~(0xFF00#64)) ||| (((new.den env).setWidth 8).setWidth 64 <<< 8) := by
  simp [setHiByte, E.den, AluOp.resultN]

/-! ## Bir9 shapes -/

end Silmaril.X86.Bir9
