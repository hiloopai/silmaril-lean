module

public import Silmaril.Apps.Sha256sum.Binary.Startup.SetNameRuns
public meta import Lean

/-! # `set_program_name` (`sha256sum-min`): the `/` case after the scan

From the scan exit `0x403444` with `rcx` at a `/` of `argv[0]` (`scanDone`, `rcx ≠ 0`), the
`"/.libs/"` check (guarded by `i + 1 > 6`, a loop at `0x403476`, cut `134`) and the `"lt-"`
check (a loop at `0x4036ea`, cut `762`) end at the join `0x403486` with `common`, on every path:
a mismatch exits early, a full match strips the prefix (`r8`). The bytes read lie in `argv[0]`
before its NUL, or in `.rodata`.

* `vc_slash_entry` (VERIFIED): from the scan exit to the join or the `"/.libs/"` loop;
* the loop VCs: `vc_libs_kN` (`SetNameLibsKN.lean`), `vc_libs` (`SetNameLibs.lean`), `vc_lt`;
  the composition to `SlashCase` is downstream.
-/

@[expose] public section

open Lean Elab Tactic Meta in
/-- `sv_split1'` that also closes a branch whose condition is a false literal comparison
(`(47#8 == 0#8) = true`) and drops a true one. -/
elab "sl_split1" : tactic => withMainContext do
  let g := (← instantiateMVars (← getMainTarget)).consumeMData
  if g.isForall then
    let .forallE _ ty body _ := g | throwError "sl_split1"
    let ty := ty.consumeMData
    if !body.hasLooseBVars && (ty.eq?.map (fun (t, _, _) => t.isConstOf ``Bool)).getD false then
      let h := mkIdent (← mkFreshUserName `hb)
      evalTactic (← `(tactic| intro $h:ident))
      try evalTactic (← `(tactic| (simp only [BitVec.reduceBEq, Bool.false_eq_true, Bool.true_eq_false, false_implies] at $h:ident; done)))
      catch _ => pure ()
      if (← getGoals).isEmpty then return
      try evalTactic (← `(tactic| (simp only [Bool.not_eq_false', Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne] at $h:ident; simp only [$h:ident])))
      catch _ => pure ()
      return
  evalTactic (← `(tactic| sv_split1))

macro "sl_go " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (sv [$ls,*]; ((repeat' sl_split1) <;> sv_close); iterate 60 (all_goals (try (sv [$ls,*]; ((repeat' sl_split1) <;> sv_close))))))

namespace Silmaril.Apps.Sha256sum.Binary.Startup.SetName

open Silmaril.X86 (Word Byte State Reg)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Loaded loadN storeN Mem)
open Silmaril.X86.SegVC
open Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Apps.Sha256sum.Binary.Startup
open Silmaril.Machine.Execution (Reaches)

set_option maxRecDepth 200000
set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

/-- A byte of `.rodata` through `W1`. -/
theorem ro_byte {c : Ctx} (hc : LaunchFacts c) {m : Memory} (hww : Memory.WritesWithin c.m0 m (W1 c.sp0))
    (off : Nat) (v : Word) (hoff : off < 0x2010)
    (hv : BitVec.ofNat 64 (Silmaril.X86.Ext.leValue ((Image.seg2.contents.drop off).take 1)) = v) :
    loadN m (BitVec.ofNat 64 (0x406000 + off)) 1 = some v := by
  rw [rodata_load hc.mapped hww off hoff (by have := hc.spLo; simp only [W1]; omega), hv]

/-- A byte of `argv[0]` (at index `j`, by its address) through `W1`. -/
theorem arg_byte {c : Ctx} (hc : LaunchFacts c) {m : Memory} (hww : Memory.WritesWithin c.m0 m (W1 c.sp0))
    {j : Nat} (hj : j < c.arg.length) (q : Word) (hq : q.toNat = c.argv0.toNat + j) :
    loadN m q 1 = some (c.arg[j]!.setWidth 64) := by
  have lo := hc.spLo
  have hab : c.sp0.toNat + 32 ≤ c.argv0.toNat := by have := hc.above c.argv0 (by simp); omega
  rw [getElem!_pos c.arg j hj]
  exact cstring_load hww hc.argStr (fun k hk => by simp only [W1]; omega) q j hj hq

/-- The signed guard `i + 1 > 6` (`jle` not taken) gives `6 ≤ i`. -/
theorem six_le_of_sle {i : Nat} (h : (BitVec.ofNat 64 (i + 1)).sle 6#64 = false) : 6 ≤ i := by
  by_contra hi
  have : (BitVec.ofNat 64 (i + 1)).sle 6#64 = true := by
    simp only [BitVec.sle, decide_eq_true_eq, BitVec.toInt, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; simp; omega
  rw [h] at this; cases this

/-- At the `"/.libs/"` loop head (`0x403476`): the `/` at `i ≥ 6`, `k < 7` bytes compared. -/
def libsInv (c : Ctx) (s : XState) : Prop :=
  ∃ n i k, n < c.arg.length ∧ c.arg[n]! = 0 ∧ i < n ∧ 6 ≤ i ∧ k < 7 ∧
    s.core.read .rcx = c.argv0 + BitVec.ofNat 64 i ∧ (s.core.read .rax).toNat = k ∧ common c s

/-- At the `"lt-"` loop head (`0x4036ea`): `k < 3` bytes after the `/` compared, all before the NUL. -/
def ltInv (c : Ctx) (s : XState) : Prop :=
  ∃ n i k, n < c.arg.length ∧ c.arg[n]! = 0 ∧ k < 3 ∧ i + 1 + k ≤ n ∧
    s.core.read .rcx = c.argv0 + BitVec.ofNat 64 i ∧ (s.core.read .rax).toNat = k ∧ common c s

def libsMeasure (s : XState) : Nat := 10 - (s.core.read .rax).toNat
def ltMeasure (s : XState) : Nat := 3 - (s.core.read .rax).toNat

/-- The cuts of the `/` case. -/
def slashCuts (c : Ctx) : List (Nat × Cut (σ := XState)) :=
  [(134, ⟨libsInv c, libsMeasure⟩), (762, ⟨ltInv c, ltMeasure⟩)]

/-- The VC at the `"/.libs/"` loop head, behind an irreducible name (so that checking a
statement against it never unfolds `wpN`). -/
@[irreducible] def LibsGoal (c : Ctx) (s : XState) : Prop :=
  wpN Isa.sys8 Main.code postListing (slashCuts c) [(150, common c)] [] [] Main.base
    (some (libsMeasure s)) 20 134 s

/-- The scan exit with a `/`. -/
def slashPre (c : Ctx) (s : XState) : Prop := scanDone c s ∧ s.core.read .rcx ≠ 0#64

set_option hygiene false in
/-- `common` of a symbolically executed state (the registers and the memory unchanged). -/
macro "common_close" : tactic => `(tactic| (simp only [common]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  first | (seg_read [hsp, hdi, hr11, hrsi, hr14]; done) | with_reducible assumption))

set_option maxHeartbeats 8000000 in
/-- **VERIFIED.** From the scan exit with a `/`: the join (`jle` taken) or the `"/.libs/"` loop. -/
theorem vc_slash_entry (c : Ctx) (_hc : LaunchFacts c) :
    ∀ s : XState, s.faulted = false → Loaded s.memory Main.base Main.code →
      s.core.rip = Main.base + BitVec.ofNat 64 84 → slashPre c s →
      wpN Isa.sys8 Main.code postListing (slashCuts c) [(150, common c)] [] [] Main.base none 20 84 s := by
  intro s hlv hl hrip ⟨⟨n, hn, hn0, hnz, hrcx, hsp, hdi, hr11, hrsi, hr14, hww⟩, h0⟩
  obtain ⟨i, hi, hrcx, -⟩ := hrcx.resolve_left h0
  have hR0 : (s.core.read .rcx == 0#64) = false := by simpa using h0
  have hsub : c.argv0 + BitVec.ofNat 64 i + 1#64 - c.argv0 = BitVec.ofNat 64 (i+1) := by
    rw [add_ofNat_succ, add_ofNat_sub]
  rw [hrcx] at hR0
  sl_go [postListing, slashCuts, hrip, hl, hrcx, hdi, hR0, hsub]
  all_goals (try cmn_close)
  rename_i hb
  exact ⟨n, i, 0, hn, hn0, hi, six_le_of_sle (by rw [BitVec.ofNat_add]; exact hb), by omega, by seg_read [hrcx], by seg_read []; try decide, by cmn_close⟩


end Silmaril.Apps.Sha256sum.Binary.Startup.SetName
