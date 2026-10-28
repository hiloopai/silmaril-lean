module

public import Silmaril.Apps.Sha256sum.Binary.Startup.Cuts
public import Silmaril.Apps.Sha256sum.Binary.Startup.PrologueCMain
public import Silmaril.Apps.Sha256sum.Binary.Digest.Spec
public import Silmaril.Apps.Sha256sum.X86Sys.SegVC8
public meta import Lean

/-! # The prologue of `digest_file` for the operand `"-"`

From `digest_file`'s entry on the stdin path (`Startup.AtDigestEntry`, `0x402de0`) to the read
loop's head (`0x402ef0`), over `X86Sys.Isa.sys8` (`cmp %r13b,%bpl` is an `Ext8` new form):

* the six pushes and the frame (`sub $0x98,%rsp`): `digest_file`'s stack pointer is
  `sp0 - 448`;
* the inlined `c_streq(file, "-")`, two rounds over the literal `"-"` at `0x406052` (the
  operand *is* that literal): equal, so no `openat`; `*missing = 0` (`missing` is `cmain`'s
  `0x90(%rsp)`), `have_read_stdin = 1` (`0x40a0a0`), the descriptor slot `8(%rsp) = 0`;
* the inlined `sha_init`: the SHA-256 initial value as four quadwords at `0x20(%rsp)`,
  `blen = total = 0` (`0x80(%rsp)`, `0x88(%rsp)`), `rbx = 64`.

`vc_entry` (VERIFIED): the segment VC from the entry to the stop `0x402ef0` with `post`: the
registers of the loop frame, the locals and the `struct sha` of `sha_init`, the six saved
registers and the return address, `have_read_stdin = 1`, the footprint `PW` relative to the
entry memory. `PrologueRun` turns it into the run and the read loop's cut point.

The load tactic `pr_ld` resolves a load of a stored memory through its store, as the same span
when the addresses agree up to reducible unfolding, else as a disjoint span.

Everything here is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Startup.Prologue

open Lean Elab Tactic Meta

/-- Resolve one load of a stored memory in the goal through its store: the same span when the
addresses agree syntactically, else a disjoint one (as `gnu-r3-cmain`'s `cm_ld`). -/
meta def ldOnce : TacticM Bool := do
  if (← getGoals).isEmpty then return false
  withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  let mut prods : Array (Lean.Expr × Lean.Expr × Lean.Expr × Bool) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless rhs.isAppOfArity ``Option.some 2 do continue
    if lhs.isAppOfArity ``Silmaril.Process.Memory.writeBytes 3 then
      prods := prods.push (rhs.getArg! 1, d.toExpr, lhs.getArg! 1, false)
    else if lhs.isAppOfArity ``Silmaril.X86.Ext.storeN 4 then
      prods := prods.push (rhs.getArg! 1, d.toExpr, lhs.getArg! 1, true)
  let isProduced := fun (m : Lean.Expr) => prods.any fun p => p.1 == m
  let some ld := Silmaril.Apps.Sha256sum.Binary.Startup.findLoad g isProduced | return false
  let some (_, h, addr, isSt) := prods.find? fun p => p.1 == ld.getArg! 0 | return false
  let a := ld.getArg! 1
  let same ← if isSt then withReducible (isDefEq addr a) else
    if addr.isAppOfArity ``BitVec.toNat 2 then withReducible (isDefEq (addr.getArg! 1) a)
    else pure false
  let hs ← Term.exprToSyntax h
  let lds ← Term.exprToSyntax ld
  if isSt then
    if same then
      evalTactic (← `(tactic| (have e : $lds = _ := Silmaril.Apps.Sha256sum.Binary.Startup.loadN_st_same $hs (by sv_perm); simp only [e]; try clear e)))
    else
      evalTactic (← `(tactic| (have e : $lds = _ := Silmaril.Apps.Sha256sum.Binary.Startup.loadN_st_disj $hs (by sv_disj); simp only [e]; try clear e)))
  else
    if same then
      evalTactic (← `(tactic| (have e : $lds = _ := Silmaril.Apps.Sha256sum.Binary.Startup.loadN_wb_word $hs (by sv_perm); simp only [e]; try clear e)))
    else
      evalTactic (← `(tactic| (have e : $lds = _ := Silmaril.Apps.Sha256sum.Binary.Startup.loadN_wb_disj $hs (by sv_disj); simp only [e]; try clear e)))
  return true

end Silmaril.Apps.Sha256sum.Binary.Startup.Prologue

open Lean Elab Tactic in
/-- `pr_ld`: resolve the loads of stored memories in the goal. -/
elab "pr_ld" : tactic => do
  for _ in [0:100] do
    unless ← Silmaril.Apps.Sha256sum.Binary.Startup.Prologue.ldOnce do break

open Lean Elab Tactic in
/-- `pr_ld'`: `pr_ld`, keeping the progress made before a step fails. -/
elab "pr_ld'" : tactic => do
  for _ in [0:100] do
    unless ← (Silmaril.Apps.Sha256sum.Binary.Startup.Prologue.ldOnce <|> pure false) do break

/-- `pr_go [lemmas]`: `sv`, `sv_split`, `pr_ld`, repeated. -/
macro "pr_go " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (sv [$ls,*]; sv_split; all_goals (try pr_ld); iterate 40 (all_goals (try (sv [$ls,*]; sv_split; all_goals (try pr_ld))))))

namespace Silmaril.Apps.Sha256sum.Binary.Startup.Prologue

set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

open Silmaril.X86 (State Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext
open Silmaril.X86.SegVC
open Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Apps.Sha256sum.Binary.Startup.Digest

/-- A footprint fact, kept whole by `sv_split`. -/
@[irreducible] def WW (m0 m : Memory) (W : Nat → Prop) : Prop := Memory.WritesWithin m0 m W

theorem WW.of {m0 m : Memory} {W : Nat → Prop} (h : Memory.WritesWithin m0 m W) : WW m0 m W := by
  unfold WW; exact h

theorem WW.ww {m0 m : Memory} {W : Nat → Prop} (h : WW m0 m W) : Memory.WritesWithin m0 m W := by
  unfold WW at h; exact h

theorem ofNat_toNat_mod8 (x : Word) : BitVec.ofNat 64 (x.toNat % 2 ^ (8 * 8)) = x := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt x.isLt]

theorem ofNat_toNat_mod64 (x : Word) : BitVec.ofNat 64 (x.toNat % 18446744073709551616) = x :=
  ofNat_toNat_mod8 x

/-- At the loop head (`0x402ef0`), from the entry state `s0`. -/
def post (c : Ctx) (s0 s : XState) : Prop :=
  s.core.read .rsp = c.sp0 - 448#64 ∧ s.core.read .rbx = 64#64 ∧
    s.core.read .rbp = 0#64 ∧ s.core.read .r13 = 0#64 ∧
    loadN s.memory (c.sp0 - 448#64 + 8#64) 8 = some 0#64 ∧
    loadN s.memory (c.sp0 - 448#64 + 16#64) 8 = some (s0.core.read .rsi) ∧
    loadN s.memory (c.sp0 - 448#64 + 0x20#64) 8 = some 0xbb67ae856a09e667#64 ∧
    loadN s.memory (c.sp0 - 448#64 + 0x28#64) 8 = some 0xa54ff53a3c6ef372#64 ∧
    loadN s.memory (c.sp0 - 448#64 + 0x30#64) 8 = some 0x9b05688c510e527f#64 ∧
    loadN s.memory (c.sp0 - 448#64 + 0x38#64) 8 = some 0x5be0cd191f83d9ab#64 ∧
    loadN s.memory (c.sp0 - 448#64 + 0x80#64) 8 = some 0#64 ∧
    loadN s.memory (c.sp0 - 448#64 + 0x88#64) 8 = some 0#64 ∧
    loadN s.memory (c.sp0 - 296#64) 8 = some (s0.core.read .rbx) ∧
    loadN s.memory (c.sp0 - 288#64) 8 = some (s0.core.read .rbp) ∧
    loadN s.memory (c.sp0 - 280#64) 8 = some (s0.core.read .r12) ∧
    loadN s.memory (c.sp0 - 272#64) 8 = some (s0.core.read .r13) ∧
    loadN s.memory (c.sp0 - 264#64) 8 = some (s0.core.read .r14) ∧
    loadN s.memory (c.sp0 - 256#64) 8 = some (s0.core.read .r15) ∧
    loadN s.memory (c.sp0 - 248#64) 8 = some 0x40419f#64 ∧
    loadN s.memory 0x40a0a0#64 4 = some 1#64 ∧
    WW s0.memory s.memory (PW c.sp0) ∧ Ro s.memory

theorem base_have : base + 29376#64 = 0x40a0a0#64 := rfl

def stops (c : Ctx) (s0 : XState) : List (Nat × (XState → Prop)) := [(272, post c s0)]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem vc_entry (c : Ctx) (s : XState) (_hlv : s.faulted = false)
    (hl : Loaded s.memory base code) (hrip : s.core.rip = base + BitVec.ofNat 64 0)
    (hrsp : s.core.read .rsp = c.sp0 - 248#64)
    (hrdi : s.core.read .rdi = 0x406052#64)
    (hrdx : s.core.read .rdx = c.sp0 - 240#64 + 0x90#64)
    (hret : loadN s.memory (c.sp0 - 248#64) 8 = some 0x40419f#64)
    (hro : Ro s.memory) (hlo : 0x423150 ≤ c.sp0.toNat) (hhi : c.sp0.toNat + 16 < 2 ^ 64)
    (hpw : s.memory.Permitted .write (c.sp0.toNat - 0x10000) (0x10000 + 16))
    (hpr : s.memory.Permitted .read (c.sp0.toNat - 0x10000) (0x10000 + 16))
    (hgw : s.memory.Permitted .write 0x40a0a0 4)
    (hgr : s.memory.Permitted .read 0x40a0a0 4)
    (g0 : loadN s.memory 0x406052#64 1 = some 0x2d#64)
    (g1 : loadN s.memory 0x406053#64 1 = some 0#64) :
    wpN Isa.sys8 code listing [] (stops c s) [] [] base none 60 0 s := by
  have hw0 : Memory.WritesWithin s.memory s.memory (PW c.sp0) := .refl _ _
  pr_go [listing, stops, post, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl, hrsp, hrdi, hrdx, g0, g1,
    hret, Nat.reducePow, Nat.reduceMul, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd,
    BitVec.reduceOfNat, BitVec.reduceSetWidth, Bool.not_true, Bool.not_false, Mem.ofRip,
    Base.value, base_have, BitVec.toNat_ofNat, ofNat_toNat_mod8, ofNat_toNat_mod64]
  all_goals (try (simp only [ofNat_toNat_mod64, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMul,
    Nat.reduceMod]))
  all_goals (try (exact hret))
  all_goals (try (refine WW.of ?_; sv_mem))
  all_goals (intro i hi; (try simp only [Silmaril.Machine.LittleEndian.encodeWords_length,
    List.length_cons, List.length_nil] at hi); simp only [PW]; sv_disj)

end Silmaril.Apps.Sha256sum.Binary.Startup.Prologue
