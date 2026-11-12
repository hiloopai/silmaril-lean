module

public import Silmaril.Raw.Elf.Link.Dyn.Program.Main
public meta import Lean

/-! # `verify_main`: proving `main` by symbolic execution and call-site contracts

`verify_main ok spec` proves `MainProof B spec tier` for a `main` made of straight-line code
and calls of the contracted imports, ending in `return`:

* `main_start ok`: introduce `main`'s entry `t` and the facts the proof keeps: `F` (the
  program's checked facts), `X` (the entry's stack and layout), `R` (the frame of the current
  memory), `O` (what `stdout` has been handed so far), `hg` (the library state is `t`'s but for
  `out`);
* `mstep`: one instruction (`must_main`, then `xstep`);
* `mcall_puts`: a call of `puts` with a string literal: its precondition from the frame, its
  effect `O := O ++ str ++ "\n"` (`OutIs.appended`), the frame after the call (`Fr.call`);
* `mfinish spec`: back at the library (after `ret`): `MainPost` from `O`, `hg` and `eax`.

The tactics are unhygienic on purpose: each step rebinds `R`, `O`, `hd`, `hrip`, `hrsp`, `hg`
to the current state, so the next step finds them. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program

open Lean Elab Tactic Meta in
/-- **The register facts in context**, as `simp` lemmas: every hypothesis `x.read r = e`,
`x.rip = e` or `x.fsBase = e` about a machine state `x`, and `u.g = e` about the library state of
a named state `u` (whatever their names), but those in
`excl` and those whose right side contains their left side. The steps below find the facts
they need by their statements, not by their names. -/
meta def regFacts (excl : Array FVarId := #[]) : TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :=
  withMainContext do
    let mut out := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail || excl.contains d.fvarId then continue
      let ty ← instantiateMVars d.type
      let some (_, lhs, rhs) := ty.eq? | continue
      unless lhs.isAppOfArity ``Silmaril.X86.State.read 2 || lhs.isAppOfArity ``Silmaril.X86.State.rip 1 ||
          lhs.isAppOfArity ``Silmaril.X86.State.fsBase 1 ||
          (lhs.isAppOfArity ``Silmaril.Elf.Link.Dyn.Proc.PState.g 1 && (lhs.getArg! 0).isFVar) do continue
      if (rhs.find? (· == lhs)).isSome then continue
      let t ← Term.exprToSyntax d.toExpr
      out := out.push (← `(Lean.Parser.Tactic.simpLemma| $t:term))
    return out

open Lean Elab Tactic Meta in
/-- `simp` with the register facts in context (`regFacts`): the stack pointer, the registers
a block or a call left. -/
elab "msimp" : tactic => do
  let fs ← regFacts
  evalTactic (← `(tactic| first | simp [$fs,*] | simp))

open Lean Elab Tactic Meta in
/-- Fail unless the goal is an application of the constant `c` (so the steps below try a lemma
only on goals of its shape: a failed unification against an unrelated goal can unfold deep). -/
elab "mgoal_is " c:ident : tactic => withMainContext do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let g ← whnfR (← instantiateMVars (← getMainTarget))
  unless g.isAppOf n do throwError "mgoal_is: the goal is not `{n}`"

open Lean Elab Tactic Meta in
/-- Close the goal by a hypothesis, compared at reducible transparency, newest first; a frame
bundle `Frm` also offers its frame `Fr`. The steps use it instead of fixed names (`R`, `hd`,
`hrip`), so a proof never rebinds a name for the next step. -/
elab "mfind" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let decls := (← getLCtx).decls.toArray.reverse
  for d? in decls do
    let some d := d? | continue
    if d.isImplementationDetail then continue
    let mut cands := #[d.toExpr]
    if (← instantiateMVars d.type).isAppOf `Silmaril.Elf.Link.Dyn.Program.Frm then
      cands := cands.push (← mkAppM `Silmaril.Elf.Link.Dyn.Program.Frm.fr #[d.toExpr])
    for e in cands do
      let s ← saveState
      if ← withReducible (isDefEq (← inferType e) ty) then
        g.assign e
        replaceMainGoal []
        return
      s.restore
  throwError "mfind: no hypothesis for{indentExpr ty}"

set_option hygiene false in
/-- Introduce `main`'s entry and the facts the proof keeps. -/
macro "main_start " ok:term : tactic => `(tactic| (
  intro w hw S b lb gate args fs argv P hfs henv Q t hd hrip hal hret hroom hm hx hat hpre hrdi hrsi k _kx
  have F := Bin.facts $ok
  have X := Ctx.of F P hal hroom hat
  have R := Fr.of ⟨hm, hx.1, hx.2.2.2.2⟩ hroom hret
  have O := OutIs.atMain hat
  have hsp := X.sp
  have hsp2 := X.sp2
  have hal8 := X.al
  have hdisj := X.disj
  have hlo := X.lo
  have hg : t.g = { t.g with out := t.g.out } := rfl
  have hrel : w.stdoutFull = false := hw))

set_option hygiene false in
/-- One instruction of `main` that is not a call. -/
macro "mstep" : tactic => `(tactic| (
  refine must_main F rfl P.hb R.code hd (by first | exact hrip | rfl) ⟨by decide, by decide⟩ rfl ?_
  first | xstep [hrip, hrsp, Silmaril.X86.popWord, R.ret] | xstep [hrip, Silmaril.X86.popWord, R.ret]))

set_option hygiene false in
/-- A call of `puts (str)` with a string literal `str` of `main`. -/
macro "mcall_puts" : tactic => `(tactic| (
  refine call_at F P R.code hd (by first | exact hrip | rfl) ⟨by decide, by decide⟩ rfl rfl
    (by msimp; exact R.permitted (Or.inr rfl) (by omega) (by omega) hsp2) (by msimp; omega) rfl
    (fun _ h => h) ?pre ?_
  case pre =>
    refine ⟨abiEntry_call (by msimp; omega) (by msimp; omega)
      (by msimp; exact R.permitted (Or.inl rfl) (by omega) (by omega) hsp2)
      (by msimp; exact R.permitted (Or.inr rfl) (by omega) (by omega) hsp2), ?_, ?_⟩
    · simp only [Proc.callEntry_mem]
      exact ⟨_, Code.str F P.hb (R.code.push F P.hb (by msimp; omega)) rfl⟩
    · simp only [Proc.callEntry_mem]
      refine O.stdout_push ?_
      msimp; omega
  rintro v ⟨hlib, hout, -, happ⟩
  have O := OutIs.appended (happ _ (by
    simp only [Proc.callEntry_mem]
    exact Code.str F P.hb (R.code.push F P.hb (by msimp; omega)) rfl)) (by simp only [world0]; rw [hrel]; rfl) (by
    simp only [Proc.callEntry_mem, Proc.callEntry_g]
    refine O.push ?_
    msimp; omega)
  obtain ⟨R, hrip, hrsp', -, -⟩ := Fr.call F rfl hlib X R (fun _ h => h.elim)
    (by msimp; omega) (by msimp; omega) (by msimp; omega)
  have hd : v.g.done = none := by rw [hout]; exact hd
  have hg : v.g = { t.g with out := v.g.out } := by
    rw [hout]; first | rfl | (simp only [Proc.callEntry_g]; rw [hg])
  first | simp [hrsp] at hrsp' | simp at hrsp'
  have hrsp := hrsp'
  clear hrsp' hout happ hlib))

set_option hygiene false in
/-- `ret` to the library: `main`'s postcondition from `O`, `hg` and `eax`. -/
macro "mfinish " spec:ident : tactic => `(tactic| (
  refine k _ rfl (by rw [hg]) (by rw [hg]) hd R.code.1 ⟨?_, ?_, ?_⟩
  · obtain ⟨st, h1, h2⟩ := O
    exact ⟨st, h1, by rw [h2]; rfl⟩
  · rw [hg]; simp [$spec:ident, Streams.ofSpec]
  · simp [Silmaril.Elf.Link.Dyn.Proc.low32, Silmaril.X86.Ext.AluOp.resultN, $spec:ident]))

end Silmaril.Elf.Link.Dyn.Program
