module

public import Silmaril.Raw.Elf.Link.Dyn.Program.StdExe.Basic
public import Silmaril.Raw.Elf.Link.Dyn.Program.Exec
public meta import Lean

/-! # Tactics for standard executables: start at `main`, end at its return

A proof of `E.Verified` for a standard executable `E` reads

```
theorem hello_verified : helloStd.Verified := by
  at_main helloStd_ok       -- loader, `_start`, `__libc_start_main` done: at `main`'s first instruction
  …                         -- `main`, block by block and call by call
  main_returns              -- `ret` to `__libc_start_main`: the outcome
```

* `at_main ok` (`ok : E.ok = true`, by `decide +kernel`): applies `StdExe.verified` (the loader
  relation, the C runtime `Crt.crt_run'` and the bridge to the outcome are proved once,
  `Program.verified`), unfolds `E`, and introduces `main`'s entry `t` in the world `w`. In
  context: `entry : Entry …` (`argc`/`argv`, the three streams, the ghost state, TLS and the
  guard word, the stack), `view : GlibcView …` (what `main` knows of glibc's state), the frame
  bundle `K` (`Frm`, the guard word as a library word), `O : StdoutIs …` (`stdout`, nothing
  buffered), and for the steps below `F` (the checked facts), `P` (the placement), `X` (the entry's
  stack), the continuations `k` (return) and `kx` (exit through the library).
* `main_returns`: back at `__libc_start_main` after `ret` (the state a block ending in `ret`
  leaves): `k`'s side conditions from the facts in context; left: `main`'s postcondition
  (`MainPost`: what was handed to `stdout`, `stderr`, the status).
* `main_exits st`: the process ended through the library at the current state (`exit (st)`,
  `error (st, …)` with `st ≠ 0`): `kx`'s side conditions; left: `MainPostX`.

The steps of `main` are those of the Program API, re-exported by this module:

| tactic | step |
|---|---|
| `mblock`, `mbranch` | one certified straight-line block (`Bin.blks`), ending in a conditional jump |
| `mcallN u`, `mcallNE u` | a call of a contracted import at the state named `u` |
| `mret h` | back from the call (`Frm.call`): frame bundle, registers |
| `mghost h` | the library state after a call (`done`, `jobs`, `atexit`, `err`, `inp`) from its ghost clause `h` |
| `mfile h` | a stream across the stores into the frame since `h` (`mstdout` for `stdout`) |
| `main_straight spec` | a straight-line `main` of blocks and `puts` calls, to its outcome |
| `mcanary` | gcc's stack-protector check before `ret` (the inlined code, outlined) |
| `mloop I`, `mnext`, `mexit` | a loop with invariant `I`, measured by the unread input |
| `mstores K`, `mkept`, `mloadK h`, `mslot` | stores into the frame, library words, saved words |
| `mregs`, `mnat`, `mnorm`, `mfind` | register facts, address arithmetic, facts by statement |
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program

open Lean Elab Tactic Meta in
/-- Unfold the standard executable named by the check `ok : StdExe.ok E = true` (when `E` is a
constant) in the goal, and reduce its fields. -/
elab "stdexe_unfold " ok:term:max : tactic => withMainContext do
  let e ← Term.elabTerm ok none
  let ty ← whnfR (← instantiateMVars (← inferType e))
  let some (_, lhs, _) := ty.eq? | throwError "stdexe_unfold: `{ok}` is not a check `StdExe.ok E = true`"
  let E := lhs.appArg!
  let some c := E.getAppFn.constName? | return
  let ci := mkIdent c
  evalTactic (← `(tactic| (unfold $ci:ident; dsimp only)))

open Lean Elab Tactic Meta in
/-- `F : Bin.Facts B _ _`, the checked facts of the executable `B` of the placement `P` in
context, from the check `ok : StdExe.ok E = true` (`B` is `E.bin`, unfolded). -/
elab "stdexe_facts " ok:term:max : tactic => withMainContext do
  let P ← getLocalDeclFromUserName `P
  let some B := (← instantiateMVars P.type).getAppArgs[0]? | throwError "stdexe_facts: no placement `P`"
  let Bs ← Term.exprToSyntax B
  evalTactic (← `(tactic| have $(mkIdent `F) : Bin.Facts $Bs _ _ := StdExe.facts $ok))

set_option hygiene false in
/-- **Start at `main`** (see the module docstring). -/
macro "at_main " ok:term:max : tactic => `(tactic| (
  refine StdExe.verified $ok ?_
  unfold StdExe.Main
  stdexe_unfold $ok
  intro w hw S b lb gate args fs argv P hfs henv Q t hd hrip hal hret hroom hm hx hat hpre hrdi hrsi k kx
  stdexe_facts $ok
  have X := Ctx.of F P hal hroom hat
  have entry := Entry.of hal hroom hx hat hpre hrdi hrsi
  have view := GlibcView.entry entry
  have hfsb := entry.tls
  obtain ⟨guard, hguard⟩ := entry.guard
  have K := Frm.entry (Fr.of ⟨hm, hx.1, hx.2.2.2.2⟩ hroom hret)
    (KSlots.word hguard fun _ _ => Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
  have hstdout := entry.stdout
  -- for straight-line `main`s (`main_straight`): the frame and what was handed to `stdout`
  have R := K.fr
  have O := OutIs.atMain hat
  have hsp := X.sp
  have hsp2 := X.sp2
  have hal8 := X.al
  have hdisj := X.disj
  have hlo := X.lo
  have hg : t.g = { t.g with out := t.g.out } := rfl
  try have hrel : w.stdoutFull = false := by first | exact hw | exact hw.1 | exact hw.1.1
  clear hx hpre hm hret))

set_option hygiene false in
/-- A stream (`S.E.S.file m f st`) across the stores into `main`'s frame since the fact `h`. -/
macro "mfile " h:term:max : tactic => `(tactic| (
  repeat (refine file_store ?_ (by mnat))
  exact $h))

set_option hygiene false in
/-- **A straight-line `main`** (no branch, no loop) of blocks and calls of `puts` with string
literals, ending in `return`: each block by `mblock`, each call by `mcall_puts`, the end by
`mfinish spec` (the outcome `spec w`). -/
macro "main_straight " spec:ident : tactic => `(tactic| (
  repeat (first | mcall_puts | mblock | mstep)
  mfinish $spec))

open Lean Elab Tactic Meta in
/-- **The library state after a call** (`mghost h`, `h : v.g = { s.g with … }`, e.g. a contract's
`OutOnly` or its ghost clause): the fields the call kept, as facts about `v` in terms of the facts
in context (`v.g.done = none`, `v.g.jobs = …`, `v.g.atexit = …`, `v.g.err = …`, `v.g.inp = …`);
`h` itself is read past the call's entry (`(callEntry u …).g = u.g`). -/
elab "mghost " h:term:max : tactic => withMainContext do
  let hfv? ← (do
    let e ← Term.elabTerm h none
    pure (if e.isFVar then some e.fvarId! else none))
  for (f, toNone) in [(``Proc.Ghost.done, true), (``Proc.Ghost.jobs, false), (``Proc.Ghost.atexit, false),
      (``Proc.Ghost.err, false), (``Proc.Ghost.inp, false)] do
    let n := mkIdent (← mkFreshUserName `hgh)
    evalTactic (← `(tactic| have $n := congrArg $(mkIdent f) $h))
    evalTactic (← `(tactic| (try dsimp only at $n:ident)))
    evalTactic (← `(tactic| (try simp only [Proc.callEntry_g] at $n:ident)))
    withMainContext do
      let nfv ← getFVarId n
      let fs ← regFacts (#[nfv] ++ hfv?.toArray)
      evalTactic (← `(tactic| (try simp only [$fs,*] at $n:ident)))
    if toNone then evalTactic (← `(tactic| (try replace $n := ($n).trans (by mfind))))
  if hfv?.isSome then
    evalTactic (← `(tactic| (try simp only [Proc.callEntry_g] at $(⟨h.raw⟩):ident)))

set_option hygiene false in
/-- **`main` returns**: `k` at the current state (the gate, after `ret`), its side conditions
from the facts in context; left: `MainPost` (stdout, stderr, status). -/
macro "main_returns" : tactic => `(tactic| (
  refine k _ (by first | rfl | mfind | (mregs; mfind)) (by first | mfind | (mregs; done) | (mregs; mfind))
    (by first | mfind | (mregs; done) | (mregs; mfind)) (by first | mfind | (mregs; done) | (mregs; mfind))
    (Fr.code (by mfind)).1 ⟨?_, ?_, ?_⟩))

set_option hygiene false in
/-- **`main` ends the process through the library** with status `st` (after `exit (st)` or
`error (st, …)`): `kx` at the current state; left: the side conditions not found in context,
then `MainPostX` (stdout, stderr, status). -/
macro "main_exits " st:term:max : tactic => `(tactic| (
  refine kx _ $st ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_⟩))

end Silmaril.Elf.Link.Dyn.Program
