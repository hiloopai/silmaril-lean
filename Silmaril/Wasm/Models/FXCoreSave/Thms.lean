module

public import Silmaril.Proofs.Wasm.Models.FXCoreSave.Example

/-!
# Saving and restoring asyncify frames in Core 3.0: results

The header of `Defs`. For every profile and host of Core 3.0 `Step`:

* **`saveAtCheck`** (`chk_unwind`): in a non-zero mode, the call-site check `chkCode` of a frame
  whose locals `0, …, n-1` hold `q.locals` builds the record struct of `q` (`struct.new` of a
  record type `RecTy`), pushes it on the linked buffer in global `b`, and reaches `return`;
  **`checkNormal`** (`chk_normal`): in mode `0` the check is a no-op.
* **`restoreAtEntry`** (`restore_run`): from a buffer whose head is `q`, the restore code sets
  the locals to `q.locals`, stores `q.r` in the dispatch global and pops the record; the rest
  stays a chain.
* **`unwindChk`** (`unwind_chk_step`): one unwinding step of `FXAsyncPC.fstep` at a check and the
  Core check that saves the same record; with `recRel_unwind`, the linked buffer stays the
  reverse of `fstep`'s buffer.
* **`rewindDispatch`** (`rewind_step`): one rewinding step of `fstep` (dispatch of the next
  record on its resume index) and the Core restore code followed by the `br_table` prologue of
  `FXDispatch`, which joins the body written to start at that resume point, with the locals
  restored and the record popped.
* Non-vacuity: `recTy_ex` (a concrete record struct type meets `RecTy`) and **`saveRestoreEx`**
  (save at a check, then restore in a later frame: local, resume index and buffer are as
  before).

What is **not** proved: a compiler from `fstep` programs (`AIns` code) to Core 3.0 functions and
the simulation of whole runs. In particular the save code returns but the caller's unwinding
(the `return` reaching the check of the caller, through `frame` contexts), the handled `rchk`
(turning the buffer into a heap record), `startUnwind`/`startRewind`, the heap of one-shot
record lists, the last rewinding step (mode back to `0`, arguments pushed), operand stacks that
are not spilled to locals, and continuation references among saved values are not covered. See
"Stretch, fx (ws5 an earlier step)" in `docs/projects/wasm-wasi.md`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXCoreSave

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Models.FXCoreSave

variable {H : Type}

/-- **The check in a non-zero mode saves the frame and returns.** -/
theorem saveAtCheck (P : Profile) (host : HostSemantics H) {s : Store H} {f : Frame}
    {m : GlobalIdx} {am : Nat} {gm : GlobalInst} (hm : s.global? f m = some (am, gm))
    {c : BitVec 32} (hv : gm.value = .i32 c) (hc : c ≠ 0) {x : TypeIdx} {b : GlobalIdx}
    {n : Nat} (hx : RecTy f x n) {ab : Nat} {gb : GlobalInst} (hb : s.global? f b = some (ab, gb))
    (q : CRec) (hL : LocalsAre f q.locals) (hn : q.locals.length = n) (rest : List Admin) :
    ∃ d, Steps P host ⟨s, f, expression (chkCode m x b n q.fn q.r) ++ rest⟩
      ⟨saveStore s d q gb.value ab, f, [.plain .return_] ++ rest⟩ :=
  chk_unwind hm hv hc hx hb q hL hn rest

/-- **The check in normal mode is a no-op.** -/
theorem checkNormal (P : Profile) (host : HostSemantics H) {s : Store H} {f : Frame}
    {m : GlobalIdx} {am : Nat} {gm : GlobalInst} (hm : s.global? f m = some (am, gm))
    (hv : gm.value = .i32 0) (x : TypeIdx) (b : GlobalIdx) (n : Nat) (fn r : BitVec 32)
    (rest : List Admin) :
    Steps P host ⟨s, f, expression (chkCode m x b n fn r) ++ rest⟩ ⟨s, f, rest⟩ :=
  chk_normal hm hv x b n fn r rest

/-- **The restore code at the head of the buffer.** -/
theorem restoreAtEntry (P : Profile) (host : HostSemantics H) {s : Store H} {f : Frame}
    {x : TypeIdx} {b g : GlobalIdx} {n : Nat} (hx : RecTy f x n) (h32 : n + 3 ≤ 2 ^ 32)
    {ab : Nat} {gb : GlobalInst} (hb : s.global? f b = some (ab, gb)) {ag : Nat} {gg : GlobalInst}
    (hg : s.global? f g = some (ag, gg)) (hne : ag ≠ ab) {q : CRec} {qs : List CRec}
    (hbuf : BufIs s gb.value (q :: qs)) (hn : q.locals.length = n) (hloc : n ≤ f.locals.length)
    (rest : List Admin) :
    ∃ nx, BufIs (restoreStore s q nx ag ab) nx qs ∧
      LocalsAre (setLocals f q.locals 0) q.locals ∧
      Steps P host ⟨s, f, expression (restoreCode x b g n) ++ rest⟩
        ⟨restoreStore s q nx ag ab, setLocals f q.locals 0, rest⟩ := by
  obtain ⟨nx, h1, h2⟩ := restore_run (P := P) (host := host) hx h32 hb hg hne hbuf hn hloc rest
  exact ⟨nx, h1, localsAre_restored f q.locals (by omega) (by omega), h2⟩

/-- **Unwinding at a check: `fstep` and Core 3.0 save the same record.** -/
theorem unwindChk (PA : FXAsync.Prog (FXAsyncPC.AIns Val))
    (hp : List (Option (List (FXAsyncPC.Rec Val)))) (t : Nat) (pay : List (FXAsync.SV Val))
    (buf : List (FXAsyncPC.Rec Val)) (fn r : Nat) (ops : List (FXAsync.SV Val))
    (c : List (FXAsyncPC.AIns Val)) (st : List (FXAsyncPC.AFrame Val))
    (P : Profile) (host : HostSemantics H) {s : Store H} {f : Frame} {m : GlobalIdx} {am : Nat}
    {gm : GlobalInst} (hm : s.global? f m = some (am, gm)) {k : BitVec 32}
    (hv : gm.value = .i32 k) (hk : k ≠ 0) {x : TypeIdx} {b : GlobalIdx} {n : Nat}
    (hx : RecTy f x n) {ab : Nat} {gb : GlobalInst} (hb : s.global? f b = some (ab, gb))
    (hmb : ab ≠ am) {qs : List CRec} (hbuf : BufIs s gb.value qs)
    (hrel : List.Forall₂ RecRel qs buf.reverse) (q : CRec) (hq : RecRel q ⟨fn, r, ops⟩)
    (hL : LocalsAre f q.locals) (hn : q.locals.length = n) (rest : List Admin) :
    FXAsyncPC.funwind PA hp t pay buf ⟨.chk fn r :: c, ops⟩ st =
        .next ⟨hp, 1, t, pay, buf ++ [⟨fn, r, ops⟩], st⟩ ∧
      ∃ d, Steps P host ⟨s, f, expression (chkCode m x b n q.fn q.r) ++ rest⟩
          ⟨saveStore s d q gb.value ab, f, [.plain .return_] ++ rest⟩ ∧
        BufIs (saveStore s d q gb.value ab) (.ref (.struct s.structs.length)) (q :: qs) ∧
        List.Forall₂ RecRel (q :: qs) (buf ++ [(⟨fn, r, ops⟩ : FXAsyncPC.Rec Val)]).reverse ∧
        (saveStore s d q gb.value ab).global? f b =
          some (ab, { gb with value := .ref (.struct s.structs.length) }) ∧
        (saveStore s d q gb.value ab).global? f m = some (am, gm) := by
  obtain ⟨h1, d, h2, h3, h4, h5⟩ := unwind_chk_step (P := P) (host := host) PA hp t pay buf fn r
    ops c st hm hv hk hx hb hmb hbuf q hL hn rest
  exact ⟨h1, d, h2, h3, recRel_unwind hrel hq, h4, h5⟩

/-- **Rewinding: `fstep`'s dispatch and the Core 3.0 restore code with the `br_table`
prologue.** -/
theorem rewindDispatch {V : Type} (PA : FXAsync.Prog (FXAsyncPC.AIns V))
    (B : Nat → Option (List (FXAsync.TIns V))) (test : V → Bool)
    (hp : List (Option (List (FXAsyncPC.Rec V)))) (t : Nat) (pay : List (FXAsync.SV V))
    (p p' : FXAsyncPC.Rec V) (ps : List (FXAsyncPC.Rec V)) (st : List (FXAsyncPC.AFrame V))
    {code : List (FXAsyncPC.AIns V)} (hd : FXAsyncPC.disp B p.fn p.r = some code)
    (P : Profile) (host : HostSemantics H) {s : Store H} {f : Frame} {x : TypeIdx}
    {b g : GlobalIdx} {n : Nat} (hx : RecTy f x n) (h32 : n + 3 ≤ 2 ^ 32) {ab : Nat}
    {gb : GlobalInst} (hb : s.global? f b = some (ab, gb)) {ag : Nat} {gg : GlobalInst}
    (hg : s.global? f g = some (ag, gg)) (hne : ag ≠ ab) {q : CRec} {qs : List CRec}
    (hbuf : BufIs s gb.value (q :: qs)) (hn : q.locals.length = n) (hloc : n ≤ f.locals.length)
    (segs : List (List Instr)) (hr : q.r.toNat < segs.length) :
    FXAsyncPC.fstep PA B test ⟨hp, 2, t, pay, p :: p' :: ps, st⟩ =
        .next ⟨hp, 2, t, pay, p' :: ps, ⟨code, p.ops⟩ :: st⟩ ∧
      ∃ nx cfg, BufIs (restoreStore s q nx ag ab) nx qs ∧
        LocalsAre (setLocals f q.locals 0) q.locals ∧
        Steps P host ⟨s, f, expression (restoreCode x b g n ++ FXDispatch.prologue g segs)⟩ cfg ∧
        Steps P host ⟨restoreStore s q nx ag ab, setLocals f q.locals 0,
          expression (FXDispatch.resumeAt segs q.r.toNat)⟩ cfg :=
  rewind_step PA B test hp t pay p p' ps st hd hx h32 hb hg hne hbuf hn hloc segs hr

/-- **Non-vacuity: save at a check, then restore.** -/
theorem saveRestoreEx (P : Profile) (host : HostSemantics H) (gm gb gg : CGlobalType)
    (rest : List Admin) :
    ∃ s', Steps P host ⟨storeEx gm gb gg, ⟨[some (.i32 42)], modEx⟩,
        expression (chkCode (ix 0) (ix 0) (ix 1) 1 3 4) ++ rest⟩
        ⟨s', ⟨[some (.i32 42)], modEx⟩, [.plain .return_] ++ rest⟩ ∧
      ∀ f' : Frame, f'.module = modEx → 1 ≤ f'.locals.length →
        ∃ s'', Steps P host ⟨s', f', expression (restoreCode (ix 0) (ix 1) (ix 2) 1) ++ rest⟩
            ⟨s'', setLocals f' [.i32 42] 0, rest⟩ ∧
          (setLocals f' [.i32 42] 0).local? (ix 0) = some (some (.i32 42)) ∧
          s''.global? f' (ix 2) = some (2, ⟨gg, .i32 4⟩) ∧
          s''.global? f' (ix 1) = some (1, ⟨gb, .ref .null⟩) :=
  save_restore_ex P host gm gb gg rest

/-- info: 'Silmaril.Wasm.Models.FXCoreSave.unwindChk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unwindChk

/-- info: 'Silmaril.Wasm.Models.FXCoreSave.rewindDispatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rewindDispatch

/-- info: 'Silmaril.Wasm.Models.FXCoreSave.saveRestoreEx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms saveRestoreEx

end Silmaril.Wasm.Models.FXCoreSave
