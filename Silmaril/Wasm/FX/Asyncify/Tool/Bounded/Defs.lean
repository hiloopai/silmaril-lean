module

public import Silmaril.Wasm.FX.Asyncify.Tool.Sys.Defs

/-!
# The asyncify tool with a bounded memory

The frame machine of `Silmaril.Wasm.FX.Asyncify.Tool.Machine` reads and writes an unbounded word
memory. The output module of the pass declares one memory of `pages` pages, so in Core 3.0 an
`i32.load` or `i32.store` whose four bytes end past `65536 · pages` traps. This module adds that
check:

* `access c`: the byte address of the access that the next instruction of the top frame makes
  (an `i32.load` with an address on the stack, an `i32.store` with a value and an address), if it
  is one;
* `OOB cap c`: that access ends past `cap` bytes (`a + 4 > cap`);
* `stepB cap E`: the machine step, except that it traps at an out-of-bounds access;
* `tgtStepB cap E H`: the target system of `Silmaril.Wasm.FX.Asyncify.Tool.Sys` (asyncify host
  protocol) on `stepB cap E`;
* `Safe step Bad x`: no state reachable from `x` is `Bad`.
* `Task.fits`: the open target that the asyncified program stays in bounds when every source
  state fits its frames into the memory (`FitsIn`). A frozen statement, not proved.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-- The bytes of one memory of `pages` pages. -/
def capOf (pages : Nat) : Nat := 65536 * pages

/-- The byte address that instruction `i` accesses when the operands are `ops` (top first). -/
def accessAt : Instr → List W → Option Nat
  | .intLoad .i32 none _ arg, a :: _ => some (a.toNat + arg.offset.val)
  | .intStore .i32 none _ arg, _ :: a :: _ => some (a.toNat + arg.offset.val)
  | _, _ => none

/-- The access of the next instruction of the top frame. -/
def access (c : Cfg) : Option Nat :=
  match c.frames with
  | fr :: _ =>
    match fr.code with
    | i :: _ => accessAt i fr.ops
    | [] => none
  | [] => none

/-- The next access ends past `cap` bytes. -/
def OOB (cap : Nat) (c : Cfg) : Prop := ∃ a, access c = some a ∧ cap < a + 4

instance (cap : Nat) (c : Cfg) : Decidable (OOB cap c) :=
  match h : access c with
  | some a =>
    if hc : cap < a + 4 then isTrue ⟨a, h, hc⟩
    else isFalse fun ⟨a', h', hc'⟩ => hc (by rw [h] at h'; cases h'; exact hc')
  | none => isFalse fun ⟨_, h', _⟩ => by rw [h] at h'; cases h'

/-- **The bounded machine step**: a trap at an access past `cap` bytes, else `step`. -/
def stepB (cap : Nat) (E : Env) (c : Cfg) : Res := if OOB cap c then .trap else step E c

/-- The target system on the bounded machine (same host protocol as `tgtStep`). -/
def tgtStepB {σ : Type} (cap : Nat) (E : Env) (H : Host σ) (t : TSt σ) : SRes (TSt σ) σ :=
  match stepB cap E t.cfg with
  | .next c' => .next { t with cfg := c' }
  | .done vs c' =>
    if c'.globals[0]? = some 1 then
      let f := (c'.mem 0).toNat
      match E.imps[f]?, E.fns[t.fid - E.imps.length]? with
      | some (n, m), some fn =>
        let r := H.answer t.host f ((List.range n).map fun i => c'.mem (4 * (i + 1)))
        .next ⟨⟨[entry t.fid fn t.args], c'.globals.set 0 2, writeWords c'.mem 0 (fit m r.2)⟩,
          r.1, t.fid, t.args⟩
      | _, _ => .stop (.trap t.host)
    else .stop (.done vs t.host)
  | .trap => .stop (.trap t.host)
  | .ask _ _ _ => .stop (.trap t.host)

/-- No state reachable from `x` is `Bad`. -/
def Safe {X σ : Type} (step : X → SRes X σ) (Bad : X → Prop) (x : X) : Prop :=
  ∀ n y, runN step n x = .next y → ¬ Bad y

/-- Every source state reachable from `x` fits its frames, `4 F` bytes each, above the request
area in `cap` bytes. -/
def FitsIn {σ : Type} (cap : Nat) (P : Prog) (H : Host σ) (x : Cfg × σ) : Prop :=
  ∀ n y, runN (srcStep P.env H) n x = .next y → P.sb + 4 * P.frameWords * y.1.frames.length ≤ cap

/-- **Open target** (frozen, not proved): if every reachable source state fits its frames in
`cap` bytes, the asyncified program never accesses memory past `cap` (each saved frame takes
`4 F` bytes above `SB`, and at most one frame per source frame is ever saved). -/
def Task.fits : Prop :=
  ∀ (P : Prog) (_ : P.WF) {σ : Type} (H : Host σ) (cap : Nat) (e : Nat) (fn : FnSrc)
    (args : List W) (s : σ), P.imps.length ≤ e → P.fns[e - P.imps.length]? = some fn →
    args.length = fn.nparams →
    FitsIn cap P H (⟨[entry e ⟨fn.nparams, fn.nlocals, fn.nres, fn.body⟩ args], [], fun _ => 0⟩, s) →
    Safe (tgtStep (asyncifyProg P) H) (fun t => OOB cap t.cfg)
      ⟨⟨[entry e ⟨fn.nparams, P.frameWords - fn.nparams, fn.nres, P.tBody fn⟩ args],
        P.tGlobals, fun _ => 0⟩, s, e, args⟩

end Silmaril.Wasm.FX.Asyncify.Tool
