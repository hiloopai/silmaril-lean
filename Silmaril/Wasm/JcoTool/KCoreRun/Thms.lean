module

public import Silmaril.Wasm.JcoTool.KCoreRun.Defs
public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Runtime
public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Agree
public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.SafeGen
public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Inst
public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Entry
public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.SafeTee
public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.EntryT

/-!
# The KCore/KDrop fragment on silmaril-lean's Core 3.0: results

Proofs in `Silmaril.Proofs.Wasm.JcoTool.KCoreRun.*`. For every profile `Pf` of silmaril-lean's
Core 3.0 `Step`, every type `H` of host functions and every assignment `hb : BI → H` of host
functions to the built-ins, with the built-ins answered by `bans ma` on memory `ma`:

* **`hstep_core`**: each `HStep` is a Core 3.0 `Step` against the stateless host of its host-state
  transition (`hostAt hb ma q q'`); host-free steps are steps against every host.
* **`stmt_run`** (the whole fragment, *checked semantics*): a statement `S` that `bexec nl`
  runs from `s` to `(o, s')` — byte memory (`i32.load8_u`, `i32.store8`, `memory.copy`),
  sequences, `block`, `loop`, `br`, `br_if`, `if`, `return`, `unreachable` and the built-in calls
  `stream.read`, `stream.write`, `stream.drop-readable`, `stream.drop-writable` — runs, as the
  instructions `KCoreEmit.sCode S` of the emitted module, from every Core configuration related to
  `s` (`Rel`: locals, globals, memory `0`, imported host functions), under any code after it, to a
  configuration related to `s'` whose code is `outCode o` (nothing, `br k`, or `i32.const v;
  return`), the frame's module instance and the store's functions unchanged. `bexec`'s fuel
  bounds `dloopN`'s iterations; Core's loop is unbounded, and a run that `bexec` finishes is a Core
  run with as many iterations.
* **`bexec_dexec`**: where `bexec nl` is defined it is `KDrop.dexec`. `bexec` adds the conditions
  under which Core does not trap where `dexec` does not (nonzero divisors, accesses and buffers
  below `MSZ`, forward `memory.copy`, local, global and branch indices in range).
* **`invoke_run`**: the Core invocation `invoke cs a args` of the callback of `P` (held by the
  store at address `a`, `CbAt`, with the code `KCoreEmit.toModule P name` gives it,
  `toModule_cb`) on three `i32`s runs, when `bexec CBL` runs the body to `return code`, to the
  value `code` (`return-label`, `return-frame`), with the instance holding the globals and memory
  `bexec` leaves (`InstR`).
* **`rstep_core`**: **every step of the drop runtime `KDrop.DRStep P` is a step `CRStep` of the
  callback runtime on Core 3.0** (Core invocations of the callback; events taken from the drop
  store; delivered items written into the instance's memory, `deliverC`), when the callback is
  `CbSafe` at the machine's globals: `dexec` runs of the callback with the runtime's parameters are
  `bexec` runs.
* **`genD_safe`**: the callback of `KDrop.genD k N` is `CbSafe` for `N ≤ 256` and globals with the
  buffer bounds of `KDrop.okD` (a Hoare-style walk, `KCoreRun.Safe`/`SafeGen`).
* **`genD_step_core`**: for the generated modules `KDrop.genD k N`: every runtime step of a module
  in the bounds of `okD` is a Core runtime step.
* **`toModule_inst`**, **`genD_inst`**: Core instantiation of `KCoreEmit.toModule P name`, with
  the built-ins supplied as host functions (`ImpsOK`), gives `InstR` (globals `P.g0`, memory zero)
  and the lift and the callback at functions `9` and `10` (`EntryAt`, `CbAt`).
* **The lift** (`entry_run`, `genD_lift_core`): `LStep` answers every built-in as a host function,
  the lift's `stream.new`, `waitable-set.new`, `waitable.join` and `task.return` (`lans`) besides the
  runtime's (`bans`); every `HStep` run is an `LStep` run (`hsteps_lsteps`), each `LStep` a Core
  `Step` (`lstep_core`). The Core invocation of the lift runs to `YIELD` with the instance at
  `KDrop.initMSD`; with `genD_inst`, instantiation then the lift leave the module where
  `genD_step_core` takes over.
* **Any arity of `task.return`**: `Rel` and `InstR` leave the arity of the
  `task.return` import open (the callback never calls it), `RetAt hb cs mi n` fixes it, and
  `lans` records any number of `i32` results. `ImpsOKN n` supplies the built-ins with `task.return`
  of `n` values; `toModuleI_inst` instantiates `KCoreEmit.toModule P name` with any import list
  (`KTeeEmit.toModuleT` is the tee's), giving `RetAt … n`; `toModule_ret` gives `RetAt … 1` for
  the stream modules, which `entry_run` now takes.
* **The generated tee** (`KTee.genT`): `genT_safe` (its callback is `CbSafe` when the batch length
  is at most `256`), `genT_step_core` (every runtime step of the tee in `KTee.okT`'s bounds is a
  Core 3.0 runtime step), `entryT_run` (its lift on Core 3.0: two `stream.new`, `waitable-set.new`,
  **one `task.return` of two values**, three joins, then `YIELD`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KCoreRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCore (S BI Out M32 locals FUEL Prog MS CAP BLEN OLEN OOFF)
open Silmaril.Wasm.JcoTool.KDrop (DSt dexec DRStep genD okD)
open Silmaril.Wasm.Component.Streams.Drop (DStore)
open Silmaril.Wasm.JcoTool.KCoreEmit (sCode)

variable {H : Type}

/-- **An `HStep` is a Core 3.0 `Step`** against the stateless host of its host-state transition. -/
theorem hstep_core {Pf : Profile} {hb : BI → H} {ma : Nat} {x y : HQ × Config H}
    (h : HStep Pf hb ma x y) : Step Pf (hostAt hb ma x.1 y.1) x.2 y.2 :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreRun.hstep_core h

/-- **Every checked run of a statement is a Core 3.0 run.** -/
theorem stmt_run (Pf : Profile) (hb : BI → H) (ma nl : Nat) (S : S) (f : Nat) {s s' : DSt} {o : Out}
    {cs : Store H} {F : Frame} (hx : bexec nl S f s = some (o, s')) (h : Rel hb nl ma cs F s) :
    (∀ k, o = .br k → k < M32) ∧ (∀ v, o = .ret v → v < M32) ∧
      ∀ rest : List Admin, ∃ (cs' : Store H) (F' : Frame) (junk : List Admin),
        Rel hb nl ma cs' F' s' ∧ F'.module = F.module ∧ cs'.funcs = cs.funcs ∧
        (o = .norm → junk = []) ∧
        HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, (sCode S).map Admin.plain ++ rest⟩)
          ((s'.st, s'.rp), ⟨cs', F', outCode o ++ junk ++ rest⟩) :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreRun.stmt_run S f hx h

/-- **The checked semantics refines `dexec`.** -/
theorem bexec_dexec {nl : Nat} (S : S) (f : Nat) {s s' : DSt} {o : Out}
    (h : bexec nl S f s = some (o, s')) : dexec S f s = some (o, s') :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreRun.bexec_dexec S f h

/-- **The Core invocation of the callback** runs as `bexec` runs its body to `return code`. -/
theorem invoke_run (Pf : Profile) {hb : BI → H} {ma : Nat} {cs : Store H} {mi : ModuleInst}
    {P : Prog} {a : Nat} {g m : Nat → Nat} {st : DStore} {rp : Option (Nat × Nat)}
    (hI : InstR hb ma cs mi g m) (hcb : CbAt cs mi P a) {x y z : Nat} (hx : x < M32) (hy : y < M32)
    (hz : z < M32) {code : Nat} {s' : DSt}
    (hrun : bexec CBL P.cb FUEL ⟨g, m, locals [x, y, z], st, rp⟩ = some (.ret code, s')) :
    code < M32 ∧ ∃ cs', InstR hb ma cs' mi s'.g s'.m ∧ cs'.funcs = cs.funcs ∧
      HSteps Pf hb ma ((st, rp), invoke cs a ([x, y, z].map (Val.i32 ∘ w)))
        ((s'.st, s'.rp), ⟨cs', {}, vals [Val.i32 (w code)]⟩) :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreRun.invoke_run Pf hI hcb hx hy hz hrun

/-- The callback of `toModule P name` (its third defined function, function `10`) has the code
`CbAt` asks for. -/
theorem toModule_cb (P : Prog) (name : String) :
    (KCoreEmit.toModule P name).funcs[2]? =
      some ⟨KCoreEmit.ix 2, cbLocals, sCode P.cb ++ [.unreachable]⟩ := rfl

/-- **Every step of the drop runtime is a step of the runtime on Core 3.0.** -/
theorem rstep_core (Pf : Profile) {hb : BI → H} {ma : Nat} {P : Prog} {mi : ModuleInst} {a : Nat}
    {st st' : DStore} {ms ms' : MS} {cs : Store H} (hI : InstR hb ma cs mi ms.g ms.m)
    (hcb : CbAt cs mi P a) (hsafe : CbSafe P ms.g) (h : DRStep P st ms st' ms') :
    ∃ cs', CRStep Pf hb ma a (st, cs, ms.rp, ms.mode) (st', cs', ms'.rp, ms'.mode) ∧
      InstR hb ma cs' mi ms'.g ms'.m ∧ CbAt cs' mi P a :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreRun.rstep_core Pf hI hcb hsafe h

/-- The buffer bounds of `KDrop.okD` on the globals. -/
def BufOK (g : Nat → Nat) : Prop := g BLEN ≤ CAP ∧ g OLEN ≤ CAP ∧ g OOFF ≤ g OLEN

/-- **The callback of a generated module is safe** (formerly the open target `Task.genD_safe`):
`CbSafe (genD k N) g` at globals within the buffer bounds, for read sizes `N ≤ 256`. A Hoare-style
walk through `callbackD` (`KCoreRun.Safe`, `KCoreRun.SafeGen`): the guards of `emitS`, `pushS` and
`emitBufS` keep every `i32.store8` and `memory.copy` below `MSZ` (the kernel's code keeps
`BLEN, OLEN ≤ CAP`), the invariant `LI ≤ LN ≤ 256` of `feedLoop` its `i32.load8_u`; `stream.read`
counts at most `N` bytes, a read event at most `256` (`KDrop.wfD`); every divisor is `16`. -/
theorem genD_safe (k : Silmaril.Wasm.Component.Streams.Kernel.KM) {N : Nat} (hN : N ≤ 256)
    (g : Nat → Nat) (hg : BufOK g) : CbSafe (genD k N) g :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreRun.genD_cbSafe k hN g hg

/-- **Every step of the runtime of a generated module**, in the bounds of `okD`, is a step of the
runtime on Core 3.0 (no hypothesis on the callback: `genD_safe`). -/
theorem genD_step_core (Pf : Profile) {hb : BI → H} {ma : Nat}
    {k : Silmaril.Wasm.Component.Streams.Kernel.KM} {N : Nat} (hN : N ≤ 256) {r wh s : Nat}
    {mi : ModuleInst} {a : Nat} {st st' : DStore} {ms ms' : MS} {cs : Store H}
    (hok : okD ms r wh s) (hI : InstR hb ma cs mi ms.g ms.m) (hcb : CbAt cs mi (genD k N) a)
    (h : DRStep (genD k N) st ms st' ms') :
    ∃ cs', CRStep Pf hb ma a (st, cs, ms.rp, ms.mode) (st', cs', ms'.rp, ms'.mode) ∧
      InstR hb ma cs' mi ms'.g ms'.m ∧ CbAt cs' mi (genD k N) a :=
  rstep_core Pf hI hcb (genD_safe k hN ms.g ⟨hok.2.2.2.1, hok.2.2.2.2.1, hok.2.2.2.2.2⟩) h

/-- **Core instantiation of the emitted module gives `CbAt` and `InstR`**: Core 3.0 instantiation
(`Execution.Core.Instantiate`, any profile and host) of `KCoreEmit.toModule P name`, with the eight
imported built-ins supplied as the host functions `hb b` (`ImpsOK`), leaves no code to run (no
segments, no start function); its module instance holds the lift at function `9` (`EntryAt`) and
the callback at function `10` (`CbAt`); its globals hold `P.g0` as `i32`s, its memory `MSZ` zero
bytes, its imports the built-ins (`InstR`). -/
theorem toModule_inst {Pf : Profile} {host : HostSemantics H} {hb : BI → H} {s : Store H}
    {P : Prog} {name : String} {as : List Nat} {c : Config H}
    (hI : Instantiate Pf host s (KCoreEmit.toModule P name) (as.map .func) c) (himp : ImpsOK hb s as) :
    c.code = [] ∧ ∃ ma a₉ a₁₀, InstR hb ma c.store c.frame.module (fun i => P.g0 i % M32) (fun _ => 0) ∧
      c.frame.module.funcs[9]? = some a₉ ∧ EntryAt c.store c.frame.module P a₉ ∧
      c.frame.module.funcs[10]? = some a₁₀ ∧ CbAt c.store c.frame.module P a₁₀ :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Inst.toModule_inst hI himp

theorem initG_lt (k : Silmaril.Wasm.Component.Streams.Kernel.KM) (i : Nat) :
    Silmaril.Wasm.JcoTool.KCore.initG k i < M32 := by
  unfold Silmaril.Wasm.JcoTool.KCore.initG Silmaril.Wasm.JcoTool.KCore.upd
  split
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.pos_of_ne_zero (by decide)

/-- **For a generated module**: instantiation leaves the globals at `initG k`, the memory zero. -/
theorem genD_inst {Pf : Profile} {host : HostSemantics H} {hb : BI → H} {s : Store H}
    {k : Silmaril.Wasm.Component.Streams.Kernel.KM} {N : Nat} {name : String} {as : List Nat}
    {c : Config H} (hI : Instantiate Pf host s (KCoreEmit.toModule (genD k N) name) (as.map .func) c)
    (himp : ImpsOK hb s as) :
    c.code = [] ∧ ∃ ma a₉ a₁₀, InstR hb ma c.store c.frame.module (Silmaril.Wasm.JcoTool.KCore.initG k)
      (fun _ => 0) ∧ c.frame.module.funcs[9]? = some a₉ ∧ EntryAt c.store c.frame.module (genD k N) a₉ ∧
      c.frame.module.funcs[10]? = some a₁₀ ∧ CbAt c.store c.frame.module (genD k N) a₁₀ := by
  have hg : (fun i => (genD k N).g0 i % M32) = Silmaril.Wasm.JcoTool.KCore.initG k :=
    funext fun i => Nat.mod_eq_of_lt (initG_lt k i)
  have h := toModule_inst hI himp
  rw [hg] at h
  exact h

/-- **Every `HStep` run is an `LStep` run** (the runtime's results carry over to the relation that
also answers the lift's built-ins; the task's results are unchanged). -/
theorem hsteps_lsteps {Pf : Profile} {hb : BI → H} {ma : Nat} {x y : HQ × Config H}
    (h : HSteps Pf hb ma x y) (t : List Nat) : LSteps Pf hb ma ((x.1, t), x.2) ((y.1, t), y.2) :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Entry.hsteps_l h t

/-- **An `LStep` is a Core 3.0 `Step`** against the stateless host of its host-state transition
(every built-in, the lift's included, answered by `lansAll`). -/
theorem lstep_core {Pf : Profile} {hb : BI → H} {ma : Nat} {x y : HL × Config H}
    (h : LStep Pf hb ma x y) : Step Pf (hostAtL hb ma x.1 y.1) x.2 y.2 :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Entry.lstep_core h

/-- **The lift on Core 3.0**: the Core invocation of the lift of `KCore.entry` on the input's
readable end `r` runs to `YIELD`, creating the output stream `(r', w')` and the waitable set `ws`
in the drop store, returning `r'` (`task.return`), joining both ends to `ws`, and leaving the
globals `liftG g r w' ws`. -/
theorem entry_run (Pf : Profile) {hb : BI → H} {ma : Nat} {cs : Store H} {mi : ModuleInst} {P : Prog}
    {a : Nat} {g m : Nat → Nat} {st st₁ st₂ st₃ st₄ : DStore} {rp : Option (Nat × Nat)} {t : List Nat}
    {r r' w' ws : Nat} {u₁ u₂ : Silmaril.Wasm.Component.Async.Res}
    (hP : P.entry = Silmaril.Wasm.JcoTool.KCore.entry) (hI : InstR hb ma cs mi g m) (hret : RetAt hb cs mi 1)
    (hen : EntryAt cs mi P a)
    (hr : r < M32) (hnew : Silmaril.Wasm.Component.Streams.Drop.dstep st .streamNew = some (st₁, .ends r' w'))
    (hr' : r' < M32) (hw' : w' < M32)
    (hws : Silmaril.Wasm.Component.Streams.Drop.dstep st₁ .wsNew = some (st₂, .nat ws)) (hws' : ws < M32)
    (hj₁ : Silmaril.Wasm.Component.Streams.Drop.dstep st₂ (.join r ws) = some (st₃, u₁))
    (hj₂ : Silmaril.Wasm.Component.Streams.Drop.dstep st₃ (.join w' ws) = some (st₄, u₂)) :
    ∃ cs', InstR hb ma cs' mi (liftG g r w' ws) m ∧ cs'.funcs = cs.funcs ∧
      LSteps Pf hb ma (((st, rp), t), invoke cs a [Val.i32 (w r)])
        (((st₄, rp), t ++ [r']), ⟨cs', {}, vals [Val.i32 (w 1)]⟩) :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Entry.entry_run Pf hP hI hret hen hr hnew hr' hw' hws hws' hj₁ hj₂

/-- **A generated module from instantiation to the callback runtime, on Core 3.0**: instantiate
`KCoreEmit.toModule (genD k N) name` with the built-ins as host functions; invoke its lift (function
`9`) on the input's readable end `r`; it runs to `YIELD` with the instance at the machine
`KDrop.initMSD k r w' ws` (the state `KDrop.KSys.init` gives every module of a chain) and the
callback (function `10`) in place, so `genD_step_core` applies to every runtime step from there. -/
theorem genD_lift_core (Pf : Profile) {host : HostSemantics H} {hb : BI → H} {s : Store H}
    {k : Silmaril.Wasm.Component.Streams.Kernel.KM} {N : Nat} {name : String} {as : List Nat}
    {c : Config H} (hI : Instantiate Pf host s (KCoreEmit.toModule (genD k N) name) (as.map .func) c)
    (himp : ImpsOK hb s as) {st st₁ st₂ st₃ st₄ : DStore} {rp : Option (Nat × Nat)} {t : List Nat}
    {r r' w' ws : Nat} {u₁ u₂ : Silmaril.Wasm.Component.Async.Res} (hr : r < M32)
    (hnew : Silmaril.Wasm.Component.Streams.Drop.dstep st .streamNew = some (st₁, .ends r' w'))
    (hr' : r' < M32) (hw' : w' < M32)
    (hws : Silmaril.Wasm.Component.Streams.Drop.dstep st₁ .wsNew = some (st₂, .nat ws)) (hws' : ws < M32)
    (hj₁ : Silmaril.Wasm.Component.Streams.Drop.dstep st₂ (.join r ws) = some (st₃, u₁))
    (hj₂ : Silmaril.Wasm.Component.Streams.Drop.dstep st₃ (.join w' ws) = some (st₄, u₂)) :
    c.code = [] ∧ ∃ ma a₉ a₁₀ cs', c.frame.module.funcs[9]? = some a₉ ∧
      c.frame.module.funcs[10]? = some a₁₀ ∧
      LSteps Pf hb ma (((st, rp), t), invoke c.store a₉ [Val.i32 (w r)])
        (((st₄, rp), t ++ [r']), ⟨cs', {}, vals [Val.i32 (w 1)]⟩) ∧
      InstR hb ma cs' c.frame.module (Silmaril.Wasm.JcoTool.KDrop.initMSD k r w' ws).g
        (Silmaril.Wasm.JcoTool.KDrop.initMSD k r w' ws).m ∧
      CbAt cs' c.frame.module (genD k N) a₁₀ := by
  obtain ⟨hc, ma, a₉, a₁₀, hI₀, h₉, hen, h₁₀, hcb⟩ := genD_inst hI himp
  have hret := Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Inst.toModule_ret hI himp
  obtain ⟨cs', hI', hfs, hrun⟩ := entry_run Pf (t := t) (rp := rp) rfl hI₀ hret hen hr hnew hr' hw' hws hws' hj₁ hj₂
  exact ⟨hc, ma, a₉, a₁₀, cs', h₉, h₁₀, hrun, hI',
    Silmaril.Proofs.Wasm.JcoTool.KCoreRun.cbAt_funcs hcb hfs⟩

/-! ## The lift's drop-store calls -/

open Silmaril.Wasm.Component.Streams.Drop (DStore dstep) in
open Silmaril.Wasm.Component.Async (upd) in
/-- **The lift's four drop-store calls succeed** on every store in which `r` is a readable end
below the next free handle: `stream.new` gives the next two handles, `waitable-set.new` the one
after, and both joins succeed. -/
theorem lift_calls {st : DStore} {r s : Nat}
    (ht : st.tbl r = some (.streamR s)) (hr : r < st.next) :
    ∃ st₁ st₂ st₃ st₄ u₁ u₂,
      dstep st .streamNew = some (st₁, .ends st.next (st.next + 1)) ∧
      dstep st₁ .wsNew = some (st₂, .nat (st.next + 2)) ∧
      dstep st₂ (.join r (st.next + 2)) = some (st₃, u₁) ∧
      dstep st₃ (.join (st.next + 1) (st.next + 2)) = some (st₄, u₂) := by
  have h0 : r ≠ st.next := by omega
  have h1 : r ≠ st.next + 1 := by omega
  have h2 : r ≠ st.next + 2 := by omega
  let st₁ : DStore := ⟨st.next + 2,
    upd (upd st.tbl st.next (some (.streamR st.next))) (st.next + 1) (some (.streamW st.next)),
    upd st.chans st.next {}, st.joined⟩
  let st₂ : DStore := ⟨st.next + 3, upd st₁.tbl (st.next + 2) (some .wset), st₁.chans, st₁.joined⟩
  let st₃ : DStore := ⟨st₂.next, st₂.tbl, st₂.chans, upd st₂.joined r (some (st.next + 2))⟩
  let st₄ : DStore := ⟨st₃.next, st₃.tbl, st₃.chans,
    upd st₃.joined (st.next + 1) (some (st.next + 2))⟩
  refine ⟨st₁, st₂, st₃, st₄, .unit, .unit, rfl, rfl, ?_, ?_⟩
  · simp [st₃, st₂, st₁, dstep, upd, h0, h1, h2, ht]
  · simp [st₄, st₃, st₂, st₁, dstep, upd]

open Silmaril.Wasm.Component.Streams.Drop (DStore dstep) in
/-- **Instantiation and the lift on Core 3.0, with no hypothesis on the drop store's answers**:
`genD_lift_core` on a store whose input `r` is a readable end below the next free handle, with
room for three more handles below `2 ^ 32`; the module's output stream and set are the next three
handles. -/
theorem genD_lift_core_fresh (Pf : Profile) {host : HostSemantics H} {hb : BI → H} {s : Store H}
    {k : Silmaril.Wasm.Component.Streams.Kernel.KM} {N : Nat} {name : String} {as : List Nat}
    {c : Config H} (hI : Instantiate Pf host s (KCoreEmit.toModule (genD k N) name) (as.map .func) c)
    (himp : ImpsOK hb s as) {st : DStore} {rp : Option (Nat × Nat)} {t : List Nat} {r sr : Nat}
    (ht : st.tbl r = some (.streamR sr)) (hr : r < st.next) (hn : st.next + 3 ≤ M32) :
    c.code = [] ∧ ∃ st₄ ma a₉ a₁₀ cs', c.frame.module.funcs[9]? = some a₉ ∧
      c.frame.module.funcs[10]? = some a₁₀ ∧
      LSteps Pf hb ma (((st, rp), t), invoke c.store a₉ [Val.i32 (w r)])
        (((st₄, rp), t ++ [st.next]), ⟨cs', {}, vals [Val.i32 (w 1)]⟩) ∧
      InstR hb ma cs' c.frame.module
        (Silmaril.Wasm.JcoTool.KDrop.initMSD k r (st.next + 1) (st.next + 2)).g
        (Silmaril.Wasm.JcoTool.KDrop.initMSD k r (st.next + 1) (st.next + 2)).m ∧
      CbAt cs' c.frame.module (genD k N) a₁₀ := by
  obtain ⟨st₁, st₂, st₃, st₄, u₁, u₂, hnew, hws, hj₁, hj₂⟩ := lift_calls ht hr
  obtain ⟨hc, ma, a₉, a₁₀, cs', h9, h10, hrun, hI', hcb⟩ :=
    genD_lift_core Pf (t := t) (rp := rp) hI himp (by omega) hnew (by omega) (by omega) hws
      (by omega) hj₁ hj₂
  exact ⟨hc, st₄, ma, a₉, a₁₀, cs', h9, h10, hrun, hI', hcb⟩

/-! ## Any arity of `task.return`, and the generated tee -/

/-- **Instantiation of the emitted module with any imports** (`KTeeEmit.toModuleT` is
`toModule (genT N) name` with `task.return` of two values): `toModule_inst`, and the instance's
`task.return` takes `n` values. -/
theorem toModuleI_inst {Pf : Profile} {host : HostSemantics H} {hb : BI → H} {s : Store H}
    {P : Prog} {name : String} {is : List Import} {n : Nat} {as : List Nat} {c : Config H}
    (hI : Instantiate Pf host s { KCoreEmit.toModule P name with imports := is } (as.map .func) c)
    (himp : ImpsOKN n hb s as) :
    c.code = [] ∧ ∃ ma a₉ a₁₀, InstR hb ma c.store c.frame.module (fun i => P.g0 i % M32) (fun _ => 0) ∧
      RetAt hb c.store c.frame.module n ∧
      c.frame.module.funcs[9]? = some a₉ ∧ EntryAt c.store c.frame.module P a₉ ∧
      c.frame.module.funcs[10]? = some a₁₀ ∧ CbAt c.store c.frame.module P a₁₀ :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Inst.toModuleI_inst hI himp

/-- `ImpsOK` is `ImpsOKN 1`. -/
theorem impsOK_N {hb : BI → H} {s : Store H} {as : List Nat} (h : ImpsOK hb s as) : ImpsOKN 1 hb s as :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Inst.impsOK_N h

/-- **The callback of the generated tee is safe** for read sizes `N ≤ 256`, at globals whose
batch length is at most `256`. -/
theorem genT_safe {N : Nat} (hN : N ≤ 256) (g : Nat → Nat) (hg : g KTee.LENg ≤ 256) :
    CbSafe (KTee.genT N) g :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Tee.genT_cbSafe hN g hg

/-- **Every runtime step of the generated tee** whose batch length is at most `256` (as
`KTee.okT` keeps it) is a step of the runtime on Core 3.0. -/
theorem genT_step_core (Pf : Profile) {hb : BI → H} {ma : Nat} {N : Nat} (hN : N ≤ 256)
    {mi : ModuleInst} {a : Nat} {st st' : DStore} {ms ms' : MS} {cs : Store H}
    (hL : ms.g KTee.LENg ≤ 256) (hI : InstR hb ma cs mi ms.g ms.m) (hcb : CbAt cs mi (KTee.genT N) a)
    (h : DRStep (KTee.genT N) st ms st' ms') :
    ∃ cs', CRStep Pf hb ma a (st, cs, ms.rp, ms.mode) (st', cs', ms'.rp, ms'.mode) ∧
      InstR hb ma cs' mi ms'.g ms'.m ∧ CbAt cs' mi (KTee.genT N) a :=
  rstep_core Pf hI hcb (genT_safe hN ms.g hL) h

open Silmaril.Wasm.JcoTool.KCore (upd INSR OUTSW WS) in
/-- **The tee's lift on Core 3.0**: the Core invocation of the lift of `KTee.entryT` on the input's
readable end `r` runs to `YIELD`, creating the outputs `(r₀, w₀)`, `(r₁, w₁)` and the set `ws`,
returning `r₀` and `r₁` with **one `task.return` of two values**, joining the input and both
writable ends to `ws`, and leaving the globals with the four handles. -/
theorem entryT_run (Pf : Profile) {hb : BI → H} {ma : Nat} {cs : Store H} {mi : ModuleInst} {P : Prog}
    {a : Nat} {g m : Nat → Nat} {st st₁ st₂ st₃ st₄ st₅ st₆ : DStore} {rp : Option (Nat × Nat)}
    {t : List Nat} {r r₀ w₀ r₁ w₁ ws : Nat} {u₁ u₂ u₃ : Silmaril.Wasm.Component.Async.Res}
    (hP : P.entry = KTee.entryT) (hI : InstR hb ma cs mi g m) (hret : RetAt hb cs mi 2)
    (hen : EntryAt cs mi P a) (hr : r < M32)
    (hn₀ : Silmaril.Wasm.Component.Streams.Drop.dstep st .streamNew = some (st₁, .ends r₀ w₀)) (hr₀ : r₀ < M32)
    (hw₀ : w₀ < M32)
    (hn₁ : Silmaril.Wasm.Component.Streams.Drop.dstep st₁ .streamNew = some (st₂, .ends r₁ w₁)) (hr₁ : r₁ < M32)
    (hw₁ : w₁ < M32)
    (hws : Silmaril.Wasm.Component.Streams.Drop.dstep st₂ .wsNew = some (st₃, .nat ws)) (hws' : ws < M32)
    (hj₁ : Silmaril.Wasm.Component.Streams.Drop.dstep st₃ (.join r ws) = some (st₄, u₁))
    (hj₂ : Silmaril.Wasm.Component.Streams.Drop.dstep st₄ (.join w₀ ws) = some (st₅, u₂))
    (hj₃ : Silmaril.Wasm.Component.Streams.Drop.dstep st₅ (.join w₁ ws) = some (st₆, u₃)) :
    ∃ cs', InstR hb ma cs' mi (upd (upd (upd (upd g INSR r) OUTSW w₀) KTee.W1g w₁) WS ws) m ∧
      cs'.funcs = cs.funcs ∧
      LSteps Pf hb ma (((st, rp), t), invoke cs a [Val.i32 (w r)])
        (((st₆, rp), t ++ [r₀, r₁]), ⟨cs', {}, vals [Val.i32 (w 1)]⟩) :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreRun.EntryT.entryT_run Pf hP hI hret hen hr hn₀ hr₀ hw₀ hn₁ hr₁ hw₁ hws hws'
    hj₁ hj₂ hj₃

/-- `CbAt` depends on the store only through its functions. -/
theorem cbAt_of_funcs {cs cs' : Store H} {mi : ModuleInst} {P : Prog} {a : Nat} (hcb : CbAt cs mi P a)
    (hf : cs'.funcs = cs.funcs) : CbAt cs' mi P a :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreRun.cbAt_funcs hcb hf

end Silmaril.Wasm.JcoTool.KCoreRun
