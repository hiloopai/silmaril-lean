module

public import Silmaril.Wasm.JcoTool.KTeeCore.Defs
public import Silmaril.Proofs.Wasm.JcoTool.KTeeCore.Main

/-!
# The generated tee on Core 3.0

Proofs in `Silmaril.Proofs.Wasm.JcoTool.KTeeCore.Main` and `Silmaril.Proofs.Wasm.JcoTool.KCoreRun.{SafeTee,
EntryT,Inst}` (exported by `KCoreRun.Thms`). An earlier step left the generated tee (`KTee.genT N`,
the module `KTeeEmit.toModuleT N name` whose bytes `wasm-streams-gen tee -o` writes) without a Core
3.0 link, because `KCoreRun` fixed the arity of `task.return` at one value. With that arity
generalised (`KCoreRun.RetAt`, `ImpsOKN`, `lans` of any number of `i32`s):

* **`impsOKT_host`**: the tee's host store `hostStoreT hb` supplies its eight imports, with
  `task.return` of two values (`ImpsOKN 2`).
* **`genT_inst_host`**: Core 3.0 instantiation of `toModuleT N name` on that store leaves no code
  to run; the instance holds the lift at function `9` and the callback at `10`, zero globals and
  memory, and a `task.return` of two values.
* **`genT_lift_host`**: then the Core invocation of the lift on a fresh input `r` (any drop store
  in which `r` is a readable end below the next free handle `n`) runs to `YIELD`, creating the two
  output streams `(n, n + 1)`, `(n + 2, n + 3)` and the set `n + 4`, **returning `n` and `n + 2`
  with one `task.return`**, joining the three ends; the instance then holds the machine
  `KTee.initMST r (n + 1) (n + 3) (n + 4)` (the machine `KTee.init_rel` relates to the tee node's
  start).
* **`genT_core_step`** (`KCoreRun.genT_step_core`): from there, every step of the tee's runtime
  (`KDrop.DRStep (genT N)`) whose batch length is at most `256` (as `KTee.okT`, part of the
  simulation relation `KTee.RelT`, keeps it) is a step of the runtime on Core 3.0: Core
  invocations of the callback, with `stream.read`, `stream.write` and the drops as host calls. The
  callback is safe (`KCoreRun.genT_safe`: every `dexec` run is a `bexec` run, a Hoare-style walk,
  `KCoreRun.Tee`).

So the generated tee's lift and every callback invocation run on Core 3.0 as `KTee`'s model says,
and `KTee.step_sim` relates each of those steps to a step of `Net`'s tee node.

* **`genT_lift_valid`**: when silmaril's validator accepts the tee module (`validate?`, decidable;
  `wasm-streams-gen valid-tee` runs it), there is an instantiation on the host store
  (`instT_exists`), and every one, followed by the lift, ends at `initMST`: the `Instantiate`
  hypothesis becomes a decidable check.

What is not proved here (see `docs/projects/wasm-components.md`, *streams, an earlier step*): the backward
direction for networks with tees (a Core step of the tee is a model step: it needs that the tee's
callback never traps in reachable states, part of the tee's liveness), and the validity of
`toModuleT N name` for every `N` (checked by `validate?`, not proved).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KTeeCore

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCore (BI M32 MS)
open Silmaril.Wasm.JcoTool.KCoreRun (ImpsOKN InstR RetAt EntryAt CbAt LSteps CRStep w)
open Silmaril.Wasm.JcoTool.KTee (genT initMST)
open Silmaril.Wasm.JcoTool.KDrop (DRStep)
open Silmaril.Wasm.Component.Streams.Drop (DStore)

variable {H : Type}

/-- **The tee's host store supplies its eight imports** (`task.return` of two values). -/
theorem impsOKT_host (hb : BI → H) : ImpsOKN 2 hb (hostStoreT hb) KCoreHost.hostAddrs :=
  Silmaril.Proofs.Wasm.JcoTool.KTeeCore.impsOKT_host hb

/-- **Instantiation of the generated tee on its host store.** -/
theorem genT_inst_host {Pf : Profile} {host : HostSemantics H} {hb : BI → H} {N : Nat} {name : String}
    {c : Config H}
    (hI : Instantiate Pf host (hostStoreT hb) (Silmaril.Wasm.JcoTool.KTeeEmit.toModuleT N name)
      (KCoreHost.hostAddrs.map .func) c) :
    c.code = [] ∧ ∃ ma a₉ a₁₀, InstR hb ma c.store c.frame.module (fun _ => 0) (fun _ => 0) ∧
      RetAt hb c.store c.frame.module 2 ∧
      c.frame.module.funcs[9]? = some a₉ ∧ EntryAt c.store c.frame.module (genT N) a₉ ∧
      c.frame.module.funcs[10]? = some a₁₀ ∧ CbAt c.store c.frame.module (genT N) a₁₀ :=
  Silmaril.Proofs.Wasm.JcoTool.KTeeCore.genT_inst_host hI

/-- **Instantiation and the lift of the generated tee on Core 3.0**, on a fresh input: the lift
returns both readable ends with one `task.return` and leaves the machine `initMST`. -/
theorem genT_lift_host (Pf : Profile) {host : HostSemantics H} {hb : BI → H} {N : Nat} {name : String}
    {c : Config H}
    (hI : Instantiate Pf host (hostStoreT hb) (Silmaril.Wasm.JcoTool.KTeeEmit.toModuleT N name)
      (KCoreHost.hostAddrs.map .func) c)
    {st : DStore} {rp : Option (Nat × Nat)} {t : List Nat} {r sr : Nat}
    (ht : st.tbl r = some (.streamR sr)) (hr : r < st.next) (hn : st.next + 5 ≤ M32) :
    c.code = [] ∧ ∃ st₆ ma a₉ a₁₀ cs', c.frame.module.funcs[9]? = some a₉ ∧
      c.frame.module.funcs[10]? = some a₁₀ ∧
      LSteps Pf hb ma (((st, rp), t), invoke c.store a₉ [Val.i32 (w r)])
        (((st₆, rp), t ++ [st.next, st.next + 2]), ⟨cs', {}, vals [Val.i32 (w 1)]⟩) ∧
      InstR hb ma cs' c.frame.module (initMST r (st.next + 1) (st.next + 3) (st.next + 4)).g
        (initMST r (st.next + 1) (st.next + 3) (st.next + 4)).m ∧
      CbAt cs' c.frame.module (genT N) a₁₀ :=
  Silmaril.Proofs.Wasm.JcoTool.KTeeCore.genT_lift_host Pf hI ht hr hn

/-- **Every runtime step of the generated tee is a Core 3.0 runtime step** (batch length at most
`256`, as `KTee.okT` keeps it). -/
theorem genT_core_step (Pf : Profile) {hb : BI → H} {ma : Nat} {N : Nat} (hN : N ≤ 256)
    {mi : ModuleInst} {a : Nat} {st st' : DStore} {ms ms' : MS} {cs : Store H}
    (hL : ms.g KTee.LENg ≤ 256) (hI : InstR hb ma cs mi ms.g ms.m) (hcb : CbAt cs mi (genT N) a)
    (h : DRStep (genT N) st ms st' ms') :
    ∃ cs', CRStep Pf hb ma a (st, cs, ms.rp, ms.mode) (st', cs', ms'.rp, ms'.mode) ∧
      InstR hb ma cs' mi ms'.g ms'.m ∧ CbAt cs' mi (genT N) a :=
  Silmaril.Wasm.JcoTool.KCoreRun.genT_step_core Pf hN hL hI hcb h

/-- The simulation relation of the tee keeps the batch length within `256`: the bound
`genT_core_step` needs, on every machine `KTee.RelT` relates to a live node. -/
theorem relT_len {r w₀ w₁ s : Nat} {ms : MS} {x : Silmaril.Wasm.Component.Streams.Net.NSt Unit}
    (h : KTee.RelT r w₀ w₁ s ms x) (hx : ms.mode ≠ .exited) : ms.g KTee.LENg ≤ 256 := by
  obtain ⟨-, h⟩ := h
  rw [ite_eq_right hx] at h
  exact h.2.1.2.2.2.2.1

/-- **A valid tee module has a Core 3.0 instantiation on its host store.** -/
theorem instT_exists {Pf : Profile} {host : HostSemantics H} (hb : BI → H) (N : Nat) (name : String)
    (hv : ModuleValid (Silmaril.Wasm.JcoTool.KTeeEmit.toModuleT N name)) :
    ∃ c, Instantiate Pf host (hostStoreT hb) (Silmaril.Wasm.JcoTool.KTeeEmit.toModuleT N name)
      (KCoreHost.hostAddrs.map .func) c :=
  Silmaril.Proofs.Wasm.JcoTool.KTeeCore.instT_exists hb N name hv

/-- **A tee module that silmaril's validator accepts is instantiated and lifted on Core 3.0.** -/
theorem genT_lift_valid (Pf : Profile) {host : HostSemantics H} {hb : BI → H} {N : Nat} {name : String}
    (hv : (validate? (Silmaril.Wasm.JcoTool.KTeeEmit.toModuleT N name)).isSome = true)
    {st : DStore} {rp : Option (Nat × Nat)} {t : List Nat} {r sr : Nat}
    (ht : st.tbl r = some (.streamR sr)) (hr : r < st.next) (hn : st.next + 5 ≤ M32) :
    ∃ c, Instantiate Pf host (hostStoreT hb) (Silmaril.Wasm.JcoTool.KTeeEmit.toModuleT N name)
        (KCoreHost.hostAddrs.map .func) c ∧
      c.code = [] ∧ ∃ st₆ ma a₉ a₁₀ cs', c.frame.module.funcs[9]? = some a₉ ∧
      c.frame.module.funcs[10]? = some a₁₀ ∧
      LSteps Pf hb ma (((st, rp), t), invoke c.store a₉ [Val.i32 (w r)])
        (((st₆, rp), t ++ [st.next, st.next + 2]), ⟨cs', {}, vals [Val.i32 (w 1)]⟩) ∧
      InstR hb ma cs' c.frame.module (initMST r (st.next + 1) (st.next + 3) (st.next + 4)).g
        (initMST r (st.next + 1) (st.next + 3) (st.next + 4)).m ∧
      CbAt cs' c.frame.module (genT N) a₁₀ := by
  obtain ⟨c, hc⟩ := instT_exists (Pf := Pf) (host := host) hb N name (validate?_isSome_iff.mp hv)
  exact ⟨c, hc, genT_lift_host Pf hc ht hr hn⟩

end Silmaril.Wasm.JcoTool.KTeeCore
