module

public import Silmaril.Wasm.JcoTool.KCoreHost.Defs
public import Silmaril.Wasm.JcoTool.KCoreRun.Thms
public import Silmaril.Proofs.Wasm.JcoTool.KCoreHost.Inst
public import Silmaril.Wasm.Validation.Check.ValidateFinal

/-!
# The host store supplies the built-ins: `ImpsOK` discharged

* **`impsOK_host`**: `KCoreRun.ImpsOK hb (hostStore hb) hostAddrs`, for every `hb`.
* **`genD_inst_host`**, **`genD_lift_host`**: `KCoreRun.genD_inst` and
  `KCoreRun.genD_lift_core_fresh` on the host store, with no `ImpsOK` hypothesis: every Core 3.0
  instantiation of `KCoreEmit.toModule (genD k N) name` against the host store's built-ins, then
  its lift on a fresh input, ends at the machine `KDrop.initMSD` with the callback in place.

* **The instantiation exists**:
  `instantiate?_some` (silmaril's computable instantiation of the emitted module, with any
  program and import list, succeeds on every store), `inst_exists` (a **valid** emitted module
  has a Core 3.0 instantiation on the host store: the extern types of its imports are the host
  functions' types), and **`genD_lift_valid`**: when silmaril's validator accepts the module
  (`validate? … |>.isSome`, decidable: `wasm-streams-gen valid` runs it), there is an
  instantiation, and every instantiation followed by the lift ends at `KDrop.initMSD`. The
  `Instantiate` hypothesis of `genD_inst_host`/`genD_lift_host` is so replaced by the decidable
  check of validity, which `tools/wasm-streams/tests/wat-cert.sh` runs on every module the tools
  emit in the tests. That every `genD k N` is valid (a typing proof of `KCoreEmit.sCode` for all
  kernels) is not proved.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KCoreHost

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCore (BI M32)
open Silmaril.Wasm.JcoTool.KCoreRun (ImpsOK InstR EntryAt CbAt LSteps w)
open Silmaril.Wasm.JcoTool.KDrop (genD)
open Silmaril.Wasm.Component.Streams.Drop (DStore)

variable {H : Type}

/-- **The host store supplies the eight built-ins.** -/
theorem impsOK_host (hb : BI → H) : ImpsOK hb (hostStore hb) hostAddrs := by
  refine ⟨rfl, fun b => ?_⟩
  cases b
  all_goals exact ⟨_, _, _, _, rfl, rfl, rfl, Expand.iff.mpr rfl, rfl⟩

/-- **Instantiation on the host store** (`KCoreRun.genD_inst` without `ImpsOK`). -/
theorem genD_inst_host {Pf : Profile} {host : HostSemantics H} {hb : BI → H}
    {k : Silmaril.Wasm.Component.Streams.Kernel.KM} {N : Nat} {name : String} {c : Config H}
    (hI : Instantiate Pf host (hostStore hb) (KCoreEmit.toModule (genD k N) name)
      (hostAddrs.map .func) c) :
    c.code = [] ∧ ∃ ma a₉ a₁₀, InstR hb ma c.store c.frame.module (Silmaril.Wasm.JcoTool.KCore.initG k)
      (fun _ => 0) ∧ c.frame.module.funcs[9]? = some a₉ ∧ EntryAt c.store c.frame.module (genD k N) a₉ ∧
      c.frame.module.funcs[10]? = some a₁₀ ∧ CbAt c.store c.frame.module (genD k N) a₁₀ :=
  KCoreRun.genD_inst hI (impsOK_host hb)

/-- **Instantiation and the lift on the host store** (`KCoreRun.genD_lift_core_fresh` without
`ImpsOK`): on any drop store whose input `r` is a readable end below the next free handle. -/
theorem genD_lift_host (Pf : Profile) {host : HostSemantics H} {hb : BI → H}
    {k : Silmaril.Wasm.Component.Streams.Kernel.KM} {N : Nat} {name : String} {c : Config H}
    (hI : Instantiate Pf host (hostStore hb) (KCoreEmit.toModule (genD k N) name)
      (hostAddrs.map .func) c)
    {st : DStore} {rp : Option (Nat × Nat)} {t : List Nat} {r sr : Nat}
    (ht : st.tbl r = some (.streamR sr)) (hr : r < st.next) (hn : st.next + 3 ≤ M32) :
    c.code = [] ∧ ∃ st₄ ma a₉ a₁₀ cs', c.frame.module.funcs[9]? = some a₉ ∧
      c.frame.module.funcs[10]? = some a₁₀ ∧
      LSteps Pf hb ma (((st, rp), t), invoke c.store a₉ [Val.i32 (w r)])
        (((st₄, rp), t ++ [st.next]), ⟨cs', {}, vals [Val.i32 (w 1)]⟩) ∧
      InstR hb ma cs' c.frame.module
        (Silmaril.Wasm.JcoTool.KDrop.initMSD k r (st.next + 1) (st.next + 2)).g
        (Silmaril.Wasm.JcoTool.KDrop.initMSD k r (st.next + 1) (st.next + 2)).m ∧
      CbAt cs' c.frame.module (genD k N) a₁₀ :=
  KCoreRun.genD_lift_core_fresh Pf hI (impsOK_host hb) ht hr hn

/-- **Silmaril's computable instantiation of an emitted module succeeds** on every store with the
eight imported functions at `hostAddrs` (any program, any import list). -/
theorem instantiate?_some (P : Silmaril.Wasm.JcoTool.KCore.Prog) (name : String) (is : List Import)
    (s : Store H) :
    (instantiate? evalConst? s { KCoreEmit.toModule P name with imports := is } (hostAddrs.map .func)).isSome :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreHost.instantiate?_some P name is s

/-- The closed types of `KCoreEmit.types`. -/
theorem allocTypes_types : allocTypes Silmaril.Wasm.JcoTool.KCoreEmit.types =
    Silmaril.Wasm.JcoTool.KCoreEmit.types.map fun rt => .defn (liftRec rt) 0 :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreHost.allocTypes_types

/-- **A valid emitted module has a Core 3.0 instantiation on the host store.** -/
theorem inst_exists {Pf : Profile} {host : HostSemantics H} (hb : BI → H)
    (P : Silmaril.Wasm.JcoTool.KCore.Prog) (name : String) (hv : ModuleValid (KCoreEmit.toModule P name)) :
    ∃ c, Instantiate Pf host (hostStore hb) (KCoreEmit.toModule P name) (hostAddrs.map .func) c :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreHost.inst_exists hb P name hv

/-- **A generated module that silmaril's validator accepts is instantiated and lifted on Core
3.0**: there is an instantiation on the host store, and (`genD_lift_host`) every one, followed by
the lift on a fresh input, ends at the machine `KDrop.initMSD` with the callback in place. -/
theorem genD_lift_valid (Pf : Profile) {host : HostSemantics H} {hb : BI → H}
    {k : Silmaril.Wasm.Component.Streams.Kernel.KM} {N : Nat} {name : String}
    (hv : (validate? (KCoreEmit.toModule (genD k N) name)).isSome = true)
    {st : DStore} {rp : Option (Nat × Nat)} {t : List Nat} {r sr : Nat}
    (ht : st.tbl r = some (.streamR sr)) (hr : r < st.next) (hn : st.next + 3 ≤ M32) :
    ∃ c, Instantiate Pf host (hostStore hb) (KCoreEmit.toModule (genD k N) name) (hostAddrs.map .func) c ∧
      c.code = [] ∧ ∃ st₄ ma a₉ a₁₀ cs', c.frame.module.funcs[9]? = some a₉ ∧
      c.frame.module.funcs[10]? = some a₁₀ ∧
      LSteps Pf hb ma (((st, rp), t), invoke c.store a₉ [Val.i32 (w r)])
        (((st₄, rp), t ++ [st.next]), ⟨cs', {}, vals [Val.i32 (w 1)]⟩) ∧
      InstR hb ma cs' c.frame.module
        (Silmaril.Wasm.JcoTool.KDrop.initMSD k r (st.next + 1) (st.next + 2)).g
        (Silmaril.Wasm.JcoTool.KDrop.initMSD k r (st.next + 1) (st.next + 2)).m ∧
      CbAt cs' c.frame.module (genD k N) a₁₀ := by
  obtain ⟨c, hc⟩ := inst_exists (Pf := Pf) (host := host) hb _ name (validate?_isSome_iff.mp hv)
  exact ⟨c, hc, genD_lift_host Pf hc ht hr hn⟩

end Silmaril.Wasm.JcoTool.KCoreHost
