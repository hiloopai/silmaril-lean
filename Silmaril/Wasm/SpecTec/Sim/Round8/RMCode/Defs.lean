module

public import Silmaril.Wasm.SpecTec.Sim.Round8.RMHost.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Thms

/-!
# Round 8, memory SIMD: `Step_read` and `Step` through the code-erased store (definitions)

Round 8, pass 1 proved the `Step_pure` obligation of `NullHost.RestMSHC` at memory-SIMD-free
code by moving to a store of host functions (`RMHost.hostify`). `Step_read` and `Step` read the
store, so their firings must move too. `Round8.CodeErase` shows that the evaluator commutes with
`eraseC`, which replaces the contents `u` of every `CODE` field by `hostC u`, the code of a host
function named `enc u` (an injective name). This topic uses a matching Core store:

* `codeVD hn fi`: the `CODE` field of `funcInstVD hn fi`;
* `hostSFI hn fi`: `fi` with its code replaced by the host function `enc (codeVD hn fi)`, over the
  host type `String`; `hostifyS hn s`: the store with every function instance so replaced. Its
  image under `configV id` is the `eraseC` image of `configVD hn` (at memory-SIMD-free code,
  `Round8.RMCode.eraseC_configVD`).
* `FiresEraseD env hn x i`: rule `i` of `x`, fired at the `configVD` image of a typed configuration
  with memory-SIMD-free code, also fires at the `eraseC` image. This is the declarative
  (`Fires`) counterpart of `Round8.CodeErase.derives_erase_sim`; it is the IL fact this topic
  assumes.
* `RestMSHCQ`: `RMHost.RestMSHCP` with the `Step_read` and `Step` obligations at memory-SIMD-free
  code replaced by `FiresEraseD` for the rules concerned, except `Step` rule 7 (`call_ref-func`,
  which reads `CODE`); `OpenRMRestDPQ`: `RMHost.OpenRMRestDPP` with it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.RMCode

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round6.MemSimd (AdminsMS NoMemSimd)
open Round6.Target (CastRedex)
open Round7.MemSimd (BoundedSelM configVD adminsToVD TypedD BwdUpToD msReadRules stepMSRules)
open Round7.HostD (BD)

variable {H : Type}

/-- **The `CODE` field of `funcInstVD hn fi`.** -/
def codeVD (hn : H → String) (fi : FuncInst H) : Value :=
  match fi.code with
  | .wasm fn => .case "FUNC" (.tuple [Silmaril.SpecTec.Equiv.Execution.pctV fn.type.toNat,
      .list (fn.locals.map fun t => .case "LOCAL" (Encode.toValue t)),
      .list (Round7.MemSimd.instrsToVD fn.body)])
  | .host h => .case "_HOSTFUNC" (.text (hn h))

/-- **A function instance as the host function named by its erased code.** -/
def hostSFI (hn : H → String) (fi : FuncInst H) : FuncInst String :=
  ⟨fi.type, fi.module, .host (CodeErase.Swap.enc (codeVD hn fi))⟩

/-- **The store with every function instance a host function named by its code.** -/
def hostifyS (hn : H → String) (s : Store H) : Store String :=
  { tags := s.tags, globals := s.globals, mems := s.mems, tables := s.tables,
    funcs := s.funcs.map (hostSFI hn), datas := s.datas, elems := s.elems, structs := s.structs,
    arrays := s.arrays, exns := s.exns }

/-- The configuration `c` over `hostifyS hn c.store`. -/
def hostC (hn : H → String) (c : Config H) : Config String :=
  ⟨hostifyS hn c.store, c.frame, c.code⟩

/-- **Rule `i` of `x` keeps firing when the function code is erased**, at the `configVD` images of
typed configurations whose code holds no memory SIMD instruction. -/
def FiresEraseD (env : Env) (hn : H → String) (x : Silmaril.SpecTec.IL.Id) (i : Nat) : Prop :=
  ∀ (c : Config H) (w : Value), AdminsMS c.code → TypedD env hn c →
    Fires env x i (.tuple [configVD hn c, w]) →
    Fires env x i (CodeErase.Swap.eraseC (.tuple [configVD hn c, w]))

/-- **`RMHost.RestMSHCP` with the `Step_read` and `Step` obligations at memory-SIMD-free code
replaced by `FiresEraseD`** (and `Step` rule 7 kept everywhere). -/
structure RestMSHCQ (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- `Step_pure`, at code holding memory SIMD instructions (as `RestMSHCP.pure`). -/
  pure : ∀ (i : Nat) (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    ¬ AdminsMS is → Round7.MSRest.VMS ⟨s, f, is⟩ →
    TypedD (simEnv (Prims.builtins P hn host)) hn ⟨s, f, is⟩ →
    Fires (simEnv (Prims.builtins P hn host)) "Step_pure" i (.tuple [.list (adminsToVD is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step_read`, at code holding memory SIMD instructions. -/
  read : ∀ (i : Nat), i ∉ msReadRules → ∀ (c : Config H) (w : Value), ¬ AdminsMS c.code →
    Round7.MSRest.VMS c → TypedD (simEnv (Prims.builtins P hn host)) hn c →
    Fires (simEnv (Prims.builtins P hn host)) "Step_read" i (.tuple [configVD hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩
  /-- `Step`, at code holding memory SIMD instructions, and rule 7 everywhere. -/
  step : ∀ (i : Nat), 6 ≤ i → i ∉ stepMSRules → i ≠ 8 → i ≠ 9 → ∀ (c : Config H) (w : Value),
    (¬ AdminsMS c.code ∨ i = 7) → Round7.MSRest.VMS c →
    TypedD (simEnv (Prims.builtins P hn host)) hn c →
    Fires (simEnv (Prims.builtins P hn host)) "Step" i (.tuple [configVD hn c, w]) →
    BwdUpToD hn P host c w
  /-- The `Step_read` rules keep firing when the function code is erased. -/
  firesRead : ∀ (i : Nat), i ∉ msReadRules →
    FiresEraseD (simEnv (Prims.builtins P hn host)) hn "Step_read" i
  /-- The `Step` rules from 6 on, other than 7–9 and the memory SIMD store rules, keep firing
  when the function code is erased. -/
  firesStep : ∀ (i : Nat), 6 ≤ i → i ∉ stepMSRules → i ≠ 7 → i ≠ 8 → i ≠ 9 →
    FiresEraseD (simEnv (Prims.builtins P hn host)) hn "Step" i

/-- **`RMHost.OpenRMRestDPP` with `RestMSHCQ` for `RestMSHCP`.** -/
structure OpenRMRestDPQ (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- As `RMHost.OpenRMRestDPP.forward`. -/
  forward : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → ¬ CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' → ¬ Round7.HCtx.CallCtxStep P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ SStep (simEnv (BD P hn host)) (configVD hn c) (configVD hn d')
  /-- The per-rule obligations left. -/
  restMSHC : RestMSHCQ hn P host
  /-- As `RMHost.OpenRMRestDPP.castsFwd`. -/
  castsFwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (BD P hn host) (configVD hn c) (configVD hn d')
  /-- As `RMHost.OpenRMRestDPP.castsBwd`. -/
  castsBwd : ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
    BoundedSelM c → CastRedex c.code → ¬ Round7.HPair.EasyP hn P host c →
    Round6.Int.backend.step (BD P hn host) (configVD hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c'

end Silmaril.Wasm.SpecTec.Sim.Round8.RMCode
