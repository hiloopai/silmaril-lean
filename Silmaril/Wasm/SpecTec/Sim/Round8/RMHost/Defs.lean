module

public import Silmaril.Wasm.SpecTec.Sim.Round7.MSRest.Thms

/-!
# Round 8, memory SIMD: turning every function into a host function (definitions)

The store-replacement route to the `Step_pure` part of `NullHost.RestMSHC`.

* `hostFI fi`: the function instance `fi` with its code replaced by the host function `()`; its
  type and module are kept.
* `hostify s`: the store `s` with every function instance replaced by `hostFI`, over the host
  type `Unit`. It has no Wasm function body, so no memory SIMD code, and at the host with no
  outcome (`NullHost.nullHost`) no Core step reads a function body.
* `withFuncs u F`: the store `u` with the function instances `F` (over any host type);
  `withFuncs (hostify s) s.funcs = s`.
* `setF F c`: the configuration `c` with the function instances `F`.
* `RestMSHCP`: `MSRest.RestMSHCR` without the `Step_pure` obligation at code that holds no memory
  SIMD instruction (which this round proves for every rule); `OpenRMRestDPP` is
  `MSRest.OpenRMRestDPR` with it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.RMHost

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

/-- **A function instance as a host function**: the code is the host function `()`; the type and
the module are kept. -/
def hostFI (fi : FuncInst H) : FuncInst Unit := ⟨fi.type, fi.module, .host ()⟩

/-- **The store with every function instance a host function**, over the host type `Unit`. -/
def hostify (s : Store H) : Store Unit :=
  { tags := s.tags, globals := s.globals, mems := s.mems, tables := s.tables,
    funcs := s.funcs.map hostFI, datas := s.datas, elems := s.elems, structs := s.structs,
    arrays := s.arrays, exns := s.exns }

/-- **The store `u` with the function instances `F`.** -/
def withFuncs {H' : Type} (u : Store H') (F : List (FuncInst H)) : Store H :=
  { tags := u.tags, globals := u.globals, mems := u.mems, tables := u.tables, funcs := F,
    datas := u.datas, elems := u.elems, structs := u.structs, arrays := u.arrays, exns := u.exns }

/-- The configuration `c` with the function instances `F`. -/
def setF {H' : Type} (F : List (FuncInst H)) (c : Config H') : Config H :=
  ⟨withFuncs c.store F, c.frame, c.code⟩

/-- **`MSRest.RestMSHCR` without the `Step_pure` obligation at memory-SIMD-free code**: the
`Step_pure` obligation is asked only at code holding a memory SIMD instruction. -/
structure RestMSHCP (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- `Step_pure`, at code holding memory SIMD instructions. -/
  pure : ∀ (i : Nat) (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    ¬ AdminsMS is → Round7.MSRest.VMS ⟨s, f, is⟩ →
    TypedD (simEnv (Prims.builtins P hn host)) hn ⟨s, f, is⟩ →
    Fires (simEnv (Prims.builtins P hn host)) "Step_pure" i (.tuple [.list (adminsToVD is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step_read`, as in `RestMSHCR`. -/
  read : ∀ (i : Nat), i ∉ msReadRules → ∀ (c : Config H) (w : Value), Round7.MSRest.VMS c →
    TypedD (simEnv (Prims.builtins P hn host)) hn c →
    Fires (simEnv (Prims.builtins P hn host)) "Step_read" i (.tuple [configVD hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩
  /-- `Step`, as in `RestMSHCR`. -/
  step : ∀ (i : Nat), 6 ≤ i → i ∉ stepMSRules → i ≠ 8 → i ≠ 9 → ∀ (c : Config H) (w : Value),
    Round7.MSRest.VMS c → TypedD (simEnv (Prims.builtins P hn host)) hn c →
    Fires (simEnv (Prims.builtins P hn host)) "Step" i (.tuple [configVD hn c, w]) →
    BwdUpToD hn P host c w

/-- **`MSRest.OpenRMRestDPR` with `RestMSHCP` for `RestMSHCR`.** -/
structure OpenRMRestDPP (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- As `MSRest.OpenRMRestDPR.forward`. -/
  forward : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → ¬ CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' → ¬ Round7.HCtx.CallCtxStep P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ SStep (simEnv (BD P hn host)) (configVD hn c) (configVD hn d')
  /-- The per-rule backward obligations left. -/
  restMSHC : RestMSHCP hn P host
  /-- As `MSRest.OpenRMRestDPR.castsFwd`. -/
  castsFwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (BD P hn host) (configVD hn c) (configVD hn d')
  /-- As `MSRest.OpenRMRestDPR.castsBwd`. -/
  castsBwd : ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
    BoundedSelM c → CastRedex c.code → ¬ Round7.HPair.EasyP hn P host c →
    Round6.Int.backend.step (BD P hn host) (configVD hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c'

end Silmaril.Wasm.SpecTec.Sim.Round8.RMHost
