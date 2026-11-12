module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Read2.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read2.Load
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read2.Copy
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read2.Get
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read2.StructDefault
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read2.NewData

/-!
# Round 5, pass 3, track read: assembly

* `read_done2`: the rules of `readDone2`, backward, for the concrete builtins, under `ReadValidS`.
* `readRest`: pass 2's `Round5.Read.ReadRest` holds (every rule it leaves is in `readDone2`,
  `readDone2_covers`).
* `open2_of_open3`: pass 2's `Round5.Int2.Open2` from `Open3`; hence
  `wholeStepValidOk_of_open3` and the multi-step corollary `multiOk2_of_open3`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read2

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4Int (BI)
open Round4 (SSteps)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **This track's `Step_read` rules, backward**, for the concrete builtins, under
`ReadValidS`. -/
theorem read_done2 (i : Nat) (hi : i ∈ readDone2) (c : Config H) (w : Value)
    (hv : Round5.Read.ReadValidS c) (hc : Typed (simEnv (BI P hn host)) hn c)
    (hf : Fires (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  simp only [readDone2, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [bwd_loadNumVal c w hf, bwd_loadPackVal c w hf, bwd_structNewDefault c w hf,
    bwd_structGetStruct c w hf, bwd_arrayNewDataNum c w hv hf, bwd_arrayGetArray c w hf,
    bwd_arrayCopyLe c w hv hf, bwd_arrayCopyGt c w hv hf, bwd_arrayInitDataNum c w hv hc hf]

/-- Every `Step_read` rule that pass 2's `ReadRest` leaves is in `readDone2`. -/
theorem readDone2_covers : ∀ i, i < 103 → i ∉ Bwd.readDoneUpTo → i ∉ BwdRead.readDone →
    i ∉ Round4Read.readDoneV → i ∉ Bwd.readDoneR → i ∉ Round5.Read.readDoneS →
    i ∉ Round5.Read.readDoneK → i ∈ readDone2 := by
  intro i hi h₀ h₁ h₂ h₃ h₄ h₅
  simp only [Bwd.readDoneUpTo, Bwd.readDone, BwdRead.readDone, Round4Read.readDoneV,
    Bwd.readDoneR, Round5.Read.readDoneS, Round5.Read.readDoneK, readDone2, List.mem_cons,
    List.mem_append, List.mem_nil_iff, or_false, not_or] at h₀ h₁ h₂ h₃ h₄ h₅ ⊢
  omega

/-- **Pass 2's `Round5.Read.ReadRest` holds**, for the concrete builtins. -/
theorem readRest : Round5.Read.ReadRest hn P host :=
  fun i hi h₀ h₁ h₂ h₃ h₄ h₅ c w hv hc hf =>
    Bwd.read_upTo (read_done2 i (readDone2_covers i hi h₀ h₁ h₂ h₃ h₄ h₅) c w hv hc hf)

/-- **`Round5.Int2.Open2` from `Open3`.** -/
theorem open2_of_open3 (O : Open3 hn P host) : Int2.Open2 hn P host where
  simd := O.simd
  refOk := O.refOk
  hostRespects := O.hostRespects
  vector := O.vector
  vecOps := O.vecOps
  vtestop := O.vtestop
  read := readRest

/-- `Open2` gives `Open3`: the new leaves ask no more. -/
theorem open3_of_open2 (O : Int2.Open2 hn P host) : Open3 hn P host where
  simd := O.simd
  refOk := O.refOk
  hostRespects := O.hostRespects
  vector := O.vector
  vecOps := O.vecOps
  vtestop := O.vtestop

/-- **`Round5.Task.wholeStepValidOk` from the leaves still open after pass 3, track read**, at
every injective encoding, finite `HostOk` host and `Profile.spec nd r`. -/
theorem wholeStepValidOk_of_open3
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), Open3 hn (Profile.spec nd r) host) :
    Round5.Task.wholeStepValidOk :=
  Int2.wholeStepValidOk_of_open2 fun H hn hinj host hfin hok nd r =>
    open2_of_open3 (h H hn hinj host hfin hok nd r)

/-- **The composable one-step simulations (`Int2.MultiOk2`) from `Open3`.** -/
theorem multiOk2_of_open3
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), Open3 hn (Profile.spec nd r) host) :
    Int2.MultiOk2 :=
  Int2.multiOk2_of_open2 fun H hn hinj host hfin hok nd r =>
    open2_of_open3 (h H hn hinj host hfin hok nd r)

/-- **The run corollaries of the restated target, from `Open3`**: pass 2's
`Round5.Int2.runs_of_open2` with the `read` leaf discharged. -/
theorem runs_of_open3 {nd : Bool} {r : RelaxedChoice} (hf : HostFinite host) (hh : HostOk host)
    (O : Open3 hn (Profile.spec nd r) host) :
    (∀ (c₀ c : Config H) (ts : List CValType), ConfigOk c₀ ts →
      Multi.BoundedReachNE (Profile.spec nd r) host c₀ → Steps (Profile.spec nd r) host c₀ c →
      ∃ d, Bwd.ConfigEq c d ∧
        SSteps (simEnv (BI (Profile.spec nd r) hn host)) (configV hn c₀) (configV hn d)) ∧
    (Multi.SuccTyped (BI (Profile.spec nd r) hn host) hn →
      Int2.WitnessBnd (BI (Profile.spec nd r) hn host) hn →
      ∀ (c₀ : Config H) (ts : List CValType) (w : Value), ConfigOk c₀ ts →
      Multi.BoundedReachNE (Profile.spec nd r) host c₀ →
      SSteps (simEnv (BI (Profile.spec nd r) hn host)) (configV hn c₀) w →
      ∃ c d, Bwd.ConfigEq c d ∧ w = configV hn d ∧ Steps (Profile.spec nd r) host c₀ c) :=
  Int2.runs_of_open2 hf hh (open2_of_open3 O)

end Silmaril.Wasm.SpecTec.Sim.Round5.Read2
