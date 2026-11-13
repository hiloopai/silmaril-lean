module

public import Silmaril.Wasm.Models.Functional.Defs
public import Silmaril.Wasm.Models.Profiles.Thms
import Silmaril.Proofs.Wasm.Models.Functional.Alloc

/-!
# The functional profile: what it buys

The two halves of the `functional` profile theorem of `docs/projects/spectec/README.md` §1.2.

* **No store writes beyond allocation.** `step_allocOnly`: for `S ≤ functional` and a host that
  only allocates (`HostAllocOnly`), every Core step from runtime code of `S` (`Rt.CodeIn S`),
  at every profile, changes the store by allocation only (`AllocOnly`: functions, globals,
  memories, tables, segments and tags unchanged; structs, arrays and exceptions only appended).
  `steps_allocOnly` extends it to runs that stay in `Rt.InFeat S` (which every run from code of
  `S` does, under `Rt.HostIn S`: `steps_allocOnly_of_inFeat`).
* **Determinism modulo traps and imports.** `detFn_functional`: in a store whose functions are
  of `micro functional` (functional Wasm without floats, whose NaN results are
  profile-dependent), every function is deterministic modulo traps and imports
  (`Det.Core.DetFn`) at every profile (from `detFn_of_storeIn`, as `functional ≤
  functionalMutGC`).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models

open Silmaril.Wasm Silmaril.Wasm.Execution.Core FeatureSet
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {S : FeatureSet}

theorem AllocOnly.refl (s : Store H) : AllocOnly s s :=
  Silmaril.Proofs.Wasm.Models.Functional.allocOnly_refl s

theorem AllocOnly.trans {s₁ s₂ s₃ : Store H} (h₁ : AllocOnly s₁ s₂) (h₂ : AllocOnly s₂ s₃) :
    AllocOnly s₁ s₃ :=
  ⟨h₂.funcs.trans h₁.funcs, h₂.globals.trans h₁.globals, h₂.mems.trans h₁.mems,
    h₂.tables.trans h₁.tables, h₂.datas.trans h₁.datas, h₂.elems.trans h₁.elems,
    h₂.tags.trans h₁.tags, h₁.structs.trans h₂.structs, h₁.arrays.trans h₂.arrays,
    h₁.exns.trans h₂.exns⟩

/-- **Functional code only allocates**: a step from runtime code of `S ≤ functional` under a
host that only allocates writes nothing in the store. -/
theorem step_allocOnly (hS : S ≤ functional) {P : Profile} {host : HostSemantics H}
    (hh : HostAllocOnly host) {c c' : Config H} (h : Step P host c c')
    (hc : Rt.CodeIn S c.code) : AllocOnly c.store c'.store :=
  Silmaril.Proofs.Wasm.Models.Functional.step_allocOnly
    (Silmaril.Proofs.Wasm.Models.Functional.lacks_functional.of_le hS) hh h hc

/-- Runs that stay in the runtime invariant only allocate. -/
theorem steps_allocOnly (hS : S ≤ functional) {P : Profile} {host : HostSemantics H}
    (hh : HostAllocOnly host) (hin : Rt.HostIn S host) {c c' : Config H}
    (h : Steps P host c c') (hc : Rt.InFeat S c) : AllocOnly c.store c'.store := by
  induction h with
  | refl => exact AllocOnly.refl _
  | tail hs step ih =>
    exact ih.trans (step_allocOnly hS hh step (Rt.steps_rtInFeat hin hs hc).1)

/-- **A run of an invocation of functional code only allocates** (the invocation of a function
of a store of `S` is in the runtime invariant, `Rt.invoke_rtInFeat`). -/
theorem steps_allocOnly_of_inFeat (hS : S ≤ functional) {P : Profile}
    {host : HostSemantics H} (hh : HostAllocOnly host) (hin : Rt.HostIn S host)
    {s : Store H} (hs : Rt.StoreIn S s) (a : Nat) (vs : List Val) {c' : Config H}
    (h : Steps P host (invoke s a vs) c') : AllocOnly s c'.store :=
  steps_allocOnly hS hh hin h (Rt.invoke_rtInFeat hs a vs)

/-- **Float-free functional Wasm is deterministic modulo traps and imports**, at every
profile. -/
theorem detFn_functional {P : Profile} {s : Store Nat} (hs : Rt.StoreIn (micro functional) s)
    (a : Nat) : Silmaril.Wasm.Det.Core.DetFn P s a :=
  detFn_of_storeIn ((micro_le _).trans functional_le_functionalMutGC) (micro_no_float _) hs a

end Silmaril.Wasm.Models
