module

public import Silmaril.Wasm.Models.Profiles.Defs
public import Silmaril.Wasm.Models.Charts.Thms
public import Silmaril.Proofs.Wasm.Models.Profiles.Micro
public import Silmaril.Proofs.Wasm.Models.Profiles.Det

/-!
# What the named profiles buy

**Micro Wasm** (no floats): **profile independence**. On runtime code of a feature set without
floats, Core `Step P host` depends on the profile only through its grow policy `P.grow`, not on
`$ND`, the relaxed-SIMD choice or the NaN policy:

* `micro_step_iff`: `Step P host c c' ↔ Step P' host c c'` when `P.grow = P'.grow` and
  `c.code` is runtime code of `S` (`floatNum ∉ S`; e.g. `S = micro T` for any `T`);
* `micro_behaviours_eq`: the behaviours of an invocation are equal at such profiles, for a store
  of `S` and a host keeping it in `S`;
* `microEq`: the restricted Core charts `core|micro S` at two profiles with the same grow
  policy are related by an **equality transition** (identity on points and calls); with
  `micro_stepLE` both ways this is the design's "`StepLE` both ways on micro configurations".

**Functional Wasm with mutable GC** (float-free): **determinism modulo traps and imports**, at
every profile, through `Det.NoMem`:

* `noMem_instrB`: every instruction of a float-free feature set below `functionalMutGC` passes
  `Det.NoMem.instrB` (full mode); `storeB_of_storeIn`: so does a store of such code;
* `detFn_of_storeIn`, `detFn_functionalMutGC`: every function of such a store is deterministic
  (`Silmaril.Wasm.Det.Core.DetFn`), at every profile; in particular for `micro functionalMutGC`;
* `micro_functionalMutGC_le_noMemS`: `micro functionalMutGC ≤ noMemS`.

**The `Det` subsets in the lattice** (flat instructions other than a typed `select`):
`noMem_flat`, `stateless_flat`, `growTrap_flat`.

Proofs: `Silmaril.Proofs.Wasm.Models.Profiles.{Micro,Det}`. New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Atlas
open Silmaril.Wasm.Numerics (Profile)

variable {S : FeatureSet} {H : Type}

/-! ## Micro Wasm: profile independence -/

/-- **One step**: on runtime code without floats, a step at `P` is a step at every `P'` with
the same grow policy. -/
theorem micro_stepLE {P P' : Profile} (hf : S.has .floatNum = false) (hg : P.grow = P'.grow)
    {host : HostSemantics H} {c c' : Config H} (hc : Rt.CodeIn S c.code)
    (h : Step P host c c') : Step P' host c c' :=
  Silmaril.Proofs.Wasm.Models.Micro.step_transfer hf hg h hc

theorem micro_step_iff {P P' : Profile} (hf : S.has .floatNum = false) (hg : P.grow = P'.grow)
    {host : HostSemantics H} {c c' : Config H} (hc : Rt.CodeIn S c.code) :
    Step P host c c' ↔ Step P' host c c' :=
  ⟨micro_stepLE hf hg hc, micro_stepLE hf hg.symm hc⟩

/-- **Behaviours**: equal at profiles with the same grow policy. -/
theorem micro_behaviours_eq {P P' : Profile} (hf : S.has .floatNum = false)
    (hg : P.grow = P'.grow) {host : HostSemantics H} (hh : Rt.HostIn S host) {s : Store H}
    (hs : Rt.StoreIn S s) (a : Nat) (vs : List Val) :
    behaviours P host s a vs = behaviours P' host s a vs :=
  Set.Subset.antisymm
    (Silmaril.Proofs.Wasm.Models.Micro.behavioursOf_sub hf hg hh (Rt.invoke_rtInFeat hs a vs))
    (Silmaril.Proofs.Wasm.Models.Micro.behavioursOf_sub hf hg.symm hh (Rt.invoke_rtInFeat hs a vs))

/-- **The micro charts at two profiles with the same grow policy are equal** (an equality
transition, identity on points and calls). -/
def microEq {P P' : Profile} (H : Type) (T : FeatureSet) (hg : P.grow = P'.grow) :
    Transition (coreR P H (micro T)) (coreR P' H (micro T)) :=
  BTrans.ofEq id id (fun _ hx => hx) fun _ hx _ =>
    (micro_behaviours_eq (micro_no_float T) hg (Rt.hostIn_of_keeps hx.2.1 hx.2.2) hx.1 _ _).symm

theorem microEq_dir {P P' : Profile} (T : FeatureSet) (hg : P.grow = P'.grow) :
    (microEq (P := P) (P' := P') H T hg).dir = .equal := rfl

/-! ## Functional Wasm with mutable GC: determinism through `Det.NoMem` -/

theorem micro_functionalMutGC_le_noMemS : micro functionalMutGC ≤ noMemS :=
  leB_iff.mp (by decide)

theorem micro_functionalMutGC_le : micro functionalMutGC ≤ functionalMutGC :=
  micro_le _

theorem noMem_instrB (hS : S ≤ functionalMutGC) (hf : S.has .floatNum = false) {fs : List Nat}
    {i : Instr} (h : Instr.InFeat S i) :
    Silmaril.Wasm.Det.NoMem.instrB (fun _ => true) true fs i = true :=
  Silmaril.Proofs.Wasm.Models.Profiles.noMem_instrB hS hf i h

theorem storeB_of_storeIn (hS : S ≤ functionalMutGC) (hf : S.has .floatNum = false)
    {s : Store Nat} (hs : Rt.StoreIn S s) : Silmaril.Wasm.Det.NoMem.storeB s = true :=
  Silmaril.Proofs.Wasm.Models.Profiles.storeB_of_storeIn hS hf hs

/-- **Determinism**: every function of a store of a float-free feature set below
`functionalMutGC` is deterministic modulo traps and imports, at every profile. -/
theorem detFn_of_storeIn {P : Profile} (hS : S ≤ functionalMutGC)
    (hf : S.has .floatNum = false) {s : Store Nat} (hs : Rt.StoreIn S s) (a : Nat) :
    Silmaril.Wasm.Det.Core.DetFn P s a :=
  Silmaril.Wasm.Det.NoMem.detFn_of_storeB (storeB_of_storeIn hS hf hs) a

/-- **Float-free functional Wasm with mutable GC is deterministic**, at every profile. -/
theorem detFn_functionalMutGC {P : Profile} {s : Store Nat}
    (hs : Rt.StoreIn (micro functionalMutGC) s) (a : Nat) : Silmaril.Wasm.Det.Core.DetFn P s a :=
  detFn_of_storeIn micro_functionalMutGC_le (micro_no_float _) hs a

/-! ## The `Det` subsets in the lattice -/

theorem noMem_flat {i : Instr} (h : Silmaril.Wasm.Det.NoMem.flatOk i = true)
    (hs : ∀ ts, i ≠ .select (some ts)) : Rt.instrB noMemS i = true :=
  Silmaril.Proofs.Wasm.Models.Profiles.noMem_flat h hs

theorem stateless_flat {A R W : Nat → Bool} {m : ModuleInst} {i : Instr}
    (h : Silmaril.Wasm.Det.Stateless.slInstr A R W m i = true) (hb : i.bodies = [])
    (hs : ∀ ts, i ≠ .select (some ts)) : Rt.instrB statelessS i = true :=
  Silmaril.Proofs.Wasm.Models.Profiles.stateless_flat h hb hs

theorem growTrap_flat {i : Instr} (h : Silmaril.Wasm.Det.GrowTrap.flatOk i = true)
    (hs : ∀ ts, i ≠ .select (some ts)) : Rt.instrB growTrapS i = true :=
  Silmaril.Proofs.Wasm.Models.Profiles.growTrap_flat h hs

theorem statelessS_le_growTrapS : statelessS ≤ growTrapS := leB_iff.mp (by decide)
theorem statelessS_le_noMemS : statelessS ≤ noMemS := leB_iff.mp (by decide)
theorem noMemS_le_v30 : noMemS ≤ v30 := leB_iff.mp (by decide)
theorem growTrapS_le_v30 : growTrapS ≤ v30 := leB_iff.mp (by decide)

end Silmaril.Wasm.Models
