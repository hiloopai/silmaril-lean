module

public import Silmaril.Wasm.Jco.Resource.Handle.Defs
public import Silmaril.Wasm.Jco.Resource.Wrap.Thms
public import Silmaril.Wasm.Jco.Thin.Canon.Thms

/-!
# Handle-passing modules: proofs

* `stepB_canonB`, `execB_canonB`, `runB_canonB`: with the canonical built-ins, the
  parametric adaptor semantics is `RFn.run` of `Silmaril.Wasm.Jco.Resource.Adaptor`;
* `find_thinR`: the lifts of the thin wrapper are the world's functions;
* `lowerParamsR_congr`, `lowerParamsR_realloc`: lowering with handle types through two
  `realloc`s that agree on the canonical ABI's allocation calls;
* **`thinR_fuseR`**: the thin wrapper of the fused module is `wrapR md`;
* **`thinR_follows`**: the thin wrapper of a module following the convention is `wrapR md`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Res

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Jco.RM
open Silmaril.Wasm.Component (Flat)

variable (M : CoreInst) (H : HTab) (md : MetaR)

theorem stepB_canonB (i : RInstr) (f : Frame) : i.stepB M (canonB M H) f = i.step M H f := by
  cases i <;> rfl

theorem execB_canonB : ∀ (is : List RInstr) (f : Frame),
    execB M (canonB M H) is f = execR M H is f
  | [], _ => rfl
  | i :: is, f => by
    show (i.stepB M (canonB M H) f >>= fun f' => execB M (canonB M H) is f') =
      (i.step M H f >>= fun f' => execR M H is f')
    simp only [stepB_canonB, execB_canonB is]

theorem runB_canonB (fn : RFn) (xs : List Flat) : fn.runB M (canonB M H) xs = fn.run M H xs := by
  simp only [RFn.runB, RFn.run, execB_canonB]

theorem find_thinR (r name : String) :
    (thinR md r).lifts.find? (·.sig.name == name) =
      (md.world.find? (·.name == name)).map fun s => ⟨s, .core s.name, .core r⟩ := by
  simp only [thinR, List.find?_map]
  rfl

theorem find_name {name : String} {s : RSig} (hf : md.world.find? (·.name == name) = some s) :
    md.world.find? (·.name == s.name) = some s := by
  have hn : s.name = name := by simpa using List.find?_some hf
  rw [hn]
  exact hf

theorem name_ne {r name : String} {s : RSig} (hr : md.world.all (·.name != r) = true)
    (hf : md.world.find? (·.name == name) = some s) : s.name ≠ r := by
  have hm := List.mem_of_find?_eq_some hf
  simpa using List.all_eq_true.1 hr s hm

/-- The `realloc` of `wrapR md` is the adaptor's `realloc` shim. -/
theorem callRef_reallocR' :
    (wrapR md).callRef M H (.adapt 0) = (reallocShim md.alloc).run (withTab M H.T) := by
  rw [callRef_reallocR]
  funext xs
  rw [run_withTab]
  rfl

/-- Lowering with handle types depends on the `realloc` only through `lowerParam`. -/
theorem lowerParamsR_congr {R₁ R₂ : List Flat → RM (withTab M H.T).St (List Flat)}
    (h : ∀ t v, lowerParam (withTab M H.T) R₁ t v = lowerParam (withTab M H.T) R₂ t v) :
    ∀ (ps : List RTy) (vs : List RVal), lowerParamsR M H R₁ ps vs = lowerParamsR M H R₂ ps vs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, v :: vs => by
    have hp : lowerParamR M H R₁ p v = lowerParamR M H R₂ p v := by
      cases p <;> cases v <;> simp only [lowerParamR, h]
    simp only [lowerParamsR, hp, lowerParamsR_congr h ps vs]

/-- A module `realloc` that agrees with its allocator lowers as the adaptor's `realloc` shim. -/
theorem lowerParamsR_realloc {r : String} (hR : ReallocAgrees M md.erase r) (ps : List RTy)
    (vs : List RVal) :
    lowerParamsR M H ((withTab M H.T).call r) ps vs =
      lowerParamsR M H ((wrapR md).callRef M H (.adapt 0)) ps vs := by
  refine lowerParamsR_congr M H (fun t v => ?_) ps vs
  rw [callRef_reallocR, show (withTab M H.T).call r = fun xs => (M.call r xs).onFst from rfl,
    lowerParam_withTab, lowerParam_withTab, lowerParam_realloc M md.erase hR]
  congr 1
  cases t <;> cases v <;> simp only [lowerParam, Meta.specParam, lowerBytes_wrap]

theorem fuseR_callRef_realloc :
    (fuseR M md).callRef H (.core fuseReallocName) = (wrapR md).callRef M H (.adapt 0) := by
  rw [callRef_reallocR']
  funext xs
  simp only [HMod.callRef, fuseR, ↓reduceIte]

theorem fuseR_callRef_shim (hr : md.world.all (·.name != fuseReallocName) = true) {name : String}
    {s : RSig} (hf : md.world.find? (·.name == name) = some s) {i : Nat} (hi : md.world[i]? = some s) :
    (fuseR M md).callRef H (.core s.name) = (wrapR md).callRef M H (.adapt (i + 1)) := by
  rw [callRef_shimR M H md i s hi]
  funext xs
  simp only [HMod.callRef, fuseR, name_ne md hr hf, ↓reduceIte, find_name md hf, runB_canonB]

/-- **The thin wrapper of the fused module is the adaptor-style wrapper**, on every export. -/
theorem thinR_fuseR (hr : md.world.all (·.name != fuseReallocName) = true) (name : String)
    (vs : List RVal) :
    (thinR md fuseReallocName).callExportH (fuseR M md) H name vs =
      (wrapR md).callExport M H name vs := by
  have hl : (wrapR md).lifts = liftsFromR 0 md.world := rfl
  unfold RComp.callExportH RComp.callExport
  rw [find_thinR, hl]
  cases hf : md.world.find? (·.name == name) with
  | none =>
    rw [(find_liftsFromR name 0 md.world).2 hf]
    rfl
  | some s =>
    obtain ⟨i, hi, hfind⟩ := (find_liftsFromR name 0 md.world).1 s hf
    have hidx : 0 + i + 1 = i + 1 := by omega
    rw [hfind]
    simp only [hidx, Option.map_some]
    rw [fuseR_callRef_realloc M H md, fuseR_callRef_shim M H md hr hf hi]
    rfl

/-- **A thin wrapper of a module following the handle-passing convention is the adaptor-style
wrapper** of its plain exports, when its `realloc` is a plain export agreeing with the
allocator. -/
theorem thinR_follows (N : HMod) (hF : N.Follows md) {r : String} (hP : N.PlainAt r)
    (hR : ReallocAgrees N.core md.erase r) (name : String) (vs : List RVal) :
    (thinR md r).callExportH N H name vs = (wrapR md).callExport N.core H name vs := by
  have hl : (wrapR md).lifts = liftsFromR 0 md.world := rfl
  unfold RComp.callExportH RComp.callExport
  rw [find_thinR, hl]
  cases hf : md.world.find? (·.name == name) with
  | none =>
    rw [(find_liftsFromR name 0 md.world).2 hf]
    rfl
  | some s =>
    obtain ⟨i, hi, hfind⟩ := (find_liftsFromR name 0 md.world).1 s hf
    have hidx : 0 + i + 1 = i + 1 := by omega
    rw [hfind]
    simp only [hidx, Option.map_some]
    have hce : N.callRef H (.core s.name) = (wrapR md).callRef N.core H (.adapt (i + 1)) := by
      rw [callRef_shimR N.core H md i s hi]
      funext xs
      simp only [HMod.callRef, hF _ s (List.mem_of_find?_eq_some hf), runB_canonB]
    have hre : N.callRef H (.core r) = (withTab N.core H.T).call r := hP _
    simp only [canonCallR, hce, hre, lowerParamsR_realloc N.core H md hR]

end Silmaril.Proofs.Wasm.Jco.Res
