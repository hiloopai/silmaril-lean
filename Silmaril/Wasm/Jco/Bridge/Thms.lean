module

public import Silmaril.Wasm.Jco.Bridge.Defs
public import Silmaril.Wasm.Jco.Fuse.Thms
public import Silmaril.Wasm.Jco.Thin.Canon.Thms
import Silmaril.Proofs.Wasm.Jco.Bridge.IR
import Silmaril.Proofs.Wasm.Jco.Bridge.Mem

/-!
# Relating the two settings of the jco part: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Bridge.{IR,Mem}`. On memory-free worlds (`Meta.memFree`) and
pure modules (`PMod`):

* **`simpleComp_bridge`** (component IR): the strategy of the adaptor-style component of the
  simple FFI style, `Fuse.simpleComp [] (Meta.iface md) m` over `pureSem`, is the handler
  answering `bridgeAns md m`: export `i` on component values `vs` answers
  `pureCall m s vs` for world function `i = s`. **`simpleWrapper_bridge`**: the same for the
  wrapper-style single component over the fused single core module (`fuseSem`).
* **`wrap_memFree`** (memory-based model): on memory-free worlds `wrap md` follows the C
  convention for every core instance, without `Conforms`. **`wrap_pure`**, **`thinComp_pure`**:
  over the instance of a pure module, `wrap md` and the thin wrapper `thinComp md r` (for every
  `realloc` name `r`) both behave as `specPure md m`, i.e. `RM.ofOption` of `pureCall`.
* **`simpleComp_wrap`** (the identification, per world function): for world function `i = s`,
  the IR component answers `(i, vals vs)` with `r.map resPayload` and the `i`-th lift of `wrap md`
  (the `canon lift` of adaptor function `i + 1`) is `RM.ofOption r`, for the same
  `r = pureCall m s vs`: they trap together, and return the same values otherwise.
  `simpleComp_wrap_name`: the same by export name when the world's names are distinct.

What this does not cover: modules with imports, state or memory (`PMod` is stateless and
import-free; a general `CoreInst` has no `CoreSem` counterpart here), strings and lists (the IR
has only the flat ABI), and the relation of the two notions of program (a relation `RM` against
a strategy) beyond deterministic answers.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Bridge

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Jco.Fuse
open Silmaril.Wasm.Jco (PTy PVal Meta inMem wrap thinComp canonCall)

theorem memFree_result {md : Meta} (h : md.memFree = true) :
    ∀ s ∈ md.world, inMem s.result = false := fun _ hs => (Silmaril.Wasm.Jco.memFree_mem md h hs).2

/-- **The IR side.** -/
theorem simpleComp_bridge (md : Meta) (m : PMod) (h : md.memFree = true) :
    (simpleComp [] (Meta.iface md) m).denU (baseSem pureSem) =
      Strategy.ofHandler (fun q => .pure (bridgeAns md m q)) :=
  Silmaril.Proofs.Wasm.Jco.Bridge.simpleComp_bridge md m (memFree_result h)

/-- **The IR side, wrapper style over the single fused core module.** -/
theorem simpleWrapper_bridge (md : Meta) (m : PMod) (h : md.memFree = true) :
    (simpleWrapper [] (Meta.iface md) m).denU (fuseSem pureSem) =
      Strategy.ofHandler (fun q => .pure (bridgeAns md m q)) := by
  rw [simpleWrapper_simpleComp, simpleComp_bridge md m h]

/-- **On memory-free worlds `wrap` follows the C convention for every instance.** -/
theorem wrap_memFree (M : Silmaril.Wasm.Jco.CoreInst) (md : Meta) (h : md.memFree = true)
    (name : String) (vs : List PVal) : (wrap md).callExport M name vs = md.spec M name vs :=
  Silmaril.Proofs.Wasm.Jco.Bridge.wrap_memFree M md h name vs

/-- The C convention over a pure module. -/
theorem spec_pure (md : Meta) (m : PMod) (h : md.memFree = true) (name : String)
    (vs : List Val) : md.spec m.inst name (vs.map PVal.val) = specPure md m name vs := by
  unfold Meta.spec specPure
  rcases hf : md.world.find? (·.name == name) with _ | s
  · rw [hf]
    rfl
  · rw [hf]
    have hs := Silmaril.Wasm.Jco.memFree_mem md h (List.mem_of_find?_eq_some hf)
    exact Silmaril.Proofs.Wasm.Jco.Bridge.specCall_pure md m s hs.1 hs.2 vs

/-- **The memory-based side, adaptor style.** -/
theorem wrap_pure (md : Meta) (m : PMod) (h : md.memFree = true) (name : String)
    (vs : List Val) : (wrap md).callExport m.inst name (vs.map PVal.val) = specPure md m name vs := by
  rw [wrap_memFree _ md h, spec_pure md m h]

/-- **The memory-based side, thin wrapper.** -/
theorem thinComp_pure (md : Meta) (m : PMod) (h : md.memFree = true) (r name : String)
    (vs : List Val) :
    (thinComp md r).callExport m.inst name (vs.map PVal.val) = specPure md m name vs := by
  rw [Silmaril.Wasm.Jco.thinComp_callExport, Silmaril.Wasm.Jco.canonSpec_eq_spec_memFree _ _ r h,
    spec_pure md m h]

/-- The `i`-th lift of `wrap md` over a pure module. -/
theorem wrap_lift_pure (md : Meta) (m : PMod) (h : md.memFree = true) (i : Nat)
    (s : Silmaril.Wasm.Jco.Sig) (hi : md.world[i]? = some s) (vs : List Val) :
    canonCall m.inst ((wrap md).callRef m.inst (.adapt 0)) ((wrap md).callRef m.inst (.adapt (i + 1)))
      s (vs.map PVal.val) = Silmaril.Wasm.Jco.RM.ofOption (pureCall m s vs) := by
  have hs := Silmaril.Wasm.Jco.memFree_mem md h (List.mem_of_getElem? hi)
  rw [Silmaril.Proofs.Wasm.Jco.Bridge.canonCall_wrap_memFree m.inst md i s hi hs.1 hs.2,
    Silmaril.Proofs.Wasm.Jco.Bridge.specCall_pure md m s hs.1 hs.2 vs]

/-- **`Fuse.simpleComp` is `wrap` on memory-free worlds**, world function by world function. -/
theorem simpleComp_wrap (md : Meta) (m : PMod) (h : md.memFree = true) (i : Nat)
    (s : Silmaril.Wasm.Jco.Sig) (hi : md.world[i]? = some s) (vs : List Val) :
    ∃ r : Option (Option PVal),
      (simpleComp [] (Meta.iface md) m).denU (baseSem pureSem) =
        Strategy.ofHandler (fun q => .pure (bridgeAns md m q)) ∧
      bridgeAns md m (i, .vals vs) = r.map resPayload ∧
      canonCall m.inst ((wrap md).callRef m.inst (.adapt 0))
        ((wrap md).callRef m.inst (.adapt (i + 1))) s (vs.map PVal.val) =
        Silmaril.Wasm.Jco.RM.ofOption r :=
  ⟨pureCall m s vs, simpleComp_bridge md m h, by simp [bridgeAns, hi],
    wrap_lift_pure md m h i s hi vs⟩

theorem find_name_nodup {ws : List Silmaril.Wasm.Jco.Sig} (hn : (ws.map (·.name)).Nodup) {i : Nat}
    {s : Silmaril.Wasm.Jco.Sig} (hi : ws[i]? = some s) : ws.find? (·.name == s.name) = some s := by
  induction ws generalizing i with
  | nil => cases hi
  | cons w ws ih =>
    have hn' : w.name ∉ ws.map (·.name) ∧ (ws.map (·.name)).Nodup := by
      simpa using hn
    cases i with
    | zero =>
      have e : w = s := by simpa using hi
      simp [e]
    | succ i =>
      have hs : s ∈ ws := List.mem_of_getElem? hi
      have hne : (w.name == s.name) = false := by
        have : w.name ≠ s.name := fun he => hn'.1 (he ▸ List.mem_map_of_mem hs)
        simpa using this
      simp [hne, ih hn'.2 hi]

/-- The identification by export name, when the world's names are distinct. -/
theorem simpleComp_wrap_name (md : Meta) (m : PMod) (h : md.memFree = true)
    (hn : (md.world.map (·.name)).Nodup) (i : Nat) (s : Silmaril.Wasm.Jco.Sig)
    (hi : md.world[i]? = some s) (vs : List Val) :
    bridgeAns md m (i, .vals vs) = (pureCall m s vs).map resPayload ∧
      (wrap md).callExport m.inst s.name (vs.map PVal.val) =
        Silmaril.Wasm.Jco.RM.ofOption (pureCall m s vs) := by
  refine ⟨by simp [bridgeAns, hi], ?_⟩
  rw [wrap_pure md m h]
  simp only [specPure, find_name_nodup hn hi]
  rfl

end Silmaril.Wasm.Jco.Bridge
