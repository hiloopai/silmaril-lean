module

public import Silmaril.Wasm.Models.V2Core.Defs
public import Silmaril.Wasm.Behaviour.Semantics.V1
public import Silmaril.Wasm.V1.Validation.Modules

/-!
# The own Wasm 1.0 model `v10own` and its embedding data into `v20own`

The **own 1.0 model** is silmaril-lean's `Silmaril.Wasm.V1.Execution.Step` observed through
`Silmaril.Wasm.V1.Execution.behaviours`. The copied simulation goes 1.0 → Lime1 (lock-step,
`Lime1/Execution/FromV1.lean`) → 2.0 (`Lime1/ToV2/Execution.lean`, at
`v2Profile = Profile.spec`; Lime1 is not profile-indexed).

* `lime p`: the Lime1 image of a 1.0 point (`Store.mapCode Func.toLime` and the transported
  host `HostSemantics.mapCode Func.toLime`); `toV2Store`: its 2.0 image;
* `MemTabWF`: the memory and table part of 2.0's `StoreWF`; `HostKeepsL`, `HostPreservesW`:
  a Lime1 host keeps functions and preserves `MemTabWF` of the 2.0 image;
* `liftHostL src`: the **2.0 host induced by a Lime1 host** (as `V2Core.liftHost` for Core);
* `ModsWF s`: every Wasm function's module names allocated functions;
* `dom p`: the Lime1 image satisfies the copied simulation's `ToV2.StoreWF` and
  `ToV2.HostPreserves`, the host keeps functions and preserves `MemTabWF`, and `ModsWF`;
* `obs p (a, vs)`: the 1.0 behaviours of an allocated address, **read in Core values** through
  2.0 (`Value.toV2` then `Val.toCore`), the observation type of `v20own`;
* `v10own H`: the model (`feats = v10`). Its modules are the valid 1.0 modules whose segment
  offsets read imported globals only (`SegmentOffsetsImported`): 1.0 checks segment offsets in
  the full module context, 2.0 in `C'` (imported globals only), so without it a valid 1.0 module
  need not be a valid 2.0 module (`V10.v10_v20_valid_false` in `Thms`); `ptV2`, `callV2`: the
  point and call maps into `v20own`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V10

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Models.V2Core (VStore VHost CVal)

/-- 1.0 stores. -/
abbrev OStore (H : Type) := Silmaril.Wasm.V1.Execution.Store H
/-- 1.0 hosts. -/
abbrev OHost (H : Type) := Silmaril.Wasm.V1.Execution.HostSemantics H
/-- Lime1 stores. -/
abbrev LStore (H : Type) := Silmaril.Wasm.Lime1.Execution.Store H
/-- Lime1 hosts. -/
abbrev LHost (H : Type) := Silmaril.Wasm.Lime1.Execution.HostSemantics H

/-- The memory and table part of 2.0's `StoreWF`. -/
def MemTabWF {H : Type} (s : VStore H) : Prop :=
  (∀ (i : Nat) (mi : Silmaril.Wasm.V2.Execution.MemInst), s.mems[i]? = some mi →
      mi.bytes.size ≤ 2 ^ 32) ∧
    (∀ (i : Nat) (mi : Silmaril.Wasm.V2.Execution.MemInst), s.mems[i]? = some mi →
      mi.bytes.size % Silmaril.Wasm.Execution.Memory.pageSize = 0) ∧
    (∀ (i : Nat) (ti : Silmaril.Wasm.V2.Execution.TableInst), s.tables[i]? = some ti →
      ti.refs.length < 2 ^ 32)

/-- A Lime1 host keeps the store's functions. -/
def HostKeepsL {H : Type} (src : LHost H) : Prop :=
  ∀ h s vs s' r, src h s vs (.returned s' r) → s'.funcs = s.funcs

/-- A Lime1 host preserves `MemTabWF` of the 2.0 image. -/
def HostPreservesW {H : Type} (src : LHost H) : Prop :=
  ∀ h (s : LStore H) vs s' r, src h s vs (.returned s' r) → MemTabWF s.toV2 → MemTabWF s'.toV2

/-- **The 2.0 host induced by a Lime1 host.** -/
def liftHostL {H : Type} (src : LHost H) : VHost H := fun h sV args out =>
  ∃ (s : LStore H) (vs : List Value),
    Silmaril.Wasm.Lime1.Execution.ToV2.Store.erase sV = s.toV2 ∧ args = vs.map Value.toV2 ∧
      ((src h s vs .diverged ∧ out = .diverged) ∨
       ∃ s' r sV', src h s vs (.returned s' r) ∧ out = .returned sV' r.toV2 ∧
         Silmaril.Wasm.Lime1.Execution.ToV2.Store.erase sV' = s'.toV2 ∧ sV'.funcs = sV.funcs ∧
         (Silmaril.Wasm.V2.Execution.StoreWF sV → Silmaril.Wasm.V2.Execution.StoreWF sV'))

/-- 1.0 points. -/
abbrev Pt (H : Type) := OStore H × OHost H

/-- 1.0 calls. -/
abbrev Call := FuncAddr × List Value

/-- The Lime1 store of a 1.0 point. -/
def limeStore {H : Type} (p : Pt H) : LStore H := p.1.mapCode Silmaril.Wasm.V1.Func.toLime

/-- The Lime1 host of a 1.0 point. -/
def limeHost {H : Type} (p : Pt H) : LHost H := p.2.mapCode Silmaril.Wasm.V1.Func.toLime

/-- Every Wasm function's module names allocated functions. -/
def ModsWF {H : Type} (s : OStore H) : Prop :=
  ∀ fi ∈ s.funcs, ∀ t m c, fi = .wasm t m c → ∀ a ∈ m.funcs, a.value < s.funcs.length

/-- The domain of the own 1.0 model. -/
def dom {H : Type} (p : Pt H) : Prop :=
  Silmaril.Wasm.Lime1.Execution.ToV2.StoreWF (limeStore p) ∧
    Silmaril.Wasm.Lime1.Execution.ToV2.HostPreserves (limeHost p) ∧
    HostKeepsL (limeHost p) ∧ HostPreservesW (limeHost p) ∧ ModsWF p.1

/-- A 1.0 value read as a Core value through 2.0. -/
def valCore (v : Value) : CVal := Silmaril.Wasm.V2.Execution.Val.toCore v.toV2

/-- The observations of a call: the 1.0 behaviours of an allocated address, in Core values. -/
def obs {H : Type} (p : Pt H) (c : Call) : Set (Behaviour CVal) :=
  {b | c.1.value < p.1.funcs.length ∧
    b ∈ Behaviour.mapSet valCore (Silmaril.Wasm.V1.Execution.behaviours p.2 p.1 c.1 c.2)}

/-- **The own Wasm 1.0 model.** -/
def v10own (H : Type) : WasmModel where
  feats := Silmaril.Wasm.Models.v10
  Module := Silmaril.Wasm.V1.Module
  Valid m := Silmaril.Wasm.V1.Validation.ModuleValid m ∧
    Silmaril.Wasm.Lime1.Validation.Module.SegmentOffsetsImported m.toLime
  Pt := Pt H
  Call := Call
  Obs := Behaviour CVal
  obs := obs
  dom := dom

/-- The point map into `v20own`: the 2.0 image of the Lime1 store and the induced host. -/
def ptV2 {H : Type} (p : Pt H) : Silmaril.Wasm.Models.V2Core.Pt H :=
  ((limeStore p).toV2, liftHostL (limeHost p))

/-- The call map. -/
def callV2 (c : Call) : Silmaril.Wasm.Models.V2Core.Call := (c.1.value, c.2.map Value.toV2)

end Silmaril.Wasm.Models.V10
