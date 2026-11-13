module

public import Silmaril.Wasm.Models.Charts.Defs
public import Silmaril.Wasm.Models.Runtime.Thms
public import Silmaril.Wasm.Atlas.Core.Thms

/-!
# Restricted Core charts: equality transitions

* `restrict h : Transition (core|S) (core|T)` for `S ≤ T`: the identity on points and calls,
  **equal** on every sentence (`dir = equal`);
* `toCore : Transition (core|S) (Core.chart P H)`: the embedding into the Core chart, equal on
  every sentence; `restrict_toCore`: the two routes to Core agree on points;
* `dom_runs`: on the domain, every configuration reachable from an invocation is in
  `Rt.InFeat S` (the chart's points really are "programs of `S`" during the whole run).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Atlas
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {H : Type} {S T : FeatureSet}

theorem coreDom_mono (h : S ≤ T) {x : Core.Pt H} (hx : coreDom S x) : coreDom T x :=
  ⟨Rt.storeIn_mono h hx.1, hx.2.1, Rt.hostThrowsIn_mono h hx.2.2⟩

/-- **`core|S → core|T`** for `S ≤ T`: equal on every sentence. -/
def restrict (P : Profile) (H : Type) (h : S ≤ T) : Transition (coreR P H S) (coreR P H T) :=
  BTrans.ofEq id id (fun _ hx => coreDom_mono h hx) (fun _ _ _ => rfl)

/-- **`core|S → core`**: equal on every sentence. -/
def toCore (P : Profile) (H : Type) (S : FeatureSet) : Transition (coreR P H S) (Core.chart P H) :=
  BTrans.ofEq id id (fun _ _ => trivial) (fun _ _ _ => rfl)

theorem restrict_dir (h : S ≤ T) : (restrict P H h).dir = .equal := rfl
theorem toCore_dir : (toCore P H S).dir = .equal := rfl

/-- The two routes `core|S → core|T → core` and `core|S → core` agree on points. -/
theorem restrict_toCore (h : S ≤ T) (x : Core.Pt H) :
    (toCore P H T).pt ((restrict P H h).pt x) = (toCore P H S).pt x := rfl

/-- On the domain of `core|S`, every run of an invoked function stays in `Rt.InFeat S`. -/
theorem dom_runs {x : Core.Pt H} (hx : coreDom S x) (a : Nat) (vs : List Val) {c : Config H}
    (hc : Steps P x.2 (invoke x.1 a vs) c) : Rt.InFeat S c :=
  Rt.steps_rtInFeat (Rt.hostIn_of_keeps hx.2.1 hx.2.2) hc (Rt.invoke_rtInFeat hx.1 a vs)

end Silmaril.Wasm.Models
