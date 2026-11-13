module

public import Silmaril.Wasm.Models.Model.Defs
public import Silmaril.Wasm.Models.Charts.Thms
public import Silmaril.Wasm.Models.Syntax.Thms

/-!
# Embeddings give atlas transitions; the restricted Core models

* `Emb.toTransition e : Transition A.chart (B.viewChart e.readback)`: by `BTrans.ofEq` for
  `eq` (equal on every sentence), `BTrans.ofSubsetUniv` for `sub` (the target reflects universal
  sentences), `BTrans.ofSupsetUniv` for `sup` (the target preserves universal sentences);
  `Emb.toTransitionExist`: for `eq` and `sub`, existential sentences are preserved;
* `Emb.id`: the identity embedding (conservative);
* `coreModel P H S`: Core 3.0 restricted to `S` as a model (modules `ValidIn S`, points of
  `core|S`); `coreModel_chart`: its chart is `core|S` once observations are read back by
  `some`; `coreEmb h : (coreModel P H S).Emb (coreModel P H T)` for `S ≤ T`, conservative on
  the observations, so `core|S → core|T` is an equality transition of models too.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models

open Silmaril.Wasm.Atlas Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

namespace WasmModel

variable {A B : WasmModel}

/-- Reading back along `some` changes nothing. -/
theorem view_some (B : WasmModel) (p : B.Pt) (c : B.Call) : B.view some p c = B.obs p c := by
  ext o
  simp [view]

namespace Emb

/-- **An embedding is an atlas transition** (into the target chart read back along the
embedding). -/
def toTransition (e : A.Emb B) : Transition A.chart (B.viewChart e.readback) :=
  match hd : e.dir with
  | .eq => BTrans.ofEq e.pt e.call e.dom fun p hp c => by
      have h := e.sat p hp c
      rw [hd] at h
      exact h
  | .sub => BTrans.ofSubsetUniv e.pt e.call e.dom fun p hp c => by
      have h := e.sat p hp c
      rw [hd] at h
      exact h
  | .sup => BTrans.ofSupsetUniv e.pt e.call e.dom fun p hp c => by
      have h := e.sat p hp c
      rw [hd] at h
      exact h

/-- Source observations are read-back target observations when the direction is `eq` or
`sub`. -/
theorem obs_subset (e : A.Emb B) (hd : e.dir ≠ .sup) (p : A.Pt) (hp : A.dom p) (c : A.Call) :
    A.obs p c ⊆ B.view e.readback (e.pt p) (e.call c) := by
  have h := e.sat p hp c
  cases hdir : e.dir
  · rw [hdir] at h
    exact (show B.view e.readback (e.pt p) (e.call c) = A.obs p c from h) ▸ subset_refl _
  · rw [hdir] at h
    exact h
  · exact absurd hdir hd

/-- For `eq` and `sub` embeddings: existential sentences are preserved. -/
def toTransitionExist (e : A.Emb B) (hd : e.dir ≠ .sup) :
    Transition A.chart (B.viewChart e.readback) :=
  BTrans.ofSubsetExist e.pt e.call e.dom (obs_subset e hd)

/-- The identity embedding. -/
def id (A : WasmModel) : A.Emb A where
  mod m := m
  valid _ h := h
  pt p := p
  call c := c
  readback := some
  dom _ h := h
  dir := .eq
  sat p _ c := view_some A p c

theorem id_conservative (A : WasmModel) : (Emb.id A).Conservative :=
  ⟨fun _ h => h, rfl⟩

end Emb

end WasmModel

/-! ## The restricted Core models -/

/-- **Core 3.0 restricted to `S`** as a model: `ValidIn S` modules, the points of `core|S`. -/
def coreModel (P : Profile) (H : Type) (S : FeatureSet) : WasmModel where
  feats := S
  Module := Silmaril.Wasm.Module
  Valid := ValidIn S
  Pt := Core.Pt H
  Call := Core.Call
  Obs := Behaviour Val
  obs := Core.obs P
  dom := coreDom S

theorem coreModel_chart (P : Profile) (H : Type) (S : FeatureSet) :
    (coreModel P H S).chart = coreR P H S := rfl

/-- **`core|S` embeds in `core|T`** (`S ≤ T`): identity on modules, points and calls, equal
observations. -/
def coreEmb (P : Profile) (H : Type) {S T : FeatureSet} (h : S ≤ T) :
    (coreModel P H S).Emb (coreModel P H T) where
  mod m := m
  valid _ hm := validIn_mono h hm
  pt p := p
  call c := c
  readback := some
  dom _ hp := coreDom_mono h hp
  dir := .eq
  sat p _ c := WasmModel.view_some (coreModel P H T) p c

theorem coreEmb_dir (P : Profile) (H : Type) {S T : FeatureSet} (h : S ≤ T) :
    (coreEmb P H h).dir = .eq := rfl

/-- Restriction reflects validity on modules of `S`: a module of `S` valid at `T` is valid at
`S` (so `coreEmb` is conservative on `S`-modules). -/
theorem coreEmb_reflect (P : Profile) (H : Type) {S T : FeatureSet} (h : S ≤ T) {m : Module}
    (hm : Module.InFeat S m) (hv : (coreModel P H T).Valid ((coreEmb P H h).mod m)) :
    (coreModel P H S).Valid m :=
  ⟨hv.1, hm⟩

end Silmaril.Wasm.Models
