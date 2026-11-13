module

public import Silmaril.Wasm.Tools.Gen.API.Defs
public import Silmaril.Wasm.Models.Model.Defs

/-!
# The generator API over Wasm models

The generic API (`Silmaril.Wasm.Tools.Gen.API`) is about languages; this module reads a Wasm model
(`Silmaril.Wasm.Models.WasmModel`) as one and moves generators and mutators along embeddings of
models:

* `WasmModel.toLang`: a model's modules and their validity;
* `Generator.mapEmb`, `ByteGen.mapEmb`: a generator of `A` is one of `B` through any embedding
  `A.Emb B`, with the same outputs read through the module map (`Generator.mapEmb_run`);
* `Mutator.restrict`, `SemMutator.restrict`: a mutator of `B` that commutes with a conservative
  embedding is one of `A` (`Mutator.restrict_run`);
* `Kit M`: what a fuzzer needs of a model `M`: a checker deciding validity, a generator, a
  mutator and a shrinker; `Kit.lang` (the decidable language) and `Kit.shrink` (checked
  shrinking: candidates must be valid and satisfy the predicate).

`Thms`: `Kit.shrink_spec` (checked shrinking keeps validity and the predicate, does not grow and
ends in a local minimum) and the kits of the Core models: Wasm 1.0, 2.0, 3.0, Lime1 (Core 3.0
restricted to the feature sets `v10`, `v20`, `v30`, `lime1`) and WasmFX (CoreFX).

New definitions (moved from `Gen.API`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen

open Silmaril.Wasm.Models

/-- A model's modules and their validity. -/
abbrev _root_.Silmaril.Wasm.Models.WasmModel.toLang (M : WasmModel) : Lang := ⟨M.Module, M.Valid⟩

namespace Generator

/-- **A generator of `A` is a generator of `B`** through any embedding. -/
def mapEmb {A B : WasmModel} (e : A.Emb B) (g : Generator A.toLang) : Generator B.toLang :=
  g.mapValid e.mod e.valid

theorem mapEmb_run {A B : WasmModel} (e : A.Emb B) (g : Generator A.toLang) (r : Rng) (n : Nat) :
    (mapEmb e g).run r n = e.mod (g.run r n) := rfl

end Generator

namespace ByteGen

/-- **A byte-seeded generator of `A` is one of `B`** through any embedding. -/
def mapEmb {A B : WasmModel} (e : A.Emb B) (g : ByteGen A.toLang) : ByteGen B.toLang :=
  g.mapValid e.mod e.valid

end ByteGen

namespace Mutator

/-- **Restriction along a conservative embedding**: a mutator `μ` of `B` and a rewrite `μA` of
`A` that `e.mod` carries to `μ` make a mutator of `A`. -/
def restrict {A B : WasmModel} (e : A.Emb B) (he : e.Conservative) (μ : Mutator B.toLang)
    (μA : Rng → A.Module → A.Module) (hcomm : ∀ r m, e.mod (μA r m) = μ.run r (e.mod m)) :
    Mutator A.toLang where
  run := μA
  valid r m hm := by
    have h := μ.valid r _ (e.valid m hm)
    rw [← hcomm] at h
    exact he.reflect _ h

theorem restrict_run {A B : WasmModel} (e : A.Emb B) (he : e.Conservative)
    (μ : Mutator B.toLang) (μA : Rng → A.Module → A.Module)
    (hcomm : ∀ r m, e.mod (μA r m) = μ.run r (e.mod m)) :
    (restrict e he μ μA hcomm).run = μA := rfl

end Mutator

namespace SemMutator

/-- **Restriction along a conservative embedding** that reflects equivalence. -/
def restrict {A B : WasmModel} (e : A.Emb B) (he : e.Conservative)
    {EA : A.Module → A.Module → Prop} {EB : B.Module → B.Module → Prop}
    (hE : ∀ x y, EB (e.mod x) (e.mod y) → EA x y) (μ : SemMutator B.toLang EB)
    (μA : Rng → A.Module → A.Module) (hcomm : ∀ r m, e.mod (μA r m) = μ.run r (e.mod m)) :
    SemMutator A.toLang EA where
  toMutator := Mutator.restrict e he μ.toMutator μA hcomm
  equiv r m hm := by
    have h := μ.equiv r _ (e.valid m hm)
    rw [← hcomm] at h
    exact hE _ _ h

end SemMutator

/-- **A fuzzing kit for a Wasm model `M`**: a checker deciding validity, a generator, a mutator
and a shrinker of `M`'s modules. -/
structure Kit (M : WasmModel) where
  /-- The validity checker. -/
  check : M.Module → Bool
  /-- It decides validity. -/
  check_iff : ∀ m, check m = true ↔ M.Valid m
  /-- Valid modules from a seed and a size. -/
  generator : Generator M.toLang
  /-- A validity-preserving rewrite. -/
  mutator : Mutator M.toLang
  /-- Sizes and candidates. -/
  shrinker : Shrinker M.Module

namespace Kit

variable {M : WasmModel}

/-- The model as a decidable language. -/
def lang (k : Kit M) : DecLang := ⟨M.toLang, k.check, k.check_iff⟩

/-- **Checked shrinking**: the accepted candidates are valid and satisfy `p`. -/
def shrink (k : Kit M) (p : M.Module → Bool) (m : M.Module) : M.Module :=
  k.shrinker.shrink (fun c => k.check c && p c) m

/-- The same kit with another generator. -/
def withGen (k : Kit M) (g : Generator M.toLang) : Kit M := { k with generator := g }

end Kit

end Silmaril.Wasm.Tools.Gen
