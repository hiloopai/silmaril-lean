module

public import Mathlib.Data.Set.Image
public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Relation

/-!
# `Wasm.Behaviour`: one vocabulary of observable outcomes

The shared observation type distinguishes a returned list of values, a trap,
an escaping exception and divergence. The included V1, V2 and Core 3.0 adapters
map their finite result types into this vocabulary; their behaviour-set APIs
add divergence through a separate infinite-trace predicate.

## The value parameter

`Behaviour` is parametric in the value type. V1 has numeric values; V2 and Core
3.0 also have vectors and references. `Behaviour.map` renames returned values
before outcomes are compared. Such a renaming alone does not prove a
cross-version execution simulation. See `Silmaril/Wasm/Behaviour/Relations.lean`
for the observation relations and `docs/projects/wasm-semantics.md` for the
versioned execution APIs.

## Why `throws` is a constructor and not an error

Core 3.0's `result` has three alternatives, and an escaping exception is a
genuinely different observation from a trap: the embedder can catch it. Versions
without exception handling simply never produce `throws`, which is recorded by
the range lemmas (`…_toBehaviour_ne_throws`) rather than by a narrower type.

## Stuckness

Stuckness has no constructor in `Behaviour`. A configuration with neither a
finite result nor an infinite trace can therefore have an empty behaviour set.
Excluding such configurations requires a separate progress or type-safety
theorem; this observation type does not establish one.
-/

@[expose] public section

namespace Silmaril.Wasm

universe u v w

/-- The observable outcome of running a WebAssembly computation: it returns
values, traps, throws an exception, or diverges. -/
inductive Behaviour (V : Type u) where
  /-- Terminated normally with these values. -/
  | returns (vs : List V)
  /-- Terminated with a trap. -/
  | traps
  /-- Terminated with an uncaught exception at address `a` (Core 3.0). -/
  | throws (a : Nat)
  /-- Did not terminate. -/
  | diverges
  deriving DecidableEq, Repr, Inhabited

namespace Behaviour

variable {V : Type u} {W : Type v} {X : Type w}

/-! ## Functoriality in the value type -/

/-- Rename the values of a behaviour along `f`. -/
def map (f : V → W) : Behaviour V → Behaviour W
  | .returns vs => .returns (vs.map f)
  | .traps => .traps
  | .throws a => .throws a
  | .diverges => .diverges

@[simp] theorem map_returns (f : V → W) (vs : List V) :
    map f (.returns vs) = .returns (vs.map f) := rfl

@[simp] theorem map_traps (f : V → W) : map f (.traps : Behaviour V) = .traps := rfl

@[simp] theorem map_throws (f : V → W) (a : Nat) :
    map f (.throws a : Behaviour V) = .throws a := rfl

@[simp] theorem map_diverges (f : V → W) : map f (.diverges : Behaviour V) = .diverges := rfl

@[simp] theorem map_id (b : Behaviour V) : map id b = b := by
  cases b <;> simp [map]

theorem map_comp (g : W → X) (f : V → W) (b : Behaviour V) :
    map g (map f b) = map (g ∘ f) b := by
  cases b <;> simp [map]

@[simp] theorem map_map (g : W → X) (f : V → W) (b : Behaviour V) :
    map g (map f b) = map (fun v => g (f v)) b := map_comp g f b

/-- An injective renaming is injective on behaviours. -/
theorem map_injective {f : V → W} (hf : Function.Injective f) :
    Function.Injective (map f) := by
  intro b b' h
  cases b <;> cases b' <;> simp_all [map, List.map_injective_iff.mpr hf |>.eq_iff]

/-! ## Classifying behaviours -/

/-- The behaviour produced no value: it trapped or diverged. This is the
"no result" class that the partial-correctness relation of
`Silmaril/Wasm/Behaviour/Relations.lean` collapses. -/
def NoResult : Behaviour V → Prop
  | .returns _ => False
  | .traps => True
  | .throws _ => False
  | .diverges => True

@[simp] theorem noResult_returns (vs : List V) : ¬ NoResult (.returns vs) := id
@[simp] theorem noResult_traps : NoResult (.traps : Behaviour V) := trivial
@[simp] theorem noResult_throws (a : Nat) : ¬ NoResult (.throws a : Behaviour V) := id
@[simp] theorem noResult_diverges : NoResult (.diverges : Behaviour V) := trivial

instance (b : Behaviour V) : Decidable (NoResult b) := by
  cases b <;> unfold NoResult <;> infer_instance

@[simp] theorem noResult_map (f : V → W) (b : Behaviour V) :
    NoResult (map f b) ↔ NoResult b := by
  cases b <;> simp [map]

/-- The behaviour terminated. -/
def Terminates : Behaviour V → Prop
  | .diverges => False
  | _ => True

@[simp] theorem terminates_returns (vs : List V) : Terminates (.returns vs) := trivial
@[simp] theorem terminates_traps : Terminates (.traps : Behaviour V) := trivial
@[simp] theorem terminates_throws (a : Nat) : Terminates (.throws a : Behaviour V) := trivial
@[simp] theorem terminates_diverges : ¬ Terminates (.diverges : Behaviour V) := id

/-- The values returned, when the behaviour returned. -/
def values? : Behaviour V → Option (List V)
  | .returns vs => some vs
  | _ => none

@[simp] theorem values?_returns (vs : List V) : (Behaviour.returns vs).values? = some vs := rfl

/-! ## Sets of behaviours

A semantics is in general nondeterministic — NaN payloads, the host relation,
`memory.grow` — so its observable content at a given entry point is a *set* of
behaviours rather than a single one. -/

/-- The image of a behaviour set under a value renaming. -/
def mapSet (f : V → W) (s : Set (Behaviour V)) : Set (Behaviour W) := map f '' s

@[simp] theorem mem_mapSet {f : V → W} {s : Set (Behaviour V)} {b : Behaviour W} :
    b ∈ mapSet f s ↔ ∃ a ∈ s, map f a = b := Set.mem_image _ _ _

theorem mapSet_mono {f : V → W} {s t : Set (Behaviour V)} (h : s ⊆ t) :
    mapSet f s ⊆ mapSet f t := Set.image_mono h

@[simp] theorem mapSet_id (s : Set (Behaviour V)) : mapSet id s = s := by
  ext b
  simp only [mapSet, Set.mem_image, map_id]
  exact ⟨fun ⟨a, ha, h⟩ => h ▸ ha, fun h => ⟨b, h, rfl⟩⟩

end Behaviour

end Silmaril.Wasm
