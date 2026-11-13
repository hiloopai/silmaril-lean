module

public import Silmaril.Wasm.Component.Streams.Spec.Defs
public import Silmaril.Proofs.Wasm.Component.Streams.Spec

/-!
# Stream transformers: results

Proofs in `Silmaril.Proofs.Wasm.Component.Streams.Spec`.

**Functional correctness of the basic transformers** (the list specifications):

* `run_id`, `run_map`, `run_filter`, `run_filterMap`, `run_flatMap`: `xs`, `xs.map f`,
  `xs.filter p`, `xs.filterMap f`, `xs.flatMap f`, and the same for the output so far (`runP_*`):
  these transformers emit each item's output as soon as it is read.
* `run_take`, `runP_take`: `xs.take n`; `used_take`: `take n` reads exactly `min n |xs|` items, so
  it terminates on any input of at least `n` items without reading the rest
  (`run_take_prefix`: the output is the same on any input that agrees on the first `n` items).
* `chan_run_tee`: each output of `tee` is the input; `run_tee` gives the interleaving.

**Composition.** `run_comp`, `runP_comp`: the composite's output is the second transformer
applied to the first's (so-far and whole outputs alike), including early stops of either part.

**Prefix monotonicity** (`runP_mono`, `runP_le_run`): the output so far is a prefix of the output
of every extension and of the whole output. This is what makes the finite approximations
determine the behaviour on infinite inputs.

**Reading only what is used** (`feed_take_used`, `run_take_used`): the whole output depends only
on the items the transformer reads.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Tr

open Silmaril.Proofs.Wasm.Component.Streams.Spec

variable {σ τ α β γ : Type}

/-! ## Basic transformers -/

theorem runP_id (xs : List α) : (Tr.id : Tr Unit α α).runP xs = xs := by
  rw [runP_unit Tr.id (fun x => [x]) (fun _ _ => rfl) (fun _ => rfl)]
  simp

theorem run_id (xs : List α) : (Tr.id : Tr Unit α α).run xs = xs := by
  rw [run_unit Tr.id (fun x => [x]) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)]
  simp

theorem runP_map (f : α → β) (xs : List α) : (map f).runP xs = xs.map f := by
  rw [runP_unit (map f) (fun x => [f x]) (fun _ _ => rfl) (fun _ => rfl)]
  exact flatMap_singleton' f xs

theorem run_map (f : α → β) (xs : List α) : (map f).run xs = xs.map f := by
  rw [run_unit (map f) (fun x => [f x]) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)]
  exact flatMap_singleton' f xs

theorem runP_filter (p : α → Bool) (xs : List α) : (filter p).runP xs = xs.filter p := by
  rw [runP_unit (filter p) _ (fun _ _ => rfl) (fun _ => rfl)]
  exact flatMap_filter p xs

theorem run_filter (p : α → Bool) (xs : List α) : (filter p).run xs = xs.filter p := by
  rw [run_unit (filter p) _ (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)]
  exact flatMap_filter p xs

theorem runP_filterMap (f : α → Option β) (xs : List α) :
    (filterMap f).runP xs = xs.filterMap f := by
  rw [runP_unit (filterMap f) _ (fun _ _ => rfl) (fun _ => rfl)]
  exact flatMap_filterMap f xs

theorem run_filterMap (f : α → Option β) (xs : List α) :
    (filterMap f).run xs = xs.filterMap f := by
  rw [run_unit (filterMap f) _ (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)]
  exact flatMap_filterMap f xs

theorem runP_flatMap (f : α → List β) (xs : List α) : (flatMap f).runP xs = xs.flatMap f :=
  runP_unit (flatMap f) f (fun _ _ => rfl) (fun _ => rfl) xs

theorem run_flatMap (f : α → List β) (xs : List α) : (flatMap f).run xs = xs.flatMap f :=
  run_unit (flatMap f) f (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) xs

theorem runP_take (n : Nat) (xs : List α) : (take n : Tr Nat α α).runP xs = xs.take n := by
  show ((take n : Tr Nat α α).feed n xs).2 = _
  rw [feed_take]

theorem run_take (n : Nat) (xs : List α) : (take n : Tr Nat α α).run xs = xs.take n := by
  show ((take n : Tr Nat α α).feed n xs).2 ++ [] = _
  rw [feed_take, List.append_nil]

/-- `take n` reads exactly `min n |xs|` items. -/
theorem used_take' (n : Nat) (xs : List α) :
    (take n : Tr Nat α α).used (take n : Tr Nat α α).init xs = min n xs.length :=
  used_take n n xs

theorem run_tee (xs : List α) :
    (tee : Tr Unit α (Bool × α)).run xs = xs.flatMap fun x => [(false, x), (true, x)] :=
  run_unit tee _ (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) xs

/-- **Tee**: each output is the input. -/
theorem chan_run_tee (b : Bool) (xs : List α) :
    chan b ((tee : Tr Unit α (Bool × α)).run xs) = xs := by
  rw [run_tee]
  exact chan_tee b xs

/-! ## Composition -/

/-- **Composition, whole output.** -/
theorem run_comp' (T : Tr σ α β) (U : Tr τ β γ) (xs : List α) :
    (T.comp U).run xs = U.run (T.run xs) := run_comp T U xs

/-- **Composition, output so far.** -/
theorem runP_comp' (T : Tr σ α β) (U : Tr τ β γ) (xs : List α) :
    (T.comp U).runP xs = U.runP (T.runP xs) := runP_comp T U xs

/-! ## Monotonicity -/

/-- The output so far is a prefix of the output so far of every extension. -/
theorem runP_mono (T : Tr σ α β) (xs ys : List α) : T.runP xs <+: T.runP (xs ++ ys) := by
  rw [runP_append]
  exact List.prefix_append _ _

/-- The output so far is a prefix of the whole output. -/
theorem runP_le_run (T : Tr σ α β) (xs : List α) : T.runP xs <+: T.run xs :=
  List.prefix_append _ _

/-! ## Reading only what is used -/

/-- **The whole output depends only on the items read.** -/
theorem run_take_used (T : Tr σ α β) (xs : List α) (k : Nat) (hk : T.used T.init xs ≤ k) :
    T.run (xs.take k) = T.run xs := by
  show (T.feed T.init (xs.take k)).2 ++ T.flush (T.feed T.init (xs.take k)).1 = _
  rw [feed_take_used T T.init xs k hk]
  rfl

/-- `take n` gives the same output on inputs agreeing on their first `n` items. -/
theorem run_take_prefix (n : Nat) (xs ys : List α) (h : xs.take n = ys.take n) :
    (take n : Tr Nat α α).run xs = (take n : Tr Nat α α).run ys := by
  rw [run_take, run_take, h]

end Silmaril.Wasm.Component.Streams.Tr
