module

public import Silmaril.Wasm.Jco.Real.ValidAll.Thms
public import Silmaril.Proofs.Wasm.Jco.Real.ValidRange
public import Silmaril.Proofs.Wasm.Jco.Real.ValidWrap

/-!
# `AdaptorLimeValid` settled: valid below `2^31` functions, refuted from `2^31` on

`Silmaril.Wasm.Jco.Real.ValidAll` proves validity of the adaptors when `2 * |world| + 2 < 2^32`
and leaves the frozen `AdaptorLimeValid` (hypothesis `|world| + 2 < 2^32`) open for
`2^31 - 1 ≤ |world| < 2^32 - 2`. This module settles that range.

* **`adaptorLime_valid_of_lt`**, `adaptorLime_limeValid_of_lt`: the bound is widened to
  `|world| < 2^31`, the exact range where `mkIdx` wraps no index (the largest is the last shim's,
  `2 * |world| + 1`). The new case is `|world| = 2^31 - 1`. The same for `adaptorLimeW`
  (`adaptorLimeW_valid_of_lt`).
* **`adaptorLime_wrapMeta_invalid`**: for every `N` with `2^31 ≤ N < 2^32 - 2` there is a world
  of `N` functions, `wrapMeta N` (names `a^k`, all `(u32, u32, u32) -> ()`), that meets every
  hypothesis of `AdaptorLimeValid` and whose adaptor is **not** a valid Core 3.0 module:
  the shim of function `2^32 - N - 2` gets type index `0`, the allocator's `(i32, i32) -> i32`,
  and its body reads local `2`.
* **`not_adaptorLime_valid`**: `¬ AdaptorLimeValid`.

So, under the other hypotheses (distinct names, no `cabi_realloc`, fewer than `2^32 - 2` flat
parameters), the statement holds for every world with `|world| < 2^31` and fails for some world
of each size `N` with `2^31 ≤ N < 2^32 - 2`. Not every world of that size fails: whether one
does depends on whether the wrapped shims type at the types they wrap to (for example, if every
function were `(u32, u32) -> u32`, the allocator's type; not formalised here).

The refutation inverts Core 3.0 validation symbolically (`ModuleOk`, `FuncOk`, and an
induction over `InstrsOk` showing that every `local.get` of a typed sequence reads an existing
local); nothing is evaluated.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Real

open Silmaril.Wasm

/-- **`adaptorLime md` is a valid Lime1 module for every world of fewer than `2^31` functions**
with distinct names. -/
theorem adaptorLime_limeValid_of_lt (md : Meta) (hn : (importNames md).Nodup)
    (hr : "cabi_realloc" ∉ md.world.map (·.name))
    (hp : ∀ s ∈ md.world, (flatParams s.params).length + 2 < 2 ^ 32)
    (hw : md.world.length < 2 ^ 31) :
    Lime1.Validation.ModuleValid (adaptorLime md) :=
  Silmaril.Proofs.Wasm.Jco.Real.ValidRange.adaptorLime_limeValid md hn hr hp hw

/-- **The Core 3.0 image of `adaptorLime md` validates for every world of fewer than `2^31`
functions** with distinct names. -/
theorem adaptorLime_valid_of_lt (md : Meta) (hn : (importNames md).Nodup)
    (hr : "cabi_realloc" ∉ md.world.map (·.name))
    (hp : ∀ s ∈ md.world, (flatParams s.params).length + 2 < 2 ^ 32)
    (hw : md.world.length < 2 ^ 31) :
    Validation.ModuleValid (adaptorLime md).toCore :=
  Lime1.Validation.ModuleValid.toCore (adaptorLime_limeValid_of_lt md hn hr hp hw)

/-- `adaptorLimeW md` (multi-value style, typed locals) for fewer than `2^31` functions. -/
theorem adaptorLimeW_valid_of_lt (md : Meta) (hn : (importNames md).Nodup)
    (hr : "cabi_realloc" ∉ md.world.map (·.name))
    (hp : ∀ s ∈ md.world, (flatParams s.params).length + 2 < 2 ^ 32)
    (hq : ∀ s ∈ md.world, ∀ ts ns, wideOf s.result = some (ts, ns) →
      (flatParams s.params).length + ts.length + 2 < 2 ^ 32)
    (hw : md.world.length < 2 ^ 31) :
    Validation.ModuleValid (adaptorLimeW md).toCore :=
  Lime1.Validation.ModuleValid.toCore
    (Silmaril.Proofs.Wasm.Jco.Real.ValidRange.adaptorLimeW_limeValid md hn hr hp hq hw)

/-- The world of the refutation: `N` functions `a^k : (u32, u32, u32) -> ()`, allocator `b`. -/
abbrev wrapMeta (N : Nat) : Meta := Silmaril.Proofs.Wasm.Jco.Real.ValidWrap.wrapMeta N

/-- `wrapMeta N` meets every hypothesis of `AdaptorLimeValid` when `N + 2 < 2^32`. -/
theorem wrapMeta_hyps (N : Nat) :
    (importNames (wrapMeta N)).Nodup ∧ "cabi_realloc" ∉ (wrapMeta N).world.map (·.name) ∧
      (∀ s ∈ (wrapMeta N).world, (flatParams s.params).length + 2 < 2 ^ 32) ∧
      (wrapMeta N).world.length = N :=
  ⟨Silmaril.Proofs.Wasm.Jco.Real.ValidWrap.wrapMeta_nodup N,
    Silmaril.Proofs.Wasm.Jco.Real.ValidWrap.wrapMeta_realloc N,
    Silmaril.Proofs.Wasm.Jco.Real.ValidWrap.wrapMeta_params N,
    Silmaril.Proofs.Wasm.Jco.Real.ValidWrap.wrapMeta_length N⟩

/-- **For `2^31 ≤ N < 2^32 - 2` the adaptor of `wrapMeta N` is not a valid Core 3.0 module.** -/
theorem adaptorLime_wrapMeta_invalid {N : Nat} (h₁ : 2 ^ 31 ≤ N) (h₂ : N + 2 < 2 ^ 32) :
    ¬ Validation.ModuleValid (adaptorLime (wrapMeta N)).toCore :=
  Silmaril.Proofs.Wasm.Jco.Real.ValidWrap.adaptorLime_wrapMeta_invalid h₁ h₂

/-- **`AdaptorLimeValid` is false.** -/
theorem not_adaptorLime_valid : ¬ AdaptorLimeValid :=
  Silmaril.Proofs.Wasm.Jco.Real.ValidWrap.not_adaptorLime_valid

end Silmaril.Wasm.Jco.Real

/--
info: 'Silmaril.Wasm.Jco.Real.adaptorLime_valid_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Real.adaptorLime_valid_of_lt

/--
info: 'Silmaril.Wasm.Jco.Real.adaptorLimeW_valid_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Real.adaptorLimeW_valid_of_lt

/--
info: 'Silmaril.Wasm.Jco.Real.not_adaptorLime_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Real.not_adaptorLime_valid
