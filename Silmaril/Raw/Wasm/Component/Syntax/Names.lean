module

public import Silmaril.Wasm.Component.Reference.Syntax.Names.Defs

public import Silmaril.Raw.Wasm.Component.Syntax.Basic
public import Silmaril.Raw.Wasm.Component.WIT.Package
public import Mathlib.Data.List.Nodup

/-!
# Component import and export names

The lexical grammar of `externname` and the strong-uniqueness canonicalization of
`design/mvp/Explainer.md` at component-model revision `a25fc0b`
(https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/Explainer.md),
§Import and Export Definitions (the `externname`, `plainname`, `interfacename` productions,
lines 2748–2782) and §Name Uniqueness (lines 2872–2946).

This file builds on `WIT/Package.lean`, which already provides the `label` / `words`
productions (`WIT.IsLabel`, `WIT.isLabel`, `WIT.IsWords`) and step 1.1 of the canonicalization
(`WIT.canonChars`, `WIT.canonLabel`). It adds:
* `PlainName` and `parsePlainName?`: `label`, `[constructor]l`, `[method]r.m`, `[static]r.m`,
  and the 📡 `[get]l`, `[set]l`, `[method][get]r.m`, `[method][set]r.m`, `[static][get]r.m`,
  `[static][set]r.m` forms; every label must satisfy `WIT.IsLabel`;
* `InterfaceName` and `parseInterfaceName?`: `namespace:package/label@version`, with the 🪺
  nested namespaces and projections accepted and flagged by `InterfaceName.nested`;
* `ExternName.kind`, classifying a name as plain, interface or invalid;
* `strongCanon` (step 1, i.e. sub-steps 1.1–1.3, of §Name Uniqueness) and `stronglyUnique`
  (step 2).

All functions are structural over `List Char`, so the tests below are kernel-checked with
`decide +kernel`.

Not modelled or not claimed: the `interfaceversion` is kept as an opaque string that is only
checked to be non-empty and made of the semver characters `[0-9A-Za-z.+-]` (no SemVer 2.0 or
🔗 `canonversion` parsing; `WIT.SemVer` has no parser); canonical interface names (🔗) and
`versionsuffix` are not computed. For names that are not plain names (interface names, or
invalid names), `strongCanon` applies step 1.1 to the whole string, as the Explainer text does;
it is not claimed to agree with wasmparser on invalid names.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Syntax

/-! ## Character-list helpers -/

theorem isLabelChars_toList (s : String) : isLabelChars s.toList = WIT.isLabel s := rfl

/-! ## Plain names -/

/-! ## Interface names -/

/-! ## Extern names -/

/-! ## Strong uniqueness -/

theorem toList_strongCanon (s : String) : (strongCanon s).toList = strongCanonChars s.toList :=
  String.toList_ofList

/-- `strongCanon` is determined by `strongCanonChars`. -/
theorem strongCanon_eq_iff (a b : String) :
    strongCanon a = strongCanon b ↔ strongCanonChars a.toList = strongCanonChars b.toList := by
  rw [← toList_strongCanon, ← toList_strongCanon, String.toList_inj]

theorem allDistinct_iff (xs : List (List Char)) : allDistinct xs = true ↔ xs.Nodup := by
  induction xs with
  | nil => simp [allDistinct]
  | cons x xs ih => simp [allDistinct, ih]

theorem stronglyUnique_iff (names : List String) :
    stronglyUnique names = true ↔ StronglyUnique names := by
  rw [stronglyUnique, allDistinct_iff, StronglyUnique]
  have hinj : Function.Injective String.ofList := fun a b h => by
    rw [← String.toList_ofList (l := a), h, String.toList_ofList]
  have : names.map strongCanon =
      (names.map fun s => strongCanonChars s.toList).map String.ofList := by
    simp only [List.map_map]; rfl
  rw [this, List.nodup_map_iff hinj]

/-! ## Tests -/

-- Labels (`WIT.isLabel`).
example : WIT.isLabel "a-b-c" = true := by decide +kernel
example : WIT.isLabel "A-b" = true := by decide +kernel
example : WIT.isLabel "a--b" = false := by decide +kernel
example : WIT.isLabel "1-2-3" = false := by decide +kernel
example : WIT.isLabel "m1x3d-4CR0NYMS" = true := by decide +kernel

-- Plain names.
example : parsePlainName? "[method]foo.bar" = some (.method none "foo" "bar") := by
  decide +kernel
example : parsePlainName? "[method][get]foo.prop" = some (.method (some .get) "foo" "prop") := by
  decide +kernel
example : parsePlainName? "[static][set]foo.prop-2" =
    some (.static (some .set) "foo" "prop-2") := by decide +kernel
example : parsePlainName? "[constructor]foo" = some (.constructor "foo") := by decide +kernel
example : parsePlainName? "[get]prop" = some (.get "prop") := by decide +kernel
example : parsePlainName? "[set]prop" = some (.set "prop") := by decide +kernel
example : parsePlainName? "get-JSON" = some (.label "get-JSON") := by decide +kernel
example : parsePlainName? "[method]foo" = none := by decide +kernel
example : parsePlainName? "[method]foo.bar.baz" = none := by decide +kernel
example : parsePlainName? "[bogus]foo" = none := by decide +kernel
example : parsePlainName? "fooBar" = none := by decide +kernel
example : parsePlainName? "wasi:http/types" = none := by decide +kernel

-- Interface names.
example : parseInterfaceName? "wasi:http/types@0.2.0" =
    some { namespaces := ["wasi"], package := "http", projections := ["types"],
           version := some "0.2.0" } := by decide +kernel
example : parseInterfaceName? "foo:bar/baz" =
    some { namespaces := ["foo"], package := "bar", projections := ["baz"] } := by
  decide +kernel
example : (parseInterfaceName? "a:b:c/d/e").map InterfaceName.nested = some true := by
  decide +kernel
example : parseInterfaceName? "wasi:http" = none := by decide +kernel
example : parseInterfaceName? "WASI:http/types" = none := by decide +kernel
example : parseInterfaceName? "wasi:http/types@" = none := by decide +kernel

-- Extern name kinds.
example : ExternName.kind { name := "[static]foo.baz" } = .plain (.static none "foo" "baz") := by
  decide +kernel
example : ExternName.valid { name := "wasi:http/handler" } = true := by decide +kernel
example : ExternName.valid { name := "a b" } = false := by decide +kernel

-- Canonical forms. `fooBar` is not a label, but its canonical form collides with `foo-bar`.
example : strongCanon "foo-bar" = strongCanon "fooBar" := by decide +kernel
example : strongCanon "a-b" = strongCanon "ab" := by decide +kernel
example : strongCanon "[method]foo.foo" = "foo" := by decide +kernel
example : strongCanon "[method][set]foo.prop" = "[set]foo.prop" := by decide +kernel
example : strongCanon "foo:bar/BAZ" = "foo:bar/baz" := by decide +kernel

example : stronglyUnique explainerUniqueNames = true := by decide +kernel

example : explainerConflictingNames.all
    (fun n => stronglyUnique (n :: explainerUniqueNames) = false) = true := by decide +kernel

-- `[set]foo` and `foo` are strongly unique; `[get]foo` and `foo` are not.
example : stronglyUnique ["foo", "[set]foo"] = true := by decide +kernel
example : stronglyUnique ["foo", "[get]foo"] = false := by decide +kernel

end Silmaril.Wasm.Component.Syntax
