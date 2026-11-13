module

public import Silmaril.Wasm.Tools.Gen.Cmd.WitSmith.Defs
public import Silmaril.Wasm.Tools.Gen.API.Thms
public import Silmaril.Wasm.Wit.Valid.Thms
public import Silmaril.Wasm.Wit.Text.Thms
public import Silmaril.Wasm.Tools.Gen.Cmd.Inst.Thms
public import Silmaril.Wasm.Tools.Gen.Wit.Thms

/-!
# `wasm-tools wit-smith`: specification, and the instance of the generic API

* `witLang`: the language of WIT documents valid in wasm-wit's sense (`Wit.Valid` of the
  packages they declare: unique, well-formed names, resolved references, acyclic `use`,
  type and `include` graphs, …) that its printer can spell (`Text.printable`), decided by
  `checkDoc` (`checkDoc_iff`, from `Wit.check_iff`);
* `witSmith_valid`: **every document `wit-smith` generates is in `witLang`**;
* `witSmith_print`: its printed text reads back as the document's normal form
  (`Wit.Text.parse_print`), so the WIT the encoder is given is the generated document;
* `witGen cfg arbitrary`: `wit-smith` as a `Generator witLang.toLang` of the generic API (the
  seed drawn from the API's state, as `Inst.smithGen`), and `witGen_run`: it is
  `Generator.guarded` of the raw generator with the fallback;
* **one WIT language**: `witValidF_iff` relates the two validity notions (this file's
  `WitValid` with the features of the flags is `Gen.Wit.WitValidIn` of the packages, plus
  printability); `witSmith_inF`: every document uses only the features of its flags;
  `witGenU cfg arbitrary`: `wit-smith` as a generator of the API instance's
  `Gen.Wit.witLang (feat cfg arbitrary)` (the packages of the document), so it and
  `Gen.Wit.witGen` are generators of one language, related along the flags by
  `Gen.Wit.witGen_mono`.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.WitSmith

open Silmaril.Wasm.Wit

/-- The validity of `witLang`. -/
def WitValid (d : Document) : Prop := Wit.Valid d.packages ∧ Text.printable d = true

theorem checkDoc_iff (d : Document) : checkDoc d = true ↔ WitValid d := by
  simp only [checkDoc, Bool.and_eq_true, WitValid, Wit.check_iff]

/-- **The language of `wit-smith`.** -/
def witLang : Silmaril.Wasm.Tools.Gen.DecLang where
  Syn := Document
  Valid := WitValid
  check := checkDoc
  check_iff := checkDoc_iff

theorem fallback_valid : WitValid fallback := (checkDoc_iff fallback).mp (by decide +kernel)

/-- The fallback needs no feature. -/
theorem fallback_featOk (cfg : Config) (arbitrary : Bool) : featOk cfg arbitrary fallback = true := by
  have h : Silmaril.Wasm.Tools.Gen.Wit.universeNeeds fallback.packages = {} := by decide +kernel
  unfold featOk Silmaril.Wasm.Tools.Gen.Wit.universeInF
  rw [h]
  simp [Silmaril.Wasm.Tools.Gen.Wit.WitFeat.leB]

theorem witSmith_accepts (cfg : Config) (arbitrary : Bool) (seed : ByteArray) :
    checkDoc (witSmith cfg arbitrary seed) = true ∧ featOk cfg arbitrary (witSmith cfg arbitrary seed) = true := by
  unfold witSmith
  split
  · next h => exact Bool.and_eq_true _ _ |>.mp h
  · exact ⟨(checkDoc_iff _).mpr fallback_valid, fallback_featOk cfg arbitrary⟩

/-- **Every generated document is valid and printable.** -/
theorem witSmith_valid (cfg : Config) (arbitrary : Bool) (seed : ByteArray) :
    WitValid (witSmith cfg arbitrary seed) :=
  (checkDoc_iff _).mp (witSmith_accepts cfg arbitrary seed).1

/-- **Every generated document uses only the features of its flags.** -/
theorem witSmith_inF (cfg : Config) (arbitrary : Bool) (seed : ByteArray) :
    Silmaril.Wasm.Tools.Gen.Wit.universeInF (feat cfg arbitrary) (witSmith cfg arbitrary seed).packages =
      true :=
  (witSmith_accepts cfg arbitrary seed).2

/-- **The two WIT validity notions.** A document is valid here (`WitValid`: wasm-wit's
`Valid` of its packages and printable) and uses only the features of `F` iff its packages are
valid in the API instance's language at `F` (`Gen.Wit.WitValidIn F`) and it is printable. -/
theorem witValidF_iff (F : Silmaril.Wasm.Tools.Gen.Wit.WitFeat) (d : Document) :
    (WitValid d ∧ Silmaril.Wasm.Tools.Gen.Wit.universeInF F d.packages = true) ↔
      (Silmaril.Wasm.Tools.Gen.Wit.WitValidIn F d.packages ∧ Text.printable d = true) := by
  unfold WitValid Silmaril.Wasm.Tools.Gen.Wit.WitValidIn
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨⟨h₁, h₃⟩, h₂⟩
  · rintro ⟨⟨h₁, h₃⟩, h₂⟩; exact ⟨⟨h₁, h₂⟩, h₃⟩

/-- **`wit-smith` in the API instance's language**: its packages are valid in
`Gen.Wit.witLang (feat cfg arbitrary)`. -/
theorem witSmith_validIn (cfg : Config) (arbitrary : Bool) (seed : ByteArray) :
    Silmaril.Wasm.Tools.Gen.Wit.WitValidIn (feat cfg arbitrary) (witSmith cfg arbitrary seed).packages :=
  ((witValidF_iff _ _).mp ⟨witSmith_valid cfg arbitrary seed, witSmith_inF cfg arbitrary seed⟩).1

/-- **The printed text reads back** as the document's normal form. -/
theorem witSmith_print (cfg : Config) (arbitrary : Bool) (seed : ByteArray) :
    Text.parse (Text.print (witSmith cfg arbitrary seed)) =
      some (Text.Document.norm (witSmith cfg arbitrary seed)) :=
  Text.parse_print _ (witSmith_valid cfg arbitrary seed).2

/-- `witLang` at the features of a configuration (decided by `accepts`). -/
def witLangF (cfg : Config) (arbitrary : Bool) : Silmaril.Wasm.Tools.Gen.DecLang where
  Syn := Document
  Valid d := WitValid d ∧ featOk cfg arbitrary d = true
  check := accepts cfg arbitrary
  check_iff d := by
    rw [accepts, Bool.and_eq_true, checkDoc_iff]

/-- **`wit-smith` as a generator of the generic API**: the checked generator of `witLangF`,
read in `witLang`. -/
def witGen (cfg : Config) (arbitrary : Bool) : Silmaril.Wasm.Tools.Gen.Generator witLang.toLang :=
  (Silmaril.Wasm.Tools.Gen.Generator.guarded (witLangF cfg arbitrary)
    (fun r n => rawDoc cfg arbitrary (Silmaril.Wasm.Tools.Gen.rngBytes r n)) fallback
    ⟨fallback_valid, fallback_featOk cfg arbitrary⟩).mapValid id fun _ h => h.1

theorem witGen_run (cfg : Config) (arbitrary : Bool) (r : Silmaril.Wasm.Tools.Gen.Rng) (n : Nat) :
    (witGen cfg arbitrary).run r n = witSmith cfg arbitrary (Silmaril.Wasm.Tools.Gen.rngBytes r n) := rfl

/-- **`wit-smith` as a generator of `Gen.Wit.witLang`**, the WIT language of the API instance,
at the flags' point of the feature lattice: the packages of the generated document. -/
def witGenU (cfg : Config) (arbitrary : Bool) :
    Silmaril.Wasm.Tools.Gen.Generator (Silmaril.Wasm.Tools.Gen.Wit.witLang (feat cfg arbitrary)).toLang where
  run r n := (witSmith cfg arbitrary (Silmaril.Wasm.Tools.Gen.rngBytes r n)).packages
  valid _ _ := witSmith_validIn cfg arbitrary _

theorem witGenU_run (cfg : Config) (arbitrary : Bool) (r : Silmaril.Wasm.Tools.Gen.Rng) (n : Nat) :
    (witGenU cfg arbitrary).run r n = ((witGen cfg arbitrary).run r n).packages := rfl

end Silmaril.Wasm.Tools.Gen.Cmd.WitSmith
