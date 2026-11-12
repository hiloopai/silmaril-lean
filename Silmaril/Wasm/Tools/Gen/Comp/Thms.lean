module

public import Silmaril.Wasm.Tools.Gen.Comp.Defs
public import Silmaril.Wasm.Tools.Gen.Core.Thms
public import Silmaril.Wasm.Tools.Gen.API.Thms
public import Silmaril.Wasm.Tools.Component.Validate.Thms

/-!
# The component instance: decoded core modules, shrinking, and restriction

* the verified objects over `Defs`: `coreBytesCheck_iff`, `bytesCheck_iff`, `compCheck_iff`
  (the checkers decide the properties), `compLang F S`, `empty_compValid` (the empty component
  is valid: `check_emptyBytes`, by kernel evaluation of the decoder), `compGen S`, `compMut S`,
  computing `compGenRun S`, `compMutRun S` (`compGen_run_eq`, `compMut_run_eq`);
* `coreBytes_encodes`: a valid component's core module bytes are a binary encoding
  (`Binary.Core.Encodes`, the grammar) of a module valid in `S`;
* `compValid_accepts`: **a valid component's bytes are accepted by the specification of
  `wasm-tools validate`** (`Validate.Accepts`: they decode in the component binary grammar to
  a component that is `ValidComponentCore3` under the flags, with no extra or gate problem);
* `compShrink_spec`: checked shrinking keeps validity and the predicate, does not grow, and
  ends in a local minimum;
* `compGen_mono`: a component generator of `S` is one of `T ≥ S` (validity is monotone).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Comp

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Tools.Gen.Core
open Silmaril.Wasm.Component.BinaryP3 (Ast)

/-! ## The verified objects -/

theorem coreBytesCheck_iff (S : FeatureSet) (b : ByteArray) :
    coreBytesCheck S b = true ↔ CoreBytesValid S b := by
  unfold coreBytesCheck CoreBytesValid
  cases h : Binary.Core.Decode.decodeModule b with
  | ok m => simp [featCheck_iff]
  | error e => simp


open Silmaril.Wasm.Tools.Component.Validate (CFlags) in
theorem bytesCheck_iff (F : CFlags) (bs : ByteArray) :
    bytesCheck F bs = true ↔ BytesAccepted F bs := by
  unfold bytesCheck BytesAccepted
  split <;> simp_all


open Silmaril.Wasm.Tools.Component.Validate (CFlags) in
theorem compCheck_iff (F : CFlags) (S : FeatureSet) (c : Ast) :
    compCheck F S c = true ↔ CompValid F S c := by
  unfold compCheck CompValid
  rw [Bool.and_eq_true]
  refine and_congr ?_ (by simp [List.all_eq_true, coreBytesCheck_iff])
  cases h : Silmaril.Wasm.Component.BinaryP3.encode c with
  | none => simp
  | some bs => simp [bytesCheck_iff]


open Silmaril.Wasm.Tools.Component.Validate in
/-- The empty component encodes to the preamble, which decodes, and the reference validator
accepts it (kernel evaluation). -/
theorem empty_core3 : Silmaril.Wasm.Component.BinaryP3.encode (.mk []) = some emptyBytes ∧
    ∃ rc ct, decode CFlags.default emptyBytes = .ok (.ref rc) ∧
      Silmaril.Wasm.Component.Validation.checkCore3? CFlags.default.feat rc = .ok ct := by
  refine ⟨by decide +kernel, ?_⟩
  have h : (match decode CFlags.default emptyBytes with
      | .ok (.ref c) => (Silmaril.Wasm.Component.Validation.checkCore3? CFlags.default.feat c).isOk
      | _ => false) = true := by decide +kernel
  revert h
  split
  · next rc hd =>
    intro h
    cases hc : Silmaril.Wasm.Component.Validation.checkCore3? CFlags.default.feat rc with
    | error e => simp [hc, Except.isOk, Except.toBool] at h
    | ok ct => exact ⟨rc, ct, hd, hc⟩
  · intro h; simp at h

open Silmaril.Wasm.Tools.Component.Validate in
/-- The preamble decodes to the empty component (reference syntax, `Decoded.ref []`), under every
flag set. -/
theorem decode_emptyBytes (F : CFlags) : decode F emptyBytes = .ok (.ref []) := by
  have h : (match Silmaril.Wasm.Component.Conformance.decodeP3 emptyBytes with
      | .ok [] => true
      | _ => false) = true := by decide +kernel
  have hd : Silmaril.Wasm.Component.Conformance.decodeP3 emptyBytes = .ok [] := by
    revert h
    split
    · next hd => intro _; exact hd
    · intro h; simp at h
  unfold decode
  rw [hd]
  rfl

open Silmaril.Wasm.Tools.Component.Validate in
/-- **`Validate.check` accepts the empty component** (its bytes, the preamble), under every
flag set: it decodes to `[]`, the reference validator's fold over no definitions finishes, and
the extra, gate and typed rules (total functions ; they were `partial`) find
nothing in `[]`. -/
theorem check_emptyBytes (F : CFlags) : ∃ ct, check F emptyBytes = .ok ct := by
  unfold check
  rw [decode_emptyBytes]
  exact ⟨_, rfl⟩

open Silmaril.Wasm.Tools.Component.Validate (CFlags) in
/-- **The component language** of component flags and a core feature set: `CompValid`. -/
def compLang (F : CFlags) (S : FeatureSet) : DecLang where
  Syn := Ast
  Valid := CompValid F S
  check := compCheck F S
  check_iff := compCheck_iff F S

/-- **The empty component is valid** (`CompValid`, with no exception): its bytes are accepted
by `Validate.check` (`check_emptyBytes`) and it has no core module. -/
theorem empty_compValid (F : Silmaril.Wasm.Tools.Component.Validate.CFlags) (S : FeatureSet) :
    CompValid F S (.mk []) :=
  ⟨⟨emptyBytes, empty_core3.1, check_emptyBytes F⟩, fun _ hb => by simp [coreModules, Ast.sections] at hb⟩


/-- **The component generator** of a feature set (default component flags). -/
def compGen (S : FeatureSet) : Generator (compLang dflt S).toLang :=
  Generator.guarded (compLang dflt S) (fun r n => Rand.run (Raw.component S n) r) (.mk [])
    (empty_compValid dflt S)

/-- **The component mutator**. -/
def compMut (S : FeatureSet) : Mutator (compLang dflt S).toLang :=
  Mutator.guarded (compLang dflt S) (Raw.mutate S)

/-- The verified component generator computes `compGenRun`. -/
theorem compGen_run_eq (S : FeatureSet) : (compGen S).run = compGenRun S := rfl

/-- The verified component mutator computes `compMutRun`. -/
theorem compMut_run_eq (S : FeatureSet) : (compMut S).run = compMutRun S := rfl

/-! ## Properties -/

/-- **Embedded core modules are encodings of valid modules.** -/
theorem coreBytes_encodes {F : Silmaril.Wasm.Tools.Component.Validate.CFlags} {S : FeatureSet}
    {c : Ast} (hc : CompValid F S c) {b : ByteArray}
    (hb : b ∈ coreModules c) : ∃ m, Binary.Core.Encodes b.data.toList m ∧ ValidIn S m := by
  obtain ⟨m, hd, hv⟩ := hc.2 b hb
  exact ⟨m, Binary.Core.Decode.decodeModule_sound hd, hv⟩

open Silmaril.Wasm.Tools.Component.Validate in
/-- **The encoding of a valid component is accepted by the component specification.** -/
theorem compValid_accepts {F : CFlags} {S : FeatureSet} {c : Ast} (hc : CompValid F S c) :
    ∃ bs, Silmaril.Wasm.Component.BinaryP3.encode c = some bs ∧
      ∃ rc ct, Accepts F bs rc ct := by
  obtain ⟨⟨bs, he, ct, hct⟩, -⟩ := hc
  obtain ⟨rc, hrc⟩ := check_sound hct
  exact ⟨bs, he, rc, ct, hrc⟩

open Silmaril.Wasm.Tools.Component.Validate (CFlags) in
/-- Component validity is monotone in the feature set. -/
theorem compValid_mono {F : CFlags} {S T : FeatureSet} (h : S ≤ T) {c : Ast}
    (hc : CompValid F S c) : CompValid F T c := by
  refine ⟨hc.1, fun b hb => ?_⟩
  obtain ⟨m, hd, hv⟩ := hc.2 b hb
  exact ⟨m, hd, validIn_mono h hv⟩

/-- **A component generator of `S` is one of `T ≥ S`.** -/
def compGen_mono {F : Silmaril.Wasm.Tools.Component.Validate.CFlags} {S T : FeatureSet}
    (h : S ≤ T) (g : Generator (compLang F S).toLang) : Generator (compLang F T).toLang :=
  g.mapValid id fun _ hc => compValid_mono h hc

/-- **Every generated component is accepted by the specification of `wasm-tools validate`**
(decodes in the grammar, `ValidComponentCore3`, no extra or gate problem), the fallback
(the empty component) included. -/
theorem compGen_spec (S : FeatureSet) (r : Rng) (n : Nat) :
    ∃ bs, Silmaril.Wasm.Component.BinaryP3.encode ((compGen S).run r n) = some bs ∧
      ∃ rc ct, Silmaril.Wasm.Tools.Component.Validate.Accepts dflt bs rc ct :=
  compValid_accepts ((compGen S).valid r n)

/-- **Checked component shrinking.** -/
theorem compShrink_spec (S : FeatureSet) (p : Ast → Bool) {c : Ast} (hv : CompValid dflt S c)
    (hp : p c = true) :
    CompValid dflt S (compShrink S p c) ∧ p (compShrink S p c) = true ∧
      Raw.size (compShrink S p c) ≤ Raw.size c ∧
      ∀ x ∈ Raw.cands (compShrink S p c), Raw.size x < Raw.size (compShrink S p c) →
        ((compLang dflt S).check x && p x) = false := by
  obtain ⟨h₁, h₂⟩ := Shrinker.shrink_valid (compLang dflt S) compShrinker p hv hp
  exact ⟨h₁, h₂, compShrinker.shrink_size_le _ c, compShrinker.shrink_local_min _ c⟩

end Silmaril.Wasm.Tools.Gen.Comp
