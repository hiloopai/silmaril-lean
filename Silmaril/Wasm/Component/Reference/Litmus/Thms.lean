module

public import Silmaril.Wasm.Component.Reference.Litmus.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Thms
public import Silmaril.Wasm.Component.Reference.Example.Defs
import Silmaril.Proofs.Wasm.Component.Reference.Litmus
import Silmaril.Proofs.Wasm.Component.Reference.LitmusRef
import Silmaril.Proofs.Wasm.Component.Reference.LitmusImp
import Silmaril.Proofs.Wasm.Component.Reference.LitmusSoundI
import Silmaril.Proofs.Wasm.Component.Reference.LitmusSeqI
import Silmaril.Proofs.Wasm.Component.Reference.LitmusLink
import Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkSeqRef
import Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkIR

/-!
# Litmus components: theorems

For `adderS` (`add(a: u32, b: u32) -> u32`), `recordS` (a record argument) and `optionS` (an
`option<u32>` argument):

* the fragment conditions hold and the reference validator accepts the translations
  (`*_good`, `*_valid`);
* **every profile, all arguments**: the canonical-ABI specification returns the expected
  result (`adder_spec`, `record_spec`, `option_some_spec`, `option_none_spec`; Core 3.0 runs built
  from `Step` rules), hence the IR denotation over `modSem P` has the corresponding play
  (`adder_ir`, `record_ir`, `option_some_ir`, `option_none_ir`, through `specToIR`);
* **reference machine over `core3 neverFail`**: the export calls return the same results
  (`adder_ref`, `record_ref`, `option_some_ref`, `option_none_ref`, closed runs of the copied
  drivers checked by `decide +kernel`);
* over `core3P P`, the reference behaviours are matched by the IR (`Simple.sound`, e.g.
  `adder_sound`, unconditional; the modules are instantiated as the IR assumes, `*_inst`, and
  are within the flat arities, `adderS_arity`);
* call sequences: two calls of the adder are one multi-question play of the IR denotation, at
  every profile (`adder_seq_ir`, through `seqSpecToIR`), and every reference behaviour of a
  sequence of adder calls is matched by the IR (`adder_seq_sound`, an instance of
  `Simple.sound_seq`);
* with an import (`fwdS`, the import `g` lowered into a core module that re-exports it, lifted
  as `f`): the module is instantiated as the IR assumes (`fwd_isInst`, `fwdS_good`), and at every
  profile the IR denotation over `impSem P` forwards `f(x)` to the component import `g(x)` and
  returns its answer `y` (`fwd_ir`, through `simpleI_specToIR` from the instance's play: a
  callout at once, found by `decompose?`); the validator accepts `fwdS.toRef` (`fwdS_valid`) and
  the reference machine over `core3 neverFail`, with a host answering `g(n) = n + 1`, returns
  `4` for `f(3)` (`fwd_ref`); `fwdS` is wired as `SimpleI.toRef` assumes (`fwdS_inst`, the
  validated import type checked by kernel evaluation), so at every profile every reference
  behaviour of `f(x)` under the host `g(n) = n + 1` over `core3P P` is matched by the IR
  (`fwd_sound`, an instance of `SimpleI.sound`); two calls of `f` on one instance are one IR
  play, each forwarded to `g` (`fwd_seq_ir`, every profile, all arguments and answers, through
  `seqI_den` from two instance plays), and every reference behaviour of `f(x)` then `f(y)` under
  the host `g(n) = n + 1` is matched by the IR (`fwd_seq_sound`, an instance of
  `SimpleI.sound_seq`); with the stateful counter host `fwdC` (`g(n) = n + s` in state `s`,
  moving to `s + 1`): `fwd_soundS` and `fwd_seq_soundS` (instances of `SimpleI.soundS` and
  `SimpleI.sound_seqS`), and the reference machine threads the host state between calls
  (`fwd_seq_refS`: from state `10`, `f(3)` then `f(3)` return `13` then `14`, by kernel
  evaluation of the copied drivers over `core3 neverFail`);
* two components linked (`dblFwdL`, the doubler answering `fwdS`'s import): the validator
  accepts the translation (`dblFwdL_valid`), the reference machine over `core3 neverFail` returns
  `6` for `f(3)` (`dblFwd_ref`) and, on one instance, `6` then `10` for `f(3)` then `f(5)`
  (`dblFwd_seq_ref`, kernel evaluation of the copied drivers), and the linked IR doubles at every
  profile (`dblFwd_ir`);
* the hypotheses of `RefToSpecAll` are needed: without `Simple.Inst` the statement is false
  (`refToSpec_needs_inst`, the component `oobS`), and validity of the translation does not follow
  from the fragment conditions (`toRef_valid_not_general`, the component `badNameS`).

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.{Litmus,LitmusRef,LitmusImp,LitmusSoundI,LitmusSeqI,
  LitmusLink,LitmusLinkSeqRef,LitmusLinkIR}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference.Litmus

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.Core3Adder (emb first)
open Silmaril.Wasm.Numerics (Profile)

theorem adderS_good : adderS.Good := Silmaril.Proofs.Wasm.Component.Reference.Litmus.adderS_good
theorem recordS_good : recordS.Good := Silmaril.Proofs.Wasm.Component.Reference.Litmus.recordS_good
theorem optionS_good : optionS.Good := Silmaril.Proofs.Wasm.Component.Reference.Litmus.optionS_good

theorem adderS_valid : ∃ ct, check? Silmaril.Wasm.Component.Features.p2 adderS.toRef = .ok ct :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.adderS_valid
theorem recordS_valid : ∃ ct, check? Silmaril.Wasm.Component.Features.p2 recordS.toRef = .ok ct :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.recordS_valid
theorem optionS_valid : ∃ ct, check? Silmaril.Wasm.Component.Features.p2 optionS.toRef = .ok ct :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.optionS_valid

/-- The adder's specification returns `x + y`, at every profile. -/
theorem adder_spec (P : Profile) (x y : BitVec 32) :
    Outcome.returns (some [toRefVal (.u32 (x + y))]) ∈
      exportSpec P adderS adderS.exports[0] [.u32 x, .u32 y] :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.adder_spec P x y

/-- A record argument: `sum({x, y})` returns `x + y`, at every profile. -/
theorem record_spec (P : Profile) (x y : BitVec 32) :
    Outcome.returns (some [toRefVal (.u32 (x + y))]) ∈
      exportSpec P recordS recordS.exports[0] [.record [.u32 x, .u32 y]] :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.record_spec P x y

/-- A variant argument: `get-or-zero(some y)` returns `y`, at every profile. -/
theorem option_some_spec (P : Profile) (y : BitVec 32) :
    Outcome.returns (some [toRefVal (.u32 y)]) ∈
      exportSpec P optionS optionS.exports[0] [.variant 1 (some (.u32 y))] :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.option_some_spec P y

/-- `get-or-zero(none)` returns `0`, at every profile. -/
theorem option_none_spec (P : Profile) :
    Outcome.returns (some [toRefVal (.u32 0)]) ∈
      exportSpec P optionS optionS.exports[0] [.variant 0 none] :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.option_none_spec P

/-- **The IR adder answers `x + y`**, at every profile. -/
theorem adder_ir (P : Profile) (x y : BitVec 32) :
    [.inr (.ask (⟨0, by decide⟩, .vals [.u32 x, .u32 y])),
      .inr (.ans (⟨0, by decide⟩, .vals [.u32 x, .u32 y]) (some (.vals [.u32 (x + y)])))] ∈
      adderS.toComp.den (modSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.adder_ir P x y

theorem record_ir (P : Profile) (x y : BitVec 32) :
    [.inr (.ask (⟨0, by decide⟩, .vals [.record [.u32 x, .u32 y]])),
      .inr (.ans (⟨0, by decide⟩, .vals [.record [.u32 x, .u32 y]])
        (some (.vals [.u32 (x + y)])))] ∈ recordS.toComp.den (modSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.record_ir P x y

theorem option_some_ir (P : Profile) (y : BitVec 32) :
    [.inr (.ask (⟨0, by decide⟩, .vals [.variant 1 (some (.u32 y))])),
      .inr (.ans (⟨0, by decide⟩, .vals [.variant 1 (some (.u32 y))])
        (some (.vals [.u32 y])))] ∈ optionS.toComp.den (modSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.option_some_ir P y

theorem option_none_ir (P : Profile) :
    [.inr (.ask (⟨0, by decide⟩, .vals [.variant 0 none])),
      .inr (.ans (⟨0, by decide⟩, .vals [.variant 0 none]) (some (.vals [.u32 0])))] ∈
      optionS.toComp.den (modSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.option_none_ir P

/-- **The reference machine** over `core3 neverFail`: `add(3, 4)` returns `7`. -/
theorem adder_ref : Outcome.returns (some [toRefVal (.u32 7)]) ∈
    exportBehaviours first.prof (Host.ofEmbedder emb) () adderS.toRef [] "add"
      [toRefVal (.u32 3), toRefVal (.u32 4)] :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.adder_ref

theorem record_ref : Outcome.returns (some [toRefVal (.u32 7)]) ∈
    exportBehaviours first.prof (Host.ofEmbedder emb) () recordS.toRef [] "sum"
      [toRefVal (.record [.u32 3, .u32 4])] :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.record_ref

theorem option_some_ref : Outcome.returns (some [toRefVal (.u32 5)]) ∈
    exportBehaviours first.prof (Host.ofEmbedder emb) () optionS.toRef [] "get-or-zero"
      [toRefVal (.variant 1 (some (.u32 5)))] :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.option_some_ref

theorem option_none_ref : Outcome.returns (some [toRefVal (.u32 0)]) ∈
    exportBehaviours first.prof (Host.ofEmbedder emb) () optionS.toRef [] "get-or-zero"
      [toRefVal (.variant 0 none)] :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.option_none_ref

/-- Two exports: `twoS.toRef` is accepted, and each export runs its own lifted function. -/
theorem twoS_valid : ∃ ct, check? Silmaril.Wasm.Component.Features.p2 twoS.toRef = .ok ct :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.twoS_valid

theorem two_add_ref : Outcome.returns (some [toRefVal (.u32 7)]) ∈
    exportBehaviours first.prof (Host.ofEmbedder emb) () twoS.toRef [] "add"
      [toRefVal (.u32 3), toRefVal (.u32 4)] :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.two_add_ref

theorem two_sum_ref : Outcome.returns (some [toRefVal (.u32 7)]) ∈
    exportBehaviours first.prof (Host.ofEmbedder emb) () twoS.toRef [] "sum"
      [toRefVal (.record [.u32 3, .u32 4])] :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.two_sum_ref

theorem adderS_inst : adderS.Inst := Silmaril.Proofs.Wasm.Component.Reference.Litmus.adderS_inst
theorem recordS_inst : recordS.Inst := Silmaril.Proofs.Wasm.Component.Reference.Litmus.recordS_inst
theorem optionS_inst : optionS.Inst := Silmaril.Proofs.Wasm.Component.Reference.Litmus.optionS_inst

/-- **The reference half needs `Simple.Inst`**: the statement of `RefToSpecAll` without it is
false. `oobS` meets every other hypothesis; its module does not instantiate (out-of-bounds data
segment), the reference machine over `core3P P` traps when instantiating `oobS.toRef`, and the
specification is empty. -/
theorem refToSpec_needs_inst : ¬ ∀ (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple), c.Good → c.FloatFree →
    (∃ ct, check? Silmaril.Wasm.Component.Features.p2 c.toRef = .ok ct) →
    ∀ x ∈ c.exports, ∀ vs, ValTy.checkList x.ty.params vs = true →
      exportBehaviours prof (refHost P) () c.toRef [] x.name (vs.map toRefVal) ⊆
        exportSpec P c x vs :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.refToSpec_needs_inst

/-- **Validity of the translation is not general**: `badNameS` (the adder exported as `a_b`)
meets the fragment conditions and the reference validator rejects its translation, so the
validity hypothesis of `RefToSpecAll` cannot be dropped. -/
theorem toRef_valid_not_general : ¬ ∀ c : Simple, c.Good → c.FloatFree → c.Inst →
    ∃ ct, check? Silmaril.Wasm.Component.Features.p2 c.toRef = .ok ct :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.toRef_valid_not_general

/-- `adderS` is within the flat arities. -/
theorem adderS_arity : adderS.Arity := by
  intro x hx
  simp only [adderS, List.mem_singleton] at hx
  subst hx
  decide

/-- Over `core3P P`, every reference behaviour of `add(x, y)` is matched by the IR. -/
theorem adder_sound (P : Profile)
    (prof : Silmaril.Wasm.Component.ProfileKind) (x y : BitVec 32) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHost P) () adderS.toRef [] "add"
      ([.u32 x, .u32 y].map toRefVal)) :
    IRObs (k := adderS.toComp.exports.length) (adderS.toComp.den (modSem P))
      ⟨0, by decide⟩ [.u32 x, .u32 y] b :=
  Simple.sound P prof adderS adderS_good
    (by intro x hx; simp only [adderS, List.mem_singleton] at hx; subst hx; exact ⟨rfl, rfl⟩)
    adderS_inst adderS_arity ⟨0, by decide⟩ _ rfl b hb

/-- **Two calls of the adder are one play of the IR**, for every profile and all arguments
(through the sequence half `seqSpecToIR`). -/
theorem adder_seq_ir (P : Profile) (x y x' y' : BitVec 32) :
    seqMoves adderS [(⟨0, by decide⟩, [.u32 x, .u32 y]), (⟨0, by decide⟩, [.u32 x', .u32 y'])]
      [[.u32 (x + y)], [.u32 (x' + y')]] ∈ adderS.toComp.den (modSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.adder_seq_ir P x y x' y'

/-- Over `core3P P`, every reference behaviour of a sequence of adder calls `add(xᵢ, yᵢ)` followed
by `add(x, y)` is matched by the IR (`Simple.sound_seq`). -/
theorem adder_seq_sound (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (args : List (BitVec 32 × BitVec 32)) (x y : BitVec 32)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (refHost P) () adderS.toRef
      (args.map fun a => ("add", [toRefVal (.u32 a.1), toRefVal (.u32 a.2)])) "add"
      [toRefVal (.u32 x), toRefVal (.u32 y)]) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      seqMoves adderS (args.map fun a => (⟨0, by decide⟩, [.u32 a.1, .u32 a.2])) wss ∈
        adderS.toComp.den (modSem P) ∧
      SeqIRObs adderS (adderS.toComp.den (modSem P))
        (args.map fun a => (⟨0, by decide⟩, [.u32 a.1, .u32 a.2])) wss ⟨0, by decide⟩
        [.u32 x, .u32 y] p.2 := by
  have hf : adderS.FloatFree := by
    intro x hx
    simp only [adderS, List.mem_singleton] at hx
    subst hx
    exact ⟨rfl, rfl⟩
  have ht : TypedCalls adderS (args.map fun a => (⟨0, by decide⟩, [.u32 a.1, .u32 a.2])) := by
    intro q hq
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hq
    rfl
  have hcalls : (args.map fun a => (⟨0, by decide⟩, [.u32 a.1, .u32 a.2])).map
      (fun q : Fin adderS.exports.length × List Silmaril.Wasm.Component.Val =>
        (adderS.exports[q.1].name, q.2.map toRefVal)) =
      args.map fun a => ("add", [toRefVal (.u32 a.1), toRefVal (.u32 a.2)]) := by
    rw [List.map_map]
    rfl
  exact Simple.sound_seq P prof adderS adderS_good hf adderS_inst adderS_arity _ ⟨0, by decide⟩
    _ ht rfl p (hcalls ▸ hp)

theorem fwdS_good : fwdS.Good := Silmaril.Proofs.Wasm.Component.Reference.Litmus.fwdS_good

theorem fwd_isInst : fwdMod.IsInst fwdInst :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.fwd_isInst

/-- **The IR forwards `f(x)` to the import `g`** and returns its answer, for every profile and
all `x` and `y`. -/
theorem fwd_ir (P : Profile) (x y : BitVec 32) :
    ([.inr (.ask (⟨0, by decide⟩, .vals [.u32 x])),
      .inl (.ask (⟨0, by decide⟩, .vals [.u32 x])),
      .inl (.ans (m := (⟨0, by decide⟩, .vals [.u32 x])) (some (.vals [.u32 y]))),
      .inr (.ans (m := (⟨0, by decide⟩, .vals [.u32 x])) (some (.vals [.u32 y])))] :
      List (Move (sigN fwdS.imports.length) (sigN fwdS.toComp.exports.length))) ∈
      fwdS.toComp.den (impSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.fwd_ir P x y

theorem fwdS_valid : ∃ ct, check? Silmaril.Wasm.Component.Features.p2 fwdS.toRef = .ok ct :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.fwdS_valid

/-- **The reference machine forwards `f(3)` to the host's `g`** and returns `g(3) = 4`. -/
theorem fwd_ref : Outcome.returns (some [toRefVal (.u32 4)]) ∈
    exportBehavioursI first.prof (Host.ofEmbedder embI) () fwdS.toRef fwdS.imports "f"
      [toRefVal (.u32 3)] :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.fwd_ref

/-- `fwdS` is wired as `SimpleI.toRef` assumes. -/
theorem fwdS_inst : fwdS.Inst := Silmaril.Proofs.Wasm.Component.Reference.Litmus.fwdS_inst

/-- **Soundness with imports on `fwdS`** (every profile and component choice profile, all `x`):
every reference behaviour of `f(x)` under the host `g(n) = n + 1` over `core3P P` is matched by
the IR denotation. -/
theorem fwd_sound (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) (x : BitVec 32) :
    ∀ b ∈ exportBehavioursI prof (answerHost P fwdG) () fwdS.toRef fwdS.imports "f"
        [toRefVal (.u32 x)],
      IRObsI (fwdS.toComp.den (impSem P)) ⟨0, by decide⟩ [.u32 x] fwdG b :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.fwd_sound P prof x

/-- **Two calls of `f` on one instance of `fwdS` are one IR play**, `f(x)` forwarded to `g`
answered `y` and returning `y`, then `f(x')` forwarded to `g` answered `y'` and returning `y'`
(every profile, all arguments and answers). -/
theorem fwd_seq_ir (P : Profile) (x y x' y' : BitVec 32) :
    seqMovesI fwdS [(⟨0, by decide⟩, [.u32 x]), (⟨0, by decide⟩, [.u32 x'])]
      [[⟨(⟨0, by decide⟩, .vals [.u32 x]), some (.vals [.u32 y])⟩],
        [⟨(⟨0, by decide⟩, .vals [.u32 x']), some (.vals [.u32 y'])⟩]]
      [[.u32 y], [.u32 y']] ∈ fwdS.toComp.den (impSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.fwd_seq_ir P x y x' y'

/-- **Soundness for two calls with imports on `fwdS`** (every profile and component choice
profile, all `x`, `y`): every reference behaviour of `f(x)` then `f(y)` on one instance under
the host `g(n) = n + 1` over `core3P P` is matched by the IR denotation (`SimpleI.sound_seq`). -/
theorem fwd_seq_sound (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (x y : BitVec 32) :
    ∀ p ∈ seqBehavioursI prof (answerHost P fwdG) () fwdS.toRef fwdS.imports
        [("f", [toRefVal (.u32 x)])] "f" [toRefVal (.u32 y)],
      ∃ (wss : List (List Silmaril.Wasm.Component.Val))
        (dss : List (List (Σ _ : (sigN fwdS.imports.length).Op, Option Payload))),
        p.1 = wss.map (·.map toRefVal) ∧ (∀ ds ∈ dss, ∀ d ∈ ds, HostAnswers fwdG d) ∧
        seqMovesI fwdS [(⟨0, by decide⟩, [.u32 x])] dss wss ∈ fwdS.toComp.den (impSem P) ∧
        SeqIRObsI fwdS (fwdS.toComp.den (impSem P)) [(⟨0, by decide⟩, [.u32 x])] dss wss
          ⟨0, by decide⟩ [.u32 y] fwdG p.2 :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.fwd_seq_sound P prof x y

/-- **Soundness with a stateful host on `fwdS`** (proved). -/
theorem fwd_soundS (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) (x : BitVec 32)
    (s₀ : Nat) :
    ∀ b ∈ exportBehavioursI prof (answerHostS P fwdC) s₀ fwdS.toRef fwdS.imports "f"
        [toRefVal (.u32 x)],
      IRObsIS (fwdS.toComp.den (impSem P)) ⟨0, by decide⟩ [.u32 x] fwdC s₀ b :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.fwd_soundS P prof x s₀

/-- **Sequences with a stateful host on `fwdS`** (proved). -/
theorem fwd_seq_soundS (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (x y : BitVec 32) (s₀ : Nat) :
    ∀ p ∈ seqBehavioursI prof (answerHostS P fwdC) s₀ fwdS.toRef fwdS.imports
        [("f", [toRefVal (.u32 x)])] "f" [toRefVal (.u32 y)],
      ∃ (wss : List (List Silmaril.Wasm.Component.Val))
        (dss : List (List (Σ _ : (sigN fwdS.imports.length).Op, Option Payload))) (s₁ : Nat),
        p.1 = wss.map (·.map toRefVal) ∧ HostRun fwdC s₀ dss.flatten s₁ ∧
        seqMovesI fwdS [(⟨0, by decide⟩, [.u32 x])] dss wss ∈ fwdS.toComp.den (impSem P) ∧
        SeqIRObsIS fwdS (fwdS.toComp.den (impSem P)) [(⟨0, by decide⟩, [.u32 x])] dss wss
          ⟨0, by decide⟩ [.u32 y] fwdC s₁ p.2 :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.fwd_seq_soundS P prof x y s₀

/-- **The reference machine threads the host state between calls** (proved, kernel
evaluation): under the stateful embedder `embC` from host state `10`, `f(3)` then `f(3)` return
`13` then `14`. -/
theorem fwd_seq_refS :
    ([[toRefVal (.u32 13)]], Outcome.returns (some [toRefVal (.u32 14)])) ∈
      seqBehavioursI Silmaril.Wasm.Component.Reference.Core3Adder.first.prof
        (Silmaril.Wasm.Component.Reference.Host.ofEmbedder embC) 10 fwdS.toRef fwdS.imports
        [("f", [toRefVal (.u32 3)])] "f" [toRefVal (.u32 3)] :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.fwd_seq_refS

/-! ## Two components linked -/

/-- The doubler's translation is accepted by the reference validator. -/
theorem dblS_valid : ∃ ct, check? Silmaril.Wasm.Component.Features.p2 dblS.toRef = .ok ct :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.dblS_valid

/-- The translation of `dblFwdL` (nested components, `instantiate` with an aliased export) is
accepted by the reference validator. -/
theorem dblFwdL_valid :
    ∃ ct, check? Silmaril.Wasm.Component.Features.p2 dblFwdL.toRef = .ok ct :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.dblFwdL_valid

/-- **One component's export answers another's import** in the reference machine: `f(3)` of
`dblFwdL` returns `6` over `core3 neverFail` (closed run of the copied drivers). -/
theorem dblFwd_ref : Outcome.returns (some [toRefVal (.u32 6)]) ∈
    exportBehaviours first.prof (Host.ofEmbedder emb) () dblFwdL.toRef [] "f"
      [toRefVal (.u32 3)] :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.dblFwd_ref

/-- **Two sequential calls of the linked components** in the reference machine (proved, kernel
evaluation): on one instance of `dblFwdL` over `core3 neverFail`, `f(3)` returns `6`, then `f(5)`
returns `10`. A concrete behaviour of the kind `dblFwd_sound_seq` (`LinkSound`) matches with the
linked IR. -/
theorem dblFwd_seq_ref :
    ([[toRefVal (.u32 6)]], Outcome.returns (some [toRefVal (.u32 10)])) ∈
      seqBehaviours first.prof (Host.ofEmbedder emb) () dblFwdL.toRef
        [("f", [toRefVal (.u32 3)])] "f" [toRefVal (.u32 5)] :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.dblFwd_seq_ref

/-- The doubler satisfies the fragment conditions of `Simple`. -/
theorem dblS_good : dblS.Good :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.dblS_good

/-- **The linked IR doubles**, for every profile and all `x`: the denotation of `dblFwdL.toComp`
over `impSem P` plays `f(x)` answered `x + x` (through `Linked2.specToIR`, the importer's
instance play `fwd_path` and the doubler's returned call, a Core 3.0 run from `Step` rules). -/
theorem dblFwd_ir (P : Profile) (x : BitVec 32) :
    ([.inr (.ask (⟨0, by decide⟩, .vals [.u32 x])),
      .inr (.ans (m := (⟨0, by decide⟩, .vals [.u32 x])) (some (.vals [.u32 (x + x)])))] :
      List (Silmaril.Games.Move (dblFwdL.toComp.imports.sig)
        (sigN dblFwdL.toComp.exports.length))) ∈
      dblFwdL.toComp.den (impSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.dblFwd_ir P x

end Silmaril.Wasm.Component.Reference.Litmus
