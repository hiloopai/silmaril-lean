module

public import Silmaril.Wasm.Game.Strategy.Thms
public import Silmaril.Wasm.Game.Env.Thms
public import Silmaril.Wasm.Behaviour.Semantics.Core
import Silmaril.Proofs.Wasm.Game.Adequacy.Later

/-!
# Adequacy of the instance strategy (M2)

The strategy of an instance is adequate for the Core 3.0 operational
semantics, under an **arbitrary** silmaril profile `P`. Let `K : Env I.E` be
an environment whose exception answers name existing exceptions
(`ThrowsBelow K s.exns.length`) and let the instance be well formed at `s`.
For every export call `f = ⟨j, args⟩` consider the closed-world behaviours of
`$invoke(addr j, args)` under the induced host,
`behaviours P (hostOf I.imports K) s (addr j) args`, and the closed program
`K.strategy ≫ I.strategy P s`.

## Every profile (`adequacy_profile`)

`behaviours P … = compositeObs (I.closedWith P s K) f ∪ {diverges | Diverges P …}`:

* **terminating behaviours, both inclusions** (`adequacy_answers`): a return,
  trap or uncaught exception `throws a` is a behaviour exactly when it is
  `w.toBehaviour` for an answer `w` of the closed program;
* **absence of an answer is divergence** (`diverges_of_no_answer`,
  `compositeObs_subset_behaviours`): if the closed program never answers,
  the invocation has an infinite run (by progress);
* **may-divergence** is the Core predicate `Diverges`. Under a
  nondeterministic profile a call may both diverge (on one branch) and answer
  (on another). A Silmaril `Strategy` is a set of finite plays: it cannot tell
  "answers" from "answers or diverges", so this clause cannot be read off the
  plain strategy. `adequacy_of_no_mixed` gives the exact equality
  `behaviours = compositeObs` whenever divergence excludes answers.

## Deterministic profiles (`adequacy`)

For `profile o` a divergent call never answers (`diverges_iff_no_answer`,
from uniqueness of normal forms), so the behaviours are **exactly** the
composite observations, divergence being the absence of an answer: an
infinite internal run, a host call that `K` never answers, or infinitely many
answered import calls.

## Later calls

Adequacy holds at **every** well-formed store, so later calls follow
(`adequacy_later_profile`, `adequacy_later`: the store left by a closed-world
run is a store that the strategy persists, and it is again well formed). The
closed program is itself stateful: after answering `f` with `w` it continues
as the closed program at the store left by *some* Core run of `f`
(`closedWith_after_iff`; by the unique run for `profile o`,
`closedWith_after`), so its own later observations are adequate
(`adequacy_after_profile` for terminating observations, `adequacy_after` for
`profile o`), and by induction after any finite history of answered calls.
Special cases: `adequacy_closed{,_profile}` (no imports: the empty host) and
`adequacy_divHost{,_profile}` (the silent environment: the host diverging on
every call).

Restrictions: scalar interfaces, environments that are stateless across calls
and preserve the store (exactly the hosts expressible as Core
`HostSemantics`, `isStrategyHost_iff`), and that throw only existing
exceptions. There is no restriction on the profile. Stateful and
nondeterministic environments (every environment strategy) are covered by
`Silmaril.Wasm.Game.StatefulEnv` (`sadequacy`), of which this M2 is the one-state
case (`sadequacy_ofEnv`).

Proofs: `Silmaril.Proofs.Wasm.Game.Adequacy.*`.
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.ScalarInstance

open Silmaril.Games Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

variable {I : ScalarInstance}

/-- **Game to operations.** An answer of the closed program comes from a finite Core run
under the induced host to a result. -/
theorem run_of_answer {P : Profile} {s : Store Nat} {K : Env I.E} {f : I.F.Op}
    {w : I.F.Ar f} (h : Responds (I.closedWith P s K) f w) :
    ∃ (c' : Config Nat) (r : Result),
      Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c' ∧
      c'.code = r.toAdmin ∧ Answer.ofResult? (I.exports.get f.1) r = some w :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.run_of_answer h

/-- **Operations to game.** A finite Core run to a result is answered by the closed
program. -/
theorem answer_of_run {P : Profile} {s : Store Nat} (hw : I.WellFormed s) {K : Env I.E}
    (hK : ThrowsBelow K s.exns.length) {f : I.F.Op} {c' : Config Nat} {r : Result}
    (run : Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c')
    (final : c'.code = r.toAdmin) :
    ∃ w, Answer.ofResult? (I.exports.get f.1) r = some w ∧ Responds (I.closedWith P s K) f w :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.answer_of_run hw hK run final

/-- The store left by a closed-world run of an export call to a result is well formed, and
the environment still throws only existing exceptions there (every profile). -/
theorem wellFormed_after_run {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {K : Env I.E} (hK : ThrowsBelow K s.exns.length) {f : I.F.Op} {c' : Config Nat}
    {r : Result} (run : Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c')
    (final : c'.code = r.toAdmin) :
    I.WellFormed c'.store ∧ ThrowsBelow K c'.store.exns.length :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.wellFormed_after_run hw hK run final

/-- **Progress.** A configuration reached from a well-formed invocation under the induced
host is finished or has a step. -/
theorem progress_hostOf {P : Profile} {s : Store Nat} (hw : I.WellFormed s) {K : Env I.E}
    (hK : ThrowsBelow K s.exns.length) {f : I.F.Op} {c : Config Nat}
    (run : Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c) :
    (∃ r : Result, c.code = r.toAdmin) ∨ ∃ c', Step P (hostOf I.imports K) c c' :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.progress_hostOf hw hK run

/-- **No answer is divergence** (every profile). -/
theorem diverges_of_no_answer {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {K : Env I.E} (hK : ThrowsBelow K s.exns.length) {f : I.F.Op}
    (hno : ∀ w, ¬ Responds (I.closedWith P s K) f w) :
    Diverges P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.diverges_of_no_answer hw hK hno

/-- **Divergence is the absence of an answer** (deterministic profiles). -/
theorem diverges_iff_no_answer {o : GrowOracle} {s : Store Nat} (hw : I.WellFormed s)
    {K : Env I.E} (hK : ThrowsBelow K s.exns.length) {f : I.F.Op} :
    Diverges (profile o) (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) ↔
      ∀ w, ¬ Responds (I.closedWith (profile o) s K) f w :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.diverges_iff_no_answer hw hK

/-- **Composite observations are behaviours** (every profile, both kinds: answers are
terminating behaviours, and the absence of an answer is divergence). -/
theorem compositeObs_subset_behaviours {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (K : Env I.E) (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) :
    compositeObs (I.closedWith P s K) f ⊆
      behaviours P (hostOf I.imports K) s (I.addr f.1) f.2.1 :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.compositeObs_subset_behaviours hw K hK f

/-- **M2 for every profile.** For a strategy-definable host whose environment throws only
existing exceptions, the closed-world behaviours of an export call under an arbitrary profile
`P` are the observations of the closed program `K.strategy ≫ I.strategy P s` together with
may-divergence: the terminating behaviours are exactly its answers, the absence of an answer
is divergence, and divergence is a behaviour exactly when the invocation has an infinite
run. -/
theorem adequacy_profile {P : Profile} {s : Store Nat} (hw : I.WellFormed s) (K : Env I.E)
    (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) :
    behaviours P (hostOf I.imports K) s (I.addr f.1) f.2.1 =
      compositeObs (I.closedWith P s K) f ∪
        {b | b = .diverges ∧ Diverges P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1)} :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.adequacy_profile hw K hK f

/-- **M2 for every profile, terminating observations** (both inclusions): a return, trap or
uncaught exception is a closed-world behaviour exactly when it is an answer of the closed
program. -/
theorem adequacy_answers {P : Profile} {s : Store Nat} (hw : I.WellFormed s) (K : Env I.E)
    (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) (b : Behaviour Val) (hb : b ≠ .diverges) :
    b ∈ behaviours P (hostOf I.imports K) s (I.addr f.1) f.2.1 ↔
      b ∈ compositeObs (I.closedWith P s K) f :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.adequacy_answers hw K hK f b hb

/-- **M2 for every profile, exact form.** If the invocation cannot both diverge and answer,
the closed-world behaviours are exactly the composite observations. -/
theorem adequacy_of_no_mixed {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (K : Env I.E) (hK : ThrowsBelow K s.exns.length) (f : I.F.Op)
    (hmixed : Diverges P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) →
      ∀ w, ¬ Responds (I.closedWith P s K) f w) :
    behaviours P (hostOf I.imports K) s (I.addr f.1) f.2.1 =
      compositeObs (I.closedWith P s K) f :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.adequacy_of_no_mixed hw K hK f hmixed

/-- **M2 (adequacy), deterministic profiles.** For a strategy-definable host whose
environment throws only existing exceptions, the closed-world behaviours of an export call
are exactly the observations of the closed program `K.strategy ≫ I.strategy (profile o) s`:
the behaviours of its answers, and `diverges` for the absence of an answer. -/
theorem adequacy {o : GrowOracle} {s : Store Nat} (hw : I.WellFormed s) (K : Env I.E)
    (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) :
    behaviours (profile o) (hostOf I.imports K) s (I.addr f.1) f.2.1 =
      compositeObs (I.closedWith (profile o) s K) f :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.adequacy hw K hK f

/-- **M2, later calls, every profile.** After a closed-world run of the export call `f` to a
result in configuration `c'`, the next export call `f'` is adequate at the store `c'.store`
that the run leaves. -/
theorem adequacy_later_profile {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (K : Env I.E) (hK : ThrowsBelow K s.exns.length) {f : I.F.Op} {c' : Config Nat}
    {r : Result} (run : Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c')
    (final : c'.code = r.toAdmin) (f' : I.F.Op) :
    behaviours P (hostOf I.imports K) c'.store (I.addr f'.1) f'.2.1 =
      compositeObs (I.closedWith P c'.store K) f' ∪
        {b | b = .diverges ∧
          Diverges P (hostOf I.imports K) (invoke c'.store (I.addr f'.1) f'.2.1)} :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.adequacy_later_profile hw K hK run final f'

/-- **M2, later calls, deterministic profiles.** After a closed-world run of the export call
`f` to a result in configuration `c'`, the next export call `f'` is adequate at the store
`c'.store` that the run leaves, which is the store the strategy persists. -/
theorem adequacy_later {o : GrowOracle} {s : Store Nat} (hw : I.WellFormed s) (K : Env I.E)
    (hK : ThrowsBelow K s.exns.length) {f : I.F.Op} {c' : Config Nat} {r : Result}
    (run : Steps (profile o) (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c')
    (final : c'.code = r.toAdmin) (f' : I.F.Op) :
    behaviours (profile o) (hostOf I.imports K) c'.store (I.addr f'.1) f'.2.1 =
      compositeObs (I.closedWith (profile o) c'.store K) f' :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.adequacy_later hw K hK run final f'

/-- **The closed program after an answered call, every profile**: it continues as the closed
program at the store left by *some* Core run of that call ending in the answered result. -/
theorem closedWith_after_iff {P : Profile} {s : Store Nat} {K : Env I.E} {f : I.F.Op}
    {w : I.F.Ar f} (p : List (Move Sig.empty I.F)) :
    [.inr (.ask f), .inr (.ans f w)] ++ p ∈ I.closedWith P s K ↔
      ∃ (c' : Config Nat) (r : Result),
        Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c' ∧
        c'.code = r.toAdmin ∧ Answer.ofResult? (I.exports.get f.1) r = some w ∧
        p ∈ I.closedWith P c'.store K :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.closedWith_after_iff p

/-- **The closed program after an answered call, deterministic profiles**: it continues as the
closed program at the store left by the Core run of that call. -/
theorem closedWith_after {o : GrowOracle} {s : Store Nat} {K : Env I.E} {f : I.F.Op}
    {w : I.F.Ar f} {c' : Config Nat} {r : Result}
    (run : Steps (profile o) (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c')
    (final : c'.code = r.toAdmin) (hr : Answer.ofResult? (I.exports.get f.1) r = some w)
    (p : List (Move Sig.empty I.F)) :
    [.inr (.ask f), .inr (.ans f w)] ++ p ∈ I.closedWith (profile o) s K ↔
      p ∈ I.closedWith (profile o) c'.store K :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.closedWith_after run final hr p

/-- **M2 after an answered call, every profile, terminating observations.** -/
theorem adequacy_after_profile {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (K : Env I.E) (hK : ThrowsBelow K s.exns.length) {f : I.F.Op} {w : I.F.Ar f}
    (f' : I.F.Op) (b : Behaviour Val) (hb : b ≠ .diverges) :
    b ∈ compositeObsAfter (I.closedWith P s K) [.inr (.ask f), .inr (.ans f w)] f' ↔
      ∃ (c' : Config Nat) (r : Result),
        Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c' ∧
        c'.code = r.toAdmin ∧ Answer.ofResult? (I.exports.get f.1) r = some w ∧
        b ∈ behaviours P (hostOf I.imports K) c'.store (I.addr f'.1) f'.2.1 :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.adequacy_after_profile hw K hK f' b hb

/-- **M2 after an answered call, on the closed program itself** (deterministic profiles). -/
theorem adequacy_after {o : GrowOracle} {s : Store Nat} (hw : I.WellFormed s) (K : Env I.E)
    (hK : ThrowsBelow K s.exns.length) {f : I.F.Op} {w : I.F.Ar f} {c' : Config Nat}
    {r : Result}
    (run : Steps (profile o) (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c')
    (final : c'.code = r.toAdmin) (hr : Answer.ofResult? (I.exports.get f.1) r = some w)
    (f' : I.F.Op) :
    compositeObsAfter (I.closedWith (profile o) s K) [.inr (.ask f), .inr (.ans f w)] f' =
      behaviours (profile o) (hostOf I.imports K) c'.store (I.addr f'.1) f'.2.1 :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.adequacy_after hw K hK run final hr f'

/-- **M2, closed programs, every profile.** -/
theorem adequacy_closed_profile {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (hI : I.imports = []) (K : Env I.E) (f : I.F.Op) :
    behaviours P (fun _ _ _ _ => False : HostSemantics Nat) s (I.addr f.1) f.2.1 =
      compositeObs (I.closedWith P s K) f ∪
        {b | b = .diverges ∧
          Diverges P (fun _ _ _ _ => False : HostSemantics Nat) (invoke s (I.addr f.1) f.2.1)} :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.adequacy_closed_profile hw hI K f

/-- **M2, closed programs** (deterministic profiles). With no imports, the behaviours under
the empty host are the observations of the closed strategy (composed with any environment
over the empty interface). -/
theorem adequacy_closed {o : GrowOracle} {s : Store Nat} (hw : I.WellFormed s)
    (hI : I.imports = []) (K : Env I.E) (f : I.F.Op) :
    behaviours (profile o) (fun _ _ _ _ => False : HostSemantics Nat) s (I.addr f.1) f.2.1 =
      compositeObs (I.closedWith (profile o) s K) f :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.adequacy_closed hw hI K f

/-- **M2, diverging host, every profile.** -/
theorem adequacy_divHost_profile {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (f : I.F.Op) :
    behaviours P divHost s (I.addr f.1) f.2.1 =
      compositeObs (I.closedWith P s (Env.silent _)) f ∪
        {b | b = .diverges ∧ Diverges P (hostOf I.imports (Env.silent _))
          (invoke s (I.addr f.1) f.2.1)} :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.adequacy_divHost_profile hw f

/-- **M2, diverging host** (deterministic profiles). Against the silent environment, the
behaviours under the host that diverges on every call are the observations of the closed
program. -/
theorem adequacy_divHost {o : GrowOracle} {s : Store Nat} (hw : I.WellFormed s) (f : I.F.Op) :
    behaviours (profile o) divHost s (I.addr f.1) f.2.1 =
      compositeObs (I.closedWith (profile o) s (Env.silent _)) f :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.adequacy_divHost hw f

/-- **Typing preservation.** Well-formedness persists along complete activations whose
environment answers throw only existing exceptions; the exception heap only grows. -/
theorem WellFormed.activation {P : Profile} {s s' : Store Nat} {c : List (Move I.E I.F)}
    (hw : I.WellFormed s) (hthrow : I.PlayThrowsBelow s.exns.length c)
    (hc : I.Activation P s c s') : I.WellFormed s' ∧ s.exns.length ≤ s'.exns.length :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.WellFormed.activation hw hthrow hc

/-- **No exceptions without tags.** From a well-formed store with no tags and no exception
instances, against environment answers that never throw, the instance never answers an
export call with an exception. -/
theorem no_throw_of_no_tags {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (htags : s.tags = []) (hexns : s.exns = []) {p : List (Move I.E I.F)}
    (hp : p ∈ I.strategy P s) (henv : I.PlayThrowsBelow 0 p) (f : I.F.Op) (a : Nat) :
    (.inr (.ans f (.throw a)) : Move I.E I.F) ∉ p :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.no_throw_of_no_tags hw htags hexns
    (Silmaril.Proofs.Wasm.Game.ScalarInstance.mem_strategy_iff.1 hp) henv f a

end Silmaril.Wasm.Game.ScalarInstance
