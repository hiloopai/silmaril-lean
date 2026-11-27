module

public import Silmaril.Semantics.SQLite.Isolation.Api.Defs
public import Silmaril.Semantics.ITree.Trace.Handled.Thms
import Silmaril.Proofs.Semantics.SQLite.Isolation.Api.Safety

/-!
# Theorems for the Restricted SQLite API Isolation Model

Public theorem header for `Silmaril.Semantics.SQLite.Isolation.Api`.
Longer proofs live in `Silmaril.Proofs.Semantics.SQLite.Isolation.Api.Safety`.

This module establishes universal arbitrary-input / arbitrary-request-prefix
bad-event exclusion and protected-state preservation:
1. Exact characterization of `BadEvent (readOnlyProfile db)`.
2. **Arbitrary request/response prefix theorems**:
   - Under `HandlerExcludesBad profile step`, for **any** arbitrary raw
     `t : ApiTree A` and **any** finite handled prefix `p`, no completed
     exchange in `p` is a `BadEvent profile` (`arbitrary_handled_prefix_avoids_bad_exchanges`),
     and under `FrameContract`, every reachable post-prefix state preserves
     `protectedState` (`arbitrary_handled_prefix_preserves_protected`), without
     requiring any particular return value or refusal path.
   - Under `confineTree profile onBad`, for **any** arbitrary raw `t : ApiTree A`
     and **any** safe `onBad : ApiTree A` (success, error, cleanup, or
     divergence), every finite observation prefix avoids `BadEvent profile`
     (`confineTree_avoids_bad`) and preserves `protectedState`
     (`confineTree_prefix_preserves_protected`).
3. Compositional sequencing/transition laws (`treeAvoidsBad_bind`,
   `handledTreeAvoidsBad_bind`, `treeAvoidsBad_mono`, etc.).
4. Whole-session proof for `openReadCloseSession db input` over **any**
   arbitrary `QueryInput` (parsing/preparation, execution, and cleanup), plus
   negative witnesses and `dishonestHandler_mutates_despite_avoids_bad`.
-/

public section

namespace Silmaril.SQLite.Isolation.Api

open Silmaril.Elgot
open Silmaril.Proofs.Semantics.SQLite.Isolation.Api

/-! ## `readOnlyProfile` bad-event characterization -/

@[simp] theorem badEvent_readOnly_openDb_readOnly (db target : DbId) :
    BadEvent (readOnlyProfile db) ⟨_, .openDb target .readOnly⟩ ↔ target ≠ db := by
  by_cases h : target = db <;> simp [BadEvent, isBadEvent, readOnlyProfile, h]

@[simp] theorem badEvent_readOnly_openDb_readWrite (db target : DbId) :
    BadEvent (readOnlyProfile db) ⟨_, .openDb target .readWrite⟩ := by
  simp [BadEvent, isBadEvent, readOnlyProfile]

@[simp] theorem badEvent_readOnly_prepare (db target : DbId)
    (conn : ConnHandle) (input : QueryInput) :
    BadEvent (readOnlyProfile db) ⟨_, .prepare conn target input⟩ ↔ target ≠ db := by
  by_cases h : target = db <;> simp [BadEvent, isBadEvent, readOnlyProfile, h]

@[simp] theorem badEvent_readOnly_stepRead (db target : DbId) (stmt : StmtHandle) :
    BadEvent (readOnlyProfile db) ⟨_, .stepRead stmt target⟩ ↔ target ≠ db := by
  by_cases h : target = db <;> simp [BadEvent, isBadEvent, readOnlyProfile, h]

@[simp] theorem not_badEvent_readOnly_finalize (db : DbId) (stmt : StmtHandle) :
    ¬ BadEvent (readOnlyProfile db) ⟨_, .finalize stmt⟩ := by
  simp [BadEvent, isBadEvent]

@[simp] theorem not_badEvent_readOnly_closeDb (db : DbId) (conn : ConnHandle) :
    ¬ BadEvent (readOnlyProfile db) ⟨_, .closeDb conn⟩ := by
  simp [BadEvent, isBadEvent]

@[simp] theorem badEvent_readOnly_writeDb (db target : DbId) (conn : ConnHandle)
    (offset : Nat) (bytes : List UInt8) :
    BadEvent (readOnlyProfile db) ⟨_, .writeDb conn target offset bytes⟩ := by
  simp [BadEvent, isBadEvent, readOnlyProfile]

@[simp] theorem badEvent_readOnly_attachDb (db target : DbId) (conn : ConnHandle)
    (schemaName : String) :
    BadEvent (readOnlyProfile db) ⟨_, .attachDb conn target schemaName⟩ := by
  simp [BadEvent, isBadEvent, readOnlyProfile]

@[simp] theorem badEvent_readOnly_loadExtension (db : DbId) (conn : ConnHandle)
    (path : String) :
    BadEvent (readOnlyProfile db) ⟨_, .loadExtension conn path⟩ := by
  simp [BadEvent, isBadEvent, readOnlyProfile]

@[simp] theorem badEvent_readOnly_hostEffect (db : DbId) (kind : HostEffectKind) :
    BadEvent (readOnlyProfile db) ⟨_, .hostEffect kind⟩ := by
  simp [BadEvent, isBadEvent, readOnlyProfile]

/-! ## Universal arbitrary-request / response-prefix safety theorems -/

theorem replayTo_iff_replay {S A : Type} (step : ApiHandler S) (s : S) (p : ApiTrace A) :
    (∃ s', ReplayTo step s p s') ↔ ITree.Replay step s p :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.replayTo_iff_replay step s p

/-- Every finite trace replayed under a handler satisfying `HandlerExcludesBad`
contains no forbidden completed exchange, regardless of return outcome or
divergence. -/
theorem replay_excludes_bad_exchanges {S A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} (hexcl : HandlerExcludesBad profile step)
    {s : S} {p : ApiTrace A} (hrep : ITree.Replay step s p) :
    ExchangesAvoidBad profile p :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.replay_excludes_bad_exchanges hexcl hrep

/-- Arbitrary-tree, arbitrary-prefix host-trace safety: for **any** raw tree
`t : ApiTree A` (no validity, admission, or limit premise) and **any** finite
handled prefix `p`, no completed exchange in `p` is a `BadEvent profile`. -/
theorem arbitrary_handled_prefix_avoids_bad_exchanges {S A : Type}
    {profile : AuthorityProfile} {step : ApiHandler S}
    (hexcl : HandlerExcludesBad profile step)
    (s : S) (t : ApiTree A) (p : ApiTrace A)
    (hhandled : ITree.HandledTrace step s t p) :
    ExchangesAvoidBad profile p :=
  replay_excludes_bad_exchanges hexcl hhandled.2

/-- Every finite prefix whose completed exchanges avoid `BadEvent profile`
preserves `protectedState` under `FrameContract`. -/
theorem exchangesAvoidBad_replayTo_preserves_protected {S P A : Type}
    {profile : AuthorityProfile} {step : ApiHandler S} {protectedState : S → P}
    (hframe : FrameContract profile step protectedState)
    {s s' : S} {p : ApiTrace A}
    (hsafe : ExchangesAvoidBad profile p)
    (hrep : ReplayTo step s p s') :
    protectedState s' = protectedState s :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.exchangesAvoidBad_replayTo_preserves_protected
    hframe hsafe hrep

/-- Arbitrary-tree, arbitrary-prefix protected-state preservation: for **any**
raw tree `t : ApiTree A` and **any** finite prefix `p` replayed from `s` to `s'`
under a handler satisfying `HandlerExcludesBad` and `FrameContract`,
`protectedState s' = protectedState s`. -/
theorem arbitrary_handled_prefix_preserves_protected {S P A : Type}
    {profile : AuthorityProfile} {step : ApiHandler S} {protectedState : S → P}
    (hexcl : HandlerExcludesBad profile step)
    (hframe : FrameContract profile step protectedState)
    (s s' : S) (t : ApiTree A) (p : ApiTrace A)
    (_htrace : ITree.HasTrace t p)
    (hrep : ReplayTo step s p s') :
    protectedState s' = protectedState s :=
  exchangesAvoidBad_replayTo_preserves_protected hframe
    (replay_excludes_bad_exchanges hexcl ((replayTo_iff_replay step s p).mp ⟨s', hrep⟩))
    hrep

theorem traceAvoidsBad_to_exchangesAvoidBad {A : Type} {profile : AuthorityProfile}
    {p : ApiTrace A} (h : TraceAvoidsBad profile p) :
    ExchangesAvoidBad profile p :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.traceAvoidsBad_to_exchangesAvoidBad h

/-! ## Compositional finite-prefix safety and sequencing laws -/

theorem treeAvoidsBad_ret {A : Type} (profile : AuthorityProfile) (a : A) :
    TreeAvoidsBad profile (ITree.ret a) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.treeAvoidsBad_ret profile a

theorem treeAvoidsBad_pure {A : Type} (profile : AuthorityProfile) (a : A) :
    TreeAvoidsBad profile (pure a : ApiTree A) :=
  treeAvoidsBad_ret profile a

theorem treeAvoidsBad_diverge {A : Type} (profile : AuthorityProfile) :
    TreeAvoidsBad profile (ITree.diverge : ApiTree A) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.treeAvoidsBad_diverge profile

theorem treeAvoidsBad_vis {R A : Type} {profile : AuthorityProfile}
    {e : ApiEvent R} {k : R → ApiTree A}
    (he : ¬ BadEvent profile ⟨R, e⟩)
    (hk : ∀ r, TreeAvoidsBad profile (k r)) :
    TreeAvoidsBad profile (ITree.vis e k) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.treeAvoidsBad_vis he hk

theorem treeAvoidsBad_rawCall {R : Type} {profile : AuthorityProfile} {e : ApiEvent R}
    (he : ¬ BadEvent profile ⟨R, e⟩) :
    TreeAvoidsBad profile (rawCall e) :=
  treeAvoidsBad_vis he (fun r => treeAvoidsBad_ret profile r)

/-- Reusable monadic sequencing (`bind`) law for unconditional bad-event
exclusion. -/
theorem treeAvoidsBad_bind {A B : Type} {profile : AuthorityProfile}
    {t : ApiTree A} {k : A → ApiTree B}
    (ht : TreeAvoidsBad profile t)
    (hk : ∀ a, TreeAvoidsBad profile (k a)) :
    TreeAvoidsBad profile (t >>= k) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.treeAvoidsBad_bind ht hk

/-- Finite-trace refinement (`ITree.TraceLE`) preserves bad-event exclusion
downward. -/
theorem treeAvoidsBad_mono {A : Type} {profile : AuthorityProfile} {t s : ApiTree A}
    (hle : ITree.TraceLE t s) (hs : TreeAvoidsBad profile s) :
    TreeAvoidsBad profile t :=
  fun p hp => hs p (hle p hp)

/-- Unconditional bad-event exclusion implies handler-scoped exclusion for
every nondeterministic handler `step` and initial state `s`. -/
theorem treeAvoidsBad_to_handled {S A : Type} {profile : AuthorityProfile}
    (step : ApiHandler S) (s : S) {t : ApiTree A} (ht : TreeAvoidsBad profile t) :
    HandledTreeAvoidsBad profile step s t :=
  fun p hp => ht p hp.1

theorem handledTreeAvoidsBad_mono {S A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {s : S} {t u : ApiTree A}
    (hle : ITree.HandledTraceLE step s t u) (hu : HandledTreeAvoidsBad profile step s u) :
    HandledTreeAvoidsBad profile step s t :=
  fun p hp => hu p (hle p hp)

theorem handledTreeAvoidsBad_ret {S A : Type} (profile : AuthorityProfile)
    (step : ApiHandler S) (s : S) (a : A) :
    HandledTreeAvoidsBad profile step s (ITree.ret a) :=
  treeAvoidsBad_to_handled step s (treeAvoidsBad_ret profile a)

/-- Handler-scoped single-transition safety law. -/
theorem handledTreeAvoidsBad_vis {S R A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {s : S} {e : ApiEvent R} {k : R → ApiTree A}
    (he : ¬ BadEvent profile ⟨R, e⟩)
    (hk : ∀ r s', step ⟨R, e⟩ s r s' → HandledTreeAvoidsBad profile step s' (k r)) :
    HandledTreeAvoidsBad profile step s (ITree.vis e k) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.handledTreeAvoidsBad_vis he hk

/-- Reusable handler-scoped sequencing (`bind`) law: the continuation only needs
to avoid bad events at states `y` and values `a` reachable via `ITree.ReturnsTo`. -/
theorem handledTreeAvoidsBad_bind {S A B : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {s : S} {t : ApiTree A} {k : A → ApiTree B}
    (ht : HandledTreeAvoidsBad profile step s t)
    (hk : ∀ y a, ITree.ReturnsTo step s t y a → HandledTreeAvoidsBad profile step y (k a)) :
    HandledTreeAvoidsBad profile step s (t >>= k) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.handledTreeAvoidsBad_bind ht hk

/-! ## Outcome-orthogonal arbitrary-tree confinement -/

theorem confineTree_diverge {A : Type} (profile : AuthorityProfile) (onBad : ApiTree A) :
    confineTree profile onBad ITree.diverge = ITree.diverge :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.confineTree_diverge profile onBad

theorem confineTree_ret {A : Type} (profile : AuthorityProfile) (onBad : ApiTree A) (a : A) :
    confineTree profile onBad (ITree.ret a) = ITree.ret a :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.confineTree_ret profile onBad a

theorem confineTree_vis {R A : Type} (profile : AuthorityProfile) (onBad : ApiTree A)
    (e : ApiEvent R) (k : R → ApiTree A) :
    confineTree profile onBad (ITree.vis e k) =
      if isBadEvent profile e then onBad
      else ITree.vis e (fun r => confineTree profile onBad (k r)) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.confineTree_vis profile onBad e k

/-- Universal arbitrary-tree confinement: for **any** raw `t : ApiTree A` and
**any** safe continuation `onBad : ApiTree A` (returning success, an error,
cleanup, or diverging), every finite observation prefix avoids `BadEvent profile`. -/
theorem confineTree_avoids_bad {A : Type} (profile : AuthorityProfile)
    {onBad : ApiTree A} (honBad : TreeAvoidsBad profile onBad) (t : ApiTree A) :
    TreeAvoidsBad profile (confineTree profile onBad t) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.confineTree_avoids_bad profile honBad t

/-! ## Protected-state preservation from tree safety + `FrameContract` -/

theorem handled_prefix_preserves_protected {S P A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {protectedState : S → P}
    (hframe : FrameContract profile step protectedState)
    {s s' : S} {t : ApiTree A} {p : ApiTrace A}
    (hsafe : HandledTreeAvoidsBad profile step s t)
    (htrace : ITree.HasTrace t p)
    (hrep : ReplayTo step s p s') :
    protectedState s' = protectedState s :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.handled_prefix_preserves_protected
    hframe hsafe htrace hrep

theorem treeAvoidsBad_prefix_preserves_protected {S P A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {protectedState : S → P}
    (hframe : FrameContract profile step protectedState)
    {s s' : S} {t : ApiTree A} {p : ApiTrace A}
    (hsafe : TreeAvoidsBad profile t)
    (htrace : ITree.HasTrace t p)
    (hrep : ReplayTo step s p s') :
    protectedState s' = protectedState s :=
  handled_prefix_preserves_protected hframe (treeAvoidsBad_to_handled step s hsafe) htrace hrep

theorem handled_returnsTo_preserves_protected {S P A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {protectedState : S → P}
    (hframe : FrameContract profile step protectedState)
    {s s' : S} {t : ApiTree A} {a : A}
    (hsafe : HandledTreeAvoidsBad profile step s t)
    (hret : ITree.ReturnsTo step s t s' a) :
    protectedState s' = protectedState s :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.handled_returnsTo_preserves_protected
    hframe hsafe hret

theorem treeAvoidsBad_returnsTo_preserves_protected {S P A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {protectedState : S → P}
    (hframe : FrameContract profile step protectedState)
    {s s' : S} {t : ApiTree A} {a : A}
    (hsafe : TreeAvoidsBad profile t)
    (hret : ITree.ReturnsTo step s t s' a) :
    protectedState s' = protectedState s :=
  handled_returnsTo_preserves_protected hframe (treeAvoidsBad_to_handled step s hsafe) hret

/-- For **any** raw tree `t : ApiTree A`, **any** safe `onBad : ApiTree A`, and
**any** handler satisfying `FrameContract`, every finite prefix of
`confineTree profile onBad t` preserves `protectedState`. -/
theorem confineTree_prefix_preserves_protected {S P A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {protectedState : S → P}
    (hframe : FrameContract profile step protectedState)
    {onBad : ApiTree A} (honBad : TreeAvoidsBad profile onBad) (t : ApiTree A)
    {s s' : S} {p : ApiTrace A}
    (htrace : ITree.HasTrace (confineTree profile onBad t) p)
    (hrep : ReplayTo step s p s') :
    protectedState s' = protectedState s :=
  treeAvoidsBad_prefix_preserves_protected hframe
    (confineTree_avoids_bad profile honBad t) htrace hrep

/-! ## Worked arbitrary-input open/prepare/read/finalize/close session -/

/-- For **any** arbitrary `QueryInput` (no validity, admission, or limit premise),
every finite prefix of `openReadCloseSession db input` across open, preparation,
read execution, and cleanup avoids `BadEvent (readOnlyProfile db)`. -/
theorem openReadCloseSession_avoids_bad (db : DbId) (input : QueryInput) :
    TreeAvoidsBad (readOnlyProfile db) (openReadCloseSession db input) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.openReadCloseSession_avoids_bad db input

theorem openReadCloseSession_prefix_preserves_protected {S P : Type}
    {step : ApiHandler S} {protectedState : S → P}
    (db : DbId) (input : QueryInput)
    (hframe : FrameContract (readOnlyProfile db) step protectedState)
    {s s' : S} {p : ApiTrace (Except ApiError (Option RowData))}
    (htrace : ITree.HasTrace (openReadCloseSession db input) p)
    (hrep : ReplayTo step s p s') :
    protectedState s' = protectedState s :=
  treeAvoidsBad_prefix_preserves_protected hframe
    (openReadCloseSession_avoids_bad db input) htrace hrep

theorem openReadCloseSession_returnsTo_preserves_protected {S P : Type}
    {step : ApiHandler S} {protectedState : S → P}
    (db : DbId) (input : QueryInput)
    (hframe : FrameContract (readOnlyProfile db) step protectedState)
    {s s' : S} {res : Except ApiError (Option RowData)}
    (hret : ITree.ReturnsTo step s (openReadCloseSession db input) s' res) :
    protectedState s' = protectedState s :=
  treeAvoidsBad_returnsTo_preserves_protected hframe
    (openReadCloseSession_avoids_bad db input) hret

/-! ## Negative witnesses: bad events are representable in `ApiEvent` -/

theorem unsafeWriteProgram_not_avoids_bad (conn : ConnHandle) (db : DbId)
    (offset : Nat) (bytes : List UInt8) :
    ¬ TreeAvoidsBad (readOnlyProfile db) (unsafeWriteProgram conn db offset bytes) := by
  intro hsafe
  exact hsafe (.request (.writeDb conn db offset bytes)) (ITree.hasTrace_vis_request _ _)
    (badEvent_readOnly_writeDb db db conn offset bytes)

theorem unsafeAttachProgram_not_avoids_bad (conn : ConnHandle) (db target : DbId)
    (schemaName : String) :
    ¬ TreeAvoidsBad (readOnlyProfile db) (unsafeAttachProgram conn target schemaName) := by
  intro hsafe
  exact hsafe (.request (.attachDb conn target schemaName)) (ITree.hasTrace_vis_request _ _)
    (badEvent_readOnly_attachDb db target conn schemaName)

theorem unsafeLoadExtensionProgram_not_avoids_bad (conn : ConnHandle) (db : DbId)
    (path : String) :
    ¬ TreeAvoidsBad (readOnlyProfile db) (unsafeLoadExtensionProgram conn path) := by
  intro hsafe
  exact hsafe (.request (.loadExtension conn path)) (ITree.hasTrace_vis_request _ _)
    (badEvent_readOnly_loadExtension db conn path)

theorem unsafeHostEffectProgram_not_avoids_bad (db : DbId) (kind : HostEffectKind) :
    ¬ TreeAvoidsBad (readOnlyProfile db) (unsafeHostEffectProgram kind) := by
  intro hsafe
  exact hsafe (.request (.hostEffect kind)) (ITree.hasTrace_vis_request _ _)
    (badEvent_readOnly_hostEffect db kind)

theorem unsafeReadWriteOpenProgram_not_avoids_bad (db : DbId) :
    ¬ TreeAvoidsBad (readOnlyProfile db) (unsafeReadWriteOpenProgram db) := by
  intro hsafe
  exact hsafe (.request (.openDb db .readWrite)) (ITree.hasTrace_vis_request _ _)
    (badEvent_readOnly_openDb_readWrite db db)

theorem unsafeWrongDbOpenProgram_not_avoids_bad {db otherDb : DbId} (hne : otherDb ≠ db) :
    ¬ TreeAvoidsBad (readOnlyProfile db) (unsafeWrongDbOpenProgram otherDb) := by
  intro hsafe
  exact hsafe (.request (.openDb otherDb .readOnly)) (ITree.hasTrace_vis_request _ _)
    ((badEvent_readOnly_openDb_readOnly db otherDb).mpr hne)

/-! ## Reference handler witnesses and frame-contract honesty witness -/

/-- The concrete single-connection `readOnlyReferenceHandler db` satisfies
`HandlerExcludesBad (readOnlyProfile db)` without mandating a specific return path. -/
theorem readOnlyReferenceHandler_excludesBad (db : DbId) :
    HandlerExcludesBad (readOnlyProfile db) (readOnlyReferenceHandler db) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.readOnlyReferenceHandler_excludesBad db

/-- The concrete single-connection `readOnlyReferenceHandler db` satisfies
`FrameContract` for `ReferenceState.protectedDb`. -/
theorem readOnlyReferenceHandler_frameContract (db : DbId) :
    FrameContract (readOnlyProfile db) (readOnlyReferenceHandler db) ReferenceState.protectedDb :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.readOnlyReferenceHandler_frameContract db

/-- Honesty witness: avoiding `BadEvent` in traces alone does not prevent a
dishonest handler from mutating state; `FrameContract` is genuinely required
for protected-state preservation. -/
theorem dishonestHandler_mutates_despite_avoids_bad (db : DbId) :
    TreeAvoidsBad (readOnlyProfile db) (rawCall (.openDb db .readOnly)) ∧
    ITree.ReturnsTo dishonestHandler 0 (rawCall (.openDb db .readOnly)) 1 (.ok ⟨0⟩) ∧
    (1 : Nat) ≠ 0 :=
  ⟨treeAvoidsBad_rawCall (by simp [BadEvent, isBadEvent, readOnlyProfile]),
   ITree.ReturnsTo.exchange ⟨rfl, rfl⟩
     (ITree.ReturnsTo.ret 1 (Except.ok (ConnHandle.mk 0) : Except ApiError ConnHandle)),
   Nat.one_ne_zero⟩

end Silmaril.SQLite.Isolation.Api
