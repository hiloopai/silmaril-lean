module

public import Silmaril.Semantics.ITree.Trace.Handled.Defs

/-!
# Restricted SQLite API Isolation Model (Interaction-Tree Abstraction)

This module defines a **restricted, high-level interaction-tree abstraction** of
a single-connection, single-thread SQLite API and host effect boundary, built on
Silmaril's weak interaction trees (`Silmaril.Elgot.ITree` in
`Silmaril/Semantics/ITree/Defs.lean`, `Trace/Defs.lean`, `Reindex/Defs.lean`,
and `Trace/Handled/Defs.lean`).

## Core safety framing (universal arbitrary-input bad-event exclusion)
The theorem shape is **not** input rejection or input admission filtering.
Instead, for **any** input (arbitrary SQL text, arbitrary raw bytes, or an
arbitrary raw API request tree — with no premise that the input is valid,
admitted, trusted, in a SQL subset, or within a limit), every finite execution
prefix under the configured `AuthorityProfile` and stated API/host contracts
avoids every `BadEvent profile` and preserves `protectedState`:

- **Outcome-orthogonal**: returning success, an execution/host error, another
  valid outcome, or silent divergence are all orthogonal to prefix safety; no
  specific refusal return path is required.
- **Whole-session coverage**: parsing/preparation, execution, and cleanup
  (`openDb`, `prepare`, `stepRead`, `finalize`, `closeDb`) all fall under the
  same prefix safety predicate.
- **Not vacuous**: forbidden operations (`writeDb`, `attachDb`, `loadExtension`,
  `hostEffect`, read-write `openDb`, and access to non-allowed databases) are
  explicitly representable in `ApiEvent`, witnessed by negative theorems.
- **Honest non-mutation**: excluding `BadEvent` from traces does not by itself
  imply state equality; actual protected-state preservation requires an explicit
  handler `FrameContract` (witnessed by `dishonestHandler`).

## Model boundaries and explicit non-claims
This module is a high-level effect-tree abstraction over abstract `ApiEvent`s.
It does **not** prove query-result correctness, confidentiality, termination,
blanket resource bounds, security of real `libsqlite3.so`, or C / x86-64 ELF
refinement. Connecting this API boundary to concrete VM execution, VFS/pager
implementations, and native ELF code remains outstanding follow-on work.
-/

@[expose] public section

namespace Silmaril.SQLite.Isolation.Api

open Silmaril.Elgot

/-- Identifier of a database target at the abstract SQLite API boundary. -/
structure DbId where
  name : String
  deriving DecidableEq, Repr

/-- Abstract connection handle returned by a successful open. -/
structure ConnHandle where
  id : Nat
  deriving DecidableEq, Repr

/-- Abstract prepared-statement handle returned by a successful prepare. -/
structure StmtHandle where
  id : Nat
  deriving DecidableEq, Repr

/-- Requested database open mode at the abstract API boundary. -/
inductive OpenMode where
  | readOnly
  | readWrite
  deriving DecidableEq, Repr

/-- Categories of forbidden or unmodeled host effects outside the read-only
SQLite API profile. -/
inductive HostEffectKind where
  | fileWrite (path : String)
  | network (endpoint : String)
  | processExec (command : String)
  | unmodeled (label : String)
  deriving DecidableEq, Repr

/-- Arbitrary untrusted query input passed to a session: arbitrary SQL text and
arbitrary raw parameter/payload bytes, with no validity or size premise. -/
structure QueryInput where
  sql : String
  rawPayload : List UInt8 := []
  deriving DecidableEq, Repr

/-- Errors observable at the abstract SQLite API boundary. Returning any error,
a success value, or diverging are all orthogonal to prefix safety. -/
inductive ApiError where
  | malformedSql
  | invalidHandle
  | ioError
  | busy
  | policyBlocked
  | other (code : Nat)
  deriving DecidableEq, Repr

/-- Abstract row payload returned by a read step. -/
abbrev RowData := List UInt8

/-- Result of stepping a prepared read statement. -/
inductive StepOutcome where
  | row (data : RowData)
  | done
  deriving DecidableEq, Repr

/-- Explicit authority/capability profile for a single-connection SQLite API
session. -/
structure AuthorityProfile where
  allowedDb : DbId
  allowReadOnlyOpen : Bool := true
  allowReadWriteOpen : Bool := false
  allowRead : Bool := true
  allowWrite : Bool := false
  allowAttach : Bool := false
  allowLoadExtension : Bool := false
  allowHostEffect : Bool := false
  deriving DecidableEq, Repr

/-- Canonical read-only authority profile for one identified database `db`:
permits read-only open, prepare, read-step, finalize, and close on `db`;
classifies read-write open, writes, `ATTACH`, extension loading, access to any
other database, and unmodeled host effects as bad events. -/
def readOnlyProfile (db : DbId) : AuthorityProfile where
  allowedDb := db

/-- Restricted high-level SQLite API and host effect signature.
Typed requests carry their exact reply types. Forbidden operations are
explicitly representable so bad-event exclusion is non-vacuous. -/
inductive ApiEvent : Type → Type where
  | openDb (db : DbId) (mode : OpenMode) : ApiEvent (Except ApiError ConnHandle)
  | prepare (conn : ConnHandle) (db : DbId) (input : QueryInput) :
      ApiEvent (Except ApiError StmtHandle)
  | stepRead (stmt : StmtHandle) (db : DbId) :
      ApiEvent (Except ApiError StepOutcome)
  | finalize (stmt : StmtHandle) : ApiEvent (Except ApiError Unit)
  | closeDb (conn : ConnHandle) : ApiEvent (Except ApiError Unit)
  | writeDb (conn : ConnHandle) (db : DbId) (offset : Nat) (bytes : List UInt8) :
      ApiEvent (Except ApiError Unit)
  | attachDb (conn : ConnHandle) (target : DbId) (schemaName : String) :
      ApiEvent (Except ApiError Unit)
  | loadExtension (conn : ConnHandle) (path : String) :
      ApiEvent (Except ApiError Unit)
  | hostEffect (kind : HostEffectKind) : ApiEvent (Except ApiError Unit)

/-- Weak interaction tree over the restricted SQLite API effect signature. -/
abbrev ApiTree (A : Type) := ITree.Tree ApiEvent A

/-- Finite-prefix trace over `ApiEvent`. -/
abbrev ApiTrace (A : Type) := ITree.Trace ApiEvent A

/-- Nondeterministic relational handler for `ApiEvent` over abstract state `S`. -/
abbrev ApiHandler (S : Type) := ITree.Handler S ApiEvent

/-- Boolean decision procedure classifying whether an API request is a
forbidden ("bad") event under `profile`. -/
def isBadEvent (profile : AuthorityProfile) : {R : Type} → ApiEvent R → Bool
  | _, .openDb db .readOnly => !(db == profile.allowedDb && profile.allowReadOnlyOpen)
  | _, .openDb db .readWrite => !(db == profile.allowedDb && profile.allowReadWriteOpen)
  | _, .prepare _ db _ => !(db == profile.allowedDb && profile.allowRead)
  | _, .stepRead _ db => !(db == profile.allowedDb && profile.allowRead)
  | _, .finalize _ => false
  | _, .closeDb _ => false
  | _, .writeDb _ db _ _ => !(db == profile.allowedDb && profile.allowWrite)
  | _, .attachDb _ _ _ => !profile.allowAttach
  | _, .loadExtension _ _ => !profile.allowLoadExtension
  | _, .hostEffect _ => !profile.allowHostEffect

/-- Predicate characterizing forbidden ("bad") API/host requests under `profile`. -/
def BadEvent (profile : AuthorityProfile) (q : ITree.Request ApiEvent) : Prop :=
  isBadEvent profile q.2 = true

/-- Predicate characterizing requests permitted under `profile`. -/
def EventAllowed (profile : AuthorityProfile) (q : ITree.Request ApiEvent) : Prop :=
  ¬ BadEvent profile q

instance (profile : AuthorityProfile) (q : ITree.Request ApiEvent) :
    Decidable (BadEvent profile q) :=
  inferInstanceAs (Decidable (isBadEvent profile q.2 = true))

instance (profile : AuthorityProfile) (q : ITree.Request ApiEvent) :
    Decidable (EventAllowed profile q) :=
  inferInstanceAs (Decidable (¬ BadEvent profile q))

/-- Strict finite-prefix safety: no pending request or completed exchange in
`p` is a `BadEvent profile`, regardless of return value or divergence. -/
def TraceAvoidsBad {A : Type} (profile : AuthorityProfile) : ApiTrace A → Prop
  | .prefix => True
  | .result _ => True
  | .request e => ¬ BadEvent profile ⟨_, e⟩
  | .exchange e _ tail => ¬ BadEvent profile ⟨_, e⟩ ∧ TraceAvoidsBad profile tail

/-- Host-exchange finite-prefix safety: no completed host/DB exchange in `p` is
a `BadEvent profile`. A forbidden raw request need not take any particular
return path as long as no forbidden exchange occurs in the host trace. -/
def ExchangesAvoidBad {A : Type} (profile : AuthorityProfile) : ApiTrace A → Prop
  | .prefix => True
  | .result _ => True
  | .request _ => True
  | .exchange e _ tail => ¬ BadEvent profile ⟨_, e⟩ ∧ ExchangesAvoidBad profile tail

/-- Unconditional tree safety: every finite observation (including pending
requests and non-terminating prefixes) of `t` avoids `BadEvent profile`. -/
def TreeAvoidsBad {A : Type} (profile : AuthorityProfile) (t : ApiTree A) : Prop :=
  ∀ p, ITree.HasTrace t p → TraceAvoidsBad profile p

/-- Handler-scoped tree safety: every finite observation of `t` admitted by
`step` from initial state `s` avoids `BadEvent profile`. -/
def HandledTreeAvoidsBad {S A : Type} (profile : AuthorityProfile)
    (step : ApiHandler S) (s : S) (t : ApiTree A) : Prop :=
  ∀ p, ITree.HandledTrace step s t p → TraceAvoidsBad profile p

/-- Host-handler exclusion contract: `step` never admits a completed transition
for any `BadEvent profile`. No specific return path or refusal code is forced. -/
def HandlerExcludesBad {S : Type} (profile : AuthorityProfile) (step : ApiHandler S) : Prop :=
  ∀ (q : ITree.Request ApiEvent) (s s' : S) (r : q.1),
    step q s r s' → ¬ BadEvent profile q

/-- Explicit handler frame contract: every non-bad request under `profile`
preserves the projected protected state `protectedState` across every admitted
handler transition. -/
def FrameContract {S P : Type} (profile : AuthorityProfile)
    (step : ApiHandler S) (protectedState : S → P) : Prop :=
  ∀ (q : ITree.Request ApiEvent) (s s' : S) (r : q.1),
    ¬ BadEvent profile q →
    step q s r s' →
    protectedState s' = protectedState s

/-- Replay of a finite trace `p` from state `s` reaching post-prefix state `s'`.
Captures intermediate states along partial or non-terminating prefixes as well
as completed runs. -/
def ReplayTo {S A : Type} (step : ApiHandler S) : S → ApiTrace A → S → Prop
  | s, .prefix, s' => s' = s
  | s, .request _, s' => s' = s
  | s, .result _, s' => s' = s
  | s, .exchange e r tail, s' =>
      ∃ mid, step ⟨_, e⟩ s r mid ∧ ReplayTo step mid tail s'

/-- Issue a single raw API event and return its handler reply. -/
def rawCall {R : Type} (e : ApiEvent R) : ApiTree R :=
  ITree.vis e ITree.ret

/-! ## Arbitrary-tree profile confinement (outcome-orthogonal) -/

/-- Depth-indexed confinement of an arbitrary interaction tree: whenever the tree
would issue a `BadEvent profile`, replace that branch with an arbitrary
`onBad : ApiTree A` (which may return success, an error, run cleanup, or
diverge — no refusal return value is required). -/
def Approx.confine {A : Type} (profile : AuthorityProfile) (onBad : ApiTree A) :
    (n : Nat) → ITree.Approx ApiEvent A n → ITree.Approx ApiEvent A n
  | 0, _ => PUnit.unit
  | n + 1, x => x >>= fun
      | .ret a => Part.some (.ret a)
      | .vis e next =>
          if isBadEvent profile e then
            onBad.observe (n + 1)
          else
            Part.some (.vis e (fun r => Approx.confine profile onBad n (next r)))

theorem Approx.truncate_confine {A : Type} (profile : AuthorityProfile) (onBad : ApiTree A)
    (n : Nat) (x : ITree.Approx ApiEvent A (n + 1)) :
    ITree.Approx.truncate n (Approx.confine profile onBad (n + 1) x) =
      Approx.confine profile onBad n (ITree.Approx.truncate n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ITree.Approx.truncate, Approx.confine, Part.map_eq_map, Part.bind_eq_bind,
      Part.map_bind, Part.bind_map]
    apply congrArg (Part.bind x)
    funext node
    cases node with
    | ret a => simp
    | vis e next =>
      cases hbad : isBadEvent profile e
      · simp [hbad]
        funext r
        exact ih (next r)
      · simp [hbad]
        exact onBad.coherent (n + 1)

/-- Confine an arbitrary interaction tree `t : ApiTree A` under `profile` by
diverting any `BadEvent profile` node to an arbitrary `onBad : ApiTree A`. -/
def confineTree {A : Type} (profile : AuthorityProfile) (onBad : ApiTree A)
    (t : ApiTree A) : ApiTree A where
  observe n := Approx.confine profile onBad n (t.observe n)
  coherent n := by
    rw [Approx.truncate_confine, t.coherent]

/-! ## Worked sessions, negative witnesses, and reference handlers -/

/-- Realistic single-connection read-only SQLite API session over **any**
arbitrary `QueryInput` (arbitrary SQL string and raw payload bytes, with no
validity or limit assumptions): open → prepare → step-read → finalize → close,
covering parsing/preparation, execution, and cleanup on both normal and error
paths. -/
def openReadCloseSession (db : DbId) (input : QueryInput) :
    ApiTree (Except ApiError (Option RowData)) := do
  match ← rawCall (.openDb db .readOnly) with
  | .error err => pure (.error err)
  | .ok conn =>
    match ← rawCall (.prepare conn db input) with
    | .error err =>
      let _ ← rawCall (.closeDb conn)
      pure (.error err)
    | .ok stmt =>
      let stepRes ← rawCall (.stepRead stmt db)
      let _ ← rawCall (.finalize stmt)
      let _ ← rawCall (.closeDb conn)
      match stepRes with
      | .error err => pure (.error err)
      | .ok .done => pure (.ok none)
      | .ok (.row data) => pure (.ok (some data))

/-- Negative witness: unguarded DB write request. -/
def unsafeWriteProgram (conn : ConnHandle) (db : DbId) (offset : Nat) (bytes : List UInt8) :
    ApiTree (Except ApiError Unit) :=
  rawCall (.writeDb conn db offset bytes)

/-- Negative witness: unguarded `ATTACH DATABASE` request. -/
def unsafeAttachProgram (conn : ConnHandle) (target : DbId) (schemaName : String) :
    ApiTree (Except ApiError Unit) :=
  rawCall (.attachDb conn target schemaName)

/-- Negative witness: unguarded extension-loading request. -/
def unsafeLoadExtensionProgram (conn : ConnHandle) (path : String) :
    ApiTree (Except ApiError Unit) :=
  rawCall (.loadExtension conn path)

/-- Negative witness: unguarded host effect request. -/
def unsafeHostEffectProgram (kind : HostEffectKind) :
    ApiTree (Except ApiError Unit) :=
  rawCall (.hostEffect kind)

/-- Negative witness: unguarded read-write open request. -/
def unsafeReadWriteOpenProgram (db : DbId) :
    ApiTree (Except ApiError ConnHandle) :=
  rawCall (.openDb db .readWrite)

/-- Negative witness: unguarded open of another database. -/
def unsafeWrongDbOpenProgram (otherDb : DbId) :
    ApiTree (Except ApiError ConnHandle) :=
  rawCall (.openDb otherDb .readOnly)

/-- Concrete abstract state for a single-connection reference handler witness. -/
structure ReferenceState where
  protectedDb : DbId → List UInt8
  openConn : Option (ConnHandle × DbId × OpenMode) := none
  openStmt : Option (StmtHandle × ConnHandle × DbId) := none
  nextId : Nat := 0

/-- A nondeterministic single-connection reference handler that enforces
`readOnlyProfile allowedDb` at the host boundary:
- On permitted read-only operations on `allowedDb` (`openDb _ .readOnly`,
  `prepare`, `stepRead`, `finalize`, `closeDb`), it may succeed or return
  arbitrary backend errors while leaving `protectedDb` unchanged.
- On any `BadEvent (readOnlyProfile allowedDb)`, no host transition is
  admitted (`False`), so `HandlerExcludesBad` holds without mandating any
  particular return value. -/
def readOnlyReferenceHandler (allowedDb : DbId) : ApiHandler ReferenceState
  | ⟨_, .openDb db .readOnly⟩, s, reply, s' =>
      db = allowedDb ∧
      match reply with
      | .error _ => s' = s
      | .ok h =>
          s.openConn = none ∧
          h = ⟨s.nextId⟩ ∧
          s' = { s with openConn := some (h, db, .readOnly), nextId := s.nextId + 1 }
  | ⟨_, .prepare conn db _⟩, s, reply, s' =>
      db = allowedDb ∧
      match reply with
      | .error _ => s' = s
      | .ok stmt =>
          (∃ mode, s.openConn = some (conn, db, mode)) ∧
          s.openStmt = none ∧
          stmt = ⟨s.nextId⟩ ∧
          s' = { s with openStmt := some (stmt, conn, db), nextId := s.nextId + 1 }
  | ⟨_, .stepRead stmt db⟩, s, reply, s' =>
      db = allowedDb ∧
      match reply with
      | .error _ => s' = s
      | .ok _ =>
          (∃ conn, s.openStmt = some (stmt, conn, db)) ∧
          s' = s
  | ⟨_, .finalize stmt⟩, s, reply, s' =>
      match reply with
      | .error _ => s' = s
      | .ok () =>
          (∃ conn db, s.openStmt = some (stmt, conn, db)) ∧
          s' = { s with openStmt := none }
  | ⟨_, .closeDb conn⟩, s, reply, s' =>
      match reply with
      | .error _ => s' = s
      | .ok () =>
          (∃ db mode, s.openConn = some (conn, db, mode)) ∧
          s' = { s with openConn := none, openStmt := none }
  | ⟨_, .openDb _ .readWrite⟩, _, _, _ => False
  | ⟨_, .writeDb _ _ _ _⟩, _, _, _ => False
  | ⟨_, .attachDb _ _ _⟩, _, _, _ => False
  | ⟨_, .loadExtension _ _⟩, _, _, _ => False
  | ⟨_, .hostEffect _⟩, _, _, _ => False

/-- Honesty witness: a dishonest handler that mutates its state (`Nat`) even on
a non-bad read-only `openDb` request, violating `FrameContract`. -/
def dishonestHandler : ApiHandler Nat
  | ⟨_, .openDb _ .readOnly⟩, n, reply, n' => reply = .ok ⟨n⟩ ∧ n' = n + 1
  | _, n, _, n' => n' = n

end Silmaril.SQLite.Isolation.Api
