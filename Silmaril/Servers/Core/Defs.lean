module

public import Silmaril.Logic.Institution.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Logic.Function.Basic

/-!
# The server institution: request/response traces, sentences, models, morphisms

A server, however it is run (a Wasm component, a Linux process, a container), is seen through an
**interface** (`Sig`): what a request is (`Req`) and what a response is (`Resp`). The HTTP
interface (`Silmaril.Servers.Http`) takes the RFC 9110 messages of `Silmaril.Net.Http`; others
are coarser views (status only, the path only) or finer ones (interim responses, connections).

## Traces

What can be seen of a server is a **trace** (`Trace A`): the requests it receives and the
responses it sends, in order (`Event.recv`, `Event.send`). Each request has an identity
(`ReqId`): the connection it arrives on and its position there. A second request may arrive
before the first is answered: on the same connection (HTTP/1.1 pipelining, HTTP/2 streams) or on
another (concurrent clients). A trace is **well formed** (`WF`) when no identity is received
twice and every response answers an open request (`WMon`, a monitor over the trace).

## Sentences, models, satisfaction

A **sentence** is a property of traces (`Sen A`), a **model** is a server semantics, the set
of its traces (`Model A`: everything an environment can observe of it, partial correctness:
finite observations, no liveness), and **satisfaction** is inclusion: every trace of the model
satisfies the sentence (`Model.Sat`). **Refinement** of servers is trace inclusion
(`Model.Refines M N`, `M ≤ N`): a refinement satisfies every sentence its abstraction does.

## Morphisms

A morphism `h : A ⟶ B` (`Hom`) says how `B` is a finer view of `A`: `h.req` and `h.resp` say
what `A` sees of a request and of a response of `B`. Traces map backwards (`Hom.trace`),
sentences translate forwards (`Hom.sen`), models reduce (`Hom.mod`); the satisfaction condition
holds (`Hom.sat_sen_iff`) and the interfaces form a category, so this is an institution
(`inst : Sig ⥤ Room`, `classic`), in the style of the CLI institution
(`Silmaril.Cli.Institution`).

## The readings people reason with

* **Atomic, functional** (`Sen.atomic R`): each response is allowed by `R` for its request,
  `Sen.ofFun f` for a server that is a function `f : Req → Resp`;
* **Sequential** (`History A`, `Machine A σ`): a list of request/response pairs, accepted by
  a state machine whose handler runs atomically (`Machine.Hist`). `Silmaril.Net.Http.Origin` is
  a machine;
* **Linearizable** (`Sen.lin S`): the trace is explained by atomic handler runs at points
  between each request and its response (linearization points, `LEvent.lin`), whose sequence
  is a history in `S` (Herlihy and Wing 1990). The points are a monitor (`LMon`) over the
  trace annotated with them;
* **Sequentially consistent** (`Sen.sc S`): some reordering of the trace that keeps the order
  on each connection is linearizable (Lamport 1979): the order across connections is not
  observed;
* **In-order responses** (`Sen.inOrder`): on each connection, responses come in request order
  (HTTP/1.1 pipelining, RFC 9112 §9.3.2).

The lifts between them are in `Thms`: a function lifts to a stateless machine, and for
stateless machines linearizability is the atomic sentence; the atomic-handler server of a
machine (`Machine.server`) is linearizable; refinement is preserved by every lift.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers

open CategoryTheory Silmaril.Logic.Institution

/-! ## Interfaces and traces -/

/-- **An interface** (a signature of the institution): what a request and a response are. -/
structure Sig : Type 1 where
  /-- A request. -/
  Req : Type
  /-- A response. -/
  Resp : Type

/-- **The identity of a request**: its connection and its position on that connection. -/
structure ReqId where
  /-- The connection. -/
  conn : Nat
  /-- The position on the connection (`0` for the first request). -/
  seq : Nat
  deriving DecidableEq, Repr, Inhabited

/-- **An observable event**: a request received, or a response sent. -/
inductive Event (A : Sig) : Type where
  /-- The request `r` is received, with identity `i`. -/
  | recv (i : ReqId) (r : A.Req)
  /-- The response `s` is sent to the request `i`. -/
  | send (i : ReqId) (s : A.Resp)

/-- The identity an event concerns. -/
def Event.id {A : Sig} : Event A → ReqId
  | .recv i _ => i
  | .send i _ => i

/-- **A trace**: the events seen, in order. -/
abbrev Trace (A : Sig) : Type := List (Event A)

/-- The events of a trace on the connection `c`. -/
def Trace.onConn {A : Sig} (c : Nat) (t : Trace A) : Trace A := t.filter (·.id.conn == c)

/-! ## Runs of monitors -/

/-- The runs of a step relation over a list of events, from a state to a state. -/
inductive Steps {S E : Type} (step : S → E → S → Prop) : S → List E → S → Prop where
  | nil (s : S) : Steps step s [] s
  | cons {s s' s'' : S} {e : E} {es : List E} :
      step s e s' → Steps step s' es s'' → Steps step s (e :: es) s''

/-! ## Well-formed traces -/

/-- **The well-formedness monitor**: the request of every identity received so far, and the
requests still open (received, not yet answered). -/
structure WMon (A : Sig) : Type where
  /-- The request of each identity received so far. -/
  req : ReqId → Option A.Req
  /-- The open requests. -/
  open_ : ReqId → Option A.Req

/-- The initial monitor: nothing received. -/
def WMon.init (A : Sig) : WMon A := ⟨fun _ => none, fun _ => none⟩

/-- A step of the well-formedness monitor: a fresh identity is received; an open request is
answered once. -/
inductive WMon.Step {A : Sig} : WMon A → Event A → WMon A → Prop where
  | recv {m : WMon A} {i : ReqId} {r : A.Req} : m.req i = none →
      WMon.Step m (.recv i r)
        ⟨Function.update m.req i (some r), Function.update m.open_ i (some r)⟩
  | send {m : WMon A} {i : ReqId} {r : A.Req} {s : A.Resp} : m.open_ i = some r →
      WMon.Step m (.send i s) ⟨m.req, Function.update m.open_ i none⟩

/-! ## Linearization points -/

/-- **An event annotated with linearization points**: an observable event, or the atomic run
of the handler on the request `i`, `r`, answering `s`. -/
inductive LEvent (A : Sig) : Type where
  | ev (e : Event A)
  | lin (i : ReqId) (r : A.Req) (s : A.Resp)

/-- The observable events of an annotated trace. -/
def LEvent.erase {A : Sig} (t : List (LEvent A)) : Trace A :=
  t.filterMap fun | .ev e => some e | .lin .. => none

/-- **A history**: the request/response pairs of atomic handler runs, in order. -/
abbrev History (A : Sig) : Type := List (A.Req × A.Resp)

/-- The history of an annotated trace: its linearization points in order. -/
def LEvent.lins {A : Sig} (t : List (LEvent A)) : History A :=
  t.filterMap fun | .ev _ => none | .lin _ r s => some (r, s)

/-- **The linearization monitor**: the request of each identity received so far, the requests
received and not yet run (`pending`), and the responses computed and not yet sent (`ready`). -/
structure LMon (A : Sig) : Type where
  req : ReqId → Option A.Req
  pending : ReqId → Option A.Req
  ready : ReqId → Option A.Resp

/-- The initial linearization monitor. -/
def LMon.init (A : Sig) : LMon A := ⟨fun _ => none, fun _ => none, fun _ => none⟩

/-- A step of the linearization monitor: a fresh request is received; a pending request is run
once (its linearization point); a computed response is sent once. -/
inductive LMon.Step {A : Sig} : LMon A → LEvent A → LMon A → Prop where
  | recv {m : LMon A} {i : ReqId} {r : A.Req} : m.req i = none →
      LMon.Step m (.ev (.recv i r))
        ⟨Function.update m.req i (some r), Function.update m.pending i (some r), m.ready⟩
  | lin {m : LMon A} {i : ReqId} {r : A.Req} {s : A.Resp} : m.pending i = some r →
      LMon.Step m (.lin i r s)
        ⟨m.req, Function.update m.pending i none, Function.update m.ready i (some s)⟩
  | send {m : LMon A} {i : ReqId} {s : A.Resp} : m.ready i = some s →
      LMon.Step m (.ev (.send i s)) ⟨m.req, m.pending, Function.update m.ready i none⟩

/-- The annotated trace is a run of the linearization monitor. -/
def LEvent.Valid {A : Sig} (t : List (LEvent A)) : Prop := ∃ m, Steps LMon.Step (LMon.init A) t m

/-! ## Sequential specifications -/

/-- **A sequential specification**: the histories it allows. -/
abbrev SeqSpec (A : Sig) : Type := History A → Prop

/-- **A state machine** with state `σ`: in state `q` the request `r` may be answered `s`,
with next state `q'` (an atomic handler run; `Silmaril.Net.Http.Origin σ` at the HTTP
interface). -/
def Machine (A : Sig) (σ : Type) : Type := σ → A.Req → A.Resp → σ → Prop

/-- The histories of a machine from a state, ending in a state. -/
inductive Machine.Run {A : Sig} {σ : Type} (M : Machine A σ) : σ → History A → σ → Prop where
  | nil (q : σ) : Machine.Run M q [] q
  | cons {q q' q'' : σ} {r : A.Req} {s : A.Resp} {h : History A} :
      M q r s q' → Machine.Run M q' h q'' → Machine.Run M q ((r, s) :: h) q''

/-- The histories a machine allows from `q₀`. -/
def Machine.Hist {A : Sig} {σ : Type} (M : Machine A σ) (q₀ : σ) : SeqSpec A :=
  fun h => ∃ q, M.Run q₀ h q

/-- The stateless machine of a relation: every request may be answered as `R` allows. -/
def Machine.ofRel {A : Sig} (R : A.Req → A.Resp → Prop) : Machine A Unit :=
  fun _ r s _ => R r s

/-- The stateless machine of a function. -/
def Machine.ofFun {A : Sig} (f : A.Req → A.Resp) : Machine A Unit :=
  Machine.ofRel fun r s => s = f r

/-- The sequential specification where every pair is allowed by `R`. -/
def SeqSpec.pointwise {A : Sig} (R : A.Req → A.Resp → Prop) : SeqSpec A :=
  fun h => ∀ p ∈ h, R p.1 p.2

/-! ## Sentences -/

/-- **A sentence**: a property of traces. Entailment between sentences is `≤`. -/
abbrev Sen (A : Sig) : Type := Trace A → Prop

namespace Sen

variable {A : Sig}

/-- **Well formed**: identities are fresh and each response answers an open request. -/
def WF : Sen A := fun t => ∃ m, Steps WMon.Step (WMon.init A) t m

/-- **Atomic**: every response is allowed by `R` for the request with its identity. -/
def atomic (R : A.Req → A.Resp → Prop) : Sen A :=
  fun t => ∀ i r s, Event.recv i r ∈ t → Event.send i s ∈ t → R r s

/-- **Functional**: every response is `f` of its request. -/
def ofFun (f : A.Req → A.Resp) : Sen A := atomic fun r s => s = f r

/-- **Linearizable** with respect to `S`: some placement of atomic handler runs between each
request and its response, in a valid annotated trace, explains the trace by a history in `S`.
Pending requests may or may not have been run. -/
def lin (S : SeqSpec A) : Sen A :=
  fun t => ∃ t' : List (LEvent A), LEvent.Valid t' ∧ LEvent.erase t' = t ∧ S (LEvent.lins t')

/-- **Sequentially consistent** with respect to `S`: a reordering of the trace that keeps the
events of each connection in order is linearizable. -/
def sc (S : SeqSpec A) : Sen A :=
  fun t => ∃ t₂ : Trace A, (∀ c, t₂.onConn c = t.onConn c) ∧ lin S t₂

/-- **In-order responses** (HTTP/1.1 pipelining, RFC 9112 §9.3.2): when the request `j` is
answered, every earlier request received on its connection has been answered. -/
def inOrder : Sen A :=
  fun t => ∀ pre post j s, t = pre ++ Event.send j s :: post →
    ∀ i r, Event.recv i r ∈ pre → i.conn = j.conn → i.seq < j.seq → ∃ s', Event.send i s' ∈ pre

/-- **Sequential use**: the trace answers each request before the next arrives. -/
def Sequential : Sen A :=
  fun t => ∃ h : List (ReqId × A.Req × A.Resp), (h.map (·.1)).Nodup ∧
    t = h.flatMap fun p => [Event.recv p.1 p.2.1, Event.send p.1 p.2.2]

end Sen

/-! ## Models -/

/-- **A model**: a server semantics, the traces an environment can observe of it. -/
@[ext] structure Model (A : Sig) : Type where
  /-- `Tr t`: the server can be observed doing `t`. -/
  Tr : Trace A → Prop

instance (A : Sig) : PartialOrder (Model A) :=
  PartialOrder.lift Model.Tr fun _ _ h => Model.ext h

/-- **Satisfaction**: every trace of the model satisfies the sentence. -/
def Model.Sat {A : Sig} (M : Model A) (φ : Sen A) : Prop := ∀ t, M.Tr t → φ t

/-- **Refinement**: trace inclusion. -/
def Model.Refines {A : Sig} (M N : Model A) : Prop := M ≤ N

/-- A step of the atomic-handler server of a machine: the monitor's step, and at a
linearization point a step of the machine. -/
def Machine.serverStep {A : Sig} {σ : Type} (M : Machine A σ) :
    σ × LMon A → LEvent A → σ × LMon A → Prop
  | (q, m), .ev e, (q', m') => q' = q ∧ LMon.Step m (.ev e) m'
  | (q, m), .lin i r s, (q', m') => M q r s q' ∧ LMon.Step m (.lin i r s) m'

/-- **The atomic-handler server of a machine**: requests arrive in any order the environment
chooses, on fresh identities; the handler runs atomically on some pending request, in any
order; computed responses are sent in any order. Its traces are the observable parts of the
interleavings of these steps. -/
def Machine.server {A : Sig} {σ : Type} (M : Machine A σ) (q₀ : σ) : Model A :=
  ⟨fun t => ∃ (t' : List (LEvent A)) (fin : σ × LMon A),
    Steps (Machine.serverStep M) (q₀, LMon.init A) t' fin ∧ LEvent.erase t' = t⟩

/-- The model of a function server: every well-formed trace whose responses are `f` of their
requests. -/
def Model.ofFun {A : Sig} (f : A.Req → A.Resp) : Model A := ⟨fun t => Sen.WF t ∧ Sen.ofFun f t⟩

/-! ## Morphisms and the institution -/

/-- **A morphism of interfaces** `A ⟶ B`: what `A` sees of a request and of a response of
`B`. -/
@[ext] structure Hom (A B : Sig) : Type where
  req : B.Req → A.Req
  resp : B.Resp → A.Resp

namespace Hom

variable {A B C : Sig}

def id (A : Sig) : Hom A A := ⟨_root_.id, _root_.id⟩

def comp (f : Hom A B) (g : Hom B C) : Hom A C := ⟨f.req ∘ g.req, f.resp ∘ g.resp⟩

/-- What `A` sees of an event of `B`. -/
def event (h : Hom A B) : Event B → Event A
  | .recv i r => .recv i (h.req r)
  | .send i s => .send i (h.resp s)

/-- What `A` sees of a trace of `B`. -/
def trace (h : Hom A B) (t : Trace B) : Trace A := t.map h.event

/-- What `A` sees of a history of `B`. -/
def history (h : Hom A B) (hs : History B) : History A := hs.map fun p => (h.req p.1, h.resp p.2)

/-- **Sentence translation**: `φ` of what `A` sees. -/
def sen (h : Hom A B) (φ : Sen A) : Sen B := fun t => φ (h.trace t)

/-- **The reduct of a model**: what `A` sees of its traces. -/
def mod (h : Hom A B) (M : Model B) : Model A := ⟨fun t => ∃ t', M.Tr t' ∧ h.trace t' = t⟩

/-- Translation of a sequential specification. -/
def seq (h : Hom A B) (S : SeqSpec A) : SeqSpec B := fun hs => S (h.history hs)

/-- **The satisfaction condition.** -/
theorem sat_sen_iff (h : Hom A B) (M : Model B) (φ : Sen A) :
    M.Sat (h.sen φ) ↔ (h.mod M).Sat φ :=
  ⟨fun H _ ⟨t', ht', he⟩ => he ▸ H t' ht', fun H t ht => H _ ⟨t, ht, rfl⟩⟩

theorem mod_mono (h : Hom A B) {M N : Model B} (hMN : M ≤ N) : h.mod M ≤ h.mod N :=
  fun _ ⟨t', ht', he⟩ => ⟨t', hMN t' ht', he⟩

theorem event_comp (f : Hom A B) (g : Hom B C) (e : Event C) :
    (comp f g).event e = f.event (g.event e) := by
  cases e <;> rfl

theorem trace_comp (f : Hom A B) (g : Hom B C) (t : Trace C) :
    (comp f g).trace t = f.trace (g.trace t) := by
  simp only [trace, List.map_map]; congr 1; funext e; exact event_comp f g e

theorem trace_id (t : Trace A) : (id A).trace t = t := by
  simp only [trace]; conv => rhs; rw [← List.map_id t]
  congr 1; funext e; cases e <;> rfl

end Hom

instance : Category Sig where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

/-- The room of an interface: its sentences, its models ordered by trace inclusion, and
satisfaction. -/
def room (A : Sig) : Room.{0, 0, 0} := ⟨Sen A, Cat.of (Model A), fun M φ => M.Sat φ⟩

/-- The corridor of a morphism. -/
def corridor {A B : Sig} (h : A ⟶ B) : room A ⟶ room B :=
  ⟨Hom.sen h, (Monotone.functor (f := Hom.mod h) fun _ _ hMN => Hom.mod_mono h hMN :
    Model B ⥤ Model A), fun M φ => Hom.sat_sen_iff h M φ⟩

theorem Hom.sen_id (A : Sig) : Hom.sen (𝟙 A) = _root_.id := by
  funext φ t; exact congrArg φ (Hom.trace_id t)

theorem Hom.sen_comp {A B C : Sig} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.sen (f ≫ g) = Hom.sen g ∘ Hom.sen f := by
  funext φ t; exact congrArg φ (Hom.trace_comp f g t)

theorem Hom.mod_id (A : Sig) (M : Model A) : Hom.mod (𝟙 A) M = M := by
  apply Model.ext; funext t; apply propext
  exact ⟨fun ⟨t', ht', he⟩ => by rw [← he]; exact (Hom.trace_id t').symm ▸ ht',
    fun ht => ⟨t, ht, Hom.trace_id t⟩⟩

theorem Hom.mod_comp {A B C : Sig} (f : A ⟶ B) (g : B ⟶ C) (M : Model C) :
    Hom.mod (f ≫ g) M = Hom.mod f (Hom.mod g M) := by
  apply Model.ext; funext t; apply propext
  constructor
  · rintro ⟨t', ht', rfl⟩
    exact ⟨g.trace t', ⟨t', ht', rfl⟩, (Hom.trace_comp f g t').symm⟩
  · rintro ⟨_, ⟨t', ht', rfl⟩, rfl⟩
    exact ⟨t', ht', Hom.trace_comp f g t'⟩

/-- **The server institution**, as a functor into rooms. -/
def inst : Sig ⥤ Room.{0, 0, 0} where
  obj := room
  map h := corridor h
  map_id A := Room.hom_ext (Hom.sen_id A)
    (CategoryTheory.Functor.ext (fun M => Hom.mod_id A M) (fun _ _ _ => rfl))
  map_comp f g := Room.hom_ext (Hom.sen_comp f g)
    (CategoryTheory.Functor.ext (fun M => Hom.mod_comp f g M) (fun _ _ _ => rfl))

/-- The server institution in the classic presentation. -/
def classic : ClassicInstitution.{1, 0, 0, 0, 0} Sig := ClassicInstitution.ofRoomFunctor inst

end Silmaril.Servers
