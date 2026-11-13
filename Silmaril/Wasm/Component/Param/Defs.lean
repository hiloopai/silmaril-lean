module

public import Silmaril.Wasm.Component.Reference.Sound.Defs
public import Silmaril.Wasm.Component.Reference.LinkSound.Defs

/-!
# The Component Model parametrized by a core engine: definitions

The reference component machine (`Silmaril.Wasm.Component.Reference`) is generic over a core engine
`E : Engine` (silmaril-lean's `CoreEngine`), but its soundness chain is stated for the Core 3.0
engine `core3P P`. This module gives the engine-generic objects of `docs/projects/spectec/README.md` §3:

* **The game semantics of an engine.** `engineStrategy E I imps exps` is the strategy of an
  engine instance `I` (a store and the function addresses of its exports) over the IR's flat
  signatures. An export question of the right flat types invokes the export function. Engine
  `Internal` steps are silent. A thread parked on a callout of host function `h` asks import
  question `h`; the answer resumes it (`E.resume`), with a trap for an answer of the wrong flat
  types. A returned thread answers the export question, and the store persists to the next
  question. Ill-typed export questions are answered by a trap. It is the analogue of
  `Silmaril.Wasm.Game.ScalarInstance.strategy`, defined once for every engine.
* `instOf E m imps exps`: the engine instance of module `m`. Import `i` is a host function with
  code `i` (`allocHost`), the module is prepared (`prepare?`) against these functions, and the
  exports are found by name. A start function is not run: such a module has no instance here.
* `engineSem E M emb : CoreSem M`: the core semantics of the IR given by an engine, through a
  map `emb : M → E.Module` (a module without an instance traps on every question).
* `GameEngine`: an engine with its `Lawful` laws, its ABI law (`AbiLawful`), an IR module type
  and `emb`.
* `restrict E r`: a restriction of an engine to the modules satisfying `r.Mod` (in `Valid`)
  and to internal steps landing in `r.Rt` (`Internal`). Everything else is `E`'s, so the
  component machine over `restrict E r` takes only steps of the machine over `E` (theorems in
  `Param.Thms`).

**Soundness properties of an engine** (the fallback of the design, `docs/projects/spectec/README.md` §3).
The reference-machine half `refToSpec` is proved by symbolic execution of `core3P P`, and its
proof goes through Core 3.0 runs, host-type transport and Core 3.0 typing, so it is not
generalised to an arbitrary engine here. Instead the halves are `Prop`-valued properties of an
engine over Core 3.0 module syntax (`ofCore : Silmaril.Wasm.Module → E.Module`):

* `RefToSpec E ofCore P`: reference behaviours of simple components over `E` are outcomes of the
  Core 3.0 canonical-ABI specification `exportSpec P` (`Reference.refToSpec_of_arity` for `E`);
* `SeqRefToSpec E ofCore P`: the same for sequences of calls (`Reference.seq_refToSpec`);
* `Link2Sound E ofCore P`, `Link2SoundSeq E ofCore P`: soundness of two linked components
  (`Reference.Linked2.sound`, `Reference.Linked2.sound_seq`).

`core3P P` has all four (from the existing proofs), every restriction of an engine that has them
has them too, and each gives soundness against the IR over `modSem P` / `impSem P` by composing
with the engine-independent IR half (`Param.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Param

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm (NumType)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component.Engine (CallResult Status)
open Silmaril.Wasm.Component.Engine.CoreEngine (Steps Lawful)

/-! ## The game semantics of an engine -/

/-- The flat values `xs` have the core types `ts`. -/
def FlatTyped (ts : List NumType) (xs : List Flat) : Prop := xs.map (·.type) = ts

instance (ts : List NumType) (xs : List Flat) : Decidable (FlatTyped ts xs) :=
  inferInstanceAs (Decidable (_ = _))

/-- An instance of an engine: the store after instantiation, and the function address of each
export, in the order of the IR's exports. Host function code `i` denotes import `i`. -/
structure EInstance (E : Engine) where
  /-- The store after instantiation. -/
  store : E.Store Nat
  /-- The function address of each export. -/
  addrs : List E.FuncAddr

/-- The export function invoked by the question `q`, when `q` has the export's flat parameter
types. -/
def callee? {E : Engine} (addrs : List E.FuncAddr) (exps : CoreIface)
    (q : (sigN exps.length).Op) : Option (E.FuncAddr × List Flat) :=
  match q.2 with
  | .flat xs =>
    if FlatTyped exps[q.1].2.params xs then (addrs[q.1.1]?).map fun a => (a, xs) else none
  | .vals _ => none

/-- The core result of an answer to an import call with flat result types `ts`: the flat
values of these types, and a trap for anything else. -/
def resultOf (ts : List NumType) : Option Payload → CallResult
  | some (.flat ys) => if FlatTyped ts ys then .values ys else .trap
  | _ => .trap

/-- Hidden states of the engine strategy. -/
inductive EState (E : Engine) (n k : Nat) where
  /-- No export call is active; the store persists. -/
  | idle (s : E.Store Nat)
  /-- The export question `q` is answered by the thread `t`. -/
  | running (q : (sigN k).Op) (s : E.Store Nat) (t : E.Thread Nat)
  /-- The thread waits for the answer to the import question `e`. -/
  | waiting (q : (sigN k).Op) (s : E.Store Nat) (t : E.Thread Nat) (e : (sigN n).Op)
  /-- The ill-typed export question `q` is about to be answered by a trap. -/
  | refusing (q : (sigN k).Op) (s : E.Store Nat)

/-- The moves of an engine instance with flat imports `imps` and exports `exps`, with their
effect on the hidden state. -/
inductive ETrans (E : Engine) (addrs : List E.FuncAddr) (imps exps : CoreIface) :
    EState E imps.length exps.length → Move (sigN imps.length) (sigN exps.length) →
      EState E imps.length exps.length → Prop where
  /-- An export question of the right flat types invokes the export (Opponent). -/
  | call {s : E.Store Nat} {q : (sigN exps.length).Op} {a : E.FuncAddr} {xs : List Flat}
      (h : callee? addrs exps q = some (a, xs)) :
      ETrans E addrs imps exps (.idle s) (.inr (.ask q)) (.running q s (E.invoke a xs))
  /-- Any other export question is refused (Opponent). -/
  | refuse {s : E.Store Nat} {q : (sigN exps.length).Op} (h : callee? addrs exps q = none) :
      ETrans E addrs imps exps (.idle s) (.inr (.ask q)) (.refusing q s)
  /-- The refused question is answered by a trap (Proponent). -/
  | refused {s : E.Store Nat} {q : (sigN exps.length).Op} :
      ETrans E addrs imps exps (.refusing q s) (.inr (.ans q none)) (.idle s)
  /-- A run of internal steps to a callout of host function `h` asks import `h` (Proponent). -/
  | ucall {q : (sigN exps.length).Op} {s s' : E.Store Nat} {t t' : E.Thread Nat} {h : Nat}
      {args : List Flat} (run : Steps E (s, t) (s', t'))
      (callout : E.status s' t' = .callout h args) (hh : h < imps.length) :
      ETrans E addrs imps exps (.running q s t) (.inl (.ask (⟨h, hh⟩, .flat args)))
        (.waiting q s' t' (⟨h, hh⟩, .flat args))
  /-- The answer to the import call resumes the thread (Opponent). -/
  | uret {q : (sigN exps.length).Op} {s : E.Store Nat} {t : E.Thread Nat}
      {e : (sigN imps.length).Op} (r : Option Payload) :
      ETrans E addrs imps exps (.waiting q s t e) (.inl (.ans e r))
        (.running q s (E.resume s t (resultOf imps[e.1].2.results r)))
  /-- A run of internal steps to returned values answers the export question (Proponent). -/
  | oret {q : (sigN exps.length).Op} {s s' : E.Store Nat} {t t' : E.Thread Nat}
      {ys : List Flat} (run : Steps E (s, t) (s', t'))
      (final : E.status s' t' = .returned (.values ys)) :
      ETrans E addrs imps exps (.running q s t) (.inr (.ans q (some (.flat ys)))) (.idle s')
  /-- A run of internal steps to a trap answers the export question with a trap (Proponent). -/
  | otrap {q : (sigN exps.length).Op} {s s' : E.Store Nat} {t t' : E.Thread Nat}
      (run : Steps E (s, t) (s', t')) (final : E.status s' t' = .returned .trap) :
      ETrans E addrs imps exps (.running q s t) (.inr (.ans q none)) (.idle s')

/-- The transition system of an engine instance. -/
def engineLTS (E : Engine) (I : EInstance E) (imps exps : CoreIface) :
    LTS (sigN imps.length) (sigN exps.length) where
  State := EState E imps.length exps.length
  init := .idle I.store
  step x l y := ∃ m, l = some m ∧ ETrans E I.addrs imps exps x m y

/-- **The game semantics of an engine instance**: the strategy of its transition system. The
store is hidden and persists across export calls. -/
def engineStrategy (E : Engine) (I : EInstance E) (imps exps : CoreIface) :
    Strategy (sigN imps.length) (sigN exps.length) :=
  Strategy.ofLTS (engineLTS E I imps exps)

/-! ## Engine instances of modules -/

/-- The flat signature of a core function type. -/
def v1Type (ft : CoreFuncTy) : Silmaril.Wasm.V1.FuncType := ⟨ft.params, ft.results⟩

/-- Allocate one host function per import, with code its index (starting at `i`). -/
def allocHosts (E : Engine) : E.Store Nat → Nat → CoreIface → E.Store Nat × List E.FuncAddr
  | s, _, [] => (s, [])
  | s, i, (_, ft) :: is =>
    let (s₁, a) := E.allocHost s (v1Type ft) i
    let (s₂, as) := allocHosts E s₁ (i + 1) is
    (s₂, a :: as)

/-- The function addresses of the exports named in `exps`. -/
def exportAddrs (E : Engine) (inst : E.Inst) (exps : CoreIface) : Option (List E.FuncAddr) :=
  exps.mapM fun x => ((E.exports inst).lookup x.1).bind E.asFunc?

/-- **The engine instance of module `m`** with imports `imps` and exports `exps`: the imports
are host functions with codes `0, 1, …` in the empty store, the module is prepared against them,
and the exports are looked up by name. A module with a start function has no instance here. -/
def instOf (E : Engine) (m : E.Module) (imps exps : CoreIface) : Option (EInstance E) :=
  let (s, as) := allocHosts E (E.empty Nat) 0 imps
  match E.prepare? s m (as.map E.ofFunc) with
  | some (s', inst, none) => (exportAddrs E inst exps).map fun addrs => ⟨s', addrs⟩
  | _ => none

/-- **The core semantics of the IR given by an engine**: each module denotes the game semantics
of its engine instance (through `emb`), and traps on every question when it has none. -/
def engineSem (E : Engine) (M : Type) [CoreModule M] (emb : M → E.Module) : CoreSem M where
  sem m :=
    match instOf E (emb m) (CoreModule.imports m) (CoreModule.exports m) with
    | some I => engineStrategy E I (CoreModule.imports m) (CoreModule.exports m)
    | none => trapAll _ _

/-! ## The canonical-ABI specification over an engine -/

/-- The outcomes of calling the `k`-th export of the engine instance `I` on the flat values
`xs` with no host: `some ys` for returned values, `none` for a trap (a run of internal steps to
a returned status). -/
def engineOut (E : Engine) (I : EInstance E) (k : Nat) (xs : List Flat) :
    Set (Option (List Flat)) :=
  {r | ∃ a s' t', I.addrs[k]? = some a ∧ Steps E (I.store, E.invoke a xs) (s', t') ∧
    ((∃ ys, E.status s' t' = .returned (.values ys) ∧ r = some ys) ∨
      (E.status s' t' = .returned .trap ∧ r = none))}

/-- The call may diverge. -/
def engineDiverges (E : Engine) (I : EInstance E) (k : Nat) (xs : List Flat) : Prop :=
  ∃ a, I.addrs[k]? = some a ∧
    Silmaril.Wasm.Component.Engine.CoreEngine.Diverges E (I.store, E.invoke a xs)

/-- **The canonical-ABI specification over an engine** of calling export `x` of the simple
component `c` on the IR values `vs`: lower the arguments, run the core export on the engine
instance of `c`'s module (through `emb`), lift the results. It is `Reference.exportSpec` with
the Core 3.0 run replaced by an engine run. -/
def exportSpecE (E : Engine) (emb : NumModule → E.Module) (c : Simple) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) : Set Outcome :=
  match checkLower x.ty.params vs with
  | none => {.traps}
  | some xs =>
    {b | ∃ I, instOf E (emb c.mod) (CoreModule.imports c.mod) (CoreModule.exports c.mod) = some I ∧
      ∃ r ∈ engineOut E I x.core xs, b = liftOutcome x.ty r} ∪
    {b | b = .diverges ∧ ∃ I,
      instOf E (emb c.mod) (CoreModule.imports c.mod) (CoreModule.exports c.mod) = some I ∧
      engineDiverges E I x.core xs}

/-! ## Game engines -/

/-- **The ABI law**: the canonical ABI (`Silmaril.Wasm.Component.Canon`) is defined once for
every engine and reaches core memories and tables only through `memSize?`, `memRead?`,
`memWrite?`, `memAddrType?` and `tableFunc?` (by parametricity: it is a definition over an
arbitrary `CoreEngine`). What lifting and lowering need of these accessors is that a write is
read back, leaves other ranges, all sizes and all address types alone, that accesses succeed
exactly in bounds, and that writes extend the store. -/
structure AbiLawful (E : Engine) : Prop where
  memWrite_extends : ∀ {H : Type} {s s' : E.Store H} {m st bs},
    E.memWrite? s m st bs = some s' → E.Extends s s'
  memWrite_memSize : ∀ {H : Type} {s s' : E.Store H} {m st bs},
    E.memWrite? s m st bs = some s' → ∀ m', E.memSize? s' m' = E.memSize? s m'
  memWrite_memAddrType : ∀ {H : Type} {s s' : E.Store H} {m st bs},
    E.memWrite? s m st bs = some s' → ∀ m', E.memAddrType? s' m' = E.memAddrType? s m'
  memWrite_read : ∀ {H : Type} {s s' : E.Store H} {m st bs},
    E.memWrite? s m st bs = some s' → E.memRead? s' m st bs.size = some bs
  memWrite_read_other : ∀ {H : Type} {s s' : E.Store H} {m st bs m' st' len},
    E.memWrite? s m st bs = some s' → (m' ≠ m ∨ st' + len ≤ st ∨ st + bs.size ≤ st') →
      E.memRead? s' m' st' len = E.memRead? s m' st' len
  memRead_isSome_iff : ∀ {H : Type} {s : E.Store H} {m st len},
    (E.memRead? s m st len).isSome ↔ ∃ n, E.memSize? s m = some n ∧ st + len ≤ n
  memRead_size : ∀ {H : Type} {s : E.Store H} {m st len bs},
    E.memRead? s m st len = some bs → bs.size = len
  memWrite_isSome_iff : ∀ {H : Type} {s : E.Store H} {m st bs},
    (E.memWrite? s m st bs).isSome ↔ ∃ n, E.memSize? s m = some n ∧ st + bs.size ≤ n

/-- **An engine with its game semantics**: a lawful engine, its ABI law, and the IR modules it
runs (`emb`). `CoreEngine.ResumeLawful` is not required: Core 3.0 does not satisfy it (resuming a
callout may reach another callout at once, see `Silmaril.Wasm.Component.Engine.Core3`). -/
structure GameEngine where
  /-- The engine. -/
  E : Engine
  /-- Its laws. -/
  lawful : E.Lawful
  /-- Its ABI law. -/
  abi : AbiLawful E
  /-- The IR's core modules. -/
  M : Type
  /-- Their flat interfaces. -/
  core : CoreModule M
  /-- The engine module of an IR module. -/
  emb : M → E.Module

attribute [instance] GameEngine.lawful GameEngine.core

/-- The core semantics of the IR given by a game engine. -/
def GameEngine.sem (G : GameEngine) : CoreSem G.M := engineSem G.E G.M G.emb

/-- The memory laws of a lawful engine are its ABI law. -/
theorem AbiLawful.ofLawful (E : Engine) [L : E.Lawful] : AbiLawful E :=
  ⟨L.memWrite_extends, L.memWrite_memSize, L.memWrite_memAddrType, L.memWrite_read,
    L.memWrite_read_other, L.memRead_isSome_iff, L.memRead_size, L.memWrite_isSome_iff⟩

/-- A module of the Mock engine with declared flat interfaces. -/
structure MockModule where
  /-- The Mock module. -/
  mod : Silmaril.Wasm.Component.Engine.Mock.Module
  /-- Its imported functions. -/
  imports : CoreIface
  /-- Its exported functions. -/
  exports : CoreIface

instance : CoreModule MockModule := ⟨MockModule.imports, MockModule.exports⟩

/-- **The Mock engine as a game engine**: an engine other than Core 3.0 that fits the
structure. -/
def mockG : GameEngine where
  E := Silmaril.Wasm.Component.Engine.Mock.mock
  lawful := inferInstance
  abi := AbiLawful.ofLawful _
  M := MockModule
  core := inferInstance
  emb := MockModule.mod

/-! ## Restrictions of an engine -/

/-- A restriction of an engine: the modules kept (`Mod`), and the configurations internal steps
may land in (`Rt`, a runtime invariant such as "the code is in the feature set"). -/
structure Restriction (E : Engine) where
  /-- The modules of the restriction. -/
  Mod : E.Module → Prop
  /-- The configurations of the restriction. -/
  Rt : {H : Type} → E.Config H → Prop

/-- **The restriction of an engine**: validity also requires `r.Mod`, and an internal step must
land in `r.Rt`. Everything else (stores, instantiation, memories, tables, status, resumption) is
`E`'s. -/
abbrev restrict (E : Engine) (r : Restriction E) : Engine :=
  { E with
    Valid := fun m => E.Valid m ∧ r.Mod m
    Internal := fun c c' => E.Internal c c' ∧ r.Rt c' }

instance (E : Engine) (r : Restriction E) [d : ∀ a b, Decidable (E.ExternSub a b)] :
    ∀ a b, Decidable ((restrict E r).ExternSub a b) := d

/-- An engine instance as an instance of a restriction. -/
def EInstance.res {E : Engine} {r : Restriction E} (I : EInstance E) :
    EInstance (restrict E r) :=
  ⟨I.store, I.addrs⟩

/-- A hidden state of a restriction as a hidden state of the engine. -/
def EState.unres {E : Engine} {r : Restriction E} {n k : Nat} :
    EState (restrict E r) n k → EState E n k
  | .idle s => .idle s
  | .running q s t => .running q s t
  | .waiting q s t e => .waiting q s t e
  | .refusing q s => .refusing q s

/-- A hidden state of the engine as a hidden state of a restriction. -/
def EState.res {E : Engine} {r : Restriction E} {n k : Nat} :
    EState E n k → EState (restrict E r) n k
  | .idle s => .idle s
  | .running q s t => .running q s t
  | .waiting q s t e => .waiting q s t e
  | .refusing q s => .refusing q s

/-- The runtime invariant is closed under the internal steps of `E`. -/
def Restriction.Closed {E : Engine} (r : Restriction E) : Prop :=
  ∀ {H : Type} {c c' : E.Config H}, r.Rt c → E.Internal c c' → r.Rt c'

/-! ## Soundness properties of an engine over Core 3.0 module syntax -/

/-- The reference host without host functions, over any engine. -/
def refHostE (E : Engine) : Host E Unit :=
  { hr := fun _ _ => false, impl := Silmaril.Wasm.Component.Canon.HostImpl.none }

/-- The reference host answering the core imports by `impl`, over any engine. -/
def linkHostE {E : Engine} {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl E σ) :
    Host E σ :=
  { hr := fun _ _ => false, impl := impl }

variable (E : Engine) [∀ a b, Decidable (E.ExternSub a b)]
  (ofCore : Silmaril.Wasm.Module → E.Module) (P : Profile)

/-- **The reference-machine half for engine `E`**: for a simple component in the fragment of
`Reference.refToSpec_of_arity`, every behaviour of calling export `x` of `c.toRef` (its core
module mapped by `ofCore`) over `E` is an outcome of the Core 3.0 canonical-ABI specification at
profile `P`. -/
def RefToSpec : Prop :=
  ∀ (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple), c.Good → c.FloatFree → c.Inst →
    c.Arity → ∀ x ∈ c.exports, ∀ vs, ValTy.checkList x.ty.params vs = true →
      exportBehaviours prof (refHostE E) () (c.toRef.map ofCore) [] x.name (vs.map toRefVal) ⊆
        exportSpec P c x vs

/-- **The reference-machine half for sequences of calls over engine `E`** (the statement of
`Reference.seq_refToSpec`). -/
def SeqRefToSpec : Prop :=
  ∀ (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple), c.Good → c.FloatFree → c.Inst →
    c.Arity → ∀ (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val), TypedCalls c calls →
    ValTy.checkList c.exports[j].ty.params vs = true →
    ∀ p ∈ seqBehaviours prof (refHostE E) () (c.toRef.map ofCore)
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal),
    ∃ (I : Silmaril.Wasm.Game.ScalarInstance) (wss : List (List Silmaril.Wasm.Component.Val))
      (s : Silmaril.Wasm.Execution.Core.Store Nat), c.mod.IsInst I ∧
      SeqSpec P c I I.store (specCalls c calls) wss s ∧ p.1 = wss.map (·.map toRefVal) ∧
      p.2 ∈ specAt P c I c.exports[j] vs s

/-- **Soundness of two linked components over engine `E`** (the statement of
`Reference.Linked2.sound`, with the host functions an arbitrary `HostImpl E σ`). -/
def Link2Sound : Prop :=
  ∀ (prof : Silmaril.Wasm.Component.ProfileKind) (l : Linked2), l.exp.Good → l.exp.Inst →
    l.imp.Good → l.imp.Inst → l.imp.Arity → l.imp.FloatFree → l.WireTy → l.NamesOk →
    l.WireNodup → l.SplitOk → ∀ {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl E σ)
    (h₀ : σ) (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val),
    ValTy.checkList l.imp.exports[j].ty.params vs = true →
    ∀ b ∈ exportBehaviours prof (linkHostE impl) h₀ (l.toRef.map ofCore) []
      l.imp.exports[j].name (vs.map toRefVal),
    Linked2.IRObs P l j vs b

/-- **Soundness of two linked components for sequences of calls over engine `E`** (the
statement of `Reference.Linked2.sound_seq`). -/
def Link2SoundSeq : Prop :=
  ∀ (prof : Silmaril.Wasm.Component.ProfileKind) (l : Linked2), l.exp.Good → l.exp.Inst →
    l.imp.Good → l.imp.Inst → l.imp.Arity → l.imp.FloatFree → l.WireTy → l.NamesOk →
    l.WireNodup → l.SplitOk → ∀ {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl E σ)
    (h₀ : σ) (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val),
    SimpleI.TypedCalls l.imp calls → ValTy.checkList l.imp.exports[j].ty.params vs = true →
    ∀ p ∈ seqBehaviours prof (linkHostE impl) h₀ (l.toRef.map ofCore)
      (calls.map fun q => (l.imp.exports[q.1].name, q.2.map toRefVal)) l.imp.exports[j].name
      (vs.map toRefVal),
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      Linked2.seqMoves l calls wss ∈ l.toComp.den (impSem P) ∧
      Linked2.SeqIRObs P l calls wss j vs p.2

/-- **The reference-machine half against the engine's own specification**: for a simple
component in the fragment, every behaviour of calling export `x` of `c.toRef` over `E` is an
outcome of `exportSpecE E emb`. -/
def RefToSpecE (emb : NumModule → E.Module) : Prop :=
  ∀ (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple), c.Good → c.FloatFree → c.Inst →
    c.Arity → ∀ x ∈ c.exports, ∀ vs, ValTy.checkList x.ty.params vs = true →
      exportBehaviours prof (refHostE E) () (c.toRef.map ofCore) [] x.name (vs.map toRefVal) ⊆
        exportSpecE E emb c x vs

end Silmaril.Wasm.Component.Param
