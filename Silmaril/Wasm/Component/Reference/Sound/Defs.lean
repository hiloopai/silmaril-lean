module

public import Silmaril.Wasm.Component.Reference.Bridge.Defs
public import Silmaril.Wasm.Component.Reference.Core3Sem.Defs
public import Silmaril.Wasm.Game.Instantiate.Defs

/-!
# Soundness of the component IR against the reference machine: definitions

For simple components (`Simple`, `Silmaril.Wasm.Component.Reference.Bridge`), this module defines
the objects the soundness theorem relates, at an arbitrary silmaril profile `P`:

* `modSem P : CoreSem NumModule`: the IR's core semantics. A module denotes the strategy of its
  instance (`Silmaril.Wasm.Game.IsInstance`, instantiation against no imports) through
  `core3Sem P`; a module without such an instance traps on every question.
* `coreOut P m k xs`: the Core 3.0 outcomes of calling core export `k` of the instance of
  `m` on flat arguments `xs` with no host (`some ys`: returned values; `none`: trap or uncaught
  exception), and `coreDiverges`;
* `exportSpec P c j vs`: the outcomes the canonical ABI prescribes for calling export `j` on
  the IR values `vs`: lower the arguments (`checkLower`), run the core export, lift the results
  (`liftArgs`), with failures being traps;
* `refHost`: the reference host without host functions;
* `IRObs σ j vs b`: what the IR strategy `σ` must exhibit for the reference outcome `b` of
  calling export `j` on `vs`: the two-move play `ask (j, vals vs)`, `answer` (results or trap).
  Divergence, deadlock and cancellation are not observable in the IR's strategies (finite plays)
  and impose nothing.

Soundness is split in two halves:

* `RefToSpecAll` (proved: `refToSpec` in `Sound.Thms`; the name is kept for its users): every
  reference behaviour of an export call of `c.toRef`, over
  `core3P P`, is an outcome of `exportSpec` (the reference machine side: instantiation of
  `c.toRef`, `canon lift`, the core activation and the flat lift and lower of
  `definitions.py`);
* `Simple.SpecToIR` (proved, `Silmaril.Wasm.Component.Reference.Sound.Thms`): every terminating
  outcome of `exportSpec` is a play of `c.toComp.den (modSem P)` (the IR side).

Beyond the float-free single call (theorems in `Sound.Thms`):

* floats: `floatOk`/`floatOkList` and `SimpleFloatOk` (floats anywhere except in variant
  payloads), `NanAt`/`NanAtList prof` (admissible NaN lowerings under the component choice
  profile), `canonAt`/`canonAtList` (NaN canonicalisation of lifted results), and `IRObsF`, what
  the IR exhibits for a reference outcome on some admissible lowering of the arguments;
* call sequences on one instance: `seqBehaviours` (instantiate, resolved top-level calls
  `SeqCalls`, then a last call), the specification at a Core store (`coreAt`, `specAt`), returned
  calls threading the store (`RetAt`, `SeqSpec`), the IR plays of sequences (`seqMoves`,
  `SeqIRObs`) and the IR half `SeqSpecToIR`;
* components with canon-lowered imports (`SimpleI`): `impSem P`, `SimpleI.SpecToIR`, the hosts
  answering imports (`answerImpl`, `answerHost`, `HostAnswers`; stateful: `answerImplS`,
  `answerHostS`, `HostAnswersS`, `HostRun`, `SimpleI.HostOkS`, `IRObsIS`, `SeqIRObsIS`),
  `exportBehavioursI` and `IRObsI` for single calls, and for sequences of calls on one instance `seqBehavioursI`,
  `SimpleI.TypedCalls`, the IR plays `seqMovesI` (each call with its component import calls) and
  `SeqIRObsI`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Game
open Silmaril.Wasm.Numerics (Profile)

/-! ## The core semantics of `NumModule`s -/

/-- `I` is the instance of the import-free module `m`, with `m`'s export types. -/
def NumModule.IsInst (m : NumModule) (I : ScalarInstance) : Prop :=
  (∃ mt, IsInstance m.mod mt I) ∧ I.imports = [] ∧ I.exports = m.exports.map fun p => fnOf p.2

/-- The strategy trapping on every question. -/
def trapAll (n k : Nat) : Strategy (sigN n) (sigN k) :=
  Strategy.ofHandler fun _ => .pure none

open Classical in
/-- **The IR's Core 3.0 semantics of import-free modules, at profile `P`.** -/
noncomputable def modSem (P : Profile) : CoreSem NumModule where
  sem m :=
    if h : ∃ I, m.IsInst I then
      (core3Sem P).sem
        { inst := h.choose, imports := [], exports := m.exports
          imports_eq := h.choose_spec.2.1, exports_eq := h.choose_spec.2.2 }
    else trapAll _ _

/-! ## The canonical-ABI specification of an export call -/

/-- The Core 3.0 outcomes of calling the `k`-th function export of the instance of `m` on
the flat values `xs`, with no host: `some ys` for returned values, `none` for a trap or an
uncaught exception. -/
def coreOut (P : Profile) (m : NumModule) (k : Nat) (xs : List Flat) : Set (Option (List Flat)) :=
  {r | ∃ I, m.IsInst I ∧
    ∃ (c' : Silmaril.Wasm.Execution.Core.Config Nat) (res : Silmaril.Wasm.Execution.Core.Result),
      Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
        (Silmaril.Wasm.Execution.Core.invoke I.store (I.addrs.getD k 0)
          (xs.map Silmaril.Wasm.SingleThreaded.ofFlat)) c' ∧
      c'.code = res.toAdmin ∧
      r = match res with
        | .values vs => vs.mapM Silmaril.Wasm.SingleThreaded.toFlat?
        | _ => none}

/-- The call may diverge. -/
def coreDiverges (P : Profile) (m : NumModule) (k : Nat) (xs : List Flat) : Prop :=
  ∃ I, m.IsInst I ∧
    Silmaril.Wasm.Execution.Core.Diverges P Silmaril.Wasm.SingleThreaded.Det.noHost
      (Silmaril.Wasm.Execution.Core.invoke I.store (I.addrs.getD k 0)
        (xs.map Silmaril.Wasm.SingleThreaded.ofFlat))

/-- The reference outcome of a lifted core result. -/
def liftOutcome (ft : FuncTy) : Option (List Flat) → Outcome
  | some ys =>
    match liftArgs ft.results ys with
    | some ws => .returns (some (ws.map toRefVal))
    | none => .traps
  | none => .traps

/-- **The canonical-ABI specification** of calling export `x` of `c` on the IR values `vs`. -/
def exportSpec (P : Profile) (c : Simple) (x : SimpleExport) (vs : List Silmaril.Wasm.Component.Val) :
    Set Outcome :=
  match checkLower x.ty.params vs with
  | none => {.traps}
  | some xs =>
    {b | ∃ r ∈ coreOut P c.mod x.core xs, b = liftOutcome x.ty r} ∪
      {b | b = .diverges ∧ coreDiverges P c.mod x.core xs}

/-! ## Observations of the IR -/

/-- The IR answer of a reference outcome (`none`: not observable in a finite play). -/
def Outcome.irAnswer? (ws : List Silmaril.Wasm.Component.Val) : Outcome → Option (Option Payload)
  | .returns (some _) => some (some (.vals ws))
  | .traps => some none
  | _ => none

/-- **What the IR must exhibit for a reference outcome** `b` of calling export `j` on `vs`:
for a returned call, the results are the reference images of IR values `ws` and the IR plays
`ask (j, vals vs) · ans (vals ws)`; for a trap, `ask (j, vals vs) · ans none`. -/
def IRObs {k : Nat} (σ : Strategy (sigN 0) (sigN k)) (j : Fin k)
    (vs : List Silmaril.Wasm.Component.Val) : Outcome → Prop
  | .returns (some rs) => ∃ ws, rs = ws.map toRefVal ∧
      [.inr (.ask (j, .vals vs)), .inr (.ans (j, .vals vs) (some (.vals ws)))] ∈ σ
  | .traps => [.inr (.ask (j, .vals vs)), .inr (.ans (j, .vals vs) none)] ∈ σ
  | _ => True

/-- The reference host without host functions. -/
noncomputable def refHost (P : Profile) : Host (core3P P) Unit :=
  { hr := fun _ _ => false, impl := Silmaril.Wasm.Component.Canon.HostImpl.none }

/-! ## The fragment conditions -/

/-- Export names are distinct, and every lifted core export exists and has the flat type of
the lifted function type. -/
structure Simple.Good (c : Simple) : Prop where
  names : (c.exports.map (·.name)).Nodup
  core : ∀ x ∈ c.exports, ∃ n, c.mod.exports[x.core]? = some (n, x.ty.flat)

mutual
/-- The type mentions no float. The reference canonicalises NaNs when lifting floats and may
scramble them when lowering under non-deterministic profiles, while the IR's ABI is
bit-preserving, so floats are excluded from the reference half. -/
def floatFree : ValTy → Bool
  | .f32 | .f64 => false
  | .record ts => floatFreeList ts
  | .variant cs => floatFreeCases cs
  | _ => true

/-- `floatFree` on lists. -/
def floatFreeList : List ValTy → Bool
  | [] => true
  | t :: ts => floatFree t && floatFreeList ts

/-- `floatFree` on variant cases. -/
def floatFreeCases : List (Option ValTy) → Bool
  | [] => true
  | none :: cs => floatFreeCases cs
  | some t :: cs => floatFree t && floatFreeCases cs
end

/-- No export type of `c` mentions a float. -/
def Simple.FloatFree (c : Simple) : Prop :=
  ∀ x ∈ c.exports, floatFreeList x.ty.params = true ∧ floatFreeList x.ty.results = true

/-- The names of the function exports of a Core 3.0 module, in export order. -/
def funcExportNames (m : Silmaril.Wasm.Module) : List String :=
  m.exports.filterMap fun x => match x.index with
    | .func _ => some x.name
    | _ => none

/-- **The module of `c` is instantiated as the IR assumes.** It has an instance
(`NumModule.IsInst`: it validates, instantiates against no imports and has no start function),
and the names of `c.mod.exports` are the module's function export names in order (the reference
component aliases a core export by its name, the IR calls it by its position).

Both conditions are needed for `RefToSpecAll`. Without an instance `exportSpec` is empty for
well-typed arguments, while the reference machine traps (or diverges) when the core instantiation
fails or a start function traps (or loops): `Litmus.refToSpec_needs_inst` is a counterexample
with an out-of-bounds active data segment. Without the names, the reference calls a different
core function than the IR whenever the two orders differ. -/
structure Simple.Inst (c : Simple) : Prop where
  inst : ∃ I, c.mod.IsInst I
  names : funcExportNames c.mod.mod = c.mod.exports.map (·.1)

/-- **The flat arities stay on the direct path of the canonical ABI**: every export has at
most `MAX_FLAT_PARAMS = 16` flat parameters, at most `MAX_FLAT_RESULTS = 1` flat result and at
most one result type (`Simple.toRef` emits the first result type only). Larger arities go
through linear memory (`realloc`, return pointers), which `Simple` components do not have.

The reference validator imposes these conditions through the core type of the lifted function
(the flattening of the lifted type, with pointer parameters or results past the limits, must be
the core export's type, which is `x.ty.flat` by `Simple.Good`): `Simple.ValidArity` states it,
and it is proved (`validArity`, `Silmaril.Wasm.Component.Reference.Sound.Thms`). -/
def Simple.Arity (c : Simple) : Prop :=
  ∀ x ∈ c.exports, (ValTy.flatList x.ty.params).length ≤ 16 ∧
    (ValTy.flatList x.ty.results).length ≤ 1 ∧ x.ty.results.length ≤ 1

/-- **The validator imposes the flat arities**: a `Simple` component in the fragment whose
translation the reference validator accepts satisfies `Simple.Arity` (proved: `validArity`). -/
def Simple.ValidArity : Prop :=
  ∀ c : Simple, c.Good → c.FloatFree → c.Inst →
    (∃ ct, check? Silmaril.Wasm.Component.Features.p2 c.toRef = .ok ct) → c.Arity

/-! ## The two halves of the soundness proof -/

/-- **Reference machine side** (proved: `refToSpec`, `Sound.Thms`): for a float-free simple component whose module is
instantiated as the IR assumes (`Simple.Inst`) and which is accepted by the reference
validator, every behaviour of calling export `x` on the reference images of well-typed IR
values `vs`, after instantiating `c.toRef` from the empty store, over `core3P P` at any
component choice profile, is an outcome of the canonical-ABI specification. -/
def RefToSpecAll : Prop :=
  ∀ (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple), c.Good →
    c.FloatFree → c.Inst → (∃ ct, check? Silmaril.Wasm.Component.Features.p2 c.toRef = .ok ct) →
    ∀ x ∈ c.exports, ∀ vs, ValTy.checkList x.ty.params vs = true →
      exportBehaviours prof (refHost P) () c.toRef [] x.name (vs.map toRefVal) ⊆
        exportSpec P c x vs

/-- **IR side**: every terminating outcome of the specification of export `j` is a
play of the IR denotation of `c.toComp` over `modSem P`. -/
def Simple.SpecToIR : Prop :=
  ∀ (P : Profile) (c : Simple), c.Good → ∀ (j : Fin c.exports.length) vs b,
    b ∈ exportSpec P c c.exports[j] vs →
      IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem P))
        ⟨j, by simp [Simple.toComp]⟩ vs b


/-! ## Floats -/

section Float

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.ABI
open Silmaril.Wasm.Component.Value (NanLower)
open Silmaril.Wasm (FloatType)

local notation "IVal" => Silmaril.Wasm.Component.Val

mutual
/-- Floats may occur anywhere except in variant payloads. -/
def floatOk : ValTy → Bool
  | .record ts => floatOkList ts
  | .variant cs => floatFreeCases cs
  | _ => true

/-- `floatOk` on lists. -/
def floatOkList : List ValTy → Bool
  | [] => true
  | t :: ts => floatOk t && floatOkList ts
end

mutual
/-- The canonicalisation of the floats of a value of type `t` (REF `canonicalize_nan32/64`;
variant payloads are float-free in the fragment and kept). -/
def canonAt : ValTy → IVal → IVal
  | .f32, .f32 x => .f32 (canonicalizeNaN .f32 x)
  | .f64, .f64 x => .f64 (canonicalizeNaN .f64 x)
  | .record ts, .record vs => .record (canonAtList ts vs)
  | _, v => v

/-- `canonAt` on lists. -/
def canonAtList : List ValTy → List IVal → List IVal
  | t :: ts, v :: vs => canonAt t v :: canonAtList ts vs
  | _, vs => vs
end

mutual
/-- `v'` is an admissible lowering of `v` at type `t` under the profile `prof`: the floats are
related by `NanLower prof`, everything else is equal (variant payloads are float-free in the
fragment). -/
def NanAt (prof : ProfileKind) : ValTy → IVal → IVal → Prop
  | .f32, .f32 x, .f32 y => NanLower prof .f32 x y
  | .f64, .f64 x, .f64 y => NanLower prof .f64 x y
  | .record ts, .record vs, .record ws => NanAtList prof ts vs ws
  | _, v, w => v = w

/-- `NanAt` on lists. -/
def NanAtList (prof : ProfileKind) : List ValTy → List IVal → List IVal → Prop
  | t :: ts, v :: vs, w :: ws => NanAt prof t v w ∧ NanAtList prof ts vs ws
  | _, vs, ws => vs = ws
end

/-- Floats may occur in the export types, except in variant payloads. -/
def SimpleFloatOk (c : Simple) : Prop :=
  ∀ x ∈ c.exports, floatOkList x.ty.params = true ∧ floatOkList x.ty.results = true

/-- What the IR exhibits for a reference outcome `b` with floats: the play of the call on the
arguments `vs'`, with returned values reported canonicalised. -/
def IRObsF {k : Nat} (σ : Strategy (sigN 0) (sigN k)) (j : Fin k) (rts : List ValTy)
    (vs' : List IVal) : Silmaril.Wasm.Component.Reference.Outcome → Prop
  | .returns (some rs) => ∃ ws, rs = (canonAtList rts ws).map toRefVal ∧
      [.inr (.ask (j, .vals vs')), .inr (.ans (j, .vals vs') (some (.vals ws)))] ∈ σ
  | .traps => [.inr (.ask (j, .vals vs')), .inr (.ans (j, .vals vs') none)] ∈ σ
  | _ => True

end Float

/-! ## Sequences of calls on one instance -/

section SeqSpec

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

/-- The Core outcomes of calling core export `k` of `I` on `xs` at the store `s`. -/
def coreAt (P : Profile) (I : Silmaril.Wasm.Game.ScalarInstance) (k : Nat) (xs : List Flat)
    (s : Store Nat) : Set (Option (List Flat)) :=
  {r | ∃ (c' : Config Nat) (res : Result),
    Steps P Det.noHost (invoke s (I.addrs.getD k 0) (xs.map ofFlat)) c' ∧
    c'.code = res.toAdmin ∧
    r = match res with
      | .values vs => vs.mapM toFlat?
      | _ => none}

/-- **The specification of calling export `x` on `vs` at the store `s`.** -/
def specAt (P : Profile) (_c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) (s : Store Nat) : Set Outcome :=
  match checkLower x.ty.params vs with
  | none => {.traps}
  | some xs =>
    {b | ∃ r ∈ coreAt P I x.core xs s, b = liftOutcome x.ty r} ∪
      {b | b = .diverges ∧
        Diverges P Det.noHost (invoke s (I.addrs.getD x.core 0) (xs.map ofFlat))}

/-- **A returned call** of export `x` on `vs` from the store `s`: the lowered arguments run
host-free to values whose IR lift is `ws`, leaving the store `s'`. -/
structure RetAt (P : Profile) (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance)
    (x : SimpleExport) (vs : List Silmaril.Wasm.Component.Val) (s : Store Nat)
    (ws : List Silmaril.Wasm.Component.Val) (s' : Store Nat) : Prop where
  typed : ValTy.checkList x.ty.params vs = true
  run : ∃ (t' : Thread) (cvs : List Execution.Core.Val) (ys : List Flat),
    Silmaril.Wasm.Game.Reach P
      (s, Thread.invokeFlat (I.addrs.getD x.core 0) (lowerArgs x.ty.params vs)) (s', t') ∧
    Silmaril.Wasm.Game.ResultAt s' t' (.values cvs) ∧ cvs.mapM toFlat? = some ys ∧
    liftArgs x.ty.results ys = some ws

/-- **Sequences of returned calls** from the store `s` to the store `s'`, with the IR results
of each call. -/
inductive SeqSpec (P : Profile) (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance) :
    Store Nat → List (SimpleExport × List Silmaril.Wasm.Component.Val) →
    List (List Silmaril.Wasm.Component.Val) → Store Nat → Prop where
  | nil (s : Store Nat) : SeqSpec P c I s [] [] s
  | cons {s s₁ s₂ : Store Nat} {x : SimpleExport} {vs : List Silmaril.Wasm.Component.Val}
      {ws : List Silmaril.Wasm.Component.Val} {cs : List (SimpleExport × List Silmaril.Wasm.Component.Val)}
      {wss : List (List Silmaril.Wasm.Component.Val)} :
      RetAt P c I x vs s ws s₁ → SeqSpec P c I s₁ cs wss s₂ →
      SeqSpec P c I s ((x, vs) :: cs) (ws :: wss) s₂

end SeqSpec

section SeqCalls

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}

/-- Resolved top-level calls `k, k + 1, …` of the function values `f` on `args`, from `m` to
`m'`, with their results. -/
inductive SeqCalls (prof : ProfileKind) (h : Host E σ) :
    Machine.Config E σ → Nat → List (FuncId × List Val) → List (List Val) →
    Machine.Config E σ → Prop where
  | nil (m : Machine.Config E σ) (k : Nat) : SeqCalls prof h m k [] [] m
  | cons {m m₁ m₂ : Machine.Config E σ} {k : Nat} {f : FuncId} {args rs : List Val}
      {cs : List (FuncId × List Val)} {rss : List (List Val)} :
      Calls prof h.hr h.dispatch m ⟨k⟩ f args m₁ (.resolved (some rs)) →
      SeqCalls prof h m₁ (k + 1) cs rss m₂ → SeqCalls prof h m k ((f, args) :: cs) (rs :: rss) m₂

/-- **The behaviours of a sequence of calls**: instantiate `c` from the empty store, call the
exports named in `calls` in order (top-level calls `0, 1, …`), each resolving, then call the
export `name` on `vals`. A behaviour is the list of results of the resolved calls and the
outcome of the last call; a trap or divergence of the instantiation is a behaviour with no
results. -/
def seqBehaviours (prof : ProfileKind) (h : Host E σ) (σ0 : σ) (c : CompAst E.Module)
    (calls : List (String × List Val)) (name : String) (vals : List Val) :
    Set (List (List Val) × Silmaril.Wasm.Component.Reference.Outcome) :=
  {p | (∃ m₀ inst es fs mₙ f,
      InstResult.instance m₀ inst es ∈ instBehaviours prof h (initConfig σ0) c [] ∧
      calls.mapM (fun q => es.lookup q.1) = some fs ∧
      SeqCalls prof h m₀ 0 (fs.zip (calls.map Prod.snd)) p.1 mₙ ∧
      es.lookup name = some f ∧ p.2 ∈ callBehaviours prof h mₙ ⟨calls.length⟩ f vals) ∨
    (p = ([], .traps) ∧ InstResult.traps ∈ instBehaviours prof h (initConfig σ0) c []) ∨
    (p = ([], .diverges) ∧ InstResult.diverges ∈ instBehaviours prof h (initConfig σ0) c [])}

/-- Calls of exports (by index) on IR values, as reference function values and arguments. -/
def callArgs (c : Simple) (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)) :
    List (FuncId × List Val) :=
  calls.map fun q => (⟨q.1⟩, q.2.map toRefVal)

/-- Calls of exports (by index) on IR values, as exports and IR values. -/
def specCalls (c : Simple) (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)) :
    List (SimpleExport × List Silmaril.Wasm.Component.Val) :=
  calls.map fun q => (c.exports[q.1], q.2)

/-- The calls are well typed. -/
def TypedCalls (c : Simple) (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)) :
    Prop :=
  ∀ q ∈ calls, ValTy.checkList c.exports[q.1].ty.params q.2 = true

/-- The IR play of resolved calls `calls` with IR results `wss`. -/
def seqMoves (c : Simple) :
    List (Fin c.exports.length × List Silmaril.Wasm.Component.Val) →
    List (List Silmaril.Wasm.Component.Val) →
    List (Silmaril.Games.Move (Silmaril.Wasm.Component.sigN 0)
      (Silmaril.Wasm.Component.sigN c.toComp.exports.length))
  | (j, vs) :: cs, ws :: wss =>
    .inr (.ask (⟨j, by simp [Simple.toComp]⟩, .vals vs)) ::
      .inr (.ans (m := (⟨j, by simp [Simple.toComp]⟩, .vals vs)) (some (.vals ws))) ::
      seqMoves c cs wss
  | _, _ => []

/-- **The IR side for sequences** (proved: `seqSpecToIR`, `Sound.Thms`): every sequence of
returned calls of the specification, followed by a terminating outcome of the last call, is a
play of the IR denotation, the IR's strategies keeping the instance's state between questions. -/
def SeqSpecToIR : Prop :=
  ∀ (P : Profile) (c : Simple), c.Good → ∀ (I : Silmaril.Wasm.Game.ScalarInstance), c.mod.IsInst I →
    ∀ (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
      (wss : List (List Silmaril.Wasm.Component.Val)) (s : Silmaril.Wasm.Execution.Core.Store Nat)
      (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
      (b : Silmaril.Wasm.Component.Reference.Outcome),
      SeqSpec P c I I.store (specCalls c calls) wss s → b ∈ specAt P c I c.exports[j] vs s →
      match b with
      | .returns (some rs) => ∃ ws, rs = ws.map toRefVal ∧
          seqMoves c (calls ++ [(j, vs)]) (wss ++ [ws]) ∈ c.toComp.den (modSem P)
      | .traps => seqMoves c calls wss ++
          [.inr (.ask (⟨j, by simp [Simple.toComp]⟩, .vals vs)),
            .inr (.ans (m := (⟨j, by simp [Simple.toComp]⟩, .vals vs)) none)] ∈
          c.toComp.den (modSem P)
      | _ => True

/-- **What the IR must exhibit for the last call of a sequence** with outcome `b`, after the
resolved calls `calls` with IR results `wss`: for returned results, the IR play of all calls; for
a trap, the IR play of the earlier calls followed by `ask (j, vals vs) · ans none`. Divergence,
deadlock and cancellation impose nothing. -/
def SeqIRObs (c : Simple)
    (σ : Silmaril.Games.Strategy (Silmaril.Wasm.Component.sigN 0)
      (Silmaril.Wasm.Component.sigN c.toComp.exports.length))
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (wss : List (List Silmaril.Wasm.Component.Val)) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) : Outcome → Prop
  | .returns (some rs) => ∃ ws, rs = ws.map toRefVal ∧
      seqMoves c (calls ++ [(j, vs)]) (wss ++ [ws]) ∈ σ
  | .traps => seqMoves c calls wss ++
      [.inr (.ask (⟨j, by simp [Simple.toComp]⟩, .vals vs)),
        .inr (.ans (m := (⟨j, by simp [Simple.toComp]⟩, .vals vs)) none)] ∈ σ
  | _ => True

/-- **Admissible lowerings of a list of calls** under the component choice profile `prof`: the
same exports, the arguments of each related by `NanAtList prof`. -/
def NanCalls (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple) :
    List (Fin c.exports.length × List Silmaril.Wasm.Component.Val) →
    List (Fin c.exports.length × List Silmaril.Wasm.Component.Val) → Prop :=
  List.Forall₂ fun q q' => q'.1 = q.1 ∧ NanAtList prof c.exports[q.1].ty.params q.2 q'.2

/-- The calls with their arguments canonicalised: the only admissible lowering under the
deterministic component profile. -/
def canonCalls (c : Simple) (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)) :
    List (Fin c.exports.length × List Silmaril.Wasm.Component.Val) :=
  calls.map fun q => (q.1, canonAtList c.exports[q.1].ty.params q.2)

/-- The reference results of resolved calls `calls` with IR results `wss`, as the reference
lift reports them: canonicalised (`canonAtList`) at each call's result types. -/
def canonResults (c : Simple) :
    List (Fin c.exports.length × List Silmaril.Wasm.Component.Val) →
    List (List Silmaril.Wasm.Component.Val) → List (List Val)
  | q :: cs, ws :: wss =>
    (canonAtList c.exports[q.1].ty.results ws).map toRefVal :: canonResults c cs wss
  | _, _ => []

/-- **`SeqIRObs` with floats**: returned results of the last call are reported canonicalised. -/
def SeqIRObsF (c : Simple)
    (σ : Silmaril.Games.Strategy (Silmaril.Wasm.Component.sigN 0)
      (Silmaril.Wasm.Component.sigN c.toComp.exports.length))
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (wss : List (List Silmaril.Wasm.Component.Val)) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) : Outcome → Prop
  | .returns (some rs) => ∃ ws, rs = (canonAtList c.exports[j].ty.results ws).map toRefVal ∧
      seqMoves c (calls ++ [(j, vs)]) (wss ++ [ws]) ∈ σ
  | .traps => seqMoves c calls wss ++
      [.inr (.ask (⟨j, by simp [Simple.toComp]⟩, .vals vs)),
        .inr (.ans (m := (⟨j, by simp [Simple.toComp]⟩, .vals vs)) none)] ∈ σ
  | _ => True

end SeqCalls

/-! ## Modules with imports -/

/-- `I` is the instance of `m` against fresh host functions for its imports, with `m`'s import
and export types. -/
def ImpModule.IsInst (m : ImpModule) (I : ScalarInstance) : Prop :=
  (∃ mt, IsInstance m.mod mt I) ∧ I.imports = m.imports.map (fun p => fnOf p.2) ∧
    I.exports = m.exports.map fun p => fnOf p.2

open Classical in
/-- **The IR's Core 3.0 semantics of modules with imports, at profile `P`**: the strategy of the
module's instance (`Silmaril.Wasm.Game.IsInstance`), whose import calls are questions to the
environment and whose environment answers resume it, through `core3Sem P`. A module without
an instance traps on every question. On import-free modules it is `modSem P`
(`impSem_toImp`, `Sound.Thms`). -/
noncomputable def impSem (P : Profile) : CoreSem ImpModule where
  sem m :=
    if h : ∃ I, m.IsInst I then
      (core3Sem P).sem
        { inst := h.choose, imports := m.imports, exports := m.exports
          imports_eq := h.choose_spec.2.1, exports_eq := h.choose_spec.2.2 }
    else trapAll _ _

/-- The fragment conditions with imports: export names are distinct, every lifted core export
exists with the flat type of its lifted function type, and the core imports have the flat types
of the component imports they are lowered from. -/
structure SimpleI.Good (c : SimpleI) : Prop where
  names : (c.exports.map (·.name)).Nodup
  core : ∀ x ∈ c.exports, ∃ n, c.mod.exports[x.core]? = some (n, x.ty.flat)
  imports : c.mod.imports = c.imports.map fun p => (p.1, p.2.flat)

/-- **The module of `c` is wired as `SimpleI.toRef` assumes.** It has an instance
(`ImpModule.IsInst`), the names of `c.mod.exports` are the module's function export names in
order (as for `Simple.Inst`), the component import names are distinct (the root arguments
`importArgs` bind them by name), the module's imports are the imports `"env" "name"` of the
component imports in order (the core instance exporting the lowered functions is passed as
`"env"`, and exports them under these names), and the validated import types are exactly the
flat function types that `canon lower` allocates (`Silmaril.Wasm.SingleThreaded.ofFlatType` of
the flattened import type).

The last condition is not implied by `SimpleI.Good` and `ImpModule.IsInst`, which see the
import types only through `FnType.ofDefType?`: a module may declare its import type in a
recursion group or as a non-final subtype, and then the core instantiation of the reference
machine rejects the lowered functions (`externAddrsOk?` compares defined types). -/
structure SimpleI.Inst (c : SimpleI) : Prop where
  inst : ∃ I, c.mod.IsInst I
  names : funcExportNames c.mod.mod = c.mod.exports.map (·.1)
  importNames : (c.imports.map (·.1)).Nodup
  env : c.mod.mod.imports.map (fun i => (i.moduleName, i.name)) =
    c.imports.map fun p => ("env", p.1)
  importTypes : ∃ mt, Silmaril.Wasm.Validation.validate? c.mod.mod = some mt ∧
    mt.imports = c.imports.map fun p =>
      .func (Silmaril.Wasm.SingleThreaded.ofFlatType ⟨p.2.flat.params, p.2.flat.results⟩)

/-- The moves of the answered lower calls `l`, in order. -/
def callMoves {E F : Silmaril.Games.Sig.{0}} : List (Σ m : E.Op, E.Ar m) → List (Move E F)
  | [] => []
  | ⟨m, n⟩ :: l => .inl (.ask m) :: .inl (.ans m n) :: callMoves l

/-- **An import call of the core instance, through `canon lower`.** The core import call `x.1`
(core import `k` on the core values `args`) answered `x.2` corresponds to the component import
calls `ds`: when the flat arguments lift to component values `ws` (the lower adapter's argument
lift), component import `k` is called on `ws`, answered `R`, and the core answer is `R` lowered
back (`Adapter.up (.lower ft)`, then `payloadAnswer`); otherwise the adapter traps without a
call and the core answer is a trap. -/
def ImpRel (c : SimpleI) (I : ScalarInstance) (x : Σ e : I.E.Op, I.E.Ar e)
    (ds : List (Σ _ : (sigN c.imports.length).Op, Option Payload)) : Prop :=
  ∃ (nm : String) (ft : FuncTy) (A : Option Payload), c.imports[x.1.1.val]? = some (nm, ft) ∧
    payloadAnswer (I.imports.get x.1.1) A = x.2 ∧
    match liftArgs ft.params (x.1.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) with
    | none => A = none ∧ ds = []
    | some ws => ∃ (hk : x.1.1.val < c.imports.length) (R : Option Payload),
        ds = [⟨(⟨x.1.1.val, hk⟩, .vals ws), R⟩] ∧ A = R.bind (Adapter.lower ft).up

/-- **The IR side with imports**: an export call of `c` on `vs` whose argument check fails is a
trap of the IR; otherwise, for every play of the core instance answering the lifted core export
on the lowered arguments `xs` after the import calls `cs`, and every choice of component import
calls `dss` related to them by `ImpRel`, the IR denotation plays the export question, the
component import calls `dss` (as lower moves) and the lifted answer. -/
def SimpleI.SpecToIR : Prop :=
  ∀ (P : Profile) (c : SimpleI), c.Good → ∀ (I : ScalarInstance), c.mod.IsInst I →
    ∀ (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val),
      (checkLower c.exports[j].ty.params vs = none →
        [.inr (.ask (⟨j, by simp [SimpleI.toComp]⟩, .vals vs)),
          .inr (.ans (m := (⟨j, by simp [SimpleI.toComp]⟩, .vals vs)) none)] ∈
          c.toComp.den (impSem P)) ∧
      ∀ (xs : List Flat), checkLower c.exports[j].ty.params vs = some xs →
      ∀ (f : I.F.Op), f.1.val = c.exports[j].core →
        f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat →
      ∀ (cs : List (Σ e : I.E.Op, I.E.Ar e)) (w : I.F.Ar f) (q : I.HState),
        I.Path P (.idle I.store) (.inr (.ask f) :: callMoves cs ++ [.inr (.ans f w)]) q →
      ∀ (dss : List (List (Σ _ : (sigN c.imports.length).Op, Option Payload))),
        List.Forall₂ (ImpRel c I) cs dss →
        (.inr (.ask (⟨j, by simp [SimpleI.toComp]⟩, .vals vs)) :: callMoves dss.flatten ++
          [.inr (.ans (m := (⟨j, by simp [SimpleI.toComp]⟩, .vals vs))
            ((answerPayload w).bind (Adapter.up (.lift c.exports[j].ty))))] :
          List (Move (sigN c.imports.length) (sigN c.toComp.exports.length))) ∈
          c.toComp.den (impSem P)

/-- The component types of the exports and imports of `c` have no floats. -/
def SimpleI.FloatFree (c : SimpleI) : Prop :=
  (∀ x ∈ c.exports, floatFreeList x.ty.params = true ∧ floatFreeList x.ty.results = true) ∧
    ∀ p ∈ c.imports, floatFreeList p.2.params = true ∧ floatFreeList p.2.results = true

/-- **The flat arities of the direct path of the canonical ABI**, for the exports (`canon lift`)
and the imports (`canon lower`, synchronous): at most 16 flat parameters, at most one flat
result and at most one result type. -/
def SimpleI.Arity (c : SimpleI) : Prop :=
  (∀ x ∈ c.exports, (ValTy.flatList x.ty.params).length ≤ 16 ∧
    (ValTy.flatList x.ty.results).length ≤ 1 ∧ x.ty.results.length ≤ 1) ∧
  ∀ p ∈ c.imports, (ValTy.flatList p.2.params).length ≤ 16 ∧
    (ValTy.flatList p.2.results).length ≤ 1 ∧ p.2.results.length ≤ 1

/-! ## Hosts answering component imports -/

section HostImports

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon

variable {E : Engine} {σ : Type}

/-- The component store with the host functions `k, k + 1, …` of the resolved types of the
imports `ims` allocated after those of `s` (function values `.host (witFt ft) ⟨k⟩`). -/
def hostFuncs : Nat → Iface → CStore E → CStore E
  | _, [], s => s
  | k, p :: ps, s => hostFuncs (k + 1) ps (ArenaField.funcs.alloc s (.host (witFt p.2) ⟨k⟩)).1

/-- The root instantiation arguments binding import `k` of `ims` to function value `k`. -/
def importArgs (ims : Iface) : Instantiate.Exports E :=
  ims.mapIdx fun k p => (p.1, .func ⟨k⟩)

/-- **A stateful host answering its functions by `g`**: host function `fn` called on the
component values `args` in host state `s` (the machine's host state, read after `on_start`)
resolves with `rs` and moves to state `s'` when `g s fn args = some (rs, s')`, and traps
otherwise (REF run_tests `mk_host_func` with a synchronous body: `on_start`, then
`on_resolve`). -/
def answerImplS (g : σ → HostFuncId → List Val → Option (List Val × σ)) : HostImpl E σ :=
  HostImpl.ofFns fun fn c => do
    let args ← callVals (.onStart c)
    let s ← hostGet
    match g s fn args with
    | some (rs, s') => do
      hostSet s'
      callUnit (.onResolve c (some rs))
      pure (.cancel .none)
    | none => trap (.hostTrap "answerImpl: no answer")

/-- The stateless answering function `g` as a stateful one that keeps the state. -/
def statelessG (g : HostFuncId → List Val → Option (List Val)) :
    σ → HostFuncId → List Val → Option (List Val × σ) :=
  fun s fn args => (g fn args).map fun rs => (rs, s)

/-- **A host answering its functions by `g`**: host function `fn` called on the component
values `args` resolves with `rs` when `g fn args = some rs`, and traps otherwise; the stateful
host `answerImplS` of `statelessG g` (the host state is read and written back unchanged). -/
def answerImpl (g : HostFuncId → List Val → Option (List Val)) : HostImpl E σ :=
  answerImplS (statelessG g)

/-- **A component import call answered by `g`**: the call `d` of import `k` on the IR values
`ws`, answered `R`, is answered by the host function `⟨k⟩` of `g` on `ws.map toRefVal`: `R` is
the IR image `.vals us` of `g`'s answer `us.map toRefVal`, or a trap (`none`) when `g` has no
answer. -/
def HostAnswers (g : HostFuncId → List Val → Option (List Val)) {n : Nat}
    (d : Σ _ : (sigN n).Op, Option Payload) : Prop :=
  ∃ (k : Fin n) (ws : List Silmaril.Wasm.Component.Val), d.1 = (k, .vals ws) ∧
    match d.2 with
    | none => g ⟨k.val⟩ (ws.map toRefVal) = none
    | some (.vals us) => g ⟨k.val⟩ (ws.map toRefVal) = some (us.map toRefVal)
    | some (.flat _) => False

/-- **A stateful component import call** answered by `g` from host state `s` to `s'`: the
call `d` of import `k` on the IR values `ws`, answered `R`: `R` is the IR image `.vals us` of the
answer `us.map toRefVal` that `g s` gives on `ws.map toRefVal`, moving to `s'`; or a trap
(`none`) when `g s` has no answer (and `s' = s`). -/
def HostAnswersS (g : σ → HostFuncId → List Val → Option (List Val × σ)) (s : σ) {n : Nat}
    (d : Σ _ : (sigN n).Op, Option Payload) (s' : σ) : Prop :=
  ∃ (k : Fin n) (ws : List Silmaril.Wasm.Component.Val), d.1 = (k, .vals ws) ∧
    match d.2 with
    | none => g s ⟨k.val⟩ (ws.map toRefVal) = none ∧ s' = s
    | some (.vals us) => g s ⟨k.val⟩ (ws.map toRefVal) = some (us.map toRefVal, s')
    | some (.flat _) => False

/-- **Component import calls answered by a stateful host**: the calls `ds`, in order, answered
by `g` from host state `s`, the state threaded from call to call, ending in `s'`. -/
inductive HostRun (g : σ → HostFuncId → List Val → Option (List Val × σ)) {n : Nat} :
    σ → List (Σ _ : (sigN n).Op, Option Payload) → σ → Prop
  | nil (s : σ) : HostRun g s [] s
  | cons {s s₁ s₂ : σ} {d : Σ _ : (sigN n).Op, Option Payload}
      {ds : List (Σ _ : (sigN n).Op, Option Payload)} :
      HostAnswersS g s d s₁ → HostRun g s₁ ds s₂ → HostRun g s (d :: ds) s₂

/-- The reference host answering the imports by the stateful `g`, with host state `σ`. -/
noncomputable def answerHostS (P : Profile) (g : σ → HostFuncId → List Val → Option (List Val × σ)) :
    Host (core3P P) σ :=
  { hr := fun _ _ => false, impl := answerImplS g }

/-- The reference host answering the imports by `g` (`answerHostS` of `statelessG g`). -/
noncomputable def answerHost (P : Profile) (g : HostFuncId → List Val → Option (List Val)) :
    Host (core3P P) Unit :=
  answerHostS P (statelessG g)

/-- **The stateful host answers in the IR's types**: in every state, whenever host function `k`
answers the reference image of IR values, its answer is the image of IR values of the result
types of import `k`. -/
def SimpleI.HostOkS (c : SimpleI) (g : σ → HostFuncId → List Val → Option (List Val × σ)) :
    Prop :=
  ∀ (s : σ) (k : Nat) (hk : k < c.imports.length) (ws : List Silmaril.Wasm.Component.Val)
    (rs : List Val) (s' : σ), g s ⟨k⟩ (ws.map toRefVal) = some (rs, s') →
      ∃ us, rs = us.map toRefVal ∧ ValTy.checkList c.imports[k].2.results us = true

/-- **The host answers in the IR's types**: whenever host function `k` answers the reference
image of IR values, its answer is the image of IR values of the result types of import `k`. -/
def SimpleI.HostOk (c : SimpleI) (g : HostFuncId → List Val → Option (List Val)) : Prop :=
  ∀ (k : Nat) (hk : k < c.imports.length) (ws : List Silmaril.Wasm.Component.Val) (rs : List Val),
    g ⟨k⟩ (ws.map toRefVal) = some rs →
      ∃ us, rs = us.map toRefVal ∧ ValTy.checkList c.imports[k].2.results us = true

/-- **What the IR must exhibit for a reference outcome `b` of an export call with imports**
answered by `g`: for returned results `ws.map toRefVal`, a play of `σ` asking export `j` on
`vs`, making component import calls `ds` that `g` answers (`HostAnswers`), and answering
`vals ws`; for a trap, such a play answering `none`. Divergence, deadlock and cancellation
impose nothing. -/
def IRObsI {n m : Nat} (σ : Silmaril.Games.Strategy (sigN n) (sigN m)) (j : Fin m)
    (vs : List Silmaril.Wasm.Component.Val) (g : HostFuncId → List Val → Option (List Val)) :
    Outcome → Prop
  | .returns (some rs) => ∃ (ws : List Silmaril.Wasm.Component.Val)
      (ds : List (Σ _ : (sigN n).Op, Option Payload)), rs = ws.map toRefVal ∧
      (∀ d ∈ ds, HostAnswers g d) ∧
      (.inr (.ask (j, .vals vs)) :: callMoves ds ++
        [.inr (.ans (m := (j, .vals vs)) (some (.vals ws)))]) ∈ σ
  | .traps => ∃ ds : List (Σ _ : (sigN n).Op, Option Payload), (∀ d ∈ ds, HostAnswers g d) ∧
      (.inr (.ask (j, .vals vs)) :: callMoves ds ++ [.inr (.ans (m := (j, .vals vs)) none)]) ∈ σ
  | _ => True

/-- **What the IR must exhibit for a reference outcome `b` of an export call with imports
answered by the stateful host `g` from host state `s₀`**: as `IRObsI`, with the component
import calls `ds` answered by `g` with the state threaded from `s₀` (`HostRun`). -/
def IRObsIS {n m : Nat} (σI : Silmaril.Games.Strategy (sigN n) (sigN m)) (j : Fin m)
    (vs : List Silmaril.Wasm.Component.Val) (g : σ → HostFuncId → List Val → Option (List Val × σ))
    (s₀ : σ) : Outcome → Prop
  | .returns (some rs) => ∃ (ws : List Silmaril.Wasm.Component.Val)
      (ds : List (Σ _ : (sigN n).Op, Option Payload)) (s : σ), rs = ws.map toRefVal ∧
      HostRun g s₀ ds s ∧
      (.inr (.ask (j, .vals vs)) :: callMoves ds ++
        [.inr (.ans (m := (j, .vals vs)) (some (.vals ws)))]) ∈ σI
  | .traps => ∃ (ds : List (Σ _ : (sigN n).Op, Option Payload)) (s : σ), HostRun g s₀ ds s ∧
      (.inr (.ask (j, .vals vs)) :: callMoves ds ++ [.inr (.ans (m := (j, .vals vs)) none)]) ∈ σI
  | _ => True

variable [∀ a b, Decidable (E.ExternSub a b)]

/-- **The behaviours of calling an export of a component with imports**: from the store holding
one host function per import (`hostFuncs 0 ims`), instantiate `c` with import `k` bound to host
function `k` (`importArgs ims`), then call the export `name` on `vals`. -/
def exportBehavioursI (prof : ProfileKind) (h : Host E σ) (σ0 : σ) (c : CompAst E.Module)
    (ims : Iface) (name : String) (vals : List Val) : Set Outcome :=
  let m₀ : Machine.Config E σ := Machine.Config.init (hostFuncs 0 ims CStore.empty) σ0
  {b | (∃ m₁ inst es f, InstResult.instance m₁ inst es ∈ instBehaviours prof h m₀ c
        (importArgs ims) ∧ es.lookup name = some f ∧ b ∈ callBehaviours prof h m₁ ⟨0⟩ f vals) ∨
    (b = .traps ∧ InstResult.traps ∈ instBehaviours prof h m₀ c (importArgs ims)) ∨
    (b = .diverges ∧ InstResult.diverges ∈ instBehaviours prof h m₀ c (importArgs ims))}

end HostImports

/-! ## The call phase with imports -/

section CallPhaseI

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime

/-- The import index of a `canon lower` trampoline: the index of the function it lowers. -/
def trampIdx {E : Engine} : CanonHost E → Nat
  | .lowered f _ _ _ => f.idx
  | _ => 0

/-- **The component functions after instantiating `c.toRef`**: host function `k` (of the
resolved type of import `k`) for import `k`, then the lifts of the exports at the core
addresses `addr x.core`, with default options, in instance `0`. -/
noncomputable def SimpleI.afterFuncs (P : Profile) (addr : Nat → Nat) (c : SimpleI) :
    List (CFuncInst (core3P P)) :=
  c.imports.mapIdx (fun k p => .host (witFt p.2) ⟨k⟩) ++
    c.exports.map fun x => .lifted (addr x.core) (witFt x.ty) {} ⟨0⟩

/-- The host functions of the core store `cs` are the `canon lower` trampolines of the imports
of `c` (trampoline of import `k` lowering component function `k` at its resolved type, in
instance `0`, with default options). -/
def SimpleI.TrampOk {P : Profile} (c : SimpleI) (cs : (core3P P).Store (CanonHost (core3P P))) :
    Prop :=
  ∀ (a : Nat) (fi : Silmaril.Wasm.Execution.Core.FuncInst (CanonHost (core3P P)))
    (h : CanonHost (core3P P)),
    (cs : Silmaril.Wasm.Execution.Core.Store (CanonHost (core3P P))).funcs[a]? = some fi →
    fi.code = .host h → ∃ (k : Nat) (hk : k < c.imports.length),
      h = .lowered ⟨k⟩ (witFt c.imports[k].2) {} ⟨0⟩

end CallPhaseI

/-! ## Sequences of calls with imports -/

section SeqCallsI

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine

/-- The calls are well typed. -/
def SimpleI.TypedCalls (c : SimpleI)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)) : Prop :=
  ∀ q ∈ calls, ValTy.checkList c.exports[q.1].ty.params q.2 = true

/-- **The IR play of resolved calls with imports**: each call `(j, vs)` asks export `j` on `vs`,
makes the component import calls `ds` (lower moves), and answers its IR results `ws`. -/
def seqMovesI (c : SimpleI) :
    List (Fin c.exports.length × List Silmaril.Wasm.Component.Val) →
    List (List (Σ _ : (sigN c.imports.length).Op, Option Payload)) →
    List (List Silmaril.Wasm.Component.Val) →
    List (Silmaril.Games.Move (sigN c.imports.length) (sigN c.toComp.exports.length))
  | (j, vs) :: cs, ds :: dss, ws :: wss =>
    .inr (.ask (⟨j, by simp [SimpleI.toComp]⟩, .vals vs)) :: (callMoves ds ++
      (.inr (.ans (m := (⟨j, by simp [SimpleI.toComp]⟩, .vals vs)) (some (.vals ws))) ::
        seqMovesI c cs dss wss))
  | _, _, _ => []

/-- **What the IR must exhibit for the last call of a sequence with imports** answered by `g`,
after the resolved calls `calls` with component import calls `dss` and IR results `wss`: for
returned results `ws.map toRefVal`, the IR play of all calls, the last one making import calls
`ds` answered by `g`; for a trap, the IR play of the earlier calls followed by
`ask (j, vals vs)`, import calls `ds` answered by `g`, and `ans none`. Divergence, deadlock and
cancellation impose nothing. -/
def SeqIRObsI (c : SimpleI)
    (σ : Silmaril.Games.Strategy (sigN c.imports.length) (sigN c.toComp.exports.length))
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (dss : List (List (Σ _ : (sigN c.imports.length).Op, Option Payload)))
    (wss : List (List Silmaril.Wasm.Component.Val)) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (g : HostFuncId → List Val → Option (List Val)) :
    Outcome → Prop
  | .returns (some rs) => ∃ (ws : List Silmaril.Wasm.Component.Val)
      (ds : List (Σ _ : (sigN c.imports.length).Op, Option Payload)), rs = ws.map toRefVal ∧
      (∀ d ∈ ds, HostAnswers g d) ∧
      seqMovesI c (calls ++ [(j, vs)]) (dss ++ [ds]) (wss ++ [ws]) ∈ σ
  | .traps => ∃ ds : List (Σ _ : (sigN c.imports.length).Op, Option Payload),
      (∀ d ∈ ds, HostAnswers g d) ∧
      seqMovesI c calls dss wss ++
        (.inr (.ask (⟨j, by simp [SimpleI.toComp]⟩, .vals vs)) :: callMoves ds ++
          [.inr (.ans (m := (⟨j, by simp [SimpleI.toComp]⟩, .vals vs)) none)]) ∈ σ
  | _ => True

/-- **What the IR must exhibit for the last call of a sequence with imports answered by the
stateful host `g`**, after the resolved calls `calls` with component import calls `dss` and IR
results `wss`, the host state having moved from `s₀` to `s` along `dss`: as `SeqIRObsI`, with the
last call's import calls `ds` answered by `g` from `s` (`HostRun`). -/
def SeqIRObsIS {σ : Type} (c : SimpleI)
    (σI : Silmaril.Games.Strategy (sigN c.imports.length) (sigN c.toComp.exports.length))
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (dss : List (List (Σ _ : (sigN c.imports.length).Op, Option Payload)))
    (wss : List (List Silmaril.Wasm.Component.Val)) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (g : σ → HostFuncId → List Val → Option (List Val × σ))
    (s : σ) : Outcome → Prop
  | .returns (some rs) => ∃ (ws : List Silmaril.Wasm.Component.Val)
      (ds : List (Σ _ : (sigN c.imports.length).Op, Option Payload)) (s' : σ),
      rs = ws.map toRefVal ∧ HostRun g s ds s' ∧
      seqMovesI c (calls ++ [(j, vs)]) (dss ++ [ds]) (wss ++ [ws]) ∈ σI
  | .traps => ∃ (ds : List (Σ _ : (sigN c.imports.length).Op, Option Payload)) (s' : σ),
      HostRun g s ds s' ∧
      seqMovesI c calls dss wss ++
        (.inr (.ask (⟨j, by simp [SimpleI.toComp]⟩, .vals vs)) :: callMoves ds ++
          [.inr (.ans (m := (⟨j, by simp [SimpleI.toComp]⟩, .vals vs)) none)]) ∈ σI
  | _ => True

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}

/-- **The behaviours of a sequence of calls of a component with imports**: from the store
holding one host function per import (`hostFuncs 0 ims`), instantiate `c` with import `k` bound
to host function `k` (`importArgs ims`), call the exports named in `calls` in order (top-level
calls `0, 1, …`), each resolving, then call the export `name` on `vals`. A behaviour is the list
of results of the resolved calls and the outcome of the last call; a trap or divergence of the
instantiation is a behaviour with no results. -/
def seqBehavioursI (prof : ProfileKind) (h : Host E σ) (σ0 : σ) (c : CompAst E.Module)
    (ims : Iface) (calls : List (String × List Val)) (name : String) (vals : List Val) :
    Set (List (List Val) × Outcome) :=
  let m₀ : Machine.Config E σ := Machine.Config.init (hostFuncs 0 ims CStore.empty) σ0
  {p | (∃ m₁ inst es fs mₙ f,
      InstResult.instance m₁ inst es ∈ instBehaviours prof h m₀ c (importArgs ims) ∧
      calls.mapM (fun q => es.lookup q.1) = some fs ∧
      SeqCalls prof h m₁ 0 (fs.zip (calls.map Prod.snd)) p.1 mₙ ∧
      es.lookup name = some f ∧ p.2 ∈ callBehaviours prof h mₙ ⟨calls.length⟩ f vals) ∨
    (p = ([], .traps) ∧ InstResult.traps ∈ instBehaviours prof h m₀ c (importArgs ims)) ∨
    (p = ([], .diverges) ∧ InstResult.diverges ∈ instBehaviours prof h m₀ c (importArgs ims))}

end SeqCallsI

end Silmaril.Wasm.Component.Reference
