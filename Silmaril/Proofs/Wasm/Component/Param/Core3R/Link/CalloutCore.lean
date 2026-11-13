module

public import Silmaril.Proofs.Wasm.Component.Reference.CalloutCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutRun
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqBase
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.Base

/-!
# `Silmaril.Proofs.Wasm.Component.Reference.CalloutCore` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.CalloutCore` that the
soundness of linked components (`linked2_sound`, `linked2_sound_seq`) uses and whose statements
mention the engine `core3R P V IR`, with `core3R P V IR` replaced by `core3R P V IR` (Core 3.0 with
validity `V` and an internal step `IR` contained in `InternalP P`, `Core3R.Sub`). The other
declarations of that module are engine-generic and reused from it. Proofs are unchanged except
where a core step of the machine is read as an `InternalP P` step (through `Sub P IR`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Proofs.Wasm.Component.Reference

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

variable {P : Profile} {σ : Type} {g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)} {prof : ProfileKind}

/-! ## Callout sites -/

/-- The frame `B` with the subtask and caller records `ST`, `CL` appended. -/
def extSC (B : Machine.Config (E3 P V IR) σ) (ST : List Subtask) (CL : List (Caller (E3 P V IR))) :
    Machine.Config (E3 P V IR) σ :=
  { B with store := { B.store with
      subtasks := B.store.subtasks ++ ST
      callers := B.store.callers ++ CL } }

/-- The frame `B` in host state `s`. -/
abbrev withH (B : Machine.Config (E3 P V IR) σ) (s : σ) : Machine.Config (E3 P V IR) σ := { B with host := s }

variable {Q : LowerSite P → Prop}

/-- The trampoline. -/
def _root_.Silmaril.Proofs.Wasm.Component.Reference.LowerSite.hostR (L : LowerSite P) : CanonHost (E3 P V IR) := .lowered L.f (witFt L.p) {} L.inst

/-- The conditions under which a callout to `L` from thread `th` in store `B` with flat
arguments `ys` is answered by `g` as the IR adapter prescribes: the entry check passes, the
instance may leave, `L.f` is the host function `L.fn`, the types are float-free and within the
flat arities of a synchronous lower, the arguments have the flat parameter types, and `g`
answers images of well-typed values. -/
structure _root_.Silmaril.Proofs.Wasm.Component.Reference.LowerSite.OkR (L : LowerSite P) (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ))
    (B : CStore (E3 P V IR)) (th : Option ThreadId) (ys : List Flat) : Prop where
  entry : calloutEntry B th L.hostR = none
  inst : ArenaField.insts.get? B L.inst = some L.st
  leave : L.st.mayLeave = true
  func : ArenaField.funcs.get? B L.f = some (.host L.ft' L.fn)
  pff : floatFreeList L.p.params = true
  rff : floatFreeList L.p.results = true
  typed : ys.map (·.type) = ValTy.flatList L.p.params
  maxp : (ValTy.flatList L.p.params).length ≤ 16
  res : L.p.results.length ≤ 1
  maxr : (ValTy.flatList L.p.results).length ≤ 1
  answers : ∀ (s : σ) (ws : List Silmaril.Wasm.Component.Val) rs (s' : σ),
    g s L.fn (ws.map toRefVal) = some (rs, s') →
    ∃ us, rs = us.map toRefVal ∧ ValTy.checkList L.p.results us = true

/-- The callout `h ys` from thread `th` in store `B` is to a `canon lower` site that `g` answers
as the IR prescribes. -/
def LowerAt (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)) (Q : LowerSite P → Prop)
    (B : CStore (E3 P V IR)) (th : Option ThreadId) (h : CanonHost (E3 P V IR)) (ys : List Flat) : Prop :=
  ∃ L : LowerSite P, Q L ∧ h = L.hostR ∧ L.OkR g B th ys

/-- `Ok` depends only on the fields that callouts do not change. -/
theorem _root_.Silmaril.Proofs.Wasm.Component.Reference.LowerSite.OkR.extSC {L : LowerSite P} {B : Machine.Config (E3 P V IR) σ}
    {th : Option ThreadId} {ys : List Flat} (ST : List Subtask) (CL : List (Caller (E3 P V IR)))
    (cs : (E3 P V IR).Store (CanonHost (E3 P V IR))) (hok : L.OkR g B.store th ys) :
    L.OkR g { (extSC B ST CL).store with core := cs } th ys :=
  { entry := hok.entry, inst := hok.inst, leave := hok.leave, func := hok.func, pff := hok.pff
    rff := hok.rff, typed := hok.typed, maxp := hok.maxp, res := hok.res, maxr := hok.maxr
    answers := hok.answers }

/-! ## One callout in the machine -/

/-- A callout status is neither running nor stuck. -/
theorem callout_status_ne {s : (E3 P V IR).Store (CanonHost (E3 P V IR))} {t : (E3 P V IR).Thread (CanonHost (E3 P V IR))}
    {h : CanonHost (E3 P V IR)} {ys : List Flat} (hs : (E3 P V IR).status s t = .callout h ys) :
    (E3 P V IR).status s t ≠ .running ∧ (E3 P V IR).status s t ≠ .stuck := by
  rw [hs]
  exact ⟨(fun e => by cases e), (fun e => by cases e)⟩

/-! ## Segmented runs of the core phase -/

open Silmaril.Wasm.SingleThreaded in
/-- A callout status of `core3R P V IR` is the host-call redex of the thread, with flat arguments. -/
theorem status_callout_redex {s : (E3 P V IR).Store (CanonHost (E3 P V IR))} {t : Silmaril.Wasm.SingleThreaded.Thread}
    {h : CanonHost (E3 P V IR)} {ys : List Flat} (hs : (E3 P V IR).status s t = .callout h ys) :
    ∃ E a args, decompose? s (t.config s).code = some (E, a, h, args) ∧ args.mapM toFlat? = some ys := by
  have hs' : flatStatus (Silmaril.Wasm.Game.statusP P s t) = .callout h ys := hs
  unfold flatStatus at hs'
  split at hs'
  · cases hs'
  · split at hs' <;> cases hs'
  · cases hs'
  next h' args' heq =>
    split at hs'
    next fargs hm =>
      obtain ⟨rfl, rfl⟩ : h' = h ∧ fargs = ys := by
        simpa only [Silmaril.Wasm.Component.Engine.Status.callout.injEq] using hs'
      obtain ⟨E, a, hd⟩ := statusP_callout heq
      exact ⟨E, a, args', hd, hm⟩
    next => cases hs'
  · cases hs'

open Silmaril.Wasm.SingleThreaded in
/-- The machine's resumption with flat values is the Core resumption with their values. -/
theorem resume_values (s : (E3 P V IR).Store (CanonHost (E3 P V IR))) (t : Silmaril.Wasm.SingleThreaded.Thread)
    (flat : List Flat) :
    (E3 P V IR).resume s t (.values flat) =
      resumeResult s t (.values (flat.map Silmaril.Wasm.SingleThreaded.ofFlat)) := by
  show resume s t _ = _
  simp only [resume, resumeResult, Silmaril.Wasm.Component.Engine.Core3.toCR, CallResult.toAdmin,
    Silmaril.Wasm.Execution.Core.Result.toAdmin]

variable (g Q) in
/-- **A segmented run of the core phase answered by the stateful `g`**: host-free core runs
separated by callouts to `canon lower` sites (from thread `th`, in store `B`) that `g` answers in
the current host state, each resumed with the lowered answer. Each callout is recorded with the
host states before and after it, the index of the lowered function, the core arguments and the
core result of the resumption. -/
inductive ASeg (B : CStore (E3 P V IR)) (th : Option ThreadId) :
    σ → CoreSt (E3 P V IR) → List (σ × CallRec × σ) → σ → CoreSt (E3 P V IR) → Prop
  | done {s : σ} {x y : CoreSt (E3 P V IR)} : Relation.ReflTransGen (CoreStep (E3 P V IR)) x y →
      ASeg B th s x [] s y
  | call {s s' s'' : σ} {x y z : CoreSt (E3 P V IR)} {L : LowerSite P} {ys flat : List Flat}
      {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : Nat} {args : List Silmaril.Wasm.Execution.Core.Val}
      {rest : List (σ × CallRec × σ)} :
      Relation.ReflTransGen (CoreStep (E3 P V IR)) x y → (E3 P V IR).status y.1 y.2 = .callout L.hostR ys →
      Q L → L.OkR g B th ys → L.Answers g s ys flat s' →
      Silmaril.Wasm.SingleThreaded.decompose? y.1 (y.2.config y.1).code = some (E, a, L.hostR, args) →
      ASeg B th s' (y.1, (E3 P V IR).resume y.1 y.2 (.values flat)) rest s'' z →
      ASeg B th s x ((s, (L.f.idx, args, .values (flat.map Silmaril.Wasm.SingleThreaded.ofFlat)), s') ::
        rest) s'' z

/-- Core steps of the machine are host-free thread steps. -/
theorem coreSteps_internalP [hIR : Fact (Sub P IR)] {x y : CoreSt (E3 P V IR)}
    (h : Relation.ReflTransGen (CoreStep (E3 P V IR)) x y) :
    Relation.ReflTransGen (Silmaril.Wasm.Game.InternalP P) x y :=
  Relation.ReflTransGen.mono (fun _ _ h => hIR.out h.2) _ _ h

/-! ## Inversion of the core phase with callouts -/

/-- The callouts reachable from `x` in host state `s` along runs answered by `g` are
`canon lower` sites answered as the IR prescribes. -/
def CalloutsOk (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)) (Q : LowerSite P → Prop)
    (B : CStore (E3 P V IR)) (th : Option ThreadId) (s : σ) (x : CoreSt (E3 P V IR)) : Prop :=
  ∀ calls s' y h ys, ASeg g Q B th s x calls s' y → (E3 P V IR).status y.1 y.2 = .callout h ys →
    LowerAt g Q B th h ys

/-- `CalloutsOk` after an answered callout. -/
theorem CalloutsOk.after {B : CStore (E3 P V IR)} {th : Option ThreadId} {s s' : σ}
    {x y : CoreSt (E3 P V IR)}
    {L : LowerSite P} {ys flat : List Flat} {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : Nat}
    {args : List Silmaril.Wasm.Execution.Core.Val} (hc : CalloutsOk g Q B th s x)
    (hy : Relation.ReflTransGen (CoreStep (E3 P V IR)) x y) (hs : (E3 P V IR).status y.1 y.2 = .callout L.hostR ys)
    (hq : Q L) (hok : L.OkR g B th ys) (ha : L.Answers g s ys flat s')
    (hd : Silmaril.Wasm.SingleThreaded.decompose? y.1 (y.2.config y.1).code = some (E, a, L.hostR, args)) :
    CalloutsOk g Q B th s' (y.1, (E3 P V IR).resume y.1 y.2 (.values flat)) :=
  fun _ _ z h ys' hz hs' => hc _ _ z h ys' (.call hy hs hq hok ha hd hz) hs'

end Silmaril.Proofs.Wasm.Component.Param.Core3R
