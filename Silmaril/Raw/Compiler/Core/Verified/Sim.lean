module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Machine.CBackend.Lir.Simulation.Defs
public import Silmaril.Cerberus.Core.StepLemmas.Defs

/-! # Core/Lir simulation obligations

The direction is deliberately Lir to Core: each behaviour of the deterministic
compiled program must be allowed by a possibly nondeterministic source. A
Core-to-Lir forward simulation alone would establish the opposite inclusion.

`Simulation` reuses the per-instruction Lir simulation kit, with Core as its
other machine. Its relation may inspect the entire Core state (including saved
label environments, suspended procedure continuations, and allocated objects)
and the entire Lir state. No empty-memory or empty-call-stack assumption is made.
The measure counts Lir steps matched by zero Core steps, so an infinite Lir
loop cannot be justified by endlessly stuttering at one Core state.

Reachable Core UB is an escape, including UB *after* a defined prefix. The
`stuck` obligation is essential: the backend bridge allows arbitrary machine
behaviour when the Lir program gets stuck. A successful translation must prove
that this happens only when Core can reach UB.

This is a proof interface, not a translator or a concrete memory invariant.
Instantiation, including startup, saved-label/call correspondence and LP64
object layout, is still required before any program can be accepted.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Sim

open Silmaril.Cerberus
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Machine
open Spec
open Relation

/-- UB reachable from an arbitrary Core state, without fixing startup arguments. -/
def UBFrom (file : Program) (labels : Labels) (c : CState) : Prop :=
  ∃ t loc ub, ReflTransGen (coreStep file labels) c t ∧ t.control = .halt (.ub loc ub)

/-- A terminal Core state and its process observation. Errors and unsupported
constructs have no constructor. -/
inductive Final : CState → Obs → Prop where
  | exit {c : CState} {v : Val} {k : Nat}
      (halt : c.control = .halt (.defined v)) (status : exitStatuses v k) :
      Final c (.exit k (coreBytes c.memory.stdout))
  | abort {c : CState} (halt : c.control = .halt .aborted) :
      Final c (.abort (coreBytes c.memory.stdout))

/-- Fuel-free source observations from any state. -/
inductive BehFrom (file : Program) (labels : Labels) (c : CState) : Obs → Prop where
  | finite {t o} (steps : ReflTransGen (coreStep file labels) c t) (final : Final t o) :
      BehFrom file labels c o
  | diverges (trace : InfiniteTrace (coreStep file labels) c) :
      BehFrom file labels c .diverges

/-- Local form of the frozen allowance, independent of document startup. -/
def AllowedFrom (file : Program) (labels : Labels) (c : CState) (o : Obs) : Prop :=
  o = .exhausted ∨ UBFrom file labels c ∨ BehFrom file labels c o

theorem UBFrom.prefix {file labels c t} (steps : ReflTransGen (coreStep file labels) c t)
    (ub : UBFrom file labels t) : UBFrom file labels c := by
  obtain ⟨u, loc, why, path, halt⟩ := ub
  exact ⟨u, loc, why, steps.trans path, halt⟩

theorem BehFrom.prefix {file labels c t o} (steps : ReflTransGen (coreStep file labels) c t)
    (beh : BehFrom file labels t o) : BehFrom file labels c o := by
  cases beh with
  | finite path final => exact .finite (steps.trans path) final
  | diverges trace => exact .diverges (InfiniteTrace.of_steps steps trace)

/-- Convert the parametric result to the frozen document specification only
at the boundary, using the same arguments as the loaded artifact. -/
theorem AllowedFrom.allowed {doc : Codec.Document} {initial c : CState} {labels : Labels} {args : List String} {o : Obs}
    (start : coreStart doc args = .ok (initial, labels))
    (reach : ReflTransGen (coreStep doc.file labels) initial c)
    (allowed : AllowedFrom doc.file labels c o) : Allowed doc args o := by
  rcases allowed with exhausted | ub | beh
  · exact .inl exhausted
  · obtain ⟨t, loc, why, path, halt⟩ := ub
    exact .inr (.inl (.inr ⟨t, loc, why, ⟨initial, labels, start, reach.trans path⟩, halt⟩))
  · right; right
    cases beh with
    | finite path final =>
      have reachable : CoreReach doc args _ := ⟨initial, labels, start, reach.trans path⟩
      cases final with
      | exit halt status => exact CoreBeh.exit reachable halt status
      | abort halt => exact CoreBeh.abort reachable halt
    | diverges trace => exact CoreBeh.diverges start (InfiniteTrace.of_steps reach trace)

variable {R : Type} [DecidableEq R]

/-- One invariant and one set of local instruction obligations for every rung.
The `call`, `jump`, `branch`, and `ret` fields of `cases` cover procedure calls,
saved-label transfers/loops, conditionals, and returns without changing the kit. -/
structure Simulation (file : Program) (labels : Labels) (p : Lir.Prog R) where
  cases : Lir.EscapeCaseSimulation p (coreStep file labels) (UBFrom file labels)
  returned : ∀ vs mem c, cases.Returned vs mem c →
    ∀ o, LirObs (.returned vs mem) o → Final c o
  trapped : ∀ mem c, cases.Trapped mem c →
    ∀ o, LirObs (.trapped mem) o → Final c o
  stuck : ∀ s c, cases.Match s c → Lir.step p s = .stuck → UBFrom file labels c

/-- An adapter for frontends that prove their local rules by the total Lir
step function. It produces the same per-instruction interface without a second
simulation theorem or a different invariant. -/
def Simulation.ofSteps (file : Program) (labels : Labels) (p : Lir.Prog R)
    (Match : Lir.State R → CState → Prop) (measure : Lir.State R → Nat)
    (running : ∀ s c s', Match s c → Lir.Step p s s' →
      Lir.Progress (coreStep file labels) (fun s c => Match s c ∨ UBFrom file labels c)
        measure s c s')
    (returned : ∀ s c vs mem, Match s c → Lir.step p s = .returned vs mem →
      ∃ t, ReflTransGen (coreStep file labels) c t ∧
        ((∀ o, LirObs (.returned vs mem) o → Final t o) ∨ UBFrom file labels t))
    (trapped : ∀ s c mem, Match s c → Lir.step p s = .trapped mem →
      ∃ t, ReflTransGen (coreStep file labels) c t ∧
        ((∀ o, LirObs (.trapped mem) o → Final t o) ∨ UBFrom file labels t))
    (stuck : ∀ s c, Match s c → Lir.step p s = .stuck → UBFrom file labels c) :
    Simulation file labels p where
  cases := {
    Match := Match
    measure := measure
    Returned vs mem c := ∀ o, LirObs (.returned vs mem) o → Final c o
    Trapped mem c := ∀ o, LirObs (.trapped mem) o → Final c o
    op hm hf he := running _ _ _ hm (Lir.Transition.op hf he).step_eq
    call hm hf ha he := running _ _ _ hm (Lir.Transition.call hf ha he).step_eq
    fop hm hf he := running _ _ _ hm (Lir.Transition.fop hf he).step_eq
    jump hm hf := running _ _ _ hm (Lir.Transition.jump hf).step_eq
    branch hm hf hc := running _ _ _ hm (Lir.Transition.branch hf hc).step_eq
    ret hm hf hv hs ha hw := running _ _ _ hm (Lir.Transition.ret hf hv hs ha hw).step_eq
    halt hm hf hv hs := returned _ _ _ _ hm (Lir.Transition.halt hf hv hs).step_eq
    trap hm hf := trapped _ _ _ hm (Lir.Transition.trap hf).step_eq }
  returned _ _ _ h := h
  trapped _ _ h := h
  stuck := stuck

namespace Simulation

variable {file : Program} {labels : Labels} {p : Lir.Prog R}
    (sim : Simulation file labels p) {s : Lir.State R} {c : CState}

/-- A finite compiled execution cannot acquire undefined behaviour unless
Core itself can reach UB. This also discharges the backend bridge's stuck arm. -/
theorem stuck_ub (matched : sim.cases.Match s c ∨ UBFrom file labels c)
    (beh : Lir.Behaves p s .stuck) : UBFrom file labels c := by
  obtain ⟨s', path, stopped⟩ := beh
  obtain ⟨t, steps, related⟩ := sim.cases.toCase.toForward.steps matched path
  have steps' := Stutter.reflTransGen_proj steps
  rcases related with related | ub
  · exact UBFrom.prefix steps' (sim.stuck _ _ related stopped)
  · exact UBFrom.prefix steps' ub

/-- Every observed Lir behaviour is allowed by Core. In particular divergence
requires an actual infinite Core trace or reachable UB, rather than fuel expiry. -/
theorem behaves (matched : sim.cases.Match s c ∨ UBFrom file labels c)
    {b : Lir.Behavior} {o : Obs} (beh : Lir.Behaves p s b) (obs : LirObs b o) :
    AllowedFrom file labels c o := by
  cases b with
  | returned vs mem =>
    obtain ⟨t, path, final⟩ := sim.cases.returns matched beh
    rcases final with final | ub
    · exact .inr (.inr (.finite path (sim.returned _ _ _ final _ obs)))
    · exact .inr (.inl (UBFrom.prefix path ub))
  | trapped mem =>
    obtain ⟨t, path, final⟩ := sim.cases.traps matched beh
    rcases final with final | ub
    · exact .inr (.inr (.finite path (sim.trapped _ _ final _ obs)))
    · exact .inr (.inl (UBFrom.prefix path ub))
  | stuck => exact obs.elim
  | diverges =>
    change o = .diverges at obs
    subst o
    rcases sim.cases.diverges matched beh with trace | ⟨t, path, ub⟩
    · exact .inr (.inr (.diverges trace))
    · exact .inr (.inl (UBFrom.prefix path ub))

end Simulation

/-- The remaining obligation at the compiler boundary. It quantifies over the
actual entry state and artifact memory rather than a default argument block. -/
def EntryMatches (doc : Codec.Document) (l : Mir.Linked) (a : Artifact) : Prop :=
  ∀ args, ArgsOk args → ∀ entry s, l.funcs[Silmaril.Compile.Forks.CoreComp.Target.startSymbol]? = some entry →
    l.prog.start entry [BitVec.ofNat 64 args.length, BitVec.ofNat 64 a.argBase]
      (a.lmem args) = some s →
    ∃ initial labels c, coreStart doc args = .ok (initial, labels) ∧
      ReflTransGen (coreStep doc.file labels) initial c ∧
      ∃ sim : Simulation doc.file labels l.prog, sim.cases.Match s c ∨ UBFrom doc.file labels c

/-- Compose the generic simulation with the proved backend. No construct proof
needs to unfold machine loading, register allocation, or machine observations. -/
theorem artifact_sound {doc : Codec.Document} {l : Mir.Linked} {a : Artifact}
    (compiled : Backend.artifactOf l = .ok a) (entry : EntryMatches doc l a)
    {S : X86.Backend.Space} {exit : X86.Word} {E0 : Nat} (loaded : Loaded a S exit E0)
    {args : List String} (argsOk : ArgsOk args)
    {saved : X86.Reg → X86.Word} {init : X86.State} {o : Obs}
    (machine : MachineBeh a S exit E0 saved init args o) : Allowed doc args o := by
  obtain ⟨f, s, hf, hs, result⟩ := artifactOf_sound compiled loaded machine
  obtain ⟨initial, labels, c, start, reach, sim, matched⟩ := entry args argsOk f s hf hs
  rcases result with exhausted | stuck | ⟨b, beh, obs⟩
  · exact .inl exhausted
  · exact AllowedFrom.allowed start reach (.inr (.inl (sim.stuck_ub matched stuck)))
  · exact AllowedFrom.allowed start reach (sim.behaves matched beh obs)

/-- Syntax-directed frontends can share this backend assembly function. Its
executable dependencies are the frontend and backend, never the simulation. -/
def compileWith (translate : Codec.Document → Option Mir.Linked) (doc : Codec.Document) :
    Option Artifact := do
  let linked ← translate doc
  (Backend.artifactOf linked).toOption

/-- A frontend discharges only the entry simulation; this theorem supplies
exactly the frozen `SoundSpec` for the assembled compiler. -/
theorem compileWith_sound (translate : Codec.Document → Option Mir.Linked)
    (correct : ∀ doc linked artifact, translate doc = some linked →
      Backend.artifactOf linked = .ok artifact → EntryMatches doc linked artifact) :
    SoundSpec (compileWith translate) := by
  intro doc artifact compiled
  cases translated : translate doc with
  | none => simp [compileWith, translated] at compiled
  | some linked =>
    cases emitted : Backend.artifactOf linked with
    | error why => simp [compileWith, translated, emitted, Except.toOption] at compiled
    | ok result =>
      have same : result = artifact := by simpa [compileWith, translated, emitted, Except.toOption] using compiled
      subst artifact
      refine ⟨Fragment.argSize_ok emitted, ?_⟩
      intro S exit E0 loaded args argsOk saved init o machine
      exact artifact_sound emitted (correct doc linked result translated emitted) loaded argsOk machine

end Silmaril.Compile.Core.Verified.Sim
