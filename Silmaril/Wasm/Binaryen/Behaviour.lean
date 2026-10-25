module

public import Silmaril.Wasm.Binaryen.Typing
public import Silmaril.Wasm.Equiv.Module
public import Silmaril.Wasm.Execution.Core.Typing.Store

@[expose] public section

/-! # Semantics by definition: an IR program means its lowering

Nothing here is a new semantics. A layer-D module `m` is run by instantiating
`m.lower` with Core 3.0's `Instantiate`, running its segments and start function
with Core 3.0's `Steps`, and invoking exports with Core 3.0's `behaviours`.
A layer-N module is run by resolving and then doing the same (`NModule` users
compose with `NModule.resolve`).

* `moduleEntryPoints` packages this as an `Equiv.EntryPoints Module String Val`,
  so `Equiv.FunRefines`/`FunEquiv`/`ModuleRefines`/`ModuleEquiv`/`ImportSpec`/
  `Meets`/`specOf` (`Silmaril/Wasm/Equiv/{Function,Module}.lean`) apply verbatim;
  `entryPoints` is its pullback along `BModule.lower`.
* `Session`/`moduleObs` observe a **sequence** of export invocations sharing the
  store, the observation `ExportRefines` (`Binaryen/Equiv.lean`) is built on.
* `TrapsUB := flip TrapRefines` is Binaryen's `trapsNeverHappen` contract
  (`src/pass.h:203`, version_133): in `Behaviours.Refines TrapsUB tgt src`, a
  source trap licenses any target behaviour. It belongs next to the behavior-refinement hierarchy
  lattice in `Behaviour/Relations.lean`; it lives here until that file is next
  touched, to avoid rebuilding every dependent of the lattice in this sketch.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Numerics

universe u

/-! ## The trapsNeverHappen relation -/

/-- **`TrapsUB`**: target behaviour `b` is allowed against source behaviour `b'`
when the source traps or they agree. Used as `Behaviours.Refines TrapsUB tgt src`. -/
def TrapsUB {V : Type u} (b b' : Behaviour V) : Prop := Behaviour.TrapRefines b' b

namespace TrapsUB

variable {V : Type u}

theorem refl (b : Behaviour V) : TrapsUB b b := Behaviour.TrapRefines.refl b

theorem trans {a b c : Behaviour V} (h : TrapsUB a b) (h' : TrapsUB b c) : TrapsUB a c :=
  Behaviour.TrapRefines.trans h' h

theorem of_eq {a b : Behaviour V} (h : a = b) : TrapsUB a b := h ▸ refl a

/-- A source trap licenses anything. -/
theorem licensed (b : Behaviour V) : TrapsUB b .traps := Behaviour.trapRefines_traps b

/-- `TrapsUB` refinement of behaviour sets is preserved by renaming values. -/
theorem map {W : Type u} (f : V → W) {a b : Behaviour V} (h : TrapsUB a b) :
    TrapsUB (a.map f) (b.map f) := by
  rcases h with h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inr rfl

end TrapsUB

variable {H : Type}

/-- The closed host: no host function ever returns or diverges. Definitionally
`SingleThreaded.noHost`. -/
def closedHost : HostSemantics H := fun _ _ _ _ => False

/-! ## Instantiated modules -/

/-- The function address exported under `x`. -/
def exportFunc? (mi : ModuleInst) (x : String) : Option Nat :=
  match mi.exports.find? (fun e => e.name == x) with
  | some ⟨_, .func a⟩ => some a
  | _ => none

/-- `m` was instantiated from `s` with imports `xas` and its segments and start
function ran to completion, leaving store `s'` and module instance `mi`. -/
def Ready (P : Profile) (host : HostSemantics H) (s : Store H) (m : Module)
    (xas : List ExternAddr) (s' : Store H) (mi : ModuleInst) : Prop :=
  ∃ c c', Instantiate P host s m xas c ∧ Steps P host c c' ∧ c'.code = [] ∧
    c'.store = s' ∧ c.frame.module = mi

/-- Behaviours of the instantiation run itself (segments, then start). -/
def initBeh (P : Profile) (host : HostSemantics H) (s : Store H) (m : Module)
    (xas : List ExternAddr) : Set (Behaviour Val) :=
  {b | ∃ c, Instantiate P host s m xas c ∧ b ∈ behavioursOf P host c}

/-- **Module entry points.** Instantiate `m` in an environment `Env` allows, run its
start, invoke export `x`. -/
def moduleEntryPoints (P : Profile) (host : HostSemantics H)
    (Env : Module → Store H → List ExternAddr → Prop) : Equiv.EntryPoints Module String Val where
  Ok m x vs := ∃ s xas s' mi a, Env m s xas ∧ Ready P host s m xas s' mi ∧
    exportFunc? mi x = some a ∧ InvokeOk s' a vs
  beh m x vs := {b | ∃ s xas s' mi a, Env m s xas ∧ Ready P host s m xas s' mi ∧
    exportFunc? mi x = some a ∧ b ∈ behaviours P host s' a vs}

/-- The closed environment: the empty store and no imports. -/
def closedEnv : Module → Store H → List ExternAddr → Prop := fun _ s xas => s = {} ∧ xas = []

/-- Pull entry points back along a map of programs. -/
def _root_.Silmaril.Wasm.Equiv.EntryPoints.comap {S S' : Type} {A V : Type}
    (E : Equiv.EntryPoints S A V) (f : S' → S) : Equiv.EntryPoints S' A V :=
  ⟨fun s => E.Ok (f s), fun s => E.beh (f s)⟩

/-- **The IR's entry points are those of its lowering.** -/
def entryPoints (P : Profile) (host : HostSemantics H)
    (Env : Module → Store H → List ExternAddr → Prop := closedEnv) :
    Equiv.EntryPoints BModule String Val :=
  (moduleEntryPoints P host Env).comap BModule.lower

@[simp] theorem entryPoints_beh (P : Profile) (host : HostSemantics H) (Env) (m : BModule)
    (x : String) (vs : List Val) :
    (entryPoints P host Env).beh m x vs = (moduleEntryPoints P host Env).beh m.lower x vs := rfl

/-! ## Sessions: sequences of export invocations -/

/-- An invocation request: export name and arguments. -/
abbrev Call := String × List Val

/-- `Session P host mi s script bs`: running `script` against instance `mi` from
store `s` observes `bs`. Invocations share the store; a divergence ends the
session; an ill-formed request (missing export, ill-typed arguments) ends it
with nothing further observed. -/
inductive Session (P : Profile) (host : HostSemantics H) (mi : ModuleInst) :
    Store H → List Call → List (Behaviour Val) → Prop where
  | nil {s : Store H} : Session P host mi s [] []
  | stop {s : Store H} {x : String} {vs : List Val} {rest : List Call}
      (h : ∀ a, exportFunc? mi x = some a → ¬ InvokeOk s a vs) :
      Session P host mi s ((x, vs) :: rest) []
  | done {s : Store H} {x : String} {vs : List Val} {rest : List Call} {a : Nat}
      {c : Config H} {r : Result} {bs : List (Behaviour Val)}
      (ha : exportFunc? mi x = some a) (hok : InvokeOk s a vs)
      (run : Steps P host (invoke s a vs) c) (hr : c.code = r.toAdmin)
      (tail : Session P host mi c.store rest bs) :
      Session P host mi s ((x, vs) :: rest) (r.toBehaviour :: bs)
  | diverge {s : Store H} {x : String} {vs : List Val} {rest : List Call} {a : Nat}
      (ha : exportFunc? mi x = some a) (hok : InvokeOk s a vs)
      (hd : Diverges P host (invoke s a vs)) :
      Session P host mi s ((x, vs) :: rest) [.diverges]

/-- **Module observations.** Instantiate `m` from `s` with imports `xas`; the
first observation is the instantiation run (segments and start); if it returns,
the session `script` follows. -/
def moduleObs (P : Profile) (host : HostSemantics H) (s : Store H) (xas : List ExternAddr)
    (m : Module) (script : List Call) : Set (List (Behaviour Val)) :=
  {bs | ∃ c, Instantiate P host s m xas c ∧
    ((∃ c' bs', Steps P host c c' ∧ c'.code = [] ∧
        Session P host c.frame.module c'.store script bs' ∧ bs = .returns [] :: bs') ∨
     (∃ (c' : Config H) (r : Result), Steps P host c c' ∧ c'.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
     (Diverges P host c ∧ bs = [.diverges]))}

/-- Observations of a layer-D module: those of its lowering. -/
abbrev BModule.obs (P : Profile) (host : HostSemantics H) (s : Store H) (xas : List ExternAddr)
    (m : BModule) (script : List Call) : Set (List (Behaviour Val)) :=
  moduleObs P host s xas m.lower script

end Silmaril.Wasm.Binaryen
