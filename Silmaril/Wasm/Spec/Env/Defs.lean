module

public import Silmaril.Wasm.Spec.Wasm.Defs
public import Silmaril.Wasm.Spec.Basic.Defs
public import Silmaril.Wasm.Game.StatefulEnv.Defs

@[expose] public section

/-!
# Model variants: programs, programs with environments, environments

Three readings of the models of a specification, each a semantics in the trace-institution
format, related by comorphisms and transfer theorems (`Silmaril.Wasm.Spec.Env.Thms`):

* **(a) programs** (`S`, e.g. `wasmSem P`): a model is a program; its traces cover every
  environment (game strategies are receptive). A sentence holds for all environments.
* **(b) programs with environments** (`S.withEnv`): a model is a program `p` together with an
  environment specification `K` (a good set of import-event sequences: the calls the program may
  make and the answers it may get); its traces are the traces of `p` whose import events `K`
  allows. "Import `i` only ever returns `v`" is part of the model.
* **(c) environments** (`envSem`): a model is an environment specification `K` alone, with
  every trace whose import events `K` allows (the environment against an arbitrary program, so
  it does not depend on the program semantics). Sentences about import events describe
  environment behaviour.

The traces of a (b)-model are the intersection of the traces of its program (a) and of its
environment (c) (`withEnv_traces`).

`Logic.assume L` is the assume-guarantee logic over `L`: a formula is an environment assumption
`K` with an `L`-guarantee, satisfied by `T` when the guarantee holds on the traces of `T` that `K`
allows. Assume-guarantee sentences about programs (a) are plain sentences about programs with
environments (b) (`models_assume_iff`).

`iretPost`: "every return of import `i` satisfies `Q`", an environment property.

For Wasm, `stratEnv τ` reads an environment strategy `τ : Strategy Sig.empty E` (any stateful,
nondeterministic environment of `Silmaril.Wasm.Game`) as an environment specification, and
`agreeEnv L q` a host machine `L` from state `q`.
-/

namespace Silmaril.Wasm.Spec

open Silmaril.Games Silmaril.Wasm.Game

variable {Ty A R : Type}

/-- An environment specification: a good set of import-event sequences. -/
abbrev EnvSpec {Ty : Type} (A R : Type) (X : Iface Ty) : Type :=
  {K : Set (List (SideEv A R X.imports.length)) // Good K}

/-- The chaotic environment: every import-event sequence. -/
def EnvSpec.top {X : Iface Ty} : EnvSpec A R X :=
  ⟨Set.univ, ⟨trivial, fun _ _ => trivial⟩⟩

/-- The traces whose import events the environment allows. -/
def envTraces {X : Iface Ty} (K : EnvSpec A R X) : Set (List (Event A R X)) :=
  {t | importEvents t ∈ K.1}

/-- The import events of a prefix are a prefix of the import events. -/
theorem importEvents_prefix {X : Iface Ty} {s t : List (Event A R X)} (h : s <+: t) :
    importEvents s <+: importEvents t := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨importEvents u, by simp [importEvents, List.filterMap_append]⟩

/-- A good trace set restricted by an environment is good. -/
theorem Good.inter_envTraces {X : Iface Ty} {T : Set (List (Event A R X))} (hT : Good T)
    (K : EnvSpec A R X) : Good (T ∩ envTraces K) where
  nil_mem := ⟨hT.nil_mem, K.2.nil_mem⟩
  of_prefix := fun ⟨ht, hK⟩ hs => ⟨hT.of_prefix ht hs, K.2.of_prefix hK (importEvents_prefix hs)⟩

/-- The traces allowed by an environment form a good set. -/
theorem envTraces_good {X : Iface Ty} (K : EnvSpec A R X) : Good (envTraces K) where
  nil_mem := K.2.nil_mem
  of_prefix := fun hK hs => K.2.of_prefix hK (importEvents_prefix hs)

/-- **(b) Programs with environments.** -/
abbrev Semantics.withEnv (S : Semantics Ty A R) : Semantics Ty A R where
  Prog X := S.Prog X × EnvSpec A R X
  traces pK := S.traces pK.1 ∩ envTraces pK.2
  good pK := (S.good pK.1).inter_envTraces pK.2

/-- **(c) Environments.** -/
abbrev envSem (Ty A R : Type) : Semantics Ty A R where
  Prog X := EnvSpec A R X
  traces K := envTraces K
  good K := envTraces_good K

/-- A program, against the chaotic environment. -/
def Semantics.chaosEnv (S : Semantics Ty A R) : SemMap S S.withEnv where
  prog p := (p, EnvSpec.top)
  traces_prog _ := Set.ext fun _ => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- **The assume-guarantee logic over `L`.** -/
abbrev Logic.assume (L : Logic Ty A R) : Logic Ty A R where
  Fm X := EnvSpec A R X × L.Fm X
  Sat T φ := L.Sat (T ∩ envTraces φ.1) φ.2

/-- "Every return of import `i` satisfies `Q`." -/
def IRetPost.holds {X : Iface Ty} (φ : X.Imp × (R → Prop)) (t : List (Event A R X)) : Prop :=
  ∀ r, Event.iret φ.1 r ∈ t → φ.2 r

/-- The logic of import return postconditions (environment behaviour). -/
abbrev iretPost (Ty A R : Type) : Logic Ty A R :=
  Logic.ofTrace (fun X => X.Imp × (R → Prop)) IRetPost.holds

/-! ## Wasm environments -/

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The import-event sequences of an environment strategy. -/
def stratEnvSet {X : WIface} (τ : Strategy Sig.empty (ifaceSig X.imports)) :
    Set (List (SideEv (List Val) (Behaviour Val) X.imports.length)) :=
  {v | ∃ u : List (Ev (ifaceSig X.imports)), u.map Sum.inr ∈ τ ∧ v = u.map evOf}

/-- An environment strategy as an environment specification. -/
def stratEnv {X : WIface} (τ : Strategy Sig.empty (ifaceSig X.imports)) :
    EnvSpec (List Val) (Behaviour Val) X :=
  ⟨stratEnvSet τ, ⟨⟨[], τ.nil_mem, rfl⟩, by
    rintro s t ⟨u, hu, rfl⟩ hs
    obtain ⟨u', hu', rfl⟩ := prefix_map_exists evOf hs
    exact ⟨u', τ.of_prefix hu (hu'.map Sum.inr), rfl⟩⟩⟩

/-- A prefix of an exchange that agrees with a host machine agrees with it. -/
theorem SEnv.Agrees.of_prefix {E : Sig.{0}} {L : SEnv E} :
    ∀ {q : L.S} {u v : List (Ev E)}, L.Agrees q u → v <+: u → L.Agrees q v
  | _, _, [], _, _ => .nil _
  | _, _, _ :: _, .nil _, hv => absurd (List.prefix_nil.1 hv) (List.cons_ne_nil _ _)
  | _, _, x :: v, .pending _ e, hv => by
    obtain ⟨rfl, hv'⟩ := List.cons_prefix_cons.1 hv
    rw [List.prefix_nil.1 hv']
    exact .pending _ e
  | _, _, x :: v, .answered (e := e) (w := w) hans hrest, hv => by
    obtain ⟨rfl, hv'⟩ := List.cons_prefix_cons.1 hv
    rcases v with _ | ⟨y, v⟩
    · exact .pending _ e
    · obtain ⟨rfl, hv''⟩ := List.cons_prefix_cons.1 hv'
      exact .answered hans (SEnv.Agrees.of_prefix hrest hv'')

/-- The import-event sequences agreeing with a host machine from state `q`. -/
def agreeEnv {X : WIface} (L : SEnv (ifaceSig X.imports)) (q : L.S) :
    EnvSpec (List Val) (Behaviour Val) X :=
  ⟨{v | ∃ u, L.Agrees q u ∧ v = u.map evOf}, ⟨⟨[], .nil q, rfl⟩, by
    rintro s t ⟨u, hu, rfl⟩ hs
    obtain ⟨u', hu', rfl⟩ := prefix_map_exists evOf hs
    exact ⟨u', SEnv.Agrees.of_prefix hu hu', rfl⟩⟩⟩

end Silmaril.Wasm.Spec
