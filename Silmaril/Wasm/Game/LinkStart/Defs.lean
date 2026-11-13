module

public import Silmaril.Wasm.Game.Linking.Defs
public import Silmaril.Wasm.Game.Start.Defs

/-!
# Static links whose inputs have start functions

silmaril-lean's linker `link?` rejects inputs with start functions
(`inProfile` requires `m.start = none`), so a link with start functions is,
as in an earlier development, a start-free `Linking.Setup` together with the
start functions of its inputs (`StartSetup`): `provStart` an address in the
provider store `sp`, `consStart` an address in the consumer store `scs`
(with host stubs for the provider), both of type `[] → []`.

Source: `StartSetup` adapted from `Silmaril/Wasm/Game/Linking/Start.lean`
(same revision; start functions given by address instead of index, the
linked start sequence not formalised). `linkInst` is new.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

/-- Configurations of a start sequence: the store, the running start thread, and the start
functions still to run. -/
abbrev SeqConf : Type := Store Nat × Thread × List Nat

/-- Silent steps of a start sequence: a host-free step of the running start thread, or, once it
has returned `values []`, the invocation of the next start function. -/
inductive SeqStep (P : Profile) : SeqConf → SeqConf → Prop where
  /-- A host-free step of the running start function. -/
  | run {s s' : Store Nat} {t t' : Thread} {rest : List Nat} :
      InternalP P (s, t) (s', t') → SeqStep P (s, t, rest) (s', t', rest)
  /-- The running start function has returned: invoke the next one. -/
  | next {s : Store Nat} {t : Thread} {a : Nat} {rest : List Nat} :
      ResultAt s t (.values []) → SeqStep P (s, t, a :: rest) (s, .pending a [], rest)

namespace ScalarInstance

variable (I : ScalarInstance)

/-- **The instantiable system of an instance whose instantiation runs the start functions
`starts` in order**: each must return `values []` before the next is invoked; a trap or an
uncaught exception of any of them fails instantiation; export calls then run from the
persisted store as in `instSys`. The empty finished thread `.active {} []` starts it. -/
noncomputable def instSysSeq (P : Profile) (s : Store Nat) (starts : List Nat) :
    Silmaril.Games.InstSystem I.E I.F (Behaviour Val) where
  IConf := SeqConf
  State := Store Nat
  Conf _ := Store Nat × Thread
  istart := (s, .active {} [], starts)
  istep := SeqStep P
  icall c e k := I.CallsOut (c.1, c.2.1) e ∧
    k = fun v => (c.1, resumeResult c.1 c.2.1 (Answer.toResult (ft := I.imports.get e.1) v), c.2.2)
  iready c s' := ResultAt c.1 c.2.1 (.values []) ∧ c.2.2 = [] ∧ s' = c.1
  ifail c b := StartFailed (c.1, c.2.1) b
  start q s' := (s', I.initThread q)
  step := fun {_} => InternalP P
  call := fun {_} c e k => I.CallsOut c e ∧ k = I.resumeK c.1 c.2 e
  done := fun {q} c v s' =>
    ∃ r, ResultAt c.1 c.2 r ∧ Answer.ofResult? (I.exports.get q.1) r = some v ∧ s' = c.1

end ScalarInstance

end Silmaril.Wasm.Game

namespace Silmaril.Wasm.Game.Linking

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- A static link whose inputs may have start functions (see the module docstring). -/
structure StartSetup extends Setup where
  /-- The address of the provider's start function in the provider store. -/
  provStart : Option Nat
  /-- The address of the consumer's start function in the consumer store. -/
  consStart : Option Nat
  provStartTyped : ∀ a ∈ provStart, StartTyped sp a
  consStartTyped : ∀ a ∈ consStart, StartTyped scs a
  /-- The provider's start function is a function of the provider. -/
  provStartFunc : ∀ a ∈ provStart, a ∈ fp.module.funcs
  /-- The consumer's start function is a function of the consumer (possibly an import). -/
  consStartFunc : ∀ a ∈ consStart, a ∈ fcs.module.funcs

namespace StartSetup

variable (S : StartSetup)

/-- **The link of the instantiable provider and consumer**: the provider's strategy with its
start phase below the consumer's instantiable system, the provider instantiated first. -/
noncomputable def linkInst (P : Profile) :
    DStrategy (ifaceSig []) ((ifaceSig S.exportTypes).withInst (Behaviour Val)) :=
  (S.providerI.instStrategy P S.sp S.provStart).link
    (S.consumerI.instSys P S.scs S.consStart)

/-- **The start sequence of the linked module**: the provider's start function, then the
consumer's (addresses in the linked store, where functions keep their addresses). -/
def linkedStarts : List Nat := S.provStart.toList ++ S.consStart.toList

/-- **The instantiable strategy of the linked module**: the linked module, closed, whose
instantiation runs its start sequence `linkedStarts` (`ScalarInstance.instSysSeq`). -/
noncomputable def linkedInstStrategy (P : Profile) :
    DStrategy (ifaceSig []) ((ifaceSig S.exportTypes).withInst (Behaviour Val)) :=
  DStrategy.ofInst (S.linkedI.instSysSeq P S.sl S.linkedStarts)

end StartSetup

/-- A start-free link as a link with absent start functions. -/
def Setup.noStart (S : Setup) : StartSetup where
  toSetup := S
  provStart := none
  consStart := none
  provStartTyped _ h := by cases h
  consStartTyped _ h := by cases h
  provStartFunc _ h := by cases h
  consStartFunc _ h := by cases h

end Silmaril.Wasm.Game.Linking
