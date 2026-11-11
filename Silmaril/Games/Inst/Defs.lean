module

public import Silmaril.Games.DivLTS.Defs
public import Silmaril.Games.DivComp.Defs

/-!
# Instantiation phases

A Wasm module is not a server from the start: it is first *instantiated*
(segments are initialised and the start function runs, possibly calling
imports), and only then are its exports called, against the state that
instantiation left. Instantiation may succeed, fail (trap, link error, …) or
diverge. This module adds that phase to the games.

* `F.withInst R` (signature transformer): the operations of `F` (`some q`,
  export calls) plus one operation `inst` (`none`), answered by
  `InstAns R`: `ready`, or `fail r` with an outcome `r : R` (for Wasm,
  `R = Behaviour Val`: the trap or other result of the instantiation run).
  Divergence of instantiation is not an answer: it is divergence after
  `[askInst]`, observed by `DStrategy`.
* Readings of a strategy `δ : DStrategy E (F.withInst R)`:
  `δ.InstReady`, `δ.InstFails r`, `δ.InstDiverges`.
* `InstSystem E F R`: an operational component with an instantiation phase.
  Its instantiation run is a small-step reduction with import calls into `E`
  (`istep`, `icall`), ending `ready` with a persistent state or failing;
  export calls are then reductions from the persistent state (`start`,
  `step`, `call`) that return an answer and an updated state (`done`).
  `InstSystem.toLTS` is its transition system (export calls before
  instantiation, a second instantiation, and anything after a failure are
  refused: they stay unanswered), and `DStrategy.ofInst S` its
  divergence-observing strategy.
* **Linking.** A consumer whose imports are themselves instantiable,
  `InstSystem.consumerLTS S : LTS (E.withInst R) (F.withInst R)`, first
  instantiates its provider (a lower `inst` call) and only then runs its own
  instantiation; a provider failure `fail r` is propagated as `fail r`.
  `DStrategy.link δ S = δ.comp (ofLTS S.consumerLTS)` links a provider
  strategy `δ : DStrategy X (E.withInst R)` below the consumer: linking is
  composition, so it is monotone and inherits the unit laws of
  `Silmaril.Games.DivComp`.
-/

@[expose] public section

namespace Silmaril.Games

universe u

/-- Answers to the instantiation question. -/
inductive InstAns (R : Type u) : Type u
  /-- Instantiation succeeded; exports may now be called. -/
  | ready
  /-- Instantiation failed with outcome `r`. -/
  | fail (r : R)

/-- Answers of `F.withInst R`. -/
def Sig.withInstAr (F : Sig.{u}) (R : Type u) : Option F.Op → Type u
  | none => InstAns R
  | some q => F.Ar q

/-- The signature of an instantiable component exporting `F`: an extra
instantiation operation `none` answered by `InstAns R`, and export calls
`some q`. -/
def Sig.withInst (F : Sig.{u}) (R : Type u) : Sig.{u} := ⟨Option F.Op, F.withInstAr R⟩

namespace Inst

variable {E F : Sig.{u}} {R : Type u}

/-- Opponent asks to instantiate. -/
def askInst : Move E (F.withInst R) := .inr (.ask none)

/-- The component answers the instantiation question. -/
def ansInst (a : InstAns R) : Move E (F.withInst R) := .inr (.ans (m := none) a)

/-- Opponent calls the export `q`. -/
def askEx (q : F.Op) : Move E (F.withInst R) := .inr (.ask (some q))

/-- The component answers the export call `q`. -/
def ansEx (q : F.Op) (r : F.Ar q) : Move E (F.withInst R) := .inr (.ans (m := some q) r)

end Inst

open Inst

namespace DStrategy

variable {E F : Sig.{u}} {R : Type u}

/-- Instantiation may succeed. -/
def InstReady (δ : DStrategy E (F.withInst R)) : Prop := [askInst, ansInst .ready] ∈ δ.toStrategy

/-- Instantiation may fail with outcome `r`. -/
def InstFails (δ : DStrategy E (F.withInst R)) (r : R) : Prop :=
  [askInst, ansInst (.fail r)] ∈ δ.toStrategy

/-- Instantiation may diverge before any import call or answer. -/
def InstDiverges (δ : DStrategy E (F.withInst R)) : Prop := [askInst] ∈ δ.div

end DStrategy

/-- An operational component with an instantiation phase; see the module
documentation. -/
structure InstSystem (E F : Sig.{u}) (R : Type u) : Type (u + 1) where
  /-- Configurations of the instantiation run. -/
  IConf : Type u
  /-- The persistent state left by instantiation and updated by export calls. -/
  State : Type u
  /-- Configurations of an export call. -/
  Conf : F.Op → Type u
  /-- The initial configuration of instantiation. -/
  istart : IConf
  /-- Internal steps of instantiation. -/
  istep : IConf → IConf → Prop
  /-- `icall c m k`: instantiation calls the import `m` and continues with `k`. -/
  icall : IConf → (m : E.Op) → (E.Ar m → IConf) → Prop
  /-- Instantiation is done, leaving the state `st`. -/
  iready : IConf → State → Prop
  /-- Instantiation failed with outcome `r`. -/
  ifail : IConf → R → Prop
  /-- The initial configuration of the export call `q` in state `st`. -/
  start : (q : F.Op) → State → Conf q
  /-- Internal steps of export calls. -/
  step : {q : F.Op} → Conf q → Conf q → Prop
  /-- An export call calls the import `m`. -/
  call : {q : F.Op} → Conf q → (m : E.Op) → (E.Ar m → Conf q) → Prop
  /-- An export call returns `r`, leaving the state `st`. -/
  done : {q : F.Op} → Conf q → F.Ar q → State → Prop

namespace InstSystem

variable {E F : Sig.{u}} {R : Type u}

/-- States of the transition system of an `InstSystem`. -/
inductive St (S : InstSystem E F R) : Type u
  /-- Not yet instantiated. -/
  | fresh
  /-- Instantiating. -/
  | inst (c : S.IConf)
  /-- Instantiating, waiting for an import call to return. -/
  | iwait (m : E.Op) (k : E.Ar m → S.IConf)
  /-- Instantiated and idle. -/
  | ready (st : S.State)
  /-- Running the export call `q`. -/
  | run (q : F.Op) (c : S.Conf q)
  /-- Running `q`, waiting for an import call to return. -/
  | wait (q : F.Op) (m : E.Op) (k : E.Ar m → S.Conf q)
  /-- Instantiation failed; nothing else happens. -/
  | dead
  /-- (Linking) asked to instantiate; the provider must be instantiated first. -/
  | pstart
  /-- (Linking) waiting for the provider's instantiation. -/
  | pwait
  /-- (Linking) the provider failed with `r`; report it. -/
  | pfail (r : R)

/-- Transitions of the transition system of an `InstSystem`. -/
inductive Step (S : InstSystem E F R) : S.St → Option (Move E (F.withInst R)) → S.St → Prop
  | askInst : Step S .fresh (some askInst) (.inst S.istart)
  | itau {c c' : S.IConf} : S.istep c c' → Step S (.inst c) none (.inst c')
  | icall {c : S.IConf} {m : E.Op} {k : E.Ar m → S.IConf} :
      S.icall c m k → Step S (.inst c) (some (.inl (.ask m))) (.iwait m k)
  | iresume (m : E.Op) (k : E.Ar m → S.IConf) (n : E.Ar m) :
      Step S (.iwait m k) (some (.inl (.ans m n))) (.inst (k n))
  | iready {c : S.IConf} {st : S.State} : S.iready c st →
      Step S (.inst c) (some (ansInst .ready)) (.ready st)
  | ifail {c : S.IConf} {r : R} : S.ifail c r → Step S (.inst c) (some (ansInst (.fail r))) .dead
  | askEx (st : S.State) (q : F.Op) : Step S (.ready st) (some (askEx q)) (.run q (S.start q st))
  | tau {q : F.Op} {c c' : S.Conf q} : S.step c c' → Step S (.run q c) none (.run q c')
  | call {q : F.Op} {c : S.Conf q} {m : E.Op} {k : E.Ar m → S.Conf q} :
      S.call c m k → Step S (.run q c) (some (.inl (.ask m))) (.wait q m k)
  | resume (q : F.Op) (m : E.Op) (k : E.Ar m → S.Conf q) (n : E.Ar m) :
      Step S (.wait q m k) (some (.inl (.ans m n))) (.run q (k n))
  | ret {q : F.Op} {c : S.Conf q} {r : F.Ar q} {st : S.State} :
      S.done c r st → Step S (.run q c) (some (ansEx q r)) (.ready st)

/-- The transition system of an `InstSystem`. -/
@[reducible] def toLTS (S : InstSystem E F R) : LTS E (F.withInst R) := ⟨S.St, .fresh, S.Step⟩

/-- Transitions of the consumer transition system: imports are instantiable
(`E.withInst R`), and are instantiated first. -/
inductive LinkStep (S : InstSystem E F R) :
    S.St → Option (Move (E.withInst R) (F.withInst R)) → S.St → Prop
  | askInst : LinkStep S .fresh (some (.inr (.ask none))) .pstart
  | pcall : LinkStep S .pstart (some (.inl (.ask none))) .pwait
  | pready : LinkStep S .pwait (some (.inl (.ans (m := none) .ready))) (.inst S.istart)
  | pfail (r : R) : LinkStep S .pwait (some (.inl (.ans (m := none) (.fail r)))) (.pfail r)
  | preport (r : R) : LinkStep S (.pfail r) (some (.inr (.ans (m := none) (.fail r)))) .dead
  | itau {c c' : S.IConf} : S.istep c c' → LinkStep S (.inst c) none (.inst c')
  | icall {c : S.IConf} {m : E.Op} {k : E.Ar m → S.IConf} :
      S.icall c m k → LinkStep S (.inst c) (some (.inl (.ask (some m)))) (.iwait m k)
  | iresume (m : E.Op) (k : E.Ar m → S.IConf) (n : E.Ar m) :
      LinkStep S (.iwait m k) (some (.inl (.ans (m := some m) n))) (.inst (k n))
  | iready {c : S.IConf} {st : S.State} : S.iready c st →
      LinkStep S (.inst c) (some (.inr (.ans (m := none) .ready))) (.ready st)
  | ifail {c : S.IConf} {r : R} : S.ifail c r →
      LinkStep S (.inst c) (some (.inr (.ans (m := none) (.fail r)))) .dead
  | askEx (st : S.State) (q : F.Op) :
      LinkStep S (.ready st) (some (.inr (.ask (some q)))) (.run q (S.start q st))
  | tau {q : F.Op} {c c' : S.Conf q} : S.step c c' → LinkStep S (.run q c) none (.run q c')
  | call {q : F.Op} {c : S.Conf q} {m : E.Op} {k : E.Ar m → S.Conf q} :
      S.call c m k → LinkStep S (.run q c) (some (.inl (.ask (some m)))) (.wait q m k)
  | resume (q : F.Op) (m : E.Op) (k : E.Ar m → S.Conf q) (n : E.Ar m) :
      LinkStep S (.wait q m k) (some (.inl (.ans (m := some m) n))) (.run q (k n))
  | ret {q : F.Op} {c : S.Conf q} {r : F.Ar q} {st : S.State} :
      S.done c r st → LinkStep S (.run q c) (some (.inr (.ans (m := some q) r))) (.ready st)

/-- The consumer transition system of an `InstSystem` whose imports are
provided by an instantiable component. -/
@[reducible] def consumerLTS (S : InstSystem E F R) : LTS (E.withInst R) (F.withInst R) :=
  ⟨S.St, .fresh, S.LinkStep⟩

end InstSystem

namespace DStrategy

variable {X E F : Sig.{u}} {R : Type u}

/-- The divergence-observing strategy of an `InstSystem`. -/
def ofInst (S : InstSystem E F R) : DStrategy E (F.withInst R) := ofLTS S.toLTS

/-- Linking: the provider `δ` serves the instantiable imports of the consumer
`S`, which instantiates `δ` before itself. -/
def link (δ : DStrategy X (E.withInst R)) (S : InstSystem E F R) : DStrategy X (F.withInst R) :=
  δ.comp (ofLTS S.consumerLTS)

end DStrategy

end Silmaril.Games
