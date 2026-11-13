module

public import Silmaril.Wasm.Resource.Link.Defs
public import Silmaril.Wasm.Resource.Protocol.Thms
public import Silmaril.Wasm.Logic.GameLink.Thms
public import Silmaril.Wasm.Logic.Open.Thms
public import Silmaril.Wasm.Game.DivAdequacy.Thms
public import Silmaril.Wasm.Spec.Wasm.Defs

/-!
# Protocols and the Wasm game: soundness

* `LTSInv.run`, `LTSInv.accepts`: a protocol invariant of a transition system makes every play
  of its strategy accepted (with `OTotal` for the plays receptivity adds).
* `dlts_accepts`: for the transition system `I.dlts P s` of a scalar instance (host-free Core
  steps silent, every profile), every play of `I.strategy P s` is accepted.
* `models_of_plays`, `not_models_of_play`: plays and sentences of `protoLogic` over
  `wasmSem P`.
* `provider_sound`: the provider verification condition `ProvSat` (the every-run program logic
  of `Silmaril.Wasm.Logic`, one triple per export and protocol state) gives a protocol invariant of
  `I.dlts P s`, hence acceptance of every play. The invariant follows
  `Silmaril.Proofs.Wasm.Logic.GameLink.Strategy` (`Good`), with the protocol state as an index.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Logic.GameLink Silmaril.Wasm.Spec
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (Thread resumeResult)
open Silmaril.Wasm.Logic.Strategy (ISpec resultOutcome)
open Silmaril.Wasm.Logic.Hoare (Safe callPost)
open Silmaril.Wasm.Logic.Core (Post)

/-! ## Protocol invariants of transition systems -/

section
variable {E F : Sig.{0}} {S : Type} {L : LTS E F} {π : Protocol S (Move E F)}

/-- Runs from an invariant state are accepted and end in an invariant state. -/
theorem LTSInv.run (Φ : LTSInv L π) {x y : L.State} {s : List (Move E F)} (hr : L.Run x s y) :
    ∀ {q}, Φ.J q x → ∃ q', π.run q s = some q' ∧ Φ.J q' y := by
  induction hr with
  | nil x => exact fun hq => ⟨_, rfl, hq⟩
  | tau hs _ ih => exact fun hq => ih (Φ.tau hs hq)
  | vis hs _ ih =>
    intro q hq
    obtain ⟨q', h1, h2⟩ := Φ.vis hs hq
    obtain ⟨q'', h3, h4⟩ := ih h2
    exact ⟨q'', by simp [Protocol.run_cons, h1, h3], h4⟩

/-- The traces of the system are accepted. -/
theorem LTSInv.accepts_traces (Φ : LTSInv L π) {s : List (Move E F)} (hs : s ∈ L.Traces) :
    π.Accepts s := by
  obtain ⟨y, hy⟩ := hs
  obtain ⟨q, hq, -⟩ := Φ.run hy Φ.init
  exact (π.accepts_iff_exists s).2 ⟨q, hq⟩

/-- **Every play of the strategy of the system is accepted.** -/
theorem LTSInv.accepts (Φ : LTSInv L π) (hO : OTotal π) :
    ∀ p ∈ Strategy.ofLTS L, π.Accepts p := by
  rintro p ⟨-, u, hu, hp⟩
  have hu' : π.Accepts u := by
    rcases hu with rfl | ⟨hu, -⟩
    · exact π.accepts_nil
    · exact Φ.accepts_traces hu
  rcases hp with hp | ⟨p₀, o, rfl, hp₀, ho⟩
  · exact Protocol.Accepts.of_prefix hu' hp
  · obtain ⟨q, hq⟩ := (π.accepts_iff_exists p₀).1 (Protocol.Accepts.of_prefix hu' hp₀)
    exact (π.accepts_concat_iff p₀ o).2 ⟨q, hq, Option.isSome_iff_exists.1 (hO q o ho)⟩

end

/-! ## Scalar instances -/

/-- **Every play of a scalar instance is accepted** given a protocol invariant of its
transition system with silent host-free steps (every profile). -/
theorem dlts_accepts {S : Type} {I : ScalarInstance} {P : Profile} {s : Store Nat}
    {π : Protocol S (Move I.E I.F)} (Φ : LTSInv (I.dlts P s) π) (hO : OTotal π) :
    ∀ p ∈ I.strategy P s, π.Accepts p := by
  rw [← ScalarInstance.forget_dstrategy P s]
  exact Φ.accepts hO

section
variable {S : Type} {P : Profile} {X : WIface}

/-- A sentence of the protocol logic holds of a Wasm program when its plays are accepted. -/
theorem models_of_plays (p : WasmProg X) (φ : Protocol S (WEvent X))
    (h : ∀ m ∈ p.inst.strategy P p.store, (φ.comap moveEvent).Accepts m) :
    Models (protoLogic FnType (List Val) (Behaviour Val) S) (wasmSem P) p φ := by
  rw [models_protoLogic_iff]
  rintro t ⟨m, hm, rfl⟩
  exact (φ.accepts_comap _ _).1 (h m hm)

/-- **Refutation by a play**: a play whose events the protocol rejects. -/
theorem not_models_of_play (p : WasmProg X) (φ : Protocol S (WEvent X))
    {m : List (Move (ifaceSig X.imports) (ifaceSig X.exports))}
    (hm : m ∈ p.inst.strategy P p.store) (hrej : φ.acceptsB (m.map moveEvent) = false) :
    ¬ Models (protoLogic FnType (List Val) (Behaviour Val) S) (wasmSem P) p φ :=
  not_models_of_trace (wasmSem P) p φ ⟨m, hm, rfl⟩ hrej

end

/-! ## Providers -/

section Provider
variable {S : Type} {I : ScalarInstance} {P : Profile} {π : Protocol S (Move I.E I.F)}
  {Inv : S → Store Nat → Prop}

/-- The postcondition of a run answering the export question `f` asked in store `s₀`, in
protocol state `q₁`. -/
abbrev provPost (I : ScalarInstance) (π : Protocol S (Move I.E I.F)) (Inv : S → Store Nat → Prop)
    (q₁ : S) (f : I.F.Op) (s₀ : Store Nat) : Post Nat :=
  callPost {} [] ((provSpec I π Inv q₁ f.1).post s₀ f.2.1)

/-- The most general environment. -/
abbrev topHost (I : ScalarInstance) : HostSemantics Nat := gameHost I (ISpec.top I.E)

/-- **The provider invariant**: the store meets `Inv q` when idle; a running or waiting thread
is safe for the provider postcondition in the current protocol state. -/
def ProvJ (P : Profile) (I : ScalarInstance) (π : Protocol S (Move I.E I.F))
    (Inv : S → Store Nat → Prop) : S → I.HState → Prop
  | q, .idle s => Inv q s
  | q, .running f s t => ∃ s₀, ∀ n, Safe P (topHost I) (provPost I π Inv q f s₀) n (t.config s)
  | q, .waiting f s t e => ∃ s₀, ∀ v : I.E.Ar e, ∀ n,
      Safe P (topHost I) (provPost I π Inv q f s₀) n
        ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) v)).config s)

/-- A finished safe thread answers as the provider specification requires. -/
theorem prov_final {q : S} {f : I.F.Op} {s₀ s : Store Nat} {t : Thread} {r : Result}
    {v : I.F.Ar f} (hsafe : Safe P (topHost I) (provPost I π Inv q f s₀) 1 (t.config s))
    (final : ResultAt s t r) (answer : Answer.ofResult? (I.exports.get f.1) r = some v) :
    ∃ q₂, π.step q (.inr (.ans f v)) = some q₂ ∧ Inv q₂ s := by
  have hcode : (t.config s).code = r.toAdmin := final
  have hc : t.config s = ⟨s, (t.config s).frame, r.toAdmin⟩ :=
    calc t.config s = ⟨(t.config s).store, (t.config s).frame, (t.config s).code⟩ := rfl
      _ = ⟨s, (t.config s).frame, r.toAdmin⟩ := by rw [config_store, hcode]
  have hsafe' : Safe P (topHost I) (provPost I π Inv q f s₀) 1
      ⟨s, (t.config s).frame, r.toAdmin⟩ := hc ▸ hsafe
  have hpost := Silmaril.Wasm.Logic.Open.final_post hsafe'
  have hv : v.toResult = r := Answer.toResult_of_ofResult? answer
  exact hpost f.2.2 v (by rw [hv])

/-- One visible step of the provider invariant. -/
theorem prov_vis (hm : ProvSat I π Inv P) (hn : ImportNeutral π) (hO : OTotal π) {q : S}
    {x y : I.HState} {o : Move I.E I.F} (hs : I.DTrans P x (some o) y)
    (hx : ProvJ P I π Inv q x) : ∃ q', π.step q o = some q' ∧ ProvJ P I π Inv q' y := by
  cases hs with
  | call s f =>
    obtain ⟨q₁, hq₁⟩ := Option.isSome_iff_exists.1 (hO q (.inr (.ask f)) trivial)
    refine ⟨q₁, hq₁, s, fun n => ?_⟩
    obtain ⟨j, args, ht⟩ := f
    exact hm q₁ j n s args ⟨q, hx, ht, hq₁⟩ {} [] _ trivial
  | ucall callout op =>
    obtain ⟨s₀, h⟩ := hx
    obtain ⟨E, a, hd⟩ := callout
    exact ⟨q, hn.1 q _, s₀, fun v n =>
      (h (n + 1)).step_inv (resume_step hd (gameHost_answer (Ii := ISpec.top I.E) op trivial trivial))⟩
  | uret v =>
    obtain ⟨s₀, h⟩ := hx
    exact ⟨q, hn.2 q _ v, s₀, h v⟩
  | oret final answer =>
    obtain ⟨s₀, h⟩ := hx
    exact prov_final (h 1) final answer

/-- **The provider protocol invariant** of `I.dlts P s`. -/
def provInv (hm : ProvSat I π Inv P) (hn : ImportNeutral π) (hO : OTotal π) {s : Store Nat}
    (hs : Inv π.init s) : LTSInv (I.dlts P s) π where
  J := ProvJ P I π Inv
  init := hs
  tau := by
    intro q x y hst hx
    cases hst with
    | tau h =>
      obtain ⟨s₀, hsafe⟩ := hx
      exact ⟨s₀, fun n => (hsafe (n + 1)).step_inv (internal_step h)⟩
  vis := fun hst hx => prov_vis hm hn hO hst hx

/-- **Provider soundness** (every profile): if every export meets its provider specification
in every protocol state, then from a store meeting `Inv π.init` every play is accepted. -/
theorem provider_sound (hm : ProvSat I π Inv P) (hn : ImportNeutral π) (hO : OTotal π)
    {s : Store Nat} (hs : Inv π.init s) : ∀ p ∈ I.strategy P s, π.Accepts p :=
  dlts_accepts (provInv hm hn hO hs) hO

end Provider

end Silmaril.Wasm.Resource
