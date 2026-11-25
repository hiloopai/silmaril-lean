module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep.Triple
public import Silmaril.Wasm.Component.Reference.HLinkedSessionObj.Thms

/-!
# The separating pair: equal host-realizable objects, different open objects

At the deterministic profiles `profile o`:

* `compSession_eq'`, `sep_compSession_eq`: the host-realizable session objects of `forgetL` and
  `rememberL` are equal (the bisimulation `Inv` of `Triple`);
* `sep_refSessEquivFull`: hence `RefSessEquivFull` (`refSessEquivFull_of_compSession`);
* `compTripleO_mem`, `compTripleO_refuse`, `compTripleO_ans`: the open triple of `sepL c`;
* `sep_compSessionO_ne`: the open objects differ. A bisimulation of the open triples would match
  `rememberL`'s refusal of `h()` by `forgetL`'s (whose global stays `0`), and then
  `rememberL`'s answer `1` to `f()` after `h()` is answered by an answer `1` of `forgetL`, which
  answers `0`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratSession (threadS)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.HLinkedSep
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Numerics (Profile)

variable {c : BitVec 32} {Ie : ScalarInstance} {o : GrowOracle}

/-! ## The session objects at the instances -/

theorem exists_inst (hc : sepSummary c = true) :
    ∃ Ie Ii : ScalarInstance, (sepL c).exp.mod.IsInst Ie ∧ (sepL c).imp.mod.IsInst Ii :=
  ⟨LinkedSessionIR.sgInst, sepInst c, LinkedSessionIR.sg_isInst, sep_isInst hc⟩

/-- The host-realizable object of `sepL c` is the threading of its triple at the importer's
instance. -/
theorem compSession_eq' (P : Profile) (hc : sepSummary c = true) :
    ∃ Ie : ScalarInstance, HLinked2.compSession P (sepL c) =
      threadS (HLinked2.compTripleS P (sepL c) Ie (sepInst c)) (sepStore c, Ie.store, []) := by
  have hex := exists_inst hc
  refine ⟨hex.choose, ?_⟩
  unfold HLinked2.compSession
  rw [dite_eq_left hex, ImpModule.IsInst.unique hex.choose_spec.choose_spec.2 (sep_isInst hc)]
  rfl

/-- The open object of `sepL c` is the threading of its open triple at the importer's
instance. -/
theorem compSessionO_eq' (P : Profile) (hc : sepSummary c = true) :
    ∃ Ie : ScalarInstance, HLinked2.compSessionO P (sepL c) =
      threadS (HLinked2.compTripleO P (sepL c) Ie (sepInst c)) (sepStore c, Ie.store) := by
  have hex := exists_inst hc
  refine ⟨hex.choose, ?_⟩
  unfold HLinked2.compSessionO
  rw [dite_eq_left hex, ImpModule.IsInst.unique hex.choose_spec.choose_spec.2 (sep_isInst hc)]
  rfl

/-! ## Equal host-realizable objects -/

/-- **The host-realizable objects of the pair are equal** (`profile o`). -/
theorem sep_compSession_eq :
    HLinked2.compSession (profile o) forgetL = HLinked2.compSession (profile o) rememberL := by
  obtain ⟨Ie, h⟩ := compSession_eq' (profile o) sepSummary_zero
  obtain ⟨Ie', h'⟩ := compSession_eq' (profile o) sepSummary_one
  show HLinked2.compSession (profile o) (sepL 0) = HLinked2.compSession (profile o) (sepL 1)
  rw [h, h']
  exact StratSession.threadS_eq_of_obsEq ⟨Inv 0 1, isBisim sepSummary_zero sepSummary_one,
    inv_init sepSummary_zero sepSummary_one Ie.store Ie'.store⟩

theorem forgetL_adequate : forgetL.Adequate := sepL_adequate sepSummary_zero

theorem rememberL_adequate : rememberL.Adequate := sepL_adequate sepSummary_one

theorem sep_sameTypes : HLinked2.SameTypes forgetL rememberL :=
  ⟨rfl, fun j => by match j with | ⟨0, _⟩ => rfl, rfl⟩

/-- **The pair is reference-equivalent** (`profile o`, every component choice profile). -/
theorem sep_refSessEquivFull (prof : ProfileKind) :
    HLinked2.RefSessEquivFull (profile o) prof forgetL rememberL :=
  HLinked2.refSessEquivFull_of_compSession forgetL_adequate rememberL_adequate sep_sameTypes
    (heq_of_eq sep_compSession_eq)

/-! ## The open triple -/

theorem mem_compTripleO {s : Store Nat × Store Nat} {q : Nat × Payload}
    {d : List (Call (HLinked2.hostSig (sepL c).host))}
    {e : End (Store Nat × Store Nat) (Payload ⊕ PUnit.{1})} :
    (d, e) ∈ (HLinked2.compTripleO (profile o) (sepL c) Ie (sepInst c)).1 s q ↔
      (d.map StratLegal.liftCall, e) ∈ HLinked2.compFinO (profile o) (sepL c) Ie (sepInst c) s q :=
  Iff.rfl

/-- **The finished behaviours of the open triple** on a typed call (deterministic profiles):
`h()` refused and a trap, or `h()` answered and the answer `v`. -/
theorem compTripleO_mem (hc : sepSummary c = true) {u π : Store Nat} {v : BitVec 32}
    (hu : SepSt c u v) {q : Nat × Payload} (hq : (sepL c).toL2.typedQ q ≠ none)
    {d : List (Call (HLinked2.hostSig (sepL c).host))}
    {e : End (Store Nat × Store Nat) (Payload ⊕ PUnit.{1})}
    (hx : (d, e) ∈ (HLinked2.compTripleO (profile o) (sepL c) Ie (sepInst c)).1 (u, π) q) :
    (d.map StratLegal.liftCall = [⟨mH c, none⟩] ∧
        e = .ret (.inr PUnit.unit) (u.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 c), π)) ∨
      (d.map StratLegal.liftCall = [⟨mH c, some (.vals [])⟩] ∧
        e = .ret (.inl (.vals [.u32 v]))
          ((u.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 c)).setGlobal 0
            (Silmaril.Wasm.Execution.Core.Val.i32 0), π)) := by
  have hx' := mem_compTripleO.mp hx
  simp only [HLinked2.compFinO, typed_eq hq] at hx'
  rcases hx' with ⟨r, u', π', hs, he⟩ | ⟨hd, -⟩
  · have hl : ∀ y ∈ (d.map StratLegal.liftCall).head?, y.2 = none ∨ y.2 = some (.vals []) := by
      intro y hy
      cases d with
      | nil => simp at hy
      | cons z zs =>
        simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        obtain ⟨m, a, ha⟩ := z
        cases a with
        | none => exact .inl rfl
        | some p => exact .inr (hostLegal_vals ha)
    obtain ⟨-, -, rfl, (⟨hH, rfl, rfl⟩ | ⟨hH, rfl, rfl⟩)⟩ := sess_eq hc hu hs hl
    · exact .inl ⟨hH, he⟩
    · exact .inr ⟨hH, he⟩
  · exact (not_roundDivC hc hu hd).elim

/-- The refusal of `h()` on the open interface. -/
def refuseLog (c : BitVec 32) : List (Call (HLinked2.hostSig (sepL c).host)) :=
  [⟨mH c, ⟨none, trivial⟩⟩]

/-- The answer of `h()` with no results on the open interface. -/
def ansLog (c : BitVec 32) : List (Call (HLinked2.hostSig (sepL c).host)) :=
  [⟨mH c, ⟨some (.vals []), rfl⟩⟩]

theorem compTripleO_refuse (hc : sepSummary c = true) {u π : Store Nat} {v : BitVec 32}
    (hu : SepSt c u v) {q : Nat × Payload} (hq : (sepL c).toL2.typedQ q ≠ none) :
    (refuseLog c, .ret (.inr PUnit.unit)
        (u.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 c), π)) ∈
      (HLinked2.compTripleO (profile o) (sepL c) Ie (sepInst c)).1 (u, π) q := by
  refine mem_compTripleO.mpr ?_
  simp only [HLinked2.compFinO, typed_eq hq]
  exact .inl ⟨none, _, π, sess_trap (profile o) hc hu π, rfl⟩

theorem compTripleO_ans (hc : sepSummary c = true) {u π : Store Nat} {v : BitVec 32}
    (hu : SepSt c u v) {q : Nat × Payload} (hq : (sepL c).toL2.typedQ q ≠ none) :
    (ansLog c, .ret (.inl (.vals [.u32 v]))
        ((u.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 c)).setGlobal 0
          (Silmaril.Wasm.Execution.Core.Val.i32 0), π)) ∈
      (HLinked2.compTripleO (profile o) (sepL c) Ie (sepInst c)).1 (u, π) q := by
  refine mem_compTripleO.mpr ?_
  simp only [HLinked2.compFinO, typed_eq hq]
  exact .inl ⟨some [.u32 v], _, π, sess_ans (profile o) hc hu π, rfl⟩

/-- The call `f()` is typed. -/
theorem typedQ_f : (sepL c).toL2.typedQ (0, .vals []) ≠ none := by
  intro h
  cases h

/-! ## Different open objects -/

/-- **The open triples of the pair are not bisimilar from their initial states** (`profile o`). -/
theorem threadS_compTripleO_ne {Ie Ie' : ScalarInstance} :
    threadS (HLinked2.compTripleO (profile o) (sepL 0) Ie (sepInst 0)) (sepStore 0, Ie.store) ≠
      threadS (HLinked2.compTripleO (profile o) (sepL 1) Ie' (sepInst 1))
        (sepStore 1, Ie'.store) := by
  intro h
  obtain ⟨Rel, hB, h0⟩ := (StratSession.threadS_eq_iff
    (HLinked2.storeDet_compTripleO (o := o) (l := sepL 0) (Ie := Ie) (Ii := sepInst 0))
    (HLinked2.storeDet_compTripleO (o := o) (l := sepL 1) (Ie := Ie') (Ii := sepInst 1))
    (HLinked2.noPlainTrap_compTripleO (P := profile o) (l := sepL 0) (Ie := Ie) (Ii := sepInst 0))
    (HLinked2.noPlainTrap_compTripleO (P := profile o) (l := sepL 1) (Ie := Ie')
      (Ii := sepInst 1))).mp h
  have hu₁ : SepSt 1 (sepStore 1) 0 := sepSt_init sepSummary_one
  have hu₀ : SepSt 0 (sepStore 0) 0 := sepSt_init sepSummary_zero
  obtain ⟨s₀', hm₀, hR₀⟩ := (hB _ _ h0).ret' (0, .vals []) (refuseLog 1) (.inr PUnit.unit) _
    (compTripleO_refuse sepSummary_one hu₁ typedQ_f)
  obtain ⟨s₀, π₀⟩ := s₀'
  rcases compTripleO_mem sepSummary_zero hu₀ typedQ_f hm₀ with ⟨-, he⟩ | ⟨hH, -⟩
  · simp only [End.ret.injEq, Prod.mk.injEq, true_and] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨s₀'', hm₁, -⟩ := (hB _ _ hR₀).ret' (0, .vals []) (ansLog 1)
      (.inl (.vals [.u32 1])) _ (compTripleO_ans sepSummary_one (sepSt_set hu₁ 1) typedQ_f)
    rcases compTripleO_mem sepSummary_zero (sepSt_set hu₀ 0) typedQ_f hm₁ with ⟨hH, -⟩ | ⟨-, he⟩
    · have h2 : ([⟨mH 1, some (.vals [])⟩] : List (Call (sigN (sepL 1).host.length))) =
          [⟨mH 0, none⟩] := hH
      have h3 := congrArg (fun L : List (Call (sigN (sepL 1).host.length)) =>
        L.head?.bind (·.2)) h2
      simp at h3
    · simp only [End.ret.injEq, Sum.inl.injEq, Payload.vals.injEq, List.cons.injEq, and_true]
        at he
      exact absurd (Silmaril.Wasm.Component.Val.u32.inj he.1) (by decide)
  · have h2 : ([⟨mH 1, none⟩] : List (Call (sigN (sepL 1).host.length))) =
        [⟨mH 0, some (.vals [])⟩] := hH
    have h3 := congrArg (fun L : List (Call (sigN (sepL 1).host.length)) =>
      L.head?.bind (·.2)) h2
    simp at h3

/-- **The open objects of the pair differ** (`profile o`). -/
theorem sep_compSessionO_ne :
    HLinked2.compSessionO (profile o) forgetL ≠ HLinked2.compSessionO (profile o) rememberL := by
  obtain ⟨Ie, h⟩ := compSessionO_eq' (profile o) sepSummary_zero
  obtain ⟨Ie', h'⟩ := compSessionO_eq' (profile o) sepSummary_one
  show HLinked2.compSessionO (profile o) (sepL 0) ≠ HLinked2.compSessionO (profile o) (sepL 1)
  rw [h, h']
  exact threadS_compTripleO_ne

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep
