module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep.Core
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.Det
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp.Det

/-!
# The separating pair: the rounds of a session call

For `sepL c` at its importer's instance, from every store `u` of `SepSt c u v`:

* `sess_trap`, `sess_ans`: the specification rounds of `f` whose host call `h()` is refused (a
  trap, the global set to `c`) or answered with no results (the answer `v`, the global `0`);
* `sess_eq` (deterministic profiles): every round whose first host call has a legal answer is one
  of the two (`round_detH`);
* `not_roundDivC`, `not_roundInfC` (deterministic profiles): no round diverges and none makes
  infinitely many host calls (`sep_prefix`: the core instance makes at most one import call per
  export call, and always has a Proponent move while running).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.HLinkedSep
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR (unitFn i32Fn impRel_trap)
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj (HostCompat round_detH
  sessSpec_singleH)
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs (fOp_ext)
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink (pmove_eq)
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp (not_trans_of_divB)
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RImpRel" => Silmaril.Wasm.Component.Reference.ImpRel

variable {c : BitVec 32}

/-! ## The interface of `sepL c` -/

/-- The export `f` of `sepL c`. -/
def j0 (c : BitVec 32) : Fin (sepL c).imp.exports.length := ⟨0, Nat.zero_lt_one⟩

/-- **The host call `h()`** on the host interface of `sepL c`. -/
def mH (c : BitVec 32) : (sigN (sepL c).host.length).Op := (⟨0, Nat.zero_lt_one⟩, .vals [])

theorem exports_get (j : Fin (sepL c).imp.exports.length) :
    (sepL c).imp.exports[j] = ⟨"f", LinkedSession.u32Ty, 0⟩ := by
  match j with
  | ⟨0, _⟩ => rfl

theorem j_eq (j : Fin (sepL c).imp.exports.length) : j = j0 c :=
  Fin.ext (Nat.lt_one_iff.mp j.isLt)

theorem checkLower_nil {vs : List IVal} {xs : List Flat} (h : checkLower [] vs = some xs) :
    vs = [] ∧ xs = [] := by
  cases vs with
  | nil =>
    simp only [checkLower, ValTy.checkList, ite_true, Option.some.injEq] at h
    exact ⟨rfl, h ▸ rfl⟩
  | cons _ _ => simp [checkLower, ValTy.checkList] at h

/-- The core question of a well-formed round is `f()`. -/
theorem f_eq {j : Fin (sepL c).imp.exports.length} {vs : List IVal} {xs : List Flat}
    {f : (sepInst c).F.Op} (hck : checkLower (sepL c).imp.exports[j].ty.params vs = some xs)
    (hf₁ : f.1.val = (sepL c).imp.exports[j].core)
    (hf₂ : f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat) : vs = [] ∧ f = fQ c := by
  rw [exports_get] at hck hf₁
  obtain ⟨rfl, rfl⟩ := checkLower_nil hck
  exact ⟨rfl, fOp_ext hf₁ hf₂⟩

/-! ## Core import calls -/

/-- The only import question of the importer's instance is `h()`. -/
theorem hE_eq (e : (sepInst c).E.Op) : e = hE c := by
  obtain ⟨⟨i, hi⟩, ⟨args, ha⟩⟩ := e
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  obtain rfl : args = [] := List.forall₂_nil_left_iff.mp (ha : List.Forall₂ _ [] args)
  rfl

theorem payloadAnswer_ne_throw {ft : Silmaril.Wasm.Game.FnType} (A : Option Payload) (n : Nat) :
    payloadAnswer ft A ≠ .throw n := by
  unfold payloadAnswer
  split
  · split <;> simp
  · simp

/-- The answers of `h()` other than an exception: a trap, or no results. -/
theorem hAns_cases (a : (sepInst c).E.Ar (hE c)) (hn : ∀ n, a ≠ .throw n) :
    a = .trap ∨ a = hA c := by
  cases a with
  | values vs =>
    obtain ⟨l, hl⟩ := vs
    obtain rfl : l = [] := List.forall₂_nil_left_iff.mp (hl : List.Forall₂ _ [] l)
    exact .inr rfl
  | trap => exact .inl rfl
  | throw n => exact (hn n rfl).elim

/-- **A core import call of the importer** is `h()`, answered by a trap or with no results,
and it is the one component import call `h()`. -/
theorem impRel_sep {x : Σ e : (sepInst c).E.Op, (sepInst c).E.Ar e}
    {ds : List (Σ _ : (sigN (sepI c).imports.length).Op, Option Payload)}
    (h : RImpRel (sepI c) (sepInst c) x ds) :
    ∃ a : (sepInst c).E.Ar (hE c), x = ⟨hE c, a⟩ ∧ (a = .trap ∨ a = hA c) ∧
      ∃ R : Option Payload, ds = [⟨(⟨0, Nat.zero_lt_one⟩, .vals []), R⟩] := by
  obtain ⟨e, a⟩ := x
  obtain rfl := hE_eq e
  obtain ⟨nm, ft, A, hk, ha, hm⟩ := h
  simp only [sepI] at hk
  obtain ⟨rfl, rfl⟩ := hk
  refine ⟨a, rfl, hAns_cases a fun n hn => payloadAnswer_ne_throw A n (ha.trans hn), ?_⟩
  obtain ⟨-, R, rfl, -⟩ := hm
  exact ⟨R, rfl⟩

/-! ## The core plays, deterministic profiles -/

/-- The canonical transitions of `f`: the call of `h()` from the initial thread, its answer `a`,
and the answer of `f`. -/
theorem canon {o : GrowOracle} (hc : sepSummary c = true) {u : Store Nat} {v : BitVec 32}
    (hu : SepSt c u v) {a : (sepInst c).E.Ar (hE c)} (ha : a = .trap ∨ a = hA c) :
    ∃ (W Q q' : (sepInst c).HState) (w : (sepInst c).F.Ar (fQ c)),
      (sepInst c).Trans (profile o) (.running (fQ c) u ((sepInst c).initThread (fQ c)))
        (.inl (.ask (hE c))) W ∧
      (sepInst c).Trans (profile o) W (.inl (.ans (hE c) a)) Q ∧
      (sepInst c).Trans (profile o) Q (.inr (.ans (fQ c) w)) q' := by
  rcases ha with rfl | rfl
  · have hp : (sepInst c).Path (profile o) (.idle u)
        [.inr (.ask (fQ c)), .inl (.ask (hE c)), .inl (.ans (hE c) .trap),
          .inr (.ans (fQ c) .trap)] _ := sep_path_trap (profile o) hc hu
    cases hp with
    | cons t0 hp =>
      cases t0
      cases hp with
      | cons t1 hp =>
        cases hp with
        | cons t2 hp =>
          cases hp with
          | cons t3 _ => exact ⟨_, _, _, _, t1, t2, t3⟩
  · have hp : (sepInst c).Path (profile o) (.idle u)
        [.inr (.ask (fQ c)), .inl (.ask (hE c)), .inl (.ans (hE c) (hA c)),
          .inr (.ans (fQ c) (fA c v))] _ := sep_path_ans (profile o) hc hu
    cases hp with
    | cons t0 hp =>
      cases t0
      cases hp with
      | cons t1 hp =>
        cases hp with
        | cons t2 hp =>
          cases hp with
          | cons t3 _ => exact ⟨_, _, _, _, t1, t2, t3⟩

/-- **The core instance makes at most one import call per call of `f`, and has a Proponent move
whenever it runs** (deterministic profiles). -/
theorem sep_prefix {o : GrowOracle} (hc : sepSummary c = true) {u : Store Nat} {v : BitVec 32}
    (hu : SepSt c u v) :
    ∀ {cs : List (Σ e : (sepInst c).E.Op, (sepInst c).E.Ar e)}
      {dss : List (List (Σ _ : (sigN (sepI c).imports.length).Op, Option Payload))}
      {q : (sepInst c).HState}, List.Forall₂ (RImpRel (sepI c) (sepInst c)) cs dss →
      (sepInst c).Path (profile o) (.idle u) (.inr (.ask (fQ c)) :: callMoves cs) q →
      (∃ (m : Move (sepInst c).E (sepInst c).F) (q' : (sepInst c).HState),
        (sepInst c).Trans (profile o) q m q') ∧ cs.length ≤ 1 := by
  intro cs dss q hrel hp
  cases hrel with
  | nil =>
    obtain ⟨W, -, -, -, t1, -, -⟩ := canon (o := o) hc hu (.inl rfl)
    cases hp with
    | cons t0 hp =>
      cases t0
      cases hp
      exact ⟨⟨_, _, t1⟩, by simp⟩
  | @cons x ds cs' dss' hx hrest =>
    obtain ⟨a, rfl, ha, -⟩ := impRel_sep hx
    obtain ⟨W, Q, q', w, t1', t2', t3'⟩ := canon (o := o) hc hu ha
    cases hp with
    | cons t0 hp =>
      cases t0
      cases hp with
      | cons t1 hp =>
        obtain rfl := ScalarInstance.Trans.functional t1 t1'
        cases hp with
        | cons t2 hp =>
          obtain rfl := ScalarInstance.Trans.functional t2 t2'
          cases hrest with
          | nil =>
            cases hp
            exact ⟨⟨_, _, t3'⟩, by simp⟩
          | @cons y _ _ _ _ _ =>
            obtain ⟨e, n⟩ := y
            cases hp with
            | cons t4 _ =>
              have := (pmove_eq t4 t3' trivial).1
              simp at this

/-! ## The rounds -/

/-- The round of `f` whose host call is refused. -/
def trapR (c : BitVec 32) : Linked2.SessRound (sepL c).toL2 (sepInst c) where
  j := j0 c
  vs := []
  f := fQ c
  cs := [⟨hE c, .trap⟩]
  w := .trap
  dss := [[⟨(⟨0, Nat.zero_lt_one⟩, .vals []), none⟩]]

/-- The round of `f` whose host call is answered, `f` answering `v`. -/
def ansR (c v : BitVec 32) : Linked2.SessRound (sepL c).toL2 (sepInst c) where
  j := j0 c
  vs := []
  f := fQ c
  cs := [⟨hE c, hA c⟩]
  w := fA c v
  dss := [[⟨(⟨0, Nat.zero_lt_one⟩, .vals []), some (.vals [])⟩]]

theorem trapR_ok : (trapR c).Ok :=
  ⟨[], rfl, rfl, rfl,
    .cons (impRel_trap (e := hE c) (nm := "h") (ft := LinkedSession.unitTy) rfl rfl) .nil⟩

theorem hA_impRel :
    RImpRel (sepI c) (sepInst c) ⟨hE c, hA c⟩ [⟨(⟨0, Nat.zero_lt_one⟩, .vals []), some (.vals [])⟩] := by
  refine ⟨"h", LinkedSession.unitTy, some (.flat []), rfl, ?_, ?_⟩
  · show payloadAnswer ((sepInst c).imports.get (hE c).1) (some (.flat [])) = hA c
    have ht : typed? ((sepInst c).imports.get (hE c).1).results
        (([] : List Flat).map Silmaril.Wasm.SingleThreaded.ofFlat) = some ⟨[], .nil⟩ := by
      unfold typed?
      exact dite_eq_left .nil
    unfold payloadAnswer
    dsimp only
    erw [ht]
    rfl
  · exact ⟨Nat.zero_lt_one, _, rfl, rfl⟩

theorem ansR_ok (v : BitVec 32) : (ansR c v).Ok :=
  ⟨[], rfl, rfl, rfl, .cons hA_impRel .nil⟩

variable {Ie : ScalarInstance}

/-- **The round of `f` with its host call refused** (every profile). -/
theorem sess_trap (P : Profile) (hc : sepSummary c = true) {u : Store Nat} {v : BitVec 32}
    (hu : SepSt c u v) (π : Store Nat) :
    HLinked2.SessSpec P (sepL c) Ie (sepInst c) u π [(j0 c, [])] [none] [[⟨mH c, none⟩]]
      (u.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 c)) π :=
  .round (trapR c) trapR_ok (sep_path_trap P hc hu) (.host ⟨0, Nat.zero_lt_one⟩ rfl (.nil π)) rfl
    (.nil _ _)

/-- **The round of `f` with its host call answered** (every profile). -/
theorem sess_ans (P : Profile) (hc : sepSummary c = true) {u : Store Nat} {v : BitVec 32}
    (hu : SepSt c u v) (π : Store Nat) :
    HLinked2.SessSpec P (sepL c) Ie (sepInst c) u π [(j0 c, [])] [some [.u32 v]]
      [[⟨mH c, some (.vals [])⟩]]
      ((u.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 c)).setGlobal 0
        (Silmaril.Wasm.Execution.Core.Val.i32 0)) π :=
  .round (ansR c v) (ansR_ok v) (sep_path_ans P hc hu) (.host ⟨0, Nat.zero_lt_one⟩ rfl (.nil π))
    rfl (.nil _ _)

theorem hostCompat_nil_right {n : Nat} : ∀ xs : List (Call (sigN n)), HostCompat xs []
  | [] => trivial
  | _ :: _ => trivial

/-- **Every round whose first host call is answered legally is one of the two** (deterministic
profiles). -/
theorem sess_eq {o : GrowOracle} (hc : sepSummary c = true) {u : Store Nat} {v : BitVec 32}
    (hu : SepSt c u v) {π u' π' : Store Nat} {j : Fin (sepL c).imp.exports.length}
    {vs : List IVal} {r : Option (List IVal)} {H : List (Call (sigN (sepL c).host.length))}
    (hs : HLinked2.SessSpec (profile o) (sepL c) Ie (sepInst c) u π [(j, vs)] [r] [H] u' π')
    (hl : ∀ x ∈ H.head?, x.2 = none ∨ x.2 = some (.vals [])) :
    j = j0 c ∧ vs = [] ∧ π' = π ∧
      ((H = [⟨mH c, none⟩] ∧ r = none ∧
          u' = u.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 c)) ∨
        (H = [⟨mH c, some (.vals [])⟩] ∧ r = some [.u32 v] ∧
          u' = (u.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 c)).setGlobal 0
            (Silmaril.Wasm.Execution.Core.Val.i32 0))) := by
  obtain rfl := j_eq j
  obtain ⟨d, hj, hv, ⟨xs, hck, hf₁, hf₂, -⟩, -⟩ := sessSpec_singleH hs
  obtain ⟨hvs, -⟩ := f_eq hck hf₁ hf₂
  rw [hv] at hvs
  subst hvs
  have ht := sess_trap (Ie := Ie) (profile o) hc hu π
  have ha := sess_ans (Ie := Ie) (profile o) hc hu π
  refine ⟨rfl, rfl, ?_⟩
  cases H with
  | nil =>
    obtain ⟨-, h, -, -⟩ := round_detH hs ht trivial
    cases h
  | cons x xs =>
    by_cases hx : x.1 = mH c
    · rcases hl x rfl with hn | hn
      · obtain ⟨rfl, hH, rfl, rfl⟩ := round_detH hs ht (fun _ => ⟨hx ▸ hn, hostCompat_nil_right xs⟩)
        exact ⟨rfl, .inl ⟨hH, rfl, rfl⟩⟩
      · obtain ⟨rfl, hH, rfl, rfl⟩ := round_detH hs ha (fun _ => ⟨hx ▸ hn, hostCompat_nil_right xs⟩)
        exact ⟨rfl, .inr ⟨hH, rfl, rfl⟩⟩
    · obtain ⟨-, h, -, -⟩ := round_detH hs ht (fun h => (hx h).elim)
      simp only [List.cons.injEq] at h
      exact (hx (by rw [h.1])).elim

theorem not_expRunT_cons {P : Profile} {s s' : Store Nat}
    {x : Σ _ : (sigN (sepL c).imp.imports.length).Op, Option Payload}
    {ds : List (Σ _ : (sigN (sepL c).imp.imports.length).Op, Option Payload)}
    (h : Linked2.ExpRunT P (sepL c).toL2 Ie s (x :: ds) s') : False := by
  cases h with
  | ret w hw _ _ => simp [sepL] at hw
  | trap w hw _ _ => simp [sepL] at hw

/-- **No round diverges** (deterministic profiles). -/
theorem not_roundDivC {o : GrowOracle} (hc : sepSummary c = true) {u : Store Nat} {v : BitVec 32}
    (hu : SepSt c u v) {π : Store Nat} {j : Fin (sepL c).imp.exports.length} {vs : List IVal}
    {H : List (Call (sigN (sepL c).host.length))} :
    ¬ HLinked2.RoundDivC (profile o) (sepL c) Ie (sepInst c) u π j vs H := by
  rintro ⟨d, s, t, π₁, -, -, ⟨xs, hck, hf₁, hf₂, hrel⟩, hp, -, -, hdiv⟩
  obtain ⟨-, hf⟩ := f_eq hck hf₁ hf₂
  have hp' : (sepInst c).Path (profile o) (.idle u) (.inr (.ask (fQ c)) :: callMoves d.cs)
      (.running d.f s t) := by
    rw [← hf]
    exact hp
  rcases hdiv with hb | ⟨e, -, -, -, -, -, w, -, -, -, hw, -⟩ | ⟨q, c', ds, st, -, -, hk⟩
  · obtain ⟨⟨m, q', hm⟩, -⟩ := sep_prefix hc hu hrel hp'
    exact not_trans_of_divB hb hm
  · simp [sepL] at hw
  · obtain ⟨-, hr0, he0⟩ := hk 0
    obtain ⟨-, -, -, R, hds⟩ := impRel_sep hr0
    rw [hds] at he0
    exact not_expRunT_cons he0

/-- **No round makes infinitely many host calls** (deterministic profiles). -/
theorem not_roundInfC {o : GrowOracle} (hc : sepSummary c = true) {u : Store Nat} {v : BitVec 32}
    (hu : SepSt c u v) {π : Store Nat} {j : Fin (sepL c).imp.exports.length} {vs : List IVal}
    {ω : ℕ → Call (sigN (sepL c).host.length)} :
    ¬ HLinked2.RoundInfC (profile o) (sepL c) Ie (sepInst c) u π j vs ω := by
  rintro ⟨f, xs, q, c', ds, πs, N, hck, hf₁, hf₂, hq0, -, -, hk, -⟩
  obtain ⟨-, rfl⟩ := f_eq hck hf₁ hf₂
  obtain ⟨hp0, hr0, -, -⟩ := hk 0
  obtain ⟨hp1, hr1, -, -⟩ := hk 1
  have hp : (sepInst c).Path (profile o) (.idle u)
      (.inr (.ask (fQ c)) :: callMoves [c' 0, c' 1]) (q (1 + 1)) :=
    Silmaril.Proofs.Wasm.Component.Reference.path_append
      (Silmaril.Proofs.Wasm.Component.Reference.path_append hq0 hp0) hp1
  obtain ⟨-, hlen⟩ := sep_prefix hc hu (.cons hr0 (.cons hr1 .nil)) hp
  simp at hlen

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep
