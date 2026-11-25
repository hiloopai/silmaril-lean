module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep.Round
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.Bisim2

/-!
# The separating pair: the host-realizable triples are bisimilar

For `sepL c` at its importer's instance (deterministic profiles):

* `compFin_mem`: the finished behaviours of one session call at `(u, π, R)` (`R` the refusals
  since the last answer, `[]` or `[h()]`): an untyped question traps at once; a typed call, with
  `h()` refused since the last answer, traps with no visible host call (the refusal is forced and
  hidden), otherwise it refuses `h()` and traps, or `h()` is answered and `f` answers the global;
  `compFin_*`: each of these is a behaviour; `compInf_empty`: no host chatter;
* `Inv c c'`: the same refusals, and the global `0` on both sides while nothing is refused;
  `isBisim`: it is a bisimulation of the host-realizable triples of `sepL c` and `sepL c'`. With
  `h()` refused since the last answer neither side shows the global again, so the constant `c`
  is invisible.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread (IsBisim)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.HLinkedSep
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

variable {c c' : BitVec 32} {Ie Ie' : ScalarInstance} {o : GrowOracle}

/-! ## Questions and host answers -/

theorem typedQ_vals {q : Nat × Payload} {j : Fin (sepL c).imp.exports.length} {vs : List IVal}
    (h : (sepL c).toL2.typedQ q = some (j, vs)) : vs = [] := by
  obtain ⟨n, p⟩ := q
  cases p with
  | flat _ => simp [Linked2.typedQ] at h
  | vals ws =>
    simp only [Linked2.typedQ] at h
    split_ifs at h with h1 h2
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain rfl : n = 0 := Nat.lt_one_iff.mp h1
    cases ws with
    | nil => rfl
    | cons _ _ =>
      simp [sepL, sepI, LinkedSession.u32Ty, ValTy.checkList] at h2

theorem typedQ_none_iff {q : Nat × Payload} :
    (sepL c).toL2.typedQ q = none ↔ (sepL c').toL2.typedQ q = none := Iff.rfl

theorem hostLegal_vals {m : (sigN (sepL c).host.length).Op} {p : Payload}
    (h : HLinked2.hostLegal (sepL c).host m (some p)) : some p = some (.vals []) := by
  obtain ⟨⟨i, hi⟩, _⟩ := m
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  cases p with
  | vals us =>
    cases us with
    | nil => rfl
    | cons _ _ =>
      simp [HLinked2.hostLegal, sepL, LinkedSession.hostIface, LinkedSession.unitTy,
        ValTy.checkList] at h
  | flat _ => exact (h : False).elim

theorem visRun_head {R R' : List (sigN (sepL c).host.length).Op}
    {y : Call (sigN (sepL c).host.length)} {ys : List (Call (sigN (sepL c).host.length))}
    (h : HLinked2.VisRun (sepL c).host R (y :: ys) R') : y.2 = none ∨ y.2 = some (.vals []) := by
  cases h with
  | refuse _ _ => exact .inl rfl
  | answer _ hl _ => exact .inr (hostLegal_vals hl)

theorem not_forced : ¬ HLinked2.Forced (sepL c).host [] (mH c) := by
  rintro (h | h)
  · exact List.not_mem_nil h
  · exact h ⟨[], rfl⟩

theorem forced_iff {R : List (sigN (sepL c).host.length).Op}
    (h : HLinked2.Forced (sepL c).host R (mH c)) : mH c ∈ R := by
  rcases h with h | h
  · exact h
  · exact (h ⟨[], rfl⟩).elim

/-! ## The finished behaviours -/

/-- **The finished behaviours of one session call** of `sepL c` (deterministic profiles). -/
theorem compFin_mem (hc : sepSummary c = true) {u π : Store Nat}
    {R : List (sigN (sepL c).host.length).Op} {v : BitVec 32} (hu : SepSt c u v)
    (hR : R = [] ∨ R = [mH c]) {q : Nat × Payload}
    {x : List (Call (sigN (sepL c).host.length)) × End (sepL c).St (Payload ⊕ PUnit.{1})}
    (hx : x ∈ HLinked2.compFin (profile o) (sepL c) Ie (sepInst c) (u, π, R) q) :
    ((sepL c).toL2.typedQ q = none ∧ x = ([], .ret (.inr PUnit.unit) (u, π, R))) ∨
    ((sepL c).toL2.typedQ q ≠ none ∧
      ((R = [mH c] ∧ x = ([], .ret (.inr PUnit.unit) (u.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 c), π, R))) ∨
        (R = [] ∧ x = ([⟨mH c, none⟩],
          .ret (.inr PUnit.unit) (u.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 c), π, [mH c]))) ∨
        (R = [] ∧ x = ([⟨mH c, some (.vals [])⟩], .ret (.inl (.vals [.u32 v]))
          ((u.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 c)).setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 0), π, []))))) := by
  cases hq : (sepL c).toL2.typedQ q with
  | none =>
    simp only [HLinked2.compFin, hq, Set.mem_singleton_iff] at hx
    exact .inl ⟨rfl, hx⟩
  | some jv =>
    obtain ⟨j, vs⟩ := jv
    simp only [HLinked2.compFin, hq] at hx
    refine .inr ⟨by simp, ?_⟩
    obtain ⟨xc, xe⟩ := x
    rcases hx with ⟨r, u', π', R', hs, hv, he⟩ | ⟨m, u', π', R', hs, hv, hf, he⟩ | ⟨R', hd, -, -⟩
    · simp only at hs hv he
      have hl : ∀ y ∈ xc.head?, y.2 = none ∨ y.2 = some (.vals []) := by
        intro y hy
        cases xc with
        | nil => simp at hy
        | cons z zs =>
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          subst hy
          exact visRun_head hv
      obtain ⟨-, -, rfl, (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)⟩ := sess_eq hc hu hs hl
      · cases hv with
        | refuse hnf hv' =>
          cases hv'
          rcases hR with rfl | rfl
          · rw [he]
            exact .inr (.inl ⟨rfl, rfl⟩)
          · exact (hnf (.inl (List.mem_singleton_self _))).elim
      · cases hv with
        | answer hnm _ hv' =>
          cases hv'
          rcases hR with rfl | rfl
          · rw [he]
            exact .inr (.inr ⟨rfl, rfl⟩)
          · exact (hnm (List.mem_singleton_self _)).elim
    · simp only at hs hv hf he
      have hl : ∀ y ∈ (xc ++ [(⟨m, none⟩ : Call (sigN (sepL c).host.length))]).head?,
          y.2 = none ∨ y.2 = some (.vals []) := by
        intro y hy
        cases xc with
        | nil =>
          simp only [List.nil_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          subst hy
          exact .inl rfl
        | cons z zs =>
          simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          subst hy
          exact visRun_head hv
      obtain ⟨-, -, rfl, (⟨hH, -, rfl⟩ | ⟨hH, -, -⟩)⟩ := sess_eq hc hu hs hl
      · cases xc with
        | nil =>
          simp only [List.nil_append, List.cons.injEq, and_true] at hH
          cases hv
          have hm : m = mH c := congrArg Sigma.fst hH
          subst hm
          have hmem := forced_iff hf
          rcases hR with rfl | rfl
          · exact (List.not_mem_nil hmem).elim
          · rw [he]
            exact .inl ⟨rfl, rfl⟩
        | cons z zs => simp at hH
      · cases xc with
        | nil => simp at hH
        | cons z zs => simp at hH
    · exact (not_roundDivC hc hu hd).elim

theorem compFin_untyped {u π : Store Nat} {R : List (sigN (sepL c).host.length).Op}
    {q : Nat × Payload} (hq : (sepL c).toL2.typedQ q = none) :
    (([], .ret (.inr PUnit.unit) (u, π, R)) :
        List (Call (sigN (sepL c).host.length)) × End (sepL c).St (Payload ⊕ PUnit.{1})) ∈
      HLinked2.compFin (profile o) (sepL c) Ie (sepInst c) (u, π, R) q := by
  simp only [HLinked2.compFin, hq]
  rfl

theorem typed_eq {q : Nat × Payload} (hq : (sepL c).toL2.typedQ q ≠ none) :
    (sepL c).toL2.typedQ q = some (j0 c, []) := by
  obtain ⟨⟨j, vs⟩, hq'⟩ := Option.ne_none_iff_exists'.mp hq
  obtain rfl := typedQ_vals hq'
  obtain rfl := j_eq j
  exact hq'

theorem compFin_forced (hc : sepSummary c = true) {u π : Store Nat} {v : BitVec 32}
    (hu : SepSt c u v) {q : Nat × Payload} (hq : (sepL c).toL2.typedQ q ≠ none) :
    (([], .ret (.inr PUnit.unit) (u.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 c), π, [mH c])) :
        List (Call (sigN (sepL c).host.length)) × End (sepL c).St (Payload ⊕ PUnit.{1})) ∈
      HLinked2.compFin (profile o) (sepL c) Ie (sepInst c) (u, π, [mH c]) q := by
  simp only [HLinked2.compFin, typed_eq hq]
  exact .inr (.inl ⟨mH c, _, π, [mH c], sess_trap (profile o) hc hu π, .nil _,
    .inl (List.mem_singleton_self _), rfl⟩)

theorem compFin_refuse (hc : sepSummary c = true) {u π : Store Nat} {v : BitVec 32}
    (hu : SepSt c u v) {q : Nat × Payload} (hq : (sepL c).toL2.typedQ q ≠ none) :
    (([⟨mH c, none⟩], .ret (.inr PUnit.unit) (u.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 c), π, [mH c])) :
        List (Call (sigN (sepL c).host.length)) × End (sepL c).St (Payload ⊕ PUnit.{1})) ∈
      HLinked2.compFin (profile o) (sepL c) Ie (sepInst c) (u, π, []) q := by
  simp only [HLinked2.compFin, typed_eq hq]
  exact .inl ⟨none, _, π, [mH c], sess_trap (profile o) hc hu π, .refuse not_forced (.nil _), rfl⟩

theorem compFin_ans (hc : sepSummary c = true) {u π : Store Nat} {v : BitVec 32}
    (hu : SepSt c u v) {q : Nat × Payload} (hq : (sepL c).toL2.typedQ q ≠ none) :
    (([⟨mH c, some (.vals [])⟩], .ret (.inl (.vals [.u32 v]))
        ((u.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 c)).setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 0), π, [])) :
        List (Call (sigN (sepL c).host.length)) × End (sepL c).St (Payload ⊕ PUnit.{1})) ∈
      HLinked2.compFin (profile o) (sepL c) Ie (sepInst c) (u, π, []) q := by
  simp only [HLinked2.compFin, typed_eq hq]
  exact .inl ⟨some [.u32 v], _, π, [], sess_ans (profile o) hc hu π,
    .answer (List.not_mem_nil) rfl (.nil _), rfl⟩

/-- **No host chatter** (deterministic profiles). -/
theorem compInf_empty (hc : sepSummary c = true) {s : (sepL c).St} {v : BitVec 32}
    (hu : SepSt c s.1 v) (q : Nat × Payload) :
    HLinked2.compInf (profile o) (sepL c) Ie (sepInst c) s q = ∅ := by
  ext ω
  simp only [HLinked2.compInf, Set.mem_empty_iff_false, iff_false]
  cases hq : (sepL c).toL2.typedQ q with
  | none => simp
  | some jv =>
    obtain ⟨j, vs⟩ := jv
    simp only [Set.mem_ofPred_eq, not_and]
    exact fun h => (not_roundInfC hc hu h).elim

/-! ## The bisimulation -/

theorem mem_compTripleS {s : (sepL c).St} {q : Nat × Payload}
    {d : List (Call (HLinked2.hostSig (sepL c).host))} {e : End (sepL c).St (Payload ⊕ PUnit.{1})} :
    (d, e) ∈ (HLinked2.compTripleS (profile o) (sepL c) Ie (sepInst c)).1 s q ↔
      (d.map StratLegal.liftCall, e) ∈ HLinked2.compFin (profile o) (sepL c) Ie (sepInst c) s q :=
  Iff.rfl

/-- **The relation of the bisimulation**: the same refusals since the last answer (none, or the
call `h()`), stores of the two importers' instances, and the global `0` on both sides while
nothing is refused. -/
def Inv (c c' : BitVec 32) (s : (sepL c).St) (s' : (sepL c').St) : Prop :=
  s.2.2 = s'.2.2 ∧ (s.2.2 = [] ∨ s.2.2 = [mH c]) ∧ (∃ v, SepSt c s.1 v) ∧
    (∃ v, SepSt c' s'.1 v) ∧ (s.2.2 = [] → SepSt c s.1 0 ∧ SepSt c' s'.1 0)

theorem inv_symm {s : (sepL c).St} {s' : (sepL c').St} (h : Inv c c' s s') : Inv c' c s' s := by
  obtain ⟨hR, hR', hu, hu', h0⟩ := h
  refine ⟨hR.symm, ?_, hu', hu, fun h => ⟨(h0 (hR.trans h)).2, (h0 (hR.trans h)).1⟩⟩
  rcases hR' with h | h
  · exact .inl (hR.symm.trans h)
  · exact .inr (hR.symm.trans h)

theorem inv_init (hc : sepSummary c = true) (hc' : sepSummary c') (π π' : Store Nat) :
    Inv c c' (sepStore c, π, []) (sepStore c', π', []) :=
  ⟨rfl, .inl rfl, ⟨0, sepSt_init hc⟩, ⟨0, sepSt_init hc'⟩,
    fun _ => ⟨sepSt_init hc, sepSt_init hc'⟩⟩

/-- **Every finished behaviour transfers along `Inv`** (deterministic profiles): it returns, and
the other side has the same calls and answer with related end states. -/
theorem fin_transfer (hc : sepSummary c = true) (hc' : sepSummary c') {s : (sepL c).St}
    {s' : (sepL c').St} (hI : Inv c c' s s') {q : Nat × Payload}
    {x : List (Call (sigN (sepL c).host.length)) × End (sepL c).St (Payload ⊕ PUnit.{1})}
    (hx : x ∈ HLinked2.compFin (profile o) (sepL c) Ie (sepInst c) s q) :
    ∃ (b : Payload ⊕ PUnit.{1}) (s₁ : (sepL c).St) (s₁' : (sepL c').St), x.2 = .ret b s₁ ∧
      (x.1, .ret b s₁') ∈ HLinked2.compFin (profile o) (sepL c') Ie' (sepInst c') s' q ∧
      Inv c c' s₁ s₁' := by
  obtain ⟨u, π, R⟩ := s
  obtain ⟨u', π', R'⟩ := s'
  obtain ⟨hRR, hR, ⟨v, hu⟩, ⟨v', hu'⟩, h0⟩ := hI
  simp only at hRR hR hu hu' h0
  subst hRR
  rcases hR with rfl | rfl
  · obtain ⟨hu0, hu0'⟩ := h0 rfl
    rcases compFin_mem hc hu0 (.inl rfl) hx with ⟨hq, rfl⟩ |
        ⟨hq, (⟨h, -⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩)⟩
    · exact ⟨_, _, (u', π', []), rfl, compFin_untyped (typedQ_none_iff.mp hq),
        ⟨rfl, .inl rfl, ⟨v, hu⟩, ⟨v', hu'⟩, h0⟩⟩
    · exact absurd h (List.cons_ne_nil _ _).symm
    · refine ⟨_, _, (u'.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 c'), π', [mH c']), rfl,
        compFin_refuse hc' hu0' (fun h => hq (typedQ_none_iff.mpr h)), ?_⟩
      exact ⟨rfl, .inr rfl, ⟨c, sepSt_set hu c⟩, ⟨c', sepSt_set hu' c'⟩,
        fun h => absurd h (List.cons_ne_nil _ _)⟩
    · refine ⟨_, _, ((u'.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 c')).setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 0), π', []), rfl,
        compFin_ans hc' hu0' (fun h => hq (typedQ_none_iff.mpr h)), ?_⟩
      exact ⟨rfl, .inl rfl, ⟨0, sepSt_set (sepSt_set hu c) 0⟩,
        ⟨0, sepSt_set (sepSt_set hu' c') 0⟩,
        fun _ => ⟨sepSt_set (sepSt_set hu c) 0, sepSt_set (sepSt_set hu' c') 0⟩⟩
  · rcases compFin_mem hc hu (.inr rfl) hx with ⟨hq, rfl⟩ |
        ⟨hq, (⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩)⟩
    · exact ⟨_, _, (u', π', [mH c']), rfl, compFin_untyped (typedQ_none_iff.mp hq),
        ⟨rfl, .inr rfl, ⟨v, hu⟩, ⟨v', hu'⟩, h0⟩⟩
    · refine ⟨_, _, (u'.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 c'), π', [mH c']), rfl,
        compFin_forced hc' hu' (fun h => hq (typedQ_none_iff.mpr h)), ?_⟩
      exact ⟨rfl, .inr rfl, ⟨c, sepSt_set hu c⟩, ⟨c', sepSt_set hu' c'⟩,
        fun h => absurd h (List.cons_ne_nil _ _)⟩
    · exact absurd h (List.cons_ne_nil _ _)
    · exact absurd h (List.cons_ne_nil _ _)

theorem satP_transfer (hc : sepSummary c = true) (hc' : sepSummary c') {s : (sepL c).St}
    {s' : (sepL c').St} (hI : Inv c c' s s') {a : Nat × Payload}
    {x : List (Call (sigN (sepL c).host.length)) × (sigN (sepL c).host.length).Op}
    (hx : x ∈ satP (HLinked2.compFin (profile o) (sepL c) Ie (sepInst c), fun _ _ => ∅,
      HLinked2.compInf (profile o) (sepL c) Ie (sepInst c)) s a) :
    x ∈ satP (HLinked2.compFin (profile o) (sepL c') Ie' (sepInst c'), fun _ _ => ∅,
      HLinked2.compInf (profile o) (sepL c') Ie' (sepInst c')) s' a := by
  obtain ⟨-, -, ⟨v, hu⟩, -, -⟩ := id hI
  rcases hx with hx | ⟨_, _, hd, _⟩ | ⟨d, e, hd, hp⟩ | ⟨ω, hω, -⟩
  · exact hx.elim
  · exact hd.elim
  · obtain ⟨b, s₁, s₁', -, h', -⟩ := fin_transfer (Ie' := Ie') hc hc' hI hd
    exact .inr (.inr (.inl ⟨d, _, h', hp⟩))
  · have e := compInf_empty (o := o) (Ie := Ie) hc hu a
    have hω' : ω ∈ HLinked2.compInf (profile o) (sepL c) Ie (sepInst c) s a := hω
    rw [e] at hω'
    exact hω'.elim

/-- **`Inv` is a bisimulation of the host-realizable triples** (deterministic profiles). -/
theorem isBisim (hc : sepSummary c = true) (hc' : sepSummary c') :
    IsBisim (HLinked2.compTripleS (profile o) (sepL c) Ie (sepInst c))
      (HLinked2.compTripleS (profile o) (sepL c') Ie' (sepInst c')) (Inv c c') := by
  intro s s' hI
  have hI' := inv_symm hI
  refine ⟨fun a d => ⟨fun h => ?_, fun h => ?_⟩, fun a d => ⟨fun h => ?_, fun h => ?_⟩, ?_, ?_,
    ?_, ?_⟩
  · have h' := mem_compTripleS.mp h
    obtain ⟨b, s₁, s₁', he, -, -⟩ := fin_transfer (Ie' := Ie') hc hc' hI h'
    cases he
  · have h' := mem_compTripleS.mp h
    obtain ⟨b, s₁, s₁', he, -, -⟩ := fin_transfer (Ie' := Ie) hc' hc hI' h'
    cases he
  · have h' := mem_compTripleS.mp h
    obtain ⟨b, s₁, s₁', he, -, -⟩ := fin_transfer (Ie' := Ie') hc hc' hI h'
    cases he
  · have h' := mem_compTripleS.mp h
    obtain ⟨b, s₁, s₁', he, -, -⟩ := fin_transfer (Ie' := Ie) hc' hc hI' h'
    cases he
  · funext a
    ext x
    have e1 := Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.satP_compTripleS
      (P := profile o) (l := sepL c) (Ie := Ie) (Ii := sepInst c) (s := s) (a := a) (x := x)
    have e2 := Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.satP_compTripleS
      (P := profile o) (l := sepL c') (Ie := Ie') (Ii := sepInst c') (s := s') (a := a) (x := x)
    exact e1.trans ((⟨satP_transfer hc hc' hI, satP_transfer hc' hc hI'⟩ : _ ↔ _).trans e2.symm)
  · obtain ⟨-, -, ⟨v, hu⟩, ⟨v', hu'⟩, -⟩ := id hI
    funext a
    ext ω
    have e := compInf_empty (o := o) (Ie := Ie) hc hu a
    have e' := compInf_empty (o := o) (Ie := Ie') hc' hu' a
    show (fun n => StratLegal.liftCall (ω n)) ∈ HLinked2.compInf (profile o) (sepL c) Ie
        (sepInst c) s a ↔
      (fun n => StratLegal.liftCall (ω n)) ∈ HLinked2.compInf (profile o) (sepL c') Ie'
        (sepInst c') s' a
    rw [e, e']
    exact Iff.rfl
  · intro a d b s₁ h
    have h₀ := mem_compTripleS.mp h
    obtain ⟨b', s₂, s₁', he, h', hI₁⟩ := fin_transfer (Ie' := Ie') hc hc' hI h₀
    cases he
    exact ⟨s₁', mem_compTripleS.mpr h', hI₁⟩
  · intro a d b s₁' h
    have h₀ := mem_compTripleS.mp h
    obtain ⟨b', s₂, s₁, he, h', hI₁⟩ := fin_transfer (Ie' := Ie) hc' hc hI' h₀
    cases he
    exact ⟨s₁, mem_compTripleS.mpr h', inv_symm hI₁⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep
