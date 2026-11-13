module

public import Silmaril.Proofs.Wasm.Game.Untyped.Adequacy
public import Silmaril.Proofs.Wasm.Game.Shared.Host

/-!
# The typed shared game as a view of the untyped game

For a scalar instance `I`, forgetting the typing of moves (`I.eraseMove`, injective on
operations and answers) relates the typed shared game of `Silmaril.Wasm.Game.Shared` to
the untyped game of `I.toU`:

* `mem_shStrategy_iff_erase`: **a typed play is a play of the typed shared strategy
  exactly when its erasure is a play of the untyped strategy**, for every profile and
  with no well-formedness: the untyped instance asks every callout, the typed one only
  well-typed ones, and a typed play only contains well-typed calls. Proved by a
  forward simulation along the state map `eraseState` and its converse
  (`back_step`), which is functional since erasure is injective.
* `shBehavioursOf_eq_erase`: at a well-formed store and against a well-formed typed
  environment `L`, the product behaviours against `L` are those against its untyped
  reading `L.erase` (every callout of a run is then a well-typed import call, so an
  unanswered call is silent in both).

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Untyped

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

variable {I : ScalarInstance} {P : Profile}

open Silmaril.Wasm.Game.ScalarInstance

/-! ### Erasure -/

/-- A typed call is its own interface operation. -/
theorem ifaceOp?_typed {ts : List FnType} (e : (ifaceSig ts).Op) :
    ifaceOp? ts e.1.val e.2.1 = some e := by
  obtain ⟨⟨i, hi⟩, ⟨vs, hvs⟩⟩ := e
  simp only [ifaceOp?, hi, hvs, ↓reduceDIte]

/-- Erasure of typed shared calls is injective. -/
theorem eraseOp_injective {ts : List FnType} {e e' : (sharedSig ts).Op}
    (h : eraseOp e = eraseOp e') : e = e' := by
  obtain ⟨⟨i, hi⟩, s, ⟨vs, hvs⟩⟩ := e
  obtain ⟨⟨i', hi'⟩, s', ⟨vs', hvs'⟩⟩ := e'
  obtain ⟨rfl, rfl, rfl⟩ : i = i' ∧ s = s' ∧ vs = vs' := by
    simpa only [eraseOp, UCall.mk.injEq] using h
  rfl

/-- The erasure of the shared call of a valid callout. -/
theorem eraseOp_shOp {ts : List FnType} {h : Nat} {args : List Val} {e : (ifaceSig ts).Op}
    (op : ifaceOp? ts h args = some e) (s : Store Nat) :
    eraseOp (shOp s e) = ⟨h, s, args⟩ := by
  show (⟨e.1.val, s, e.2.1⟩ : UCall Nat) = ⟨h, s, args⟩
  rw [ifaceOp?_fst op, Shared.ifaceOp?_snd op]

/-- The erasure of a hidden state of the typed shared instance. -/
def eraseState : I.ShState → I.toU.State
  | .idle => .idle
  | .running f s t => .running (I.eraseF f) s t
  | .waiting f s t e => .waiting (I.eraseF f) s t (eraseOp e)

/-! ### Forward simulation -/

/-- **A typed transition is an untyped transition of the erasures.** -/
theorem trans_erase {x y : I.ShState} {l : Option (Move I.shE I.shF)} (h : I.ShTrans P x l y) :
    I.toU.Trans P (eraseState x) (l.map I.eraseMove) (eraseState y) := by
  cases h with
  | call f => exact UInstance.Trans.call (I.eraseF f)
  | tau h => exact UInstance.Trans.tau h
  | @ucall f s t hh args e callout op =>
    have hco : CalloutAt s t e.1.val e.2.1 := by
      rw [ifaceOp?_fst op, Shared.ifaceOp?_snd op]
      exact callout
    exact UInstance.Trans.ucall (f := I.eraseF f) hco
  | uret s' v => exact UInstance.Trans.uret ⟨s', v.toResult⟩
  | @oret f s t r v final answer =>
    have hr : v.toResult = r := Answer.toResult_of_ofResult? answer
    have final' : ResultAt s t v.toResult := hr ▸ final
    exact UInstance.Trans.oret (f := I.eraseF f) final'

/-- Runs of the typed shared instance are runs of the untyped one along the erased play. -/
theorem run_erase {x y : (I.shLts P).State} {p : List (Move I.shE I.shF)} (h : (I.shLts P).Run x p y) :
    (I.toU.lts P).Run (eraseState x) (p.map I.eraseMove) (eraseState y) := by
  induction h with
  | nil x => exact .nil _
  | tau hs _ ih => exact .tau (trans_erase hs) ih
  | vis hs _ ih => exact .vis (trans_erase hs) ih

/-! ### Backward simulation -/

/-- An untyped silent transition from an erased state is the erasure of a typed one. -/
theorem back_tau {x : I.ShState} {y' : I.toU.State} (h : I.toU.Trans P (eraseState x) none y') :
    ∃ y, y' = eraseState y ∧ I.ShTrans P x none y := by
  cases x with
  | idle => cases h
  | running f s t =>
    cases h with
    | tau hi => exact ⟨.running f _ _, rfl, .tau hi⟩
  | waiting f s t e => cases h

/-- Backward step from an idle state. -/
theorem back_idle {m : Move I.shE I.shF} {y' : I.toU.State}
    (h : I.toU.Trans P .idle (some (I.eraseMove m)) y') :
    ∃ y, y' = eraseState y ∧ I.ShTrans P .idle (some m) y := by
  rcases m with (⟨e⟩ | ⟨e, a⟩) | (⟨f⟩ | ⟨f, a⟩)
  · cases h
  · cases h
  · cases h with
    | call => exact ⟨_, rfl, .call f⟩
  · cases h

/-- Backward step from a running state. -/
theorem back_running {f : I.shF.Op} {s : Store Nat} {t : Thread} {m : Move I.shE I.shF}
    {y' : I.toU.State} (h : I.toU.Trans P (.running (I.eraseF f) s t) (some (I.eraseMove m)) y') :
    ∃ y, y' = eraseState y ∧ I.ShTrans P (.running f s t) (some m) y := by
  rcases m with (⟨⟨⟨i, hi⟩, s₀, ⟨vs, hvs⟩⟩⟩ | ⟨e, a⟩) | (⟨f'⟩ | ⟨⟨⟨j, hj⟩, s₁, ⟨us, hus⟩⟩, ⟨s', w⟩⟩)
  · cases h with
    | ucall callout =>
      have op : I.importOp? i vs = some ⟨⟨i, hi⟩, ⟨vs, hvs⟩⟩ := ifaceOp?_typed ⟨⟨i, hi⟩, ⟨vs, hvs⟩⟩
      exact ⟨.waiting f _ t ⟨⟨i, hi⟩, _, ⟨vs, hvs⟩⟩, rfl, .ucall callout op⟩
  · cases h
  · cases h
  · obtain ⟨⟨j', hj'⟩, s₂, ⟨us', hus'⟩⟩ := f
    cases h with
    | oret final =>
      exact ⟨.idle, rfl, .oret final (Answer.ofResult?_toResult w)⟩

/-- Backward step from a waiting state. -/
theorem back_waiting {f : I.shF.Op} {s : Store Nat} {t : Thread} {e : I.shE.Op}
    {m : Move I.shE I.shF} {y' : I.toU.State}
    (h : I.toU.Trans P (.waiting (I.eraseF f) s t (eraseOp e)) (some (I.eraseMove m)) y') :
    ∃ y, y' = eraseState y ∧ I.ShTrans P (.waiting f s t e) (some m) y := by
  rcases m with (⟨e'⟩ | ⟨⟨⟨i', hi'⟩, s₀', ⟨vs', hvs'⟩⟩, ⟨s', w⟩⟩) | (⟨f'⟩ | ⟨f', a⟩)
  · cases h
  · obtain ⟨⟨i, hi⟩, s₀, ⟨vs, hvs⟩⟩ := e
    cases h with
    | uret a => exact ⟨.running f s' (resumeResult s t w.toResult), rfl, .uret s' w⟩
  · cases h
  · cases h

/-- **An untyped visible transition from an erased state along an erased move is the erasure
of a typed one.** -/
theorem back_step {x : I.ShState} {m : Move I.shE I.shF} {y' : I.toU.State}
    (h : I.toU.Trans P (eraseState x) (some (I.eraseMove m)) y') :
    ∃ y, y' = eraseState y ∧ I.ShTrans P x (some m) y := by
  cases x with
  | idle => exact back_idle h
  | running f s t => exact back_running h
  | waiting f s t e => exact back_waiting h

/-- An erased play is the erasure of exactly one play: the head of an erased cons. -/
theorem map_eraseMove_cons {m' : Move I.toU.E I.toU.F} {q : List (Move I.toU.E I.toU.F)}
    {p : List (Move I.shE I.shF)} (h : m' :: q = p.map I.eraseMove) :
    ∃ m p₀, p = m :: p₀ ∧ m' = I.eraseMove m ∧ q = p₀.map I.eraseMove := by
  cases p with
  | nil => cases h
  | cons m p₀ =>
    obtain ⟨h₁, h₂⟩ := List.cons.inj h
    exact ⟨m, p₀, rfl, h₁, h₂⟩

/-- **Runs of the untyped instance along an erased play are erasures of typed runs.** -/
theorem run_of_erase {x' y' : (I.toU.lts P).State} {q : List (Move I.toU.E I.toU.F)}
    (h : (I.toU.lts P).Run x' q y') :
    ∀ (x : I.ShState) (p : List (Move I.shE I.shF)), x' = eraseState x → q = p.map I.eraseMove →
      ∃ y, y' = eraseState y ∧ (I.shLts P).Run x p y := by
  induction h with
  | nil x' =>
    intro x p hx hp
    have hp' : p = [] := List.map_eq_nil_iff.mp hp.symm
    exact ⟨x, hx, hp' ▸ .nil _⟩
  | tau hs _ ih =>
    intro x p hx hp
    obtain ⟨y, rfl, hy⟩ := back_tau (hx ▸ hs)
    obtain ⟨z, hz, hrun⟩ := ih y p rfl hp
    exact ⟨z, hz, .tau hy hrun⟩
  | vis hs _ ih =>
    intro x p hx hp
    obtain ⟨m, p₀, rfl, rfl, hp₀⟩ := map_eraseMove_cons hp
    obtain ⟨y, rfl, hy⟩ := back_step (hx ▸ hs)
    obtain ⟨z, hz, hrun⟩ := ih y p₀ rfl hp₀
    exact ⟨z, hz, .vis hy hrun⟩

/-- **Typed traces are the typed plays whose erasure is an untyped trace.** -/
theorem traces_iff_erase {p : List (Move I.shE I.shF)} :
    p ∈ (I.shLts P).Traces ↔ p.map I.eraseMove ∈ (I.toU.lts P).Traces := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨_, run_erase hy⟩
  · rintro ⟨y', hy'⟩
    obtain ⟨y, -, hy⟩ := run_of_erase hy' .idle p rfl rfl
    exact ⟨y, hy⟩

/-- **The typed shared strategy is the untyped strategy read on typed plays**, every
profile, no well-formedness. -/
theorem mem_shStrategy_iff_erase {p : List (Move I.shE I.shF)} :
    p ∈ I.shStrategy P ↔ p.map I.eraseMove ∈ I.toU.strategy P := by
  rw [← Shared.denotes P p, mem_strategy_iff]
  exact traces_iff_erase

/-! ### Product semantics -/

section Product

variable {L : SEnv I.shE}

/-- **Typed product steps are untyped product steps** against the erased environment. -/
theorem uStep_of_shStep {x y : Config Nat × L.S} (h : ShStep P L x y) : UStep P L.erase x y := by
  obtain ⟨c, q⟩ := x
  obtain ⟨c', q'⟩ := y
  rcases Shared.shStep_elim h with ⟨h0, hq⟩ | ⟨E, fa, hh, args, e, s', w, hd, op, ans, hy⟩ |
      ⟨E, fa, hh, args, e, hd, op, hs, hy⟩
  · have hq' : q' = q := hq
    rw [hq']
    exact .internal h0
  · have hy' : c' = ⟨(eraseAr (e := shOp c.store e) (s', w)).store, c.frame,
        E.fill (eraseAr (e := shOp c.store e) (s', w)).result.toAdmin⟩ := hy
    rw [hy']
    exact .answer hd ⟨shOp c.store e, (s', w), eraseOp_shOp op c.store, rfl, ans⟩
  · have hy' : (c', q') = (c, q) := hy
    rw [hy']
    refine .silent hd (hs.imp (fun hdiv => ⟨_, eraseOp_shOp op c.store, hdiv⟩) ?_)
    rintro hno a q'' ⟨e', a', he', rfl, hans⟩
    have he'' : e' = shOp c.store e := eraseOp_injective (he'.trans (eraseOp_shOp op c.store).symm)
    subst he''
    exact hno a' q'' hans

/-- An erased call answered or diverged by the erased environment is a typed call. -/
theorem typed_of_erase {s : Store Nat} {hh : Nat} {args : List Val} {e' : I.shE.Op}
    (he' : eraseOp e' = ⟨hh, s, args⟩) :
    ∃ e : I.E.Op, ifaceOp? I.imports hh args = some e ∧ e' = shOp s e := by
  obtain ⟨⟨i, hi⟩, s₀, ⟨vs, hvs⟩⟩ := e'
  obtain ⟨rfl, rfl, rfl⟩ : i = hh ∧ s₀ = s ∧ vs = args := by
    simpa only [eraseOp, UCall.mk.injEq] using he'
  exact ⟨⟨⟨i, hi⟩, ⟨vs, hvs⟩⟩, ifaceOp?_typed ⟨⟨i, hi⟩, ⟨vs, hvs⟩⟩, rfl⟩

/-- **Untyped product steps against the erased environment are typed product steps**, from a
configuration satisfying the typed run invariant. -/
theorem shStep_of_uStep {s₀ : Store Nat} {ts : List CValType} {x y : Config Nat × L.S}
    (hg : Shared.ShGood I s₀ ts x.1) (h : UStep P L.erase x y) : ShStep P L x y := by
  obtain ⟨c, q⟩ := x
  obtain ⟨c', q'⟩ := y
  rcases uStep_elim h with ⟨h0, hq⟩ | ⟨E, fa, hh, args, a, hd, ans, hy⟩ |
      ⟨E, fa, hh, args, hd, hs, hy⟩
  · have hq' : q' = q := hq
    rw [hq']
    exact .internal h0
  · obtain ⟨e', ⟨s', w⟩, he', rfl, hans⟩ := ans
    obtain ⟨e, op, rfl⟩ := typed_of_erase he'
    have hy' : c' = ⟨s', c.frame, E.fill (w.toResult).toAdmin⟩ := hy
    rw [hy']
    exact .answer hd op hans
  · have hy' : (c', q') = (c, q) := hy
    rw [hy']
    rcases hs with ⟨e', he', hdiv⟩ | hno
    · obtain ⟨e, op, rfl⟩ := typed_of_erase he'
      exact .silent hd op (.inl hdiv)
    · obtain ⟨e, op⟩ := Shared.shGood_callout_valid (P := P) hg hd
      exact .silent hd op (.inr fun a' q'' hans =>
        hno (eraseAr a') q'' ⟨shOp c.store e, a', eraseOp_shOp op c.store, rfl, hans⟩)

variable {s₀ : Store Nat} (hL : I.ShEnvOk s₀ L) {ts : List CValType}
include hL

omit hL in
/-- Typed product runs are untyped product runs against the erased environment. -/
theorem uSteps_of_shSteps {x y : Config Nat × L.S} (h : ShSteps P L x y) :
    USteps P L.erase x y := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (uStep_of_shStep hst)

/-- Untyped product runs against the erased environment are typed product runs, from the
typed run invariant. -/
theorem shSteps_of_uSteps {x y : Config Nat × L.S} (hg : Shared.ShGood I s₀ ts x.1)
    (h : USteps P L.erase x y) : ShSteps P L x y := by
  induction h with
  | refl => exact .refl
  | @tail b y hb hst ih =>
    have hgb : Shared.ShGood I s₀ ts b.1 := Shared.shGood_shSteps hL hg ih
    exact ih.tail (shStep_of_uStep hgb hst)

omit hL in
/-- Infinite typed product runs are infinite untyped ones. -/
theorem inf_erase {x : Config Nat × L.S} (h : InfiniteTrace (ShStep P L) x) :
    InfiniteTrace (UStep P L.erase) x := by
  refine InfiniteTrace.coinduct (fun x => InfiniteTrace (ShStep P L) x) ?_ h
  intro x hinf
  obtain ⟨y, hst, hinf'⟩ := hinf.unfold
  exact ⟨y, uStep_of_shStep hst, hinf'⟩

/-- Infinite untyped product runs against the erased environment are infinite typed ones,
from the typed run invariant. -/
theorem inf_of_erase {x : Config Nat × L.S} (hg : Shared.ShGood I s₀ ts x.1)
    (h : InfiniteTrace (UStep P L.erase) x) : InfiniteTrace (ShStep P L) x := by
  refine InfiniteTrace.coinduct
    (fun x => Shared.ShGood I s₀ ts x.1 ∧ InfiniteTrace (UStep P L.erase) x) ?_ ⟨hg, h⟩
  rintro x ⟨hgx, hinf⟩
  obtain ⟨y, hst, hinf'⟩ := hinf.unfold
  have hst' : ShStep P L x y := shStep_of_uStep hgx hst
  exact ⟨y, hst', Shared.shGood_shStep hL hgx hst', hinf'⟩

omit hL in
/-- **The typed product behaviours are the untyped ones of the erased environment**, at a
well-formed store and against a well-formed typed environment. -/
theorem shBehavioursOf_eq_erase {f : I.shF.Op} (hw : I.WellFormed f.2.1) (hL : I.ShEnvOk f.2.1 L)
    (q : L.S) :
    shBehavioursOf P L q (invoke f.2.1 (I.addr f.1) f.2.2.1) =
      uBehavioursOf P L.erase q (invoke f.2.1 (I.addr f.1) f.2.2.1) := by
  have hg := Shared.shGood_invoke (f := f) hw
  ext b
  constructor
  · rintro (⟨c', q', r, run, final, rfl⟩ | ⟨rfl, hinf⟩)
    · exact .inl ⟨c', q', r, uSteps_of_shSteps run, final, rfl⟩
    · exact .inr ⟨rfl, inf_erase hinf⟩
  · rintro (⟨c', q', r, run, final, rfl⟩ | ⟨rfl, hinf⟩)
    · exact .inl ⟨c', q', r, shSteps_of_uSteps hL hg run, final, rfl⟩
    · exact .inr ⟨rfl, inf_of_erase hL hg hinf⟩

end Product

end Silmaril.Proofs.Wasm.Game.Untyped

namespace Silmaril.Proofs.Wasm.Game.Untyped

open Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

/-- A typed shared export call at a well-formed store is a well-typed untyped call. -/
theorem callOk_of_wellFormed {I : ScalarInstance} {f : I.shF.Op} (hw : I.WellFormed f.2.1) :
    I.toU.CallOk (I.eraseF f) (Ty.ofList ((I.exports.get f.1).params.map ScalarType.toC))
      (Ty.ofList ((I.exports.get f.1).results.map ScalarType.toC)) := by
  obtain ⟨fi, hfi, hexp⟩ := hw.export_type f.1
  have hargs : List.Forall₂ (ValOk f.2.1) f.2.2.1
      (Ty.ofList ((I.exports.get f.1).params.map ScalarType.toC)).toList := by
    exact ScalarInstance.forall₂_valOk_of_hasVal f.2.2.2
  exact ⟨hw.storeOk, fi, hfi, hexp, hargs⟩

end Silmaril.Proofs.Wasm.Game.Untyped
