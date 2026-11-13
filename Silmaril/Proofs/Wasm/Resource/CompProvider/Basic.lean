module

public import Silmaril.Wasm.Resource.CompProvider.Defs
public import Silmaril.Wasm.Spec.Component.RefMulti.Thms
public import Silmaril.Wasm.Resource.CompTable.Thms
public import Silmaril.Wasm.Component.Reference.Laws.Thms

/-!
# Components defining a resource, over several calls: proofs

* `runCalls_inv`, `lastWords_run`, **`multiInv_accepts`**: an invariant method (`MultiInv`)
  makes every multi-call trace accepted;
* `compProviderEv_ret`: a return is the provider event `alloc n` only when it is the
  constructor returning `own n`, and `skip` otherwise; `handleStep_provider_sub`: a provider
  step on a non-`alloc` event blames the environment or shrinks the live list;
* `ctr_multiInv`, **`compProvider_of_ctr`**: the counter verification condition `CtrVC` gives
  an invariant method for `compProviderSpec new drop`, hence the sentence in `refMultiSem`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component (Calls)
open Silmaril.Wasm.Component.Runtime (FuncId CallId)
open Silmaril.Wasm.Component.Machine (Config)

variable {E : Engine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}
variable {prof : Silmaril.Wasm.Component.ProfileKind} {h : Host E σ} {σ0 : σ} {X : CIface}
  {p : RefProg E X}

/-! ## The invariant method -/

section Method

variable {S : Type} {π : Protocol S (CEvent X)} {Inv : List (String × FuncId) → S → Config E σ → Prop}

theorem doneEvents_cons (d : DoneCall X) (ds : List (DoneCall X)) :
    doneEvents (d :: ds) = [Event.call d.exp d.args, Event.ret d.exp (.returns d.res)] ++
      doneEvents ds := rfl

/-- The resolved calls of a run keep the invariant. -/
theorem runCalls_inv (M : MultiInv prof h σ0 p π Inv) {es : List (String × FuncId)} {q : S}
    {m m' : Config E σ} {k : ℕ} {ds : List (DoneCall X)} (hi : Inv es q m)
    (hr : RunCalls prof h p.names es m k ds m') :
    ∃ q', π.run q (doneEvents ds) = some q' ∧ Inv es q' m' := by
  induction hr generalizing q with
  | nil => exact ⟨q, rfl, hi⟩
  | @cons _ _ _ _ d ds _ hf hc _ ih =>
    obtain ⟨q₁, h₁, hi₁⟩ := M.done _ _ _ _ _ _ _ _ _ hi hf hc
    obtain ⟨q₂, h₂, hi₂⟩ := ih hi₁
    have e : π.run q (doneEvents (d :: ds)) = some q₂ := by
      rw [doneEvents_cons, Protocol.run_append, h₁, Option.bind_some, h₂]
    exact ⟨q₂, e, hi₂⟩

theorem run_single_isSome {q : S} {e : CEvent X} (he : (π.step q e).isSome) :
    (π.run q [e]).isSome := by
  obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1 he
  simp [Protocol.run, hq']

/-- The last words of a run are accepted. -/
theorem lastWords_run (M : MultiInv prof h σ0 p π Inv) {es : List (String × FuncId)} {q : S}
    {m : Config E σ} {n : ℕ} (hi : Inv es q m) {u : List (CEvent X)}
    (hu : u ∈ lastWords prof h p.names es m n) : (π.run q u).isSome := by
  rcases hu with rfl | ⟨j, a, rfl⟩ | ⟨j, a, f, b, hf, hb, rfl⟩
  · rfl
  · exact run_single_isSome (M.calls q j a)
  · exact M.last es q m n j a f b hi hf hb

/-- **The invariant method**: every multi-call trace is accepted. -/
theorem multiInv_accepts (M : MultiInv prof h σ0 p π Inv) {t : List (CEvent X)}
    (ht : t ∈ refMultiTraces prof h σ0 p) : π.Accepts t := by
  obtain ⟨w, hw, hp⟩ := ht
  refine Protocol.Accepts.of_prefix ?_ hp
  rcases hw with rfl | ⟨j, a, rfl⟩ | ⟨m₀, inst, es, ds, mₙ, u, hi, hr, hu, rfl⟩ |
      ⟨j, a, -, rfl⟩ | ⟨j, a, -, rfl⟩
  · exact Protocol.accepts_nil _
  · exact run_single_isSome (M.calls _ j a)
  · obtain ⟨q, hq, hiq⟩ := runCalls_inv M (M.init _ _ _ hi) hr
    have e : π.run π.init (doneEvents ds ++ u) = π.run q u := by
      rw [Protocol.run_append, hq, Option.bind_some]
    show (π.run π.init (doneEvents ds ++ u)).isSome
    exact e ▸ lastWords_run M hiq hu
  · exact (M.instFail j a).1
  · exact (M.instFail j a).2

end Method

/-! ## Provider events -/

variable {new drop : X.Exp}

/-- A return is `alloc n` exactly when the constructor returns `own n`; otherwise `skip`. -/
theorem compProviderEv_ret (j : X.Exp) (b : Silmaril.Wasm.Spec.Component.Outcome) :
    compProviderEv new drop (Event.ret j b) = .skip ∨
      ∃ n, b = .returns (some [.own n]) ∧ j = new ∧
        compProviderEv new drop (Event.ret j b) = .alloc n := by
  rcases b with (_ | _ | ⟨v, _ | ⟨w, vs⟩⟩) | _ | _ | _
  · exact .inl rfl
  · exact .inl rfl
  · cases v <;> try exact .inl rfl
    rename_i n
    by_cases hj : j = new
    · exact .inr ⟨n, rfl, hj, by simp [compProviderEv, hj]⟩
    · exact .inl (by simp [compProviderEv, hj])
  · exact .inl (by cases v <;> rfl)
  · exact .inl rfl
  · exact .inl rfl
  · exact .inl rfl

/-- A provider step on a non-`alloc` event blames the environment or keeps a sublist. -/
theorem handleStep_provider_sub {L : List ℕ} {e : HEv ℕ} (he : ∀ r, e ≠ .alloc r) :
    handleStep .provider (some L) e = some none ∨
      ∃ L', handleStep .provider (some L) e = some (some L') ∧ ∀ x ∈ L', x ∈ L := by
  cases e with
  | alloc r => exact absurd rfl (he r)
  | use r =>
    by_cases hr : r ∈ L
    · exact .inr ⟨L, by simp [handleStep, hr], fun _ h => h⟩
    · exact .inl (by simp [handleStep, hr, fault])
  | free r =>
    by_cases hr : r ∈ L
    · exact .inr ⟨L.erase r, by simp [handleStep, hr], fun _ h => List.mem_of_mem_erase h⟩
    · exact .inl (by simp [handleStep, hr, fault])
  | skip => exact .inr ⟨L, rfl, fun _ h => h⟩

theorem compProvider_none (e : CEvent X) :
    (compProviderSpec new drop).step none e = some none := rfl

/-- Call events are never rejected by the provider sentence. -/
theorem compProvider_call_isSome (q : Option (List ℕ)) (j : X.Exp) (a : List RVal) :
    ((compProviderSpec new drop).step q (Event.call j a)).isSome := by
  rcases q with _ | L
  · rfl
  · rcases handleStep_provider_sub (L := L) (compProviderEv_call_ne_alloc new drop j a) with
      e | ⟨L', e, -⟩
    · exact (congrArg Option.isSome e).trans rfl
    · exact (congrArg Option.isSome e).trans rfl

/-- After a call, a skipped return is accepted. -/
theorem compProvider_skip_isSome (q : Option (List ℕ)) {j : X.Exp} (a : List RVal) {b : Silmaril.Wasm.Spec.Component.Outcome}
    (hb : compProviderEv new drop (Event.ret j b) = .skip) :
    ((compProviderSpec new drop).run q [Event.call j a, Event.ret j b]).isSome := by
  obtain ⟨q₁, hq₁⟩ := Option.isSome_iff_exists.1 (compProvider_call_isSome (new := new)
    (drop := drop) q j a)
  have h₂ : (compProviderSpec new drop).step q₁ (Event.ret j b) = some q₁ := by
    rcases q₁ with _ | L
    · rfl
    · show handleStep .provider (some L) (compProviderEv new drop (Event.ret j b)) = _
      rw [hb]
      rfl
  simp [Protocol.run, hq₁, h₂]

/-! ## The counter verification condition -/

variable {ctr : Config E σ → ℕ}

/-- The call step of `ctrInv`: the environment is blamed, or the live list shrinks. -/
theorem ctr_call_step {L : List ℕ} {c : ℕ} (hL : ∀ r ∈ L, r < c) (j : X.Exp) (a : List RVal) :
    (compProviderSpec new drop).step (some L) (Event.call j a) = some none ∨
      ∃ L', (compProviderSpec new drop).step (some L) (Event.call j a) = some (some L') ∧
        ∀ r ∈ L', r < c := by
  rcases handleStep_provider_sub (L := L) (compProviderEv_call_ne_alloc new drop j a) with
    e | ⟨L', e, hs⟩
  · exact .inl e
  · exact .inr ⟨L', e, fun r hr => hL r (hs r hr)⟩

/-- The return step of a resolved call under `CtrVC`. -/
theorem ctr_ret_step (vc : CtrVC prof h p new ctr) {es : List (String × FuncId)}
    {m m' : Config E σ} {k : ℕ} {j : X.Exp} {f : FuncId} {a : List RVal}
    {r : Option (List RVal)} (hf : es.lookup (p.names j) = some f)
    (hc : Calls prof h.hr h.dispatch m ⟨k⟩ f a m' (.resolved r)) {L : List ℕ}
    (hL : ∀ x ∈ L, x < ctr m) :
    ∃ q', (compProviderSpec new drop).step (some L) (Event.ret j (.returns r)) = some q' ∧
      ctrInv ctr es q' m' := by
  have hm : ctr m ≤ ctr m' := vc.mono es m k j f a m' r hf hc
  rcases compProviderEv_ret (new := new) (drop := drop) j (.returns r) with hs | ⟨n, hb, hj, ha⟩
  · have e : (compProviderSpec new drop).step (some L) (Event.ret j (.returns r)) = some (some L) := by
      show handleStep .provider (some L) _ = _
      rw [hs]; rfl
    exact ⟨_, e, .inr ⟨L, rfl, fun x hx => Nat.lt_of_lt_of_le (hL x hx) hm⟩⟩
  · obtain rfl : r = some [.own n] := Outcome.returns.inj hb
    obtain ⟨hn₁, hn₂⟩ := vc.fresh es m k f a m' n (hj ▸ hf) hc
    have hnL : n ∉ L := fun hn => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hL n hn) hn₁)
    have e : (compProviderSpec new drop).step (some L) (Event.ret j (.returns (some [.own n]))) =
        some (some (n :: L)) := by
      show handleStep .provider (some L) _ = _
      rw [ha]; simp [handleStep, hnL]
    refine ⟨_, e, .inr ⟨n :: L, rfl, ?_⟩⟩
    exact List.forall_mem_cons.2 ⟨hn₂, fun x hx => Nat.lt_of_lt_of_le (hL x hx) hm⟩

/-- A resolved call under `CtrVC` keeps `ctrInv`. -/
theorem ctr_done (vc : CtrVC prof h p new ctr) {es : List (String × FuncId)}
    {q : Option (List ℕ)} {m m' : Config E σ} {k : ℕ} {j : X.Exp} {f : FuncId}
    {a : List RVal} {r : Option (List RVal)} (hi : ctrInv ctr es q m)
    (hf : es.lookup (p.names j) = some f)
    (hc : Calls prof h.hr h.dispatch m ⟨k⟩ f a m' (.resolved r)) :
    ∃ q', (compProviderSpec new drop).run q [Event.call j a, Event.ret j (.returns r)] = some q' ∧
      ctrInv ctr es q' m' := by
  rcases hi with rfl | ⟨L, rfl, hL⟩
  · exact ⟨none, rfl, .inl rfl⟩
  · rcases ctr_call_step (new := new) (drop := drop) hL j a with e | ⟨L', e, hL'⟩
    · exact ⟨none, by simp [Protocol.run, e, compProvider_none], .inl rfl⟩
    · obtain ⟨q', e', hq'⟩ := ctr_ret_step (drop := drop) vc hf hc hL'
      exact ⟨q', by simp [Protocol.run, e, e'], hq'⟩

/-- A last call under `CtrVC` is accepted. -/
theorem ctr_last (vc : CtrVC prof h p new ctr) {es : List (String × FuncId)}
    {q : Option (List ℕ)} {m : Config E σ} {k : ℕ} {j : X.Exp} {f : FuncId}
    {a : List RVal} {b : Silmaril.Wasm.Spec.Component.Outcome} (hi : ctrInv ctr es q m) (hf : es.lookup (p.names j) = some f)
    (hb : b ∈ callBehaviours prof h m ⟨k⟩ f a) :
    ((compProviderSpec new drop).run q [Event.call j a, Event.ret j b]).isSome := by
  rcases hb with ⟨m', out, hc, rfl⟩ | ⟨rfl, -⟩
  · cases out with
    | resolved r =>
      obtain ⟨q', e, -⟩ := ctr_done (drop := drop) vc hi hf hc
      exact (congrArg Option.isSome e).trans rfl
    | trap => exact compProvider_skip_isSome q a rfl
    | deadlock => exact compProvider_skip_isSome q a rfl
  · exact compProvider_skip_isSome q a rfl

/-- **The counter VC is an invariant method for the provider sentence.** -/
theorem ctr_multiInv (vc : CtrVC prof h p new ctr) :
    MultiInv prof h σ0 p (compProviderSpec new drop) (ctrInv ctr) where
  calls := compProvider_call_isSome
  init _ _ _ _ := .inr ⟨[], rfl, fun _ h => nomatch h⟩
  done _ _ _ _ _ _ _ _ _ hi hf hc := ctr_done vc hi hf hc
  last _ _ _ _ _ _ _ _ hi hf hb := ctr_last vc hi hf hb
  instFail _ a := ⟨compProvider_skip_isSome _ a rfl, compProvider_skip_isSome _ a rfl⟩

/-- **A component meeting the counter VC satisfies the provider sentence over several calls**:
`new` never returns a live representation. -/
theorem compProvider_of_ctr (vc : CtrVC prof h p new ctr) :
    Models (protoLogic CFn (List RVal) Component.Outcome (Option (List ℕ)))
      (refMultiSem prof h σ0) p (compProviderSpec new drop) :=
  (models_protoLogic_iff _ _ _).2 fun _ ht => multiInv_accepts (ctr_multiInv vc) ht

/-! ## The counter VC on reachable configurations -/

variable {R : List (String × FuncId) → Config E σ → Prop}

/-- `CtrVC` is `CtrVCOn` with the trivial invariant. -/
theorem CtrVC.on (vc : CtrVC prof h p new ctr) : CtrVCOn prof h σ0 p new ctr fun _ _ => True where
  init _ _ _ _ := trivial
  step _ _ _ _ _ _ _ _ _ _ _ := trivial
  mono es m k j f a m' r _ hf hc := vc.mono es m k j f a m' r hf hc
  fresh es m k f a m' n _ hf hc := vc.fresh es m k f a m' n hf hc

/-- The return step of a resolved call from `R` under `CtrVCOn`. -/
theorem ctrOn_ret_step (vc : CtrVCOn prof h σ0 p new ctr R) {es : List (String × FuncId)}
    {m m' : Config E σ} {k : ℕ} {j : X.Exp} {f : FuncId} {a : List RVal}
    {r : Option (List RVal)} (hR : R es m) (hf : es.lookup (p.names j) = some f)
    (hc : Calls prof h.hr h.dispatch m ⟨k⟩ f a m' (.resolved r)) {L : List ℕ}
    (hL : ∀ x ∈ L, x < ctr m) :
    ∃ q', (compProviderSpec new drop).step (some L) (Event.ret j (.returns r)) = some q' ∧
      ctrInv ctr es q' m' := by
  have hm : ctr m ≤ ctr m' := vc.mono es m k j f a m' r hR hf hc
  rcases compProviderEv_ret (new := new) (drop := drop) j (.returns r) with hs | ⟨n, hb, hj, ha⟩
  · have e : (compProviderSpec new drop).step (some L) (Event.ret j (.returns r)) = some (some L) := by
      show handleStep .provider (some L) _ = _
      rw [hs]; rfl
    exact ⟨_, e, .inr ⟨L, rfl, fun x hx => Nat.lt_of_lt_of_le (hL x hx) hm⟩⟩
  · obtain rfl : r = some [.own n] := Outcome.returns.inj hb
    obtain ⟨hn₁, hn₂⟩ := vc.fresh es m k f a m' n hR (hj ▸ hf) hc
    have hnL : n ∉ L := fun hn => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hL n hn) hn₁)
    have e : (compProviderSpec new drop).step (some L) (Event.ret j (.returns (some [.own n]))) =
        some (some (n :: L)) := by
      show handleStep .provider (some L) _ = _
      rw [ha]; simp [handleStep, hnL]
    refine ⟨_, e, .inr ⟨n :: L, rfl, ?_⟩⟩
    exact List.forall_mem_cons.2 ⟨hn₂, fun x hx => Nat.lt_of_lt_of_le (hL x hx) hm⟩

/-- A resolved call from `R` under `CtrVCOn` keeps `ctrInvOn`. -/
theorem ctrOn_done (vc : CtrVCOn prof h σ0 p new ctr R) {es : List (String × FuncId)}
    {q : Option (List ℕ)} {m m' : Config E σ} {k : ℕ} {j : X.Exp} {f : FuncId}
    {a : List RVal} {r : Option (List RVal)} (hi : ctrInvOn ctr R es q m)
    (hf : es.lookup (p.names j) = some f)
    (hc : Calls prof h.hr h.dispatch m ⟨k⟩ f a m' (.resolved r)) :
    ∃ q', (compProviderSpec new drop).run q [Event.call j a, Event.ret j (.returns r)] = some q' ∧
      ctrInvOn ctr R es q' m' := by
  have hR' : R es m' := vc.step es m k j f a m' r hi.1 hf hc
  rcases hi.2 with rfl | ⟨L, rfl, hL⟩
  · exact ⟨none, rfl, hR', .inl rfl⟩
  · rcases ctr_call_step (new := new) (drop := drop) hL j a with e | ⟨L', e, hL'⟩
    · exact ⟨none, by simp [Protocol.run, e, compProvider_none], hR', .inl rfl⟩
    · obtain ⟨q', e', hq'⟩ := ctrOn_ret_step (drop := drop) vc hi.1 hf hc hL'
      exact ⟨q', by simp [Protocol.run, e, e'], hR', hq'⟩

/-- A last call under `CtrVCOn` is accepted. -/
theorem ctrOn_last (vc : CtrVCOn prof h σ0 p new ctr R) {es : List (String × FuncId)}
    {q : Option (List ℕ)} {m : Config E σ} {k : ℕ} {j : X.Exp} {f : FuncId}
    {a : List RVal} {b : Silmaril.Wasm.Spec.Component.Outcome} (hi : ctrInvOn ctr R es q m)
    (hf : es.lookup (p.names j) = some f) (hb : b ∈ callBehaviours prof h m ⟨k⟩ f a) :
    ((compProviderSpec new drop).run q [Event.call j a, Event.ret j b]).isSome := by
  rcases hb with ⟨m', out, hc, rfl⟩ | ⟨rfl, -⟩
  · cases out with
    | resolved r =>
      obtain ⟨q', e, -⟩ := ctrOn_done (drop := drop) vc hi hf hc
      exact (congrArg Option.isSome e).trans rfl
    | trap => exact compProvider_skip_isSome q a rfl
    | deadlock => exact compProvider_skip_isSome q a rfl
  · exact compProvider_skip_isSome q a rfl

/-- **`CtrVCOn` is an invariant method for the provider sentence.** -/
theorem ctrOn_multiInv (vc : CtrVCOn prof h σ0 p new ctr R) :
    MultiInv prof h σ0 p (compProviderSpec new drop) (ctrInvOn ctr R) where
  calls := compProvider_call_isSome
  init _ _ _ hi := ⟨vc.init _ _ _ hi, .inr ⟨[], rfl, fun _ h => nomatch h⟩⟩
  done _ _ _ _ _ _ _ _ _ hi hf hc := ctrOn_done vc hi hf hc
  last _ _ _ _ _ _ _ _ hi hf hb := ctrOn_last vc hi hf hb
  instFail _ a := ⟨compProvider_skip_isSome _ a rfl, compProvider_skip_isSome _ a rfl⟩

/-- **A component meeting the counter VC on reachable configurations satisfies the provider
sentence over several calls.** -/
theorem compProvider_of_ctrOn (vc : CtrVCOn prof h σ0 p new ctr R) :
    Models (protoLogic CFn (List RVal) Component.Outcome (Option (List ℕ)))
      (refMultiSem prof h σ0) p (compProviderSpec new drop) :=
  (models_protoLogic_iff _ _ _).2 fun _ ht => multiInv_accepts (ctrOn_multiInv vc) ht

/-! ## Refutation: a constructor that returns a live representation again -/

/-- The trace of two constructor calls returning the same representation is rejected. -/
theorem compProvider_reuse_rejected (n : ℕ) :
    (compProviderSpec new drop).acceptsB
      (doneEvents [⟨new, [], some [.own n]⟩, ⟨new, [], some [.own n]⟩]) = false := by
  simp [Protocol.acceptsB, Protocol.run, compProviderSpec, Protocol.comap, compProviderEv,
    handleProto, handleStep, fault, doneEvents, DoneCall.events]

/-- **Over several calls the provider sentence is not vacuous**: a reference component with a
multi-call run in which the constructor `new` (called without arguments) returns `own n` twice
violates `compProviderSpec new drop` in `refMultiSem` (in `refSem` it holds of every component,
`refSem_compProvider`). -/
theorem compProvider_refuted_of_reuse {m₀ : Config E σ} {inst : Silmaril.Wasm.Component.Runtime.InstId}
    {es : List (String × FuncId)}
    (hi : InstResult.instance m₀ inst es ∈ instBehaviours prof h (initConfig σ0) p.comp p.args)
    {n : ℕ} {mₙ : Config E σ}
    (hr : RunCalls prof h p.names es m₀ 0 [⟨new, [], some [.own n]⟩, ⟨new, [], some [.own n]⟩] mₙ) :
    ¬ Models (protoLogic CFn (List RVal) Component.Outcome (Option (List ℕ)))
      (refMultiSem prof h σ0) p (compProviderSpec new drop) :=
  not_models_of_trace (refMultiSem prof h σ0) p (compProviderSpec new drop)
    (doneEvents_mem p hi hr) (compProvider_reuse_rejected n)

end Silmaril.Wasm.Resource
