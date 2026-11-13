module

public import Silmaril.Proofs.Wasm.Spec.Live.Basic
public import Silmaril.Proofs.Wasm.Spec.Live.Chain
public import Silmaril.Games.DivComp.Thms
public import Silmaril.Wasm.Game.Env.Thms
public import Silmaril.Wasm.Game.Adequacy.Thms

@[expose] public section

/-!
# Liveness: Core 3.0 divergence as maximal behaviours of `wasmDivSem`

For an environment `K` that answers every import call (`Total K`) and every profile `P`:

* `diverges_cases`: if the Core invocation of export call `f` diverges under the host induced
  by `K`, then either the instance diverges *locally* after a play `t` (a divergent play of the
  divergence-observing strategy) whose import events agree with `K`, or there is an infinite
  chain of plays whose import events agree with `K` and whose only export event is the call
  (*infinite hidden chatter*: infinitely many answered import calls). This is
  `ScalarInstance.mem_div_closedD_iff` and `closedD_eq_comp` read through
  `DStrategy.mem_div_comp`; the third clause of the composite's divergence (the environment
  diverges) is excluded by totality.
* `diverges_of_local`: conversely, local divergence against `K` is Core divergence.
* `maximal_div`: a divergence trace of `wasmDivSem` is a maximal trace.
* `diverges_witness`: hence **Core divergence is a maximal behaviour of `wasmDivSem`** that
  calls `f` and never returns anything but `diverges` (`DivWitness`).
* `exists_trace_of_behaviour`: every terminating Core behaviour is the return of a trace of
  `wasmDivSem` with import events agreeing with `K` (adequacy M2).
-/

namespace Silmaril.Wasm.Spec.Live

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-! ## Environments over the empty signature -/

/-- There is no event over the empty signature. -/
theorem ev_empty_false (a : Ev (Sig.empty : Sig.{0})) : False := by
  cases a with
  | ask m => exact m.elim
  | ans m _ => exact m.elim

/-- Interaction with an environment: the environment's moves are the lower events of `t`, and
the visible play is its upper part. -/
theorem zip_env_iff {E F : Sig.{0}} {s : List (Move Sig.empty E)} {t : List (Move E F)}
    {p : List (Move Sig.empty F)} :
    Zip s t p ↔ s = (lower t).map .inr ∧ p = (upper t).map .inr := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨rfl, rfl⟩
    | left a _ _ => exact (ev_empty_false a).elim
    | right c _ ih => obtain ⟨rfl, rfl⟩ := ih; exact ⟨rfl, rfl⟩
    | sync b _ ih => obtain ⟨rfl, rfl⟩ := ih; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    induction t with
    | nil => exact .nil
    | cons m t ih =>
      rcases m with b | c
      · exact .sync b ih
      · exact .right c ih

/-- A total environment never diverges. -/
theorem total_not_div {E : Sig.{0}} {K : Env E} (hK : Total K) (s : List (Move Sig.empty E)) :
    s ∉ K.dstrategy.div := by
  intro hs
  obtain ⟨⟨y, -, hdiv⟩, -⟩ := hs
  obtain ⟨y', hstep, -⟩ := hdiv.unfold
  have hstep' : K.DStep y none y' := hstep
  cases hstep' with
  | loop hno =>
    obtain ⟨w, hw⟩ := hK _
    exact hno w hw

/-- A play of the divergence-observing environment interacting with `t` to show the export
call `f`: the lower events of `t` agree with `K`, and its only upper event is the call. -/
theorem env_play {E F : Sig.{0}} {K : Env E} {f : F.Op} {s : List (Move Sig.empty E)}
    {t : List (Move E F)} (hz : Zip s t [.inr (.ask f)]) (hs : s ∈ K.dstrategy.toStrategy) :
    K.Agrees (lower t) ∧ upper t = [.ask f] := by
  obtain ⟨rfl, hp⟩ := zip_env_iff.1 hz
  have hfk : K.dstrategy.toStrategy = K.strategy := Env.forget_dstrategy K
  have hs' : (lower t).map .inr ∈ K.strategy := hfk ▸ hs
  obtain ⟨u, hu, heq⟩ := Env.mem_strategy_iff.1 hs'
  have hul : lower t = u := List.map_injective_iff.2 Sum.inr_injective heq
  refine ⟨hul ▸ hu, ?_⟩
  exact List.map_injective_iff.2 Sum.inr_injective (by rw [← hp]; rfl)

/-- The play of the environment agreeing with `t`. -/
theorem env_mem_of_agrees {E : Sig.{0}} {K : Env E} {u : List (Ev E)} (hu : K.Agrees u) :
    u.map .inr ∈ K.dstrategy.toStrategy := by
  have h : u.map .inr ∈ K.strategy := Env.mem_strategy_iff.2 ⟨u, hu, rfl⟩
  have hfk : K.dstrategy.toStrategy = K.strategy := Env.forget_dstrategy K
  exact hfk ▸ h

/-! ## Events of plays -/

/-- The behaviour of an answer is never divergence. -/
theorem toBehaviour_ne_diverges {ft : FnType} (w : Answer ft) :
    Answer.toBehaviour w ≠ .diverges := by
  unfold Answer.toBehaviour
  cases w.toResult <;> simp [Result.toBehaviour]

/-- A move is never read as a divergent return. -/
theorem moveEvent_ne_div {X : WIface} (m : Move (ifaceSig X.imports) (ifaceSig X.exports))
    (j : X.Exp) : moveEvent m ≠ Event.ret j .diverges := by
  rcases m with (e | e) | (e | ⟨f, w⟩)
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h
    simp only [moveEvent, Sum.map_inr, evOf, Event.ret, Sum.inr.injEq, SideEv.ans.injEq] at h
    exact toBehaviour_ne_diverges w h.2

/-- A play whose only upper event is a call never returns. -/
theorem not_ret_mem_of_upper {X : WIface} {t : List (Move (ifaceSig X.imports) (ifaceSig X.exports))}
    {f : (ifaceSig X.exports).Op} (hu : upper t = [.ask f]) (j : X.Exp) (r : Behaviour Val) :
    Event.ret j r ∉ t.map moveEvent := by
  intro h
  obtain ⟨m, hm, hme⟩ := List.mem_map.1 h
  rcases m with (e | e) | (e | ⟨f', w⟩)
  · cases hme
  · cases hme
  · cases hme
  · have hup : (Ev.ans f' w : Ev (ifaceSig X.exports)) ∈ upper t := List.mem_filterMap.2 ⟨_, hm, rfl⟩
    rw [hu] at hup
    simp at hup

/-- A play whose only upper event is the call `f` contains that call. -/
theorem call_mem_of_upper {X : WIface} {t : List (Move (ifaceSig X.imports) (ifaceSig X.exports))}
    {f : (ifaceSig X.exports).Op} (hu : upper t = [.ask f]) :
    Event.call f.1 f.2.1 ∈ t.map moveEvent := by
  have h : (Ev.ask f : Ev (ifaceSig X.exports)) ∈ upper t := by
    rw [hu]
    exact List.mem_singleton_self _
  obtain ⟨m, hm, hget⟩ := List.mem_filterMap.1 h
  have hm' : m = .inr (.ask f) := Sum.getRight?_eq_some_iff.1 hget
  exact List.mem_map.2 ⟨m, hm, by rw [hm']; rfl⟩

/-! ## Divergence traces are maximal -/

/-- **A divergence trace of `wasmDivSem` is maximal**: no event follows `ret q .diverges`. -/
theorem maximal_div {P : Profile} {X : WIface} (p : WasmProg X)
    {t : List (Move (ifaceSig X.imports) (ifaceSig X.exports))}
    (ht : t ∈ (p.inst.dstrategy P p.store).div) {q : (ifaceSig X.exports).Op}
    (hq : Path .idle t (.run q)) :
    Maximal ((wasmDivSem P).traces p) (t.map moveEvent ++ [Event.ret q.1 .diverges]) := by
  refine ⟨.inr ⟨t, ht, q, hq, rfl⟩, fun e he => ?_⟩
  have hdv : Event.ret q.1 .diverges ∈ (t.map moveEvent ++ [Event.ret q.1 .diverges]) ++ [e] := by
    simp
  rcases he with ⟨u, -, hu⟩ | ⟨u, -, g, -, hu⟩
  · have hmem : Event.ret q.1 .diverges ∈ u.map moveEvent := hu ▸ hdv
    obtain ⟨m, -, hm⟩ := List.mem_map.1 hmem
    exact moveEvent_ne_div m _ hm
  · obtain ⟨hl, -⟩ := List.append_inj' hu (by simp)
    have hmem : Event.ret q.1 .diverges ∈ u.map moveEvent := by
      rw [← hl]
      simp
    obtain ⟨m, -, hm⟩ := List.mem_map.1 hmem
    exact moveEvent_ne_div m _ hm

/-! ## Core divergence as game divergence -/

/-- **The two ways a closed export call diverges** (every profile, total environments). -/
theorem diverges_cases {P : Profile} {X : WIface} (p : WasmProg X) {K : Env (ifaceSig X.imports)}
    (htot : Total K) (f : (ifaceSig X.exports).Op)
    (hdiv : Diverges P (hostOf X.imports K) (invoke p.store (p.inst.addr f.1) f.2.1)) :
    (∃ t ∈ (p.inst.dstrategy P p.store).div, K.Agrees (lower t) ∧ upper t = [.ask f]) ∨
      ∃ c : Chain (Move (ifaceSig X.imports) (ifaceSig X.exports)), c.Mono ∧ c.Unbounded ∧
        ∀ m, c m ∈ p.inst.strategy P p.store ∧ K.Agrees (lower (c m)) ∧ upper (c m) = [.ask f] := by
  have h₁ : [.inr (.ask f)] ∈ (p.inst.closedD P p.store K).div :=
    (ScalarInstance.mem_div_closedD_iff (I := p.inst) (P := P) (s := p.store) (K := K) f).2 hdiv
  have h₂ : [.inr (.ask f)] ∈ (K.dstrategy.comp (p.inst.dstrategy P p.store)).div :=
    ScalarInstance.closedD_eq_comp (I := p.inst) P p.store K ▸ h₁
  rcases DStrategy.mem_div_comp.1 h₂ with ⟨s, t, hz, ⟨hs, -⟩ | ⟨hs, ht⟩⟩ | ⟨i, hi⟩
  · exact absurd hs (total_not_div htot s)
  · exact .inl ⟨t, ht, env_play hz hs⟩
  · obtain ⟨-, hu, -, -⟩ := i.chatter_inf hi
    refine .inr ⟨i.t, i.mono_t, hu, fun m => ?_⟩
    have hfi : (p.inst.dstrategy P p.store).toStrategy = p.inst.strategy P p.store :=
      ScalarInstance.forget_dstrategy (I := p.inst) P p.store
    have hm : i.t m ∈ p.inst.strategy P p.store := hfi ▸ i.mem_t m
    have hz : Zip (i.s m) (i.t m) [.inr (.ask f)] := hi m ▸ i.zip m
    exact ⟨hm, env_play hz (i.mem_s m)⟩

/-- **Local divergence against `K` is Core divergence** (every profile). -/
theorem diverges_of_local {P : Profile} {X : WIface} (p : WasmProg X) {K : Env (ifaceSig X.imports)}
    {f : (ifaceSig X.exports).Op} {t : List (Move (ifaceSig X.imports) (ifaceSig X.exports))}
    (ht : t ∈ (p.inst.dstrategy P p.store).div) (hK : K.Agrees (lower t))
    (hu : upper t = [.ask f]) :
    Diverges P (hostOf X.imports K) (invoke p.store (p.inst.addr f.1) f.2.1) := by
  have hz : Zip ((lower t).map .inr) t [.inr (.ask f)] := zip_env_iff.2 ⟨rfl, by rw [hu]; rfl⟩
  have h₂ : [.inr (.ask f)] ∈ (K.dstrategy.comp (p.inst.dstrategy P p.store)).div :=
    DStrategy.mem_div_comp_of_right (env_mem_of_agrees hK) ht hz
  have h₁ : [.inr (.ask f)] ∈ (p.inst.closedD P p.store K).div :=
    (ScalarInstance.closedD_eq_comp (I := p.inst) P p.store K).symm ▸ h₂
  exact (ScalarInstance.mem_div_closedD_iff (I := p.inst) (P := P) (s := p.store) (K := K) f).1 h₁

/-- The letter at a position of a prefix. -/
theorem getElem_prefixList {α : Type} (w : ℕ → α) {n k : ℕ} (hk : k < (prefixList w n).length) :
    (prefixList w n)[k] = w k := by
  simp [prefixList]

/-- The infinite-chatter case gives an infinite limit of `wasmDivSem` that calls `f` and never
returns. -/
theorem chatter_witness {P : Profile} {X : WIface} (p : WasmProg X) {f : (ifaceSig X.exports).Op}
    (c : Chain (Move (ifaceSig X.imports) (ifaceSig X.exports))) (hm : c.Mono)
    (hu : c.Unbounded) (hc : ∀ m, c m ∈ p.inst.strategy P p.store ∧ upper (c m) = [.ask f]) :
    ∃ w ∈ limits ((wasmDivSem P).traces p), (∃ k, w k = Event.call f.1 f.2.1) ∧
      ∀ k j r, w k ≠ Event.ret j r := by
  let w' : ℕ → Move (ifaceSig X.imports) (ifaceSig X.exports) := chainWord hm hu
  have hpre : ∀ n, prefixList (fun k => moveEvent (w' k)) n = (prefixList w' n).map moveEvent :=
    fun n => by simp [prefixList, List.map_ofFn]; rfl
  have hlim : (fun k => moveEvent (w' k)) ∈ limits ((wasmDivSem P).traces p) := by
    intro n
    obtain ⟨m, hm'⟩ := prefixList_chainWord_prefix hm hu n
    have hmem : prefixList w' n ∈ p.inst.strategy P p.store :=
      (p.inst.strategy P p.store).of_prefix (hc m).1 hm'
    have hfi : (p.inst.dstrategy P p.store).toStrategy = p.inst.strategy P p.store :=
      ScalarInstance.forget_dstrategy (I := p.inst) P p.store
    have hmem' : prefixList w' n ∈ (p.inst.dstrategy P p.store).toStrategy := hfi ▸ hmem
    exact .inl ⟨_, hmem', (hpre n).symm⟩
  refine ⟨_, hlim, ?_, fun k j r hk => ?_⟩
  · show ∃ k, moveEvent (w' k) = Event.call f.1 f.2.1
    obtain ⟨k, hk, hkc⟩ := List.getElem_of_mem (call_mem_of_upper (hc 0).2)
    have heq : prefixList w' (c 0).length = c 0 := exists_prefixList_chainWord hm hu 0
    have hk' : k < (prefixList w' (c 0).length).length := by simpa using hk
    refine ⟨k, ?_⟩
    have hw : w' k = (c 0)[k]'(by simpa using hk) := by
      rw [← getElem_prefixList w' hk']
      simp only [heq]
    rw [hw, ← List.getElem_map (f := moveEvent)]
    exact hkc
  · obtain ⟨m, hmem⟩ := chainWord_mem hm hu k
    exact not_ret_mem_of_upper (hc m).2 j r (hk ▸ List.mem_map_of_mem hmem)

/-- **Core divergence is a maximal behaviour of `wasmDivSem`** (every profile, total
environments): a maximal trace calling `f` whose only return is `diverges`, or an infinite limit
calling `f` and never returning. -/
theorem diverges_witness {P : Profile} {X : WIface} (p : WasmProg X) {K : Env (ifaceSig X.imports)}
    (htot : Total K) (f : (ifaceSig X.exports).Op)
    (hdiv : Diverges P (hostOf X.imports K) (invoke p.store (p.inst.addr f.1) f.2.1)) :
    DivWitness ((wasmDivSem P).traces p) f.1 f.2.1 (· = .diverges) := by
  rcases diverges_cases p htot f hdiv with ⟨t, ht, -, hu⟩ | ⟨c, hm, hun, hc⟩
  · obtain ⟨q, hq⟩ := (p.inst.dstrategy P p.store).div_run ht
    refine .inl ⟨_, maximal_div p ht hq, List.mem_append_left _ (call_mem_of_upper hu), ?_⟩
    intro j r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact absurd hr (not_ret_mem_of_upper hu j r)
    · have heq : Event.ret j r = Event.ret q.1 (.diverges : Behaviour Val) :=
        List.mem_singleton.1 hr
      injection heq with heq'
      injection heq' with _ hr'
  · exact .inr (chatter_witness p c hm hun fun m => ⟨(hc m).1, (hc m).2.2⟩)

/-! ## Terminating behaviours -/

/-- **Every terminating Core behaviour is a trace of `wasmDivSem`** whose export events are the
call and the return and whose import events agree with `K` (adequacy M2, every profile). -/
theorem exists_trace_of_behaviour {P : Profile} {X : WIface} (p : WasmProg X)
    (hw : p.inst.WellFormed p.store) (K : Env (ifaceSig X.imports))
    (hK : ThrowsBelow K p.store.exns.length) (f : (ifaceSig X.exports).Op) {b : Behaviour Val}
    (hb : b ≠ .diverges) (h : b ∈ behaviours P (hostOf X.imports K) p.store (p.inst.addr f.1) f.2.1) :
    ∃ t ∈ (wasmDivSem P).traces p, exportEvents t = [.ask f.1 f.2.1, .ans f.1 b] ∧
      ∃ u : List (Ev (ifaceSig X.imports)), K.Agrees u ∧ importEvents t = u.map evOf := by
  have hobs : b ∈ compositeObs (p.inst.closedWith P p.store K) f :=
    (ScalarInstance.adequacy_answers hw K hK f b hb).1 h
  obtain ⟨w, hresp, rfl⟩ : ∃ w, Responds (p.inst.closedWith P p.store K) f w ∧
      b = Answer.toBehaviour (ft := X.exports.get f.1) w := by
    rcases hobs with hobs | ⟨rfl, -⟩
    · exact hobs
    · exact absurd rfl hb
  obtain ⟨t, ht, hag, hup⟩ : ∃ t ∈ p.inst.strategy P p.store, K.Agrees (lower t) ∧
      [.inr (.ask f), .inr (.ans f w)] = (upper t).map Sum.inr :=
    Env.mem_comp_iff.1 hresp
  have hup' : upper t = [.ask f, .ans f w] :=
    List.map_injective_iff.2 Sum.inr_injective (by rw [← hup]; rfl)
  have hfi : (p.inst.dstrategy P p.store).toStrategy = p.inst.strategy P p.store :=
    ScalarInstance.forget_dstrategy (I := p.inst) P p.store
  have ht' : t ∈ (p.inst.dstrategy P p.store).toStrategy := hfi ▸ ht
  have hex : exportEvents (t.map moveEvent) = (upper t).map evOf := exportEvents_map (X := X) t
  refine ⟨t.map moveEvent, .inl ⟨t, ht', rfl⟩, ?_, lower t, hag, importEvents_map (X := X) t⟩
  rw [hex, hup']
  rfl

end Silmaril.Wasm.Spec.Live
