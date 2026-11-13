module

public import Silmaril.Proofs.Wasm.Game.Shared.Runs

/-!
# Core hosts and store-preserving environments as shared environments

* `shEnvOk_ofHost`: a host relation satisfying Core's host contract `HostOk`
  whose returned stores keep host functions typed as imports (`HostKeeps`) is a
  well-formed environment over the shared signature (`SEnv.ofHost`).
* `core_shStep_ofHost`, `core_of_shStep_ofHost`: on configurations satisfying
  the run invariant, Core steps under such a host are exactly the product steps
  against `SEnv.ofHost` (a host call with no answer of the environment diverges,
  since `HostOk` gives every valid call an outcome); hence
  `behaviours_eq_shBehavioursOf`: the Core behaviours of an export call are the
  product behaviours.
* `shStep_liftSh_eq`, `shBehavioursOf_liftSh`, `shEnvOk_liftSh`: a
  store-preserving stateful environment `L : SEnv I.E` is the shared environment
  `SEnv.liftSh L` answering in the question's store, with the same product
  semantics (`SStep P L`) and well formed when `L.ThrowsBelow`.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Shared

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

variable {I : Silmaril.Wasm.Game.ScalarInstance} {P : Profile}

/-! ### Answers and typed results -/

set_option linter.unusedTactic false in
theorem ifaceOp?_snd {ts : List FnType} {h : Nat} {args : List Val} {e : (ifaceSig ts).Op}
    (he : ifaceOp? ts h args = some e) : e.2.1 = args := by
  unfold ifaceOp? at he
  split_ifs at he
  all_goals (cases he; try rfl)

/-- A result typed at scalar result types is the result of an answer. -/
theorem answer_of_resultTyped {ft : FnType} {s : Store Nat} {r : Result}
    (h : ResultTyped s r (Ty.ofList (ft.results.map ScalarType.toC)).toList) :
    ∃ w : Answer ft, w.toResult = r := by
  cases r with
  | values vs => exact ⟨.values ⟨vs, ScalarInstance.hasVal_of_forall₂_valOk h⟩, rfl⟩
  | throw a => exact ⟨.throw a, rfl⟩
  | trap => exact ⟨.trap, rfl⟩

/-- The exception of a typed result exists. -/
theorem throwsBelow_of_resultTyped {ft : FnType} {s : Store Nat} {ts : List CValType}
    {w : Answer ft} (h : ResultTyped s w.toResult ts) : w.ThrowsBelow s.exns.length := by
  cases w with
  | values vs => trivial
  | trap => trivial
  | throw a =>
    obtain ⟨x, hx⟩ := h
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hx
    exact hlt

/-- Exception bounds grow. -/
theorem throwsBelow_mono {ft : FnType} {w : Answer ft} {n m : Nat} (h : w.ThrowsBelow n)
    (hnm : n ≤ m) : w.ThrowsBelow m := by
  cases w with
  | values vs => trivial
  | trap => trivial
  | throw a => exact Nat.lt_of_lt_of_le h hnm

/-! ### Product steps, by cases -/

/-- The three kinds of product steps, for any environment over the shared signature. -/
theorem shStep_elim {ts : List FnType} {L : SEnv (sharedSig ts)} {x y : Config Nat × L.S}
    (h : ShStep P L x y) :
    (Step P (fun _ _ _ _ => False) x.1 y.1 ∧ y.2 = x.2) ∨
      (∃ (E : Ctx) (a hh : Nat) (args : List Val) (e : (ifaceSig ts).Op) (s' : Store Nat)
          (w : Answer (ts.get e.1)),
        decompose? x.1.store x.1.code = some (E, a, hh, args) ∧ ifaceOp? ts hh args = some e ∧
        L.Ans x.2 (shOp x.1.store e) (s', w) y.2 ∧ y.1 = ⟨s', x.1.frame, E.fill w.toResult.toAdmin⟩) ∨
      (∃ (E : Ctx) (a hh : Nat) (args : List Val) (e : (ifaceSig ts).Op),
        decompose? x.1.store x.1.code = some (E, a, hh, args) ∧ ifaceOp? ts hh args = some e ∧
        L.Silent x.2 (shOp x.1.store e) ∧ y = x) := by
  cases h with
  | internal h0 => exact .inl ⟨h0, rfl⟩
  | answer hd op ans => exact .inr (.inl ⟨_, _, _, _, _, _, _, hd, op, ans, rfl⟩)
  | silent hd op hs => exact .inr (.inr ⟨_, _, _, _, _, hd, op, hs, rfl⟩)

/-! ### Core hosts -/

/-- The host contract at a valid import call of a host function of a well-formed store. -/
theorem hostOk_call {host : HostSemantics Nat} (hok : HostOk host) {s : Store Nat}
    (hw : I.WellFormed s) {fi : FuncInst Nat} {e : (ifaceSig I.imports).Op}
    (hfi : fi ∈ s.funcs) (hcode : fi.code = .host e.1.val) :
    (∃ out, host e.1.val s e.2.1 out) ∧
      ∀ s' r, host e.1.val s e.2.1 (.returned s' r) →
        StoreOk s' ∧ Extend s s' ∧
          ResultTyped s' r (Ty.ofList ((I.imports.get e.1).results.map ScalarType.toC)).toList := by
  obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hfi
  obtain ⟨hlt, hexp⟩ := hw.host_type a fi e.1.val ha hcode
  have hfin : (⟨e.1.val, hlt⟩ : Fin I.imports.length) = e.1 := Fin.ext rfl
  rw [hfin] at hexp
  have hvs := ScalarInstance.forall₂_valOk_of_hasVal (s := s) e.2.2
  have hok' := hok s fi e.1.val e.2.1 _ _ hw.storeOk hfi hcode hexp hvs
  exact ⟨hok'.1, fun s' r hr => hok'.2 _ hr⟩

/-- **Well-formedness of a host**: a `HostOk` host keeping host functions typed is a
well-formed environment over the shared signature. -/
theorem shEnvOk_ofHost {host : HostSemantics Nat} (hok : HostOk host) (hk : I.HostKeeps host)
    (s₀ : Store Nat) : I.ShEnvOk s₀ (SEnv.ofHost I.imports host) := by
  intro q e a q' _ hwf ⟨fi, hfi, hcode⟩ hans
  obtain ⟨hs', hext, hres⟩ := (hostOk_call (e := ⟨e.1, e.2.2⟩) hok hwf hfi hcode).2 _ _ hans
  exact ⟨wellFormed_of_extend hwf hs' hext (hk _ _ _ _ _ hwf hans), hext,
    throwsBelow_of_resultTyped hres⟩

/-- The host call at a host-call redex, read through the import question. -/
theorem host_at_callout {host : HostSemantics Nat} {s : Store Nat} {hh : Nat} {args : List Val}
    {e : (ifaceSig I.imports).Op} {out : HostOutcome Nat}
    (op : ifaceOp? I.imports hh args = some e) :
    host hh s args out ↔ host e.1.val s e.2.1 out := by
  rw [ifaceOp?_fst op, ifaceOp?_snd op]

/-- The host function at a host-call redex is a host function of the store. -/
theorem fi_at_callout {c : Config Nat} {E : Ctx} {a hh : Nat} {args : List Val}
    {e : (ifaceSig I.imports).Op} (hd : decompose? c.store c.code = some (E, a, hh, args))
    (op : ifaceOp? I.imports hh args = some e) :
    ∃ fi ∈ c.store.funcs, fi.code = .host e.1.val :=
  callout_host hd op

/-- A host-free or answered Core step under a `HostOk` host, from the run invariant, is a
product step against `SEnv.ofHost`. -/
theorem core_shStep_ofHost {host : HostSemantics Nat} (hok : HostOk host) {s₀ : Store Nat}
    {ts : List CValType} {c c' : Config Nat} (hg : ShGood I s₀ ts c) (h : Step P host c c') :
    ShStep P (SEnv.ofHost I.imports host) (c, ()) (c', ()) := by
  rcases Step.split_host h with h0 | ⟨E, a, hh, args, hd, ⟨s', r, hr, rfl⟩ | ⟨hdiv, rfl⟩⟩
  · exact .internal h0
  · obtain ⟨e, op⟩ := shGood_callout_valid (P := P) hg hd
    obtain ⟨fi, hfi, hcode⟩ := fi_at_callout hd op
    have hr' : host e.1.val c.store e.2.1 (.returned s' r) := (host_at_callout op).1 hr
    obtain ⟨-, -, hres⟩ := (hostOk_call hok hg.wf hfi hcode).2 s' r hr'
    obtain ⟨w, rfl⟩ := answer_of_resultTyped hres
    exact .answer (w := w) hd op hr'
  · obtain ⟨e, op⟩ := shGood_callout_valid (P := P) hg hd
    exact .silent hd op (.inl ((host_at_callout op).1 hdiv))

/-- A host call with no returned answer of `SEnv.ofHost` diverges under a `HostOk` host. -/
theorem diverged_of_silent {host : HostSemantics Nat} (hok : HostOk host) {s₀ : Store Nat}
    {ts : List CValType} {c : Config Nat} (hg : ShGood I s₀ ts c) {E : Ctx} {a hh : Nat}
    {args : List Val} {e : (ifaceSig I.imports).Op}
    (hd : decompose? c.store c.code = some (E, a, hh, args))
    (op : ifaceOp? I.imports hh args = some e)
    (hs : (SEnv.ofHost I.imports host).Silent () (shOp c.store e)) :
    host e.1.val c.store e.2.1 .diverged := by
  rcases hs with hdiv | hno
  · exact hdiv
  · obtain ⟨fi, hfi, hcode⟩ := fi_at_callout hd op
    obtain ⟨⟨out, hout⟩, htyped⟩ := hostOk_call hok hg.wf hfi hcode
    cases out with
    | diverged => exact hout
    | returned s' r =>
      obtain ⟨w, rfl⟩ := answer_of_resultTyped (htyped s' r hout).2.2
      exact absurd hout (hno (s', w) ())

/-- A product step against `SEnv.ofHost`, from the run invariant, is a Core step. -/
theorem core_of_shStep_ofHost {host : HostSemantics Nat} (hok : HostOk host) {s₀ : Store Nat}
    {ts : List CValType} {x y : Config Nat × Unit} (hg : ShGood I s₀ ts x.1)
    (h : ShStep P (SEnv.ofHost I.imports host) x y) : Step P host x.1 y.1 := by
  rcases shStep_elim h with ⟨h0, -⟩ | ⟨E, a, hh, args, e, s', w, hd, op, ans, hy⟩ |
      ⟨E, a, hh, args, e, hd, op, hs, rfl⟩
  · exact Step.of_noHost host h0
  · rw [hy]
    exact ScalarInstance.step_of_callout_returned hd ((host_at_callout op).2 ans)
  · exact ScalarInstance.step_of_callout_diverged hd
      ((host_at_callout op).2 (diverged_of_silent hok hg hd op hs))

section Runs

variable {host : HostSemantics Nat} (hok : HostOk host) (hk : I.HostKeeps host)
  {s₀ : Store Nat} {ts : List CValType}
include hok hk

/-- Core runs under the host are product runs. -/
theorem shSteps_of_steps {c c' : Config Nat} (hg : ShGood I s₀ ts c)
    (h : Steps P host c c') : ShSteps P (SEnv.ofHost I.imports host) (c, ()) (c', ()) := by
  induction h with
  | refl => exact .refl
  | @tail b c' _ hst ih =>
    have hb : ShGood I s₀ ts b := shGood_shSteps (x := (c, ())) (shEnvOk_ofHost hok hk s₀) hg ih
    exact ih.tail (core_shStep_ofHost hok hb hst)

/-- Product runs are Core runs under the host. -/
theorem steps_of_shSteps {c : Config Nat} {y : Config Nat × Unit} (hg : ShGood I s₀ ts c)
    (h : ShSteps P (SEnv.ofHost I.imports host) (c, ()) y) : Steps P host c y.1 := by
  induction h with
  | refl => exact .refl
  | @tail b y hb hst ih =>
    have hgb : ShGood I s₀ ts b.1 := shGood_shSteps (x := (c, ())) (shEnvOk_ofHost hok hk s₀) hg hb
    exact ih.tail (core_of_shStep_ofHost hok hgb hst)

/-- Infinite Core runs under the host are infinite product runs. -/
theorem inf_of_diverges {c : Config Nat} (hg : ShGood I s₀ ts c)
    (h : InfiniteTrace (Step P host) c) :
    InfiniteTrace (ShStep P (SEnv.ofHost I.imports host)) (c, ()) := by
  refine InfiniteTrace.coinduct (fun x => ShGood I s₀ ts x.1 ∧ InfiniteTrace (Step P host) x.1)
    ?_ ⟨hg, h⟩
  rintro ⟨c, ⟨⟩⟩ ⟨hgc, hinf⟩
  obtain ⟨c', hst, hinf'⟩ := hinf.unfold
  have hs : ShStep P (SEnv.ofHost I.imports host) (c, ()) (c', ()) := core_shStep_ofHost hok hgc hst
  exact ⟨(c', ()), hs, shGood_shStep (shEnvOk_ofHost hok hk s₀) hgc hs, hinf'⟩

/-- Infinite product runs are infinite Core runs under the host. -/
theorem diverges_of_inf {c : Config Nat} (hg : ShGood I s₀ ts c)
    (h : InfiniteTrace (ShStep P (SEnv.ofHost I.imports host)) (c, ())) :
    InfiniteTrace (Step P host) c := by
  refine InfiniteTrace.coinduct
    (fun c => ShGood I s₀ ts c ∧ InfiniteTrace (ShStep P (SEnv.ofHost I.imports host)) (c, ()))
    ?_ ⟨hg, h⟩
  rintro c ⟨hgc, hinf⟩
  obtain ⟨⟨c', ⟨⟩⟩, hst, hinf'⟩ := hinf.unfold
  exact ⟨c', core_of_shStep_ofHost hok hgc hst,
    shGood_shStep (x := (c, ())) (shEnvOk_ofHost hok hk s₀) hgc hst, hinf'⟩

/-- **The Core behaviours of an export call under a host are its product behaviours** against
the host as a shared environment. -/
theorem behaviours_eq_shBehavioursOf {f : I.shF.Op} (hw : I.WellFormed f.2.1) :
    behaviours P host f.2.1 (I.addr f.1) f.2.2.1 =
      shBehavioursOf P (SEnv.ofHost I.imports host) () (invoke f.2.1 (I.addr f.1) f.2.2.1) := by
  have hg := shGood_invoke (f := f) hw
  rw [behaviours_eq]
  ext b
  constructor
  · rintro (⟨c', r, run, final, rfl⟩ | ⟨rfl, hdiv⟩)
    · exact .inl ⟨c', (), r, shSteps_of_steps hok hk hg run, final, rfl⟩
    · exact .inr ⟨rfl, inf_of_diverges hok hk hg hdiv⟩
  · rintro (⟨c', q', r, run, final, rfl⟩ | ⟨rfl, hinf⟩)
    · exact .inl ⟨c', r, steps_of_shSteps hok hk hg run, final, rfl⟩
    · exact .inr ⟨rfl, diverges_of_inf hok hk hg hinf⟩

end Runs

/-- Hosts preserving the functions of the store keep host functions typed. -/
theorem hostKeeps_of_funcs {host : HostSemantics Nat}
    (h : ∀ hh s vs s' r, host hh s vs (.returned s' r) → s'.funcs = s.funcs) :
    I.HostKeeps host := by
  intro hh s vs s' r hw hr a fi h' ha hc
  exact hw.host_type a fi h' (h hh s vs s' r hr ▸ ha) hc

/-! ### Store-preserving environments -/

section Lift

variable {ts : List FnType} {L : SEnv (ifaceSig ts)}

/-- A product step of the lifted environment is a product step of `L`. -/
theorem sStep_of_shStep_liftSh {x y : Config Nat × L.S} (h : ShStep P (SEnv.liftSh L) x y) :
    SStep P L x y := by
  obtain ⟨c, q⟩ := x
  obtain ⟨c', q'⟩ := y
  rcases shStep_elim h with ⟨h0, hq⟩ | ⟨E, a, hh, args, e, s', w, hd, op, ⟨hs, hans⟩, hy⟩ |
      ⟨E, a, hh, args, e, hd, op, hs, hy⟩
  · have hq' : q' = q := hq
    rw [hq']
    exact .internal h0
  · have hs' : s' = c.store := hs
    have hy' : c' = ⟨c.store, c.frame, E.fill w.toResult.toAdmin⟩ := by rw [← hs']; exact hy
    rw [hy']
    exact .answer hd op hans
  · rw [hy]
    exact .silent hd op (hs.imp id fun h w q' hw => h (_, w) q' ⟨rfl, hw⟩)

/-- **The product steps of the lifted environment are those of `L`.** -/
theorem shStep_liftSh_iff {x y : Config Nat × L.S} :
    ShStep P (SEnv.liftSh L) x y ↔ SStep P L x y := by
  refine ⟨sStep_of_shStep_liftSh, fun h => ?_⟩
  cases h with
  | internal h0 => exact .internal h0
  | answer hd op ans => exact .answer hd op ⟨rfl, ans⟩
  | silent hd op hs => exact .silent hd op (hs.imp id fun h a q' ha => h a.2 q' ha.2)

theorem shStep_liftSh_eq : ShStep P (SEnv.liftSh L) = SStep P L := by
  funext x y
  exact propext shStep_liftSh_iff

/-- The product runs of the lifted environment are those of `L`. -/
theorem shSteps_liftSh_iff {x y : Config Nat × L.S} :
    ShSteps P (SEnv.liftSh L) x y ↔ SSteps P L x y := by
  unfold ShSteps SSteps
  rw [shStep_liftSh_eq]

/-- The lifted environment has the product behaviours of `L`. -/
theorem shBehavioursOf_liftSh (q : L.S) (c : Config Nat) :
    shBehavioursOf P (SEnv.liftSh L) q c = sbehavioursOf P L q c := by
  unfold shBehavioursOf sbehavioursOf ShSteps SSteps
  rw [shStep_liftSh_eq]

end Lift

/-- A store-preserving environment throwing existing exceptions is well formed. -/
theorem shEnvOk_liftSh {s : Store Nat} {L : SEnv I.E} (hL : L.ThrowsBelow s.exns.length) :
    I.ShEnvOk s (SEnv.liftSh L) := by
  rintro q e ⟨s', w⟩ q' hext hwf - ⟨hs, hans⟩
  have hs' : s' = e.2.1 := hs
  subst hs'
  exact ⟨hwf, Extend.refl hwf.storeOk, throwsBelow_mono (hL q (shCall e) w q' hans) hext.exns.1⟩

end Silmaril.Proofs.Wasm.Game.Shared
