module

public import Silmaril.Wasi.Versions.Stateful.Defs
public import Silmaril.Wasi.Comp.Thms
public import Silmaril.Wasi.Host.Thms

@[expose] public section

/-!
# Stateful components: the weakest-precondition method and linking

* `Wp.mono`, `Wp.bind`, `Wp.stable`: monotonicity, sequencing, and a frame rule (a predicate
  on the theory state preserved by every accepted answer survives any program).
* `ag_of_wpInv`: **the invariant method** for stateful components. If every export call in a
  state satisfying `J` runs a program whose weakest precondition gives back `J` and a return
  accepted by `P`, then the component satisfies `agP T (retG P)`.
* `link_model`: **the composite is a host**. A component of `agP T (retG P)` linked over any host
  satisfying `T` is a host satisfying `P` (its answers are the component's returns).
-/

namespace Silmaril.Wasi.Versions

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

variable {S ST SG : Type} {I X : Set FnName}

/-! ## Weakest preconditions -/

/-- Monotonicity in the postcondition. -/
theorem Wp.mono {A : Type} {T : Protocol ST WEv} {Q Q' : A → ST → Prop}
    (hQ : ∀ a q, Q a q → Q' a q) : ∀ {p : Prog (nsig I) A} {qT : ST}, Wp T p Q qT → Wp T p Q' qT
  | .pure _, _, h => hQ _ _ h
  | .call _ _, _, h => fun n qT' hn => Wp.mono hQ (h n qT' hn)

/-- Conjunction of postconditions. -/
theorem Wp.and {A : Type} {T : Protocol ST WEv} {Q Q' : A → ST → Prop} :
    ∀ {p : Prog (nsig I) A} {qT : ST}, Wp T p Q qT → Wp T p Q' qT →
      Wp T p (fun a q => Q a q ∧ Q' a q) qT
  | .pure _, _, h, h' => ⟨h, h'⟩
  | .call _ _, _, h, h' => fun n qT' hn => Wp.and (h n qT' hn) (h' n qT' hn)

/-- Sequencing. -/
theorem Wp.bind {A B : Type} {T : Protocol ST WEv} {Q : B → ST → Prop}
    (f : A → Prog (nsig I) B) : ∀ (p : Prog (nsig I) A) (qT : ST),
    Wp T (p.bind f) Q qT ↔ Wp T p (fun a q => Wp T (f a) Q q) qT
  | .pure _, _ => Iff.rfl
  | .call _ k, _ => forall_congr' fun n => forall_congr' fun _ => forall_congr' fun _ =>
      Wp.bind f (k n) _

/-- **Frame rule**: a predicate on the theory state that every accepted answer preserves
holds at the end of every program. -/
theorem Wp.stable {A : Type} {T : Protocol ST WEv} {R : ST → Prop}
    (hR : ∀ q e q', R q → T.step q e = some q' → R q')
    {Q : A → ST → Prop} (hQ : ∀ a q, R q → Q a q) :
    ∀ (p : Prog (nsig I) A) {qT : ST}, R qT → Wp T p Q qT
  | .pure a, _, hq => hQ a _ hq
  | .call _ k, _, hq => fun n _ hn => Wp.stable hR hQ (k n) (hR _ _ _ hq hn)

/-! ## The invariant method -/

/-- The state of the invariant method at a control state (for a body `h`, implicit). -/
def WpAt (T : Protocol ST WEv) (P : Protocol SG WEv) (J : S → ST → SG → Prop) :
    SCSt S I X → ST → SG → Prop
  | .idle s, qT, qG => J s qT qG
  | .run q p, qT, qG =>
    Wp T p (fun a qT' => ∃ qG', P.step qG (.imp q.1.1 q.2 a.2) = some qG' ∧ J a.1 qT' qG') qT
  | .wait q m k, qT, qG =>
    ∀ n qT', T.step qT (.imp m.1.1 m.2 n) = some qT' →
      Wp T (k n) (fun a qT'' => ∃ qG', P.step qG (.imp q.1.1 q.2 a.2) = some qG' ∧
        J a.1 qT'' qG') qT'

/-- One move keeps the state of the invariant method. -/
theorem WpAt.step {h : SBody S I X} {s₀ : S} {T : Protocol ST WEv} {P : Protocol SG WEv}
    {J : S → ST → SG → Prop} (hJ : WpInv h s₀ T P J) {c c' : SCSt S I X}
    {o : Move (nsig I) (nsig X)} (hc : SStep h c o c') {qT qT' : ST} {qG : SG}
    (hat : WpAt T P J c qT qG) (hT : T.run qT (hostView [wev o]) = some qT') :
    ∃ qG', (retG P).step qG (wev o) = some qG' ∧ WpAt T P J c' qT' qG' := by
  cases hc with
  | ask s q =>
    cases hT
    exact ⟨qG, rfl, hJ.call s qT qG q hat⟩
  | call q m k =>
    cases hT
    exact ⟨qG, rfl, hat⟩
  | reply q m k n =>
    have hT2 : (T.step qT (.imp m.1.1 m.2 n)).bind (fun q => some q) = some qT' := hT
    have hstep : T.step qT (.imp m.1.1 m.2 n) = some qT' := by simpa using hT2
    exact ⟨qG, rfl, hat n qT' hstep⟩
  | ret q s r =>
    cases hT
    obtain ⟨qG', hG, hJ'⟩ := hat
    exact ⟨qG', hG, hJ'⟩

/-- The state of the invariant method along reachable plays. -/
theorem WpInv.reach {h : SBody S I X} {s₀ : S} {T : Protocol ST WEv} {P : Protocol SG WEv}
    {J : S → ST → SG → Prop} (hJ : WpInv h s₀ T P J) {t : List (Move (nsig I) (nsig X))}
    {c : SCSt S I X} (ht : SReach h s₀ t c) :
    ∀ qT, T.run T.init (hostView (wtrace t)) = some qT →
      ∃ qG, (retG P).run P.init (wtrace t) = some qG ∧ WpAt T P J c qT qG := by
  induction ht with
  | nil => exact fun qT hT => ⟨P.init, rfl, (Option.some.inj hT) ▸ hJ.init⟩
  | @snoc t c c' o _ hc ih =>
    intro qT' hT
    have hT' : (T.run T.init (hostView (wtrace t))).bind
        (fun q => T.run q (hostView [wev o])) = some qT' := by
      rw [← Protocol.run_append, ← hostView_append, ← wtrace_concat]
      exact hT
    obtain ⟨qT, hqT, hstepT⟩ := Option.bind_eq_some_iff.1 hT'
    obtain ⟨qG, hqG, hat⟩ := ih qT hqT
    obtain ⟨qG', hstepG, hat'⟩ := WpAt.step hJ hc hat hstepT
    refine ⟨qG', ?_, hat'⟩
    rw [wtrace_concat, Protocol.run_concat]
    exact (congrArg (fun x => x.bind fun q => (retG P).step q (wev o)) hqG).trans hstepG

/-- **The invariant method** for stateful components. -/
theorem ag_of_wpInv {h : SBody S I X} {s₀ : S} {T : Protocol ST WEv} {P : Protocol SG WEv}
    {J : S → ST → SG → Prop} (hJ : WpInv h s₀ T P J) : (agP T (retG P)).holds (ofSBody h s₀) := by
  rintro t ⟨c, ht⟩ hA
  obtain ⟨qT, hqT⟩ := (Protocol.accepts_iff_exists _ _).1 hA
  obtain ⟨qG, hqG, -⟩ := hJ.reach ht qT hqT
  exact (Protocol.accepts_iff_exists _ _).2 ⟨qG, hqG⟩

/-! ## Reading returns as answers -/

/-- The run of `retG P` is the run of `P` on the returns. -/
theorem run_retG (P : Protocol SG WEv) (q : SG) (t : List WEv) :
    (retG P).run q t = P.run q (retAsImp t) := by
  induction t generalizing q with
  | nil => rfl
  | cons e t ih =>
    cases e with
    | ret f a r =>
      show (P.step q (.imp f a r)).bind (fun q' => (retG P).run q' t) =
        (P.step q (.imp f a r)).bind (fun q' => P.run q' (retAsImp t))
      exact congrArg (Option.bind _) (funext ih)
    | req f a => exact ih q
    | imp f a r => exact ih q
    | call f a => exact ih q

/-- `retG P` accepts exactly when `P` accepts the returns. -/
theorem accepts_retG (P : Protocol SG WEv) (t : List WEv) :
    (retG P).Accepts t ↔ P.Accepts (retAsImp t) := by
  unfold Protocol.Accepts
  rw [show (retG P).init = P.init from rfl, run_retG]

/-- The returns are on the export side. -/
theorem retAsImp_expView (t : List WEv) : retAsImp (expView t) = retAsImp t := by
  induction t with
  | nil => rfl
  | cons e t ih =>
    cases e <;> simp [expView, retAsImp, retImp, WEv.isExp, List.filter_cons] at ih ⊢ <;>
      exact ih

/-- The answers of a linked system are its export returns. -/
theorem htrace_eq_retAsImp {Y : Sig.{0}} (p : List (Move Y (nsig X))) :
    htrace p = retAsImp (xtrace p) := by
  induction p with
  | nil => rfl
  | cons o p ih =>
    rcases o with (⟨m⟩ | ⟨m, n⟩) | (⟨q⟩ | ⟨q, n⟩) <;>
      simp [htrace, xtrace, retAsImp, hev, xev, retImp] at ih ⊢ <;> exact ih

/-- **The composite is a host**: a component satisfying `agP T (retG P)`, linked over any host
satisfying `T`, is a host satisfying `P`. -/
theorem link_model {Y : Sig.{0}} {T : Protocol ST WEv} {P : Protocol SG WEv}
    {σ : Strategy (nsig I) (nsig X)} (hσ : (agP T (retG P)).holds σ) {η : Host Y I}
    (hη : (hostSat T.Accepts).holds η) : (hostSat P.Accepts).holds (link η σ) := by
  intro p hp
  have hG := link_sat (A := T.Accepts) (G := fun t => P.Accepts (retAsImp t))
    (fun s hs hA => by
      show P.Accepts (retAsImp (expView (wtrace s)))
      rw [retAsImp_expView]
      exact (accepts_retG P _).1 (hσ s hs hA)) hη p hp
  rw [htrace_eq_retAsImp]
  exact hG

end Silmaril.Wasi.Versions
