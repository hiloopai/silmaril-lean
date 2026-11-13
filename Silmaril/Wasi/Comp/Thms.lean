module

public import Silmaril.Wasi.Comp.Defs
public import Silmaril.Wasm.Resource.Protocol.Thms

@[expose] public section

/-!
# Components with uninterpreted imports: proving assume–guarantee sentences

`ag_of_inv`: the invariant method. To show that `ofBody h` satisfies `agP T G` (under the theory
`T` on the host's answers, the guarantee `G` holds), give an invariant `J` between the control
state of the component, the state of `T` and the state of `G`, which holds initially and is
preserved by every move of the component that `T` does not reject. Moves are steps of
`CStep h`, so the proof is a case analysis on the program of the body.
-/

namespace Silmaril.Wasi

open Silmaril.Games
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component (Val)

variable {I X : Set FnName} {h : Body I X} {ST SG : Type}

/-- The events of a play extended by a move. -/
theorem wtrace_concat (s : List (Move (nsig I) (nsig X))) (o : Move (nsig I) (nsig X)) :
    wtrace (s ++ [o]) = wtrace s ++ [wev o] :=
  List.map_append

/-- The host view distributes over concatenation. -/
theorem hostView_append (t u : List WEv) : hostView (t ++ u) = hostView t ++ hostView u :=
  List.filter_append t u

/-- A non-answer event is invisible to the host view. -/
theorem hostView_single_of_not_imp {e : WEv} (he : e.isImp = false) : hostView [e] = [] := by
  simp [hostView, he]

/-! ## Inversion of the moves of a component -/

/-- From `idle`, an export call. -/
theorem CStep.idle_inv {o : Move (nsig I) (nsig X)} {c' : CSt I X} (hc : CStep h .idle o c') :
    ∃ q, o = .inr (.ask q) ∧ c' = .run q (h q) := by
  cases hc
  exact ⟨_, rfl, rfl⟩

/-- A program calling an import makes the call. -/
theorem CStep.call_inv {q : (nsig X).Op} {m : (nsig I).Op} {k : Option (List Val) → BProg I}
    {o : Move (nsig I) (nsig X)} {c' : CSt I X} (hc : CStep h (.run q (.call m k)) o c') :
    o = .inl (.ask m) ∧ c' = .wait q m k := by
  cases hc
  exact ⟨rfl, rfl⟩

/-- A program returning returns. -/
theorem CStep.pure_inv {q : (nsig X).Op} {r : Option (List Val)} {o : Move (nsig I) (nsig X)}
    {c' : CSt I X} (hc : CStep h (.run q (.pure r)) o c') : o = .inr (.ans q r) ∧ c' = .idle := by
  cases hc
  exact ⟨rfl, rfl⟩

/-- A waiting component receives an answer. -/
theorem CStep.wait_inv {q : (nsig X).Op} {m : (nsig I).Op} {k : Option (List Val) → BProg I}
    {o : Move (nsig I) (nsig X)} {c' : CSt I X} (hc : CStep h (.wait q m k) o c') :
    ∃ n, o = .inl (.ans m n) ∧ c' = .run q (k n) := by
  cases hc
  exact ⟨_, rfl, rfl⟩

/-- The expectations of the invariant method. -/
structure Inv (h : Body I X) (T : Protocol ST WEv) (G : Protocol SG WEv)
    (J : CSt I X → ST → SG → Prop) : Prop where
  /-- The invariant holds initially. -/
  init : J .idle T.init G.init
  /-- Every move that `T` does not reject keeps the invariant, and `G` accepts its event. -/
  step : ∀ {c c' : CSt I X} {o : Move (nsig I) (nsig X)} {qT : ST} {qG : SG} {qT' : ST},
    CStep h c o c' → J c qT qG → T.run qT (hostView [wev o]) = some qT' →
      ∃ qG', G.step qG (wev o) = some qG' ∧ J c' qT' qG'

/-- The invariant along reachable plays. -/
theorem Inv.reach {T : Protocol ST WEv} {G : Protocol SG WEv} {J : CSt I X → ST → SG → Prop}
    (hJ : Inv h T G J) {s : List (Move (nsig I) (nsig X))} {c : CSt I X} (hs : Reach h s c) :
    ∀ qT, T.run T.init (hostView (wtrace s)) = some qT →
      ∃ qG, G.run G.init (wtrace s) = some qG ∧ J c qT qG := by
  induction hs with
  | nil => exact fun qT hT => ⟨G.init, rfl, (Option.some.inj hT) ▸ hJ.init⟩
  | @snoc s c c' o _ hc ih =>
    intro qT' hT
    have hT' : (T.run T.init (hostView (wtrace s))).bind
        (fun q => T.run q (hostView [wev o])) = some qT' := by
      rw [← Protocol.run_append, ← hostView_append, ← wtrace_concat]
      exact hT
    obtain ⟨qT, hqT, hstepT⟩ := Option.bind_eq_some_iff.1 hT'
    obtain ⟨qG, hqG, hJc⟩ := ih qT hqT
    obtain ⟨qG', hstepG, hJc'⟩ := hJ.step hc hJc hstepT
    refine ⟨qG', ?_, hJc'⟩
    rw [wtrace_concat, Protocol.run_concat, hqG]
    exact hstepG

/-- **The invariant method** for assume–guarantee sentences of components. -/
theorem ag_of_inv {T : Protocol ST WEv} {G : Protocol SG WEv} {J : CSt I X → ST → SG → Prop}
    (hJ : Inv h T G J) : (agP T G).holds (ofBody h) := by
  rintro s ⟨c, hs⟩ hA
  obtain ⟨qT, hqT⟩ := (Protocol.accepts_iff_exists _ _).1 hA
  obtain ⟨qG, hqG, -⟩ := hJ.reach hs qT hqT
  exact (Protocol.accepts_iff_exists _ _).2 ⟨qG, hqG⟩

end Silmaril.Wasi
