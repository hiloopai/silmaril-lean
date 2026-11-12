module

public import Silmaril.Libc.Contract.Inst.Defs

/-!
# Clients see only the contract

PROVED (standard axioms), names in `Silmaril.Libc.Contracts`:

* the institution: `inst` (`Defs`, a functor into rooms) and `inst_sat_iff` (its satisfaction
  condition, `sat_map_iff`, read off the functor);
* **clients**: `Prog.sound` (a run of a client whose weakest precondition holds, against a model
  meeting the contract relative to `I`, does not crash and ends in a state related by `I` to an
  abstract state satisfying `Q`); **`client_correct`** (the same with the invariant hidden: a
  client verified against `(S, C)` is correct on every model of `C`, from every valid start
  state); `client_swap` (two models of one contract are interchangeable);
* **clients of a smaller signature**: `Prog.run_map` (running a client through the reduct is
  running it on the bigger model) and **`client_reduct`**: a client verified against `(S, C)`
  runs correctly on every model of a bigger signature that satisfies the translation of `C`
  (e.g. a `malloc`/`free` client on a full allocator); `client_reduct'` from the reduct.
-/

@[expose] public section

namespace Silmaril.Libc.Contracts

open CategoryTheory Silmaril.Logic.Institution

variable {A : Api} {S T : Sig A} {α : Type}

/-- The satisfaction condition of `inst`. -/
theorem inst_sat_iff {S T : Sig A} (σ : S ⟶ T) (M : Model T) (C : Contract S) :
    Sat M (C.map σ) ↔ Sat (M.reduct σ) C :=
  satisfaction_condition inst σ (Discrete.mk M) C

namespace Prog

/-- **Soundness of client reasoning**, relative to the model's invariant. -/
theorem sound {M : Model S} {C : Contract S} {I : S.G → M.St → Prop} (h : Holds M C I)
    {Q : α → S.G → Prop} {p : Prog S α} {s : M.St} {o : Outcome M.St α} (hr : Run M p s o) :
    ∀ g, I g s → WP C Q p g → ∃ a t g', o = .done a t ∧ I g' t ∧ Q a g' := by
  induction hr with
  | ret a s => intro g hI hw; exact ⟨a, s, g, rfl, hI, hw⟩
  | ub hs => intro g hI hw; exact absurd hs (h.safe _ _ g _ _ hI hw.1)
  | call hs _ ih =>
    intro g hI hw
    obtain ⟨g', hI', hq⟩ := h.post _ _ g _ _ _ _ hI hw.1 hs
    exact ih g' hI' (hw.2 _ g' hq)

theorem map_of_run (σ : Sig.Hom S T) {M : Model T} {p : Prog S α} {s : (M.reduct σ).St}
    {o : Outcome (M.reduct σ).St α} (hr : Run (M.reduct σ) p s o) : Run M (p.map σ) s o := by
  induction hr with
  | ret a s => exact Run.ret (M := M) a s
  | ub hs => exact Run.ub (M := M) hs
  | call hs _ ih => exact Run.call (M := M) hs ih

theorem run_of_map (σ : Sig.Hom S T) {M : Model T} {p : Prog S α} {s : M.St}
    {o : Outcome M.St α} (hr : Run M (p.map σ) s o) : Run (M.reduct σ) p s o := by
  induction p generalizing s o with
  | ret a => cases hr; exact Run.ret (M := M.reduct σ) a s
  | call f hf x k ih =>
    cases hr with
    | ub hs => exact Run.ub (M := M.reduct σ) hs
    | call hs hr' => exact Run.call (M := M.reduct σ) hs (ih _ hr')

/-- Running a client through the reduct is running its image on the bigger model. -/
theorem run_map (σ : Sig.Hom S T) {M : Model T} {p : Prog S α} {s : M.St}
    {o : Outcome M.St α} : Run (M.reduct σ) p s o ↔ Run M (p.map σ) s o :=
  ⟨map_of_run σ, run_of_map σ⟩

end Prog

/-- **A client verified against `(S, C)` is correct on every model of `C`**: from every valid
start state, a run does not crash and its result satisfies `Q` (for some abstract state). The
model's invariant does not appear. -/
theorem client_correct {M : Model S} {C : Contract S} (hM : Sat M C) {Q : α → S.G → Prop}
    {p : Prog S α} (hp : p.Verified C Q) {s : M.St} (hs : M.init s) {o : Outcome M.St α}
    (hr : Prog.Run M p s o) : ∃ a t, o = .done a t ∧ ∃ g, Q a g := by
  obtain ⟨I, h⟩ := hM
  obtain ⟨g, hi, hI⟩ := h.init s hs
  obtain ⟨a, t, g', ho, _, hq⟩ := Prog.sound h hr g hI (hp g hi)
  exact ⟨a, t, ho, g', hq⟩

/-- **Swapping implementations is free**: a verified client is correct on both of two models of
the same contract. -/
theorem client_swap {M N : Model S} {C : Contract S} (hM : Sat M C) (hN : Sat N C)
    {Q : α → S.G → Prop} {p : Prog S α} (hp : p.Verified C Q) :
    (∀ s o, M.init s → Prog.Run M p s o → ∃ a t, o = .done a t ∧ ∃ g, Q a g) ∧
      (∀ s o, N.init s → Prog.Run N p s o → ∃ a t, o = .done a t ∧ ∃ g, Q a g) :=
  ⟨fun _ _ hs hr => client_correct hM hp hs hr, fun _ _ hs hr => client_correct hN hp hs hr⟩

/-- **A client of a smaller signature runs on a bigger library**: verified against `(S, C)`, it
is correct on every model of `T` that satisfies the translation of `C` along `σ`. -/
theorem client_reduct (σ : Sig.Hom S T) {M : Model T} {C : Contract S} (hM : Sat M (C.map σ))
    {Q : α → S.G → Prop} {p : Prog S α} (hp : p.Verified C Q) {s : M.St} (hs : M.init s)
    {o : Outcome M.St α} (hr : Prog.Run M (p.map σ) s o) : ∃ a t, o = .done a t ∧ ∃ g, Q a g :=
  client_correct ((sat_map_iff σ M C).1 hM) hp hs ((Prog.run_map σ).2 hr)

/-- The same, from the reduct: a client of `S` runs correctly on every model of `T` whose reduct
meets `C` (e.g. the reduct of a tensor's factor). -/
theorem client_reduct' (σ : Sig.Hom S T) {M : Model T} {C : Contract S}
    (hM : Sat (M.reduct σ) C) {Q : α → S.G → Prop} {p : Prog S α} (hp : p.Verified C Q)
    {s : M.St} (hs : M.init s) {o : Outcome M.St α} (hr : Prog.Run M (p.map σ) s o) :
    ∃ a t, o = .done a t ∧ ∃ g, Q a g :=
  client_correct hM hp hs ((Prog.run_map σ).2 hr)

end Silmaril.Libc.Contracts
