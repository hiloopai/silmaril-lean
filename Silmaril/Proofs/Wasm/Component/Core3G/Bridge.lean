module

public import Silmaril.Wasm.Component.Param.Defs
public import Silmaril.Wasm.Game.Instantiate.Thms
public import Silmaril.Games.Handler.Thms

/-!
# The engine semantics of `core3P P` and `modSem P`: proofs

Proofs for `Silmaril.Wasm.Component.Core3G.Thms`:

* `engine_two_refuse_iff`: an engine instance answers a question without a callee (ill-typed, or
  with no export address) by a trap, and by nothing else;
* `comp_handler_pure_iff`: composed with a handler that answers `q` at once with `r₀`, a strategy
  answers `q` exactly with `r₀`; `comp_empty_iff`: composition below with a strategy over an
  empty middle interface does not change one-call plays;
* `modSem_two_refuse_iff`: `modSem P` answers an ill-typed question by a trap, and by nothing
  else;
* `modSem_eq_of_isInst`: `modSem P` does not depend on the choice of instance.
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Core3G

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm (NumType)

universe u

/-! ## Generic facts on one-call plays -/

section Generic

variable {E F G : Sig.{u}}

/-- The one-call play answering `q` with `a`. -/
abbrev two (q : F.Op) (a : F.Ar q) : List (Move E F) := [.inr (.ask q), .inr (.ans q a)]

theorem legal_two (q : F.Op) (a : F.Ar q) : Legal (two (E := E) q a) :=
  ⟨_, .cons (.ask q) (.cons (.ret q a) (.nil _))⟩

/-- A play of a strategy of a transition system that ends with a Proponent move is a trace. -/
theorem trace_of_mem_ofLTS {L : LTS E F} {p : List (Move E F)} {o : Move E F} (ho : o.IsP)
    (h : p ++ [o] ∈ Strategy.ofLTS L) : p ++ [o] ∈ L.Traces := by
  obtain ⟨-, s, hs, hp⟩ := h
  rcases hp with hp | ⟨p₀, o', hpo, -, ho'⟩
  · rcases hs with rfl | ⟨hs, -⟩
    · exact absurd (List.prefix_nil.1 hp) (by simp)
    · exact LTS.traces_of_prefix hs hp
  · obtain ⟨-, h⟩ := List.append_inj' hpo rfl
    simp only [List.cons.injEq, and_true] at h
    subst h
    exact absurd ho' (Move.not_isO_of_isP ho)

/-- Silent runs of a transition system without silent steps stay put. -/
theorem run_nil_eq {L : LTS E F} (hτ : ∀ x y, ¬ L.step x none y) {x y : L.State}
    (h : L.Run x [] y) : y = x := by
  cases h with
  | nil => rfl
  | tau hs _ => exact absurd hs (hτ _ _)

/-- Handlers take no silent step. -/
theorem handler_no_tau (h : Handler E F) (x y : h.toReduction.State) :
    ¬ h.toReduction.toLTS.step x none y := by
  intro hs
  cases hs with
  | tau hc => exact hc

/-- **A handler that answers `q` at once with `r₀`**: composed above any strategy, `q` is answered
exactly by `r₀`. -/
theorem comp_handler_pure_iff (σ : Strategy E F) (h : Handler F G) {q : G.Op} {r₀ : G.Ar q}
    (hq : h q = .pure r₀) (r : G.Ar q) : two q r ∈ σ.comp (Strategy.ofHandler h) ↔ r = r₀ := by
  constructor
  · show two q r ∈ σ.comp (Strategy.ofHandler h) → r = r₀
    rintro ⟨s, -, t, ht, hz⟩
    obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.1 ht
    cases hz with
    | sync b hz' =>
      obtain ⟨x₁, x₂, h₀, h₁, -⟩ := LTS.Run.cons_inv hy
      cases run_nil_eq (handler_no_tau h) h₀
      cases h₁
    | right c hz' =>
      show r = r₀
      obtain ⟨x₁, x₂, h₀, h₁, hy'⟩ := LTS.Run.cons_inv hy
      cases run_nil_eq (handler_no_tau h) h₀
      cases h₁ with
      | ask _ =>
        show r = r₀
        cases hz' with
        | sync b _ =>
          obtain ⟨x₃, x₄, h₀', h₂, -⟩ := LTS.Run.cons_inv hy'
          cases run_nil_eq (handler_no_tau h) h₀'
          cases h₂ with
          | call hc => exact absurd (hq.symm.trans hc) nofun
        | right c' _ =>
          obtain ⟨x₃, x₄, h₀', h₂, -⟩ := LTS.Run.cons_inv hy'
          cases run_nil_eq (handler_no_tau h) h₀'
          cases h₂ with
          | ret hd =>
            have h' : (Prog.pure r₀ : Prog F (G.Ar q)) = .pure r := hq.symm.trans hd
            exact (Prog.pure.inj h').symm
  · intro hr
    subst hr
    refine ⟨[], σ.nil_mem, two q r, Strategy.mem_ofHandler.2 ⟨.idle, ?_⟩, .right _ (.right _ .nil)⟩
    exact .vis (Reduction.Step.ask q) (.vis (Reduction.Step.ret hq) (.nil _))

/-- Composition below with a strategy over an empty middle interface keeps one-call plays. -/
theorem comp_empty_iff (ρ : Strategy E F) (τ : Strategy F G) (hF : IsEmpty F.Op) (q : G.Op)
    (r : G.Ar q) : two q r ∈ ρ.comp τ ↔ two q r ∈ τ := by
  constructor
  · rintro ⟨s, -, t, ht, hz⟩
    cases hz with
    | sync b _ => exact (hF.false (match b with | .ask m => m | .ans m _ => m)).elim
    | right c hz' =>
      cases hz' with
      | sync b _ => exact (hF.false (match b with | .ask m => m | .ans m _ => m)).elim
      | right c' hz'' =>
        cases hz'' with
        | nil => exact ht
        | sync b _ => exact (hF.false (match b with | .ask m => m | .ans m _ => m)).elim
  · intro h
    exact ⟨[], ρ.nil_mem, _, h, .right _ (.right _ .nil)⟩

end Generic

/-! ## Ill-typed questions -/

/-- **An engine instance refuses a question without a callee**: it answers it by a trap and by
nothing else. -/
theorem engine_two_refuse_iff (E : Engine) (I : EInstance E) (imps exps : CoreIface)
    {q : (sigN exps.length).Op} (hq : callee? I.addrs exps q = none) (r : Option Payload) :
    two q r ∈ engineStrategy E I imps exps ↔ r = none := by
  constructor
  · show two q r ∈ engineStrategy E I imps exps → r = none
    intro h
    obtain ⟨y, hy⟩ := trace_of_mem_ofLTS (p := [.inr (.ask q)]) (by exact trivial) h
    have hτ : ∀ x y, ¬ (engineLTS E I imps exps).step x none y := by
      rintro _ _ ⟨_, h, _⟩
      cases h
    obtain ⟨x₁, x₂, h₀, ⟨_, hm, h₁⟩, hy'⟩ := LTS.Run.cons_inv hy
    cases run_nil_eq hτ h₀
    cases hm
    cases h₁ with
    | call hc => exact absurd (hq.symm.trans hc) nofun
    | refuse _ =>
      obtain ⟨x₃, x₄, h₀', ⟨_, hm', h₂⟩, -⟩ := LTS.Run.cons_inv hy'
      cases run_nil_eq hτ h₀'
      cases hm'
      cases h₂
      rfl
  · rintro rfl
    refine Strategy.mem_ofLTS_of_mem_traces ⟨EState.idle I.store, ?_⟩ (legal_two _ _)
    exact .vis ⟨_, rfl, ETrans.refuse hq⟩ (.vis ⟨_, rfl, ETrans.refused⟩ (.nil _))

/-- The numeric instance of a module with its instance. -/
@[expose] def numInst {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I) :
    NumInstance :=
  { inst := I, imports := [], exports := m.exports, imports_eq := hI.2.1, exports_eq := hI.2.2 }

/-- **`modSem P` does not depend on the choice of instance.** -/
theorem modSem_eq_of_isInst (P : Profile) {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) : (modSem P).sem m = (core3Sem P).sem (numInst hI) := by
  have hex : ∃ J, m.IsInst J := ⟨I, hI⟩
  have key : ∀ (J : Silmaril.Wasm.Game.ScalarInstance) (hJ : m.IsInst J),
      (core3Sem P).sem (numInst hJ) = (core3Sem P).sem (numInst hI) := by
    intro J hJ
    obtain ⟨⟨mt, hmt⟩, _, _⟩ := hJ
    obtain ⟨⟨mt', hmt'⟩, _, _⟩ := hI
    have hv : some mt = some mt' := hmt.valid.symm.trans hmt'.valid
    cases Option.some.inj hv
    obtain rfl := Silmaril.Wasm.Game.IsInstance.unique hmt hmt'
    rfl
  simp only [modSem, dite_eq_left_of_eq_true (eq_true hex)]
  exact key _ hex.choose_spec

/-- **`modSem P` refuses a question that its export handler answers at once**: by a trap and by
nothing else. -/
theorem modSem_two_refuse_iff (P : Profile) {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) {q : (CoreIface.sig m.exports).Op}
    (hq : exportH (numInst hI) q = .pure none) (r : Option Payload) :
    two (E := CoreIface.sig []) q r ∈ (modSem P).sem m ↔ r = none := by
  rw [modSem_eq_of_isInst P hI]
  have hE : IsEmpty (Silmaril.Wasm.Game.ifaceSig (numInst hI).inst.imports).Op :=
    ⟨fun e => absurd e.1.isLt (by simp [numInst, hI.2.1])⟩
  change two q r ∈ (Strategy.ofHandler (importH (numInst hI))).comp
    (((numInst hI).inst.strategy P (numInst hI).inst.store).comp
      (Strategy.ofHandler (exportH (numInst hI)))) ↔ r = none
  exact (comp_empty_iff _ _ hE q r).trans (comp_handler_pure_iff _ _ hq r)

/-! ## Ill-typed questions on both sides -/

/-- A strategy of a handler that answers `q` at once with `r₀` answers it exactly with `r₀`. -/
theorem handler_two_iff {E F : Sig.{0}} (h : Handler E F) {q : F.Op} {r₀ : F.Ar q}
    (hq : h q = .pure r₀) (r : F.Ar q) : two q r ∈ Strategy.ofHandler h ↔ r = r₀ := by
  have h' := comp_handler_pure_iff (Strategy.id E) h hq r
  rwa [Strategy.id_comp] at h'

/-- Values of numeric scalar types are flat values of these types. -/
theorem flatTyped_of_hasVal :
    ∀ {ps : List NumType} {xs : List Flat},
      List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (ps.map .num)
        (xs.map Silmaril.Wasm.SingleThreaded.ofFlat) → FlatTyped ps xs
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | p :: ps, x :: xs, h => by
    obtain _ | ⟨⟨bits, hb⟩, h'⟩ := h
    have hx : x.type = p := by
      simp only [Silmaril.Wasm.SingleThreaded.ofFlat] at hb
      injection hb with hb
      injection hb
    change x.type :: xs.map (·.type) = p :: ps
    rw [hx, flatTyped_of_hasVal h']

/-- An ill-typed question is answered at once by the export handler of `modSem`. -/
theorem exportH_ill {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I)
    {q : (CoreIface.sig m.exports).Op} (hill : ∀ xs, q.2 = .flat xs →
      ¬ FlatTyped (m.exports[q.1]).2.params xs) :
    exportH (numInst hI) q = .pure none := by
  obtain ⟨j, pl⟩ := q
  cases pl with
  | vals _ => rfl
  | flat xs =>
    show exportH (numInst hI) (j, .flat xs) = .pure none
    have hnt := hill xs rfl
    have hparams : ((numInst hI).inst.exports.get (Fin.cast (numInst hI).exports_length j)).params =
        (m.exports[j].2.params).map .num := by
      simp only [numInst, List.get_eq_getElem, hI.2.2, List.getElem_map, fnOf]
      rfl
    have ht : typed? ((numInst hI).inst.exports.get (Fin.cast (numInst hI).exports_length j)).params
        (xs.map Silmaril.Wasm.SingleThreaded.ofFlat) = none := by
      have hnf : ¬ List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal
          ((numInst hI).inst.exports.get (Fin.cast (numInst hI).exports_length j)).params
          (xs.map Silmaril.Wasm.SingleThreaded.ofFlat) := by
        intro hf
        rw [hparams] at hf
        exact hnt (flatTyped_of_hasVal hf)
      unfold typed?
      simp only [hnf, dite_false]
    simp only [exportH, ht]

/-- An ill-typed question has no callee. -/
theorem callee_ill {E : Engine} (addrs : List E.FuncAddr) (exps : CoreIface)
    {q : (sigN exps.length).Op} (hill : ∀ xs, q.2 = .flat xs → ¬ FlatTyped exps[q.1].2.params xs) :
    callee? addrs exps q = none := by
  obtain ⟨j, pl⟩ := q
  cases pl with
  | vals _ => rfl
  | flat xs => simp only [callee?, hill xs rfl, ite_false]

/-- **On ill-typed questions the engine semantics of `core3P P` traps**, with or without an
instance. -/
theorem engineSem_two_ill (P : Profile) (m : NumModule) {q : (CoreIface.sig m.exports).Op}
    (hill : ∀ xs, q.2 = .flat xs → ¬ FlatTyped (m.exports[q.1]).2.params xs) (r : Option Payload) :
    two q r ∈ (engineSem (core3P P) NumModule NumModule.mod).sem m ↔ r = none := by
  simp only [engineSem]
  split
  · exact engine_two_refuse_iff _ _ _ _ (callee_ill _ _ hill) r
  · exact handler_two_iff (E := CoreIface.sig []) (F := CoreIface.sig m.exports)
      (fun _ => .pure none) (q := q) rfl r

/-- **On ill-typed questions `modSem P` traps**, with or without an instance. -/
theorem modSem_two_ill (P : Profile) (m : NumModule) {q : (CoreIface.sig m.exports).Op}
    (hill : ∀ xs, q.2 = .flat xs → ¬ FlatTyped (m.exports[q.1]).2.params xs) (r : Option Payload) :
    two q r ∈ (modSem P).sem m ↔ r = none := by
  by_cases hex : ∃ I, m.IsInst I
  · obtain ⟨I, hI⟩ := hex
    exact modSem_two_refuse_iff P hI (exportH_ill hI hill) r
  · simp only [modSem, dite_eq_right_of_eq_false (eq_false hex)]
    exact handler_two_iff (E := CoreIface.sig []) (F := CoreIface.sig m.exports)
      (fun _ => .pure none) (q := q) rfl r

/-- **Without an instance on either side, the two semantics agree** (both trap everywhere). -/
theorem engineSem_eq_modSem_of_none (P : Profile) (m : NumModule)
    (he : instOf (core3P P) m.mod [] m.exports = none) (hm : ¬ ∃ I, m.IsInst I) :
    (engineSem (core3P P) NumModule NumModule.mod).sem m = (modSem P).sem m := by
  simp only [engineSem, modSem, dite_eq_right_of_eq_false (eq_false hm)]
  have he' : instOf (core3P P) (NumModule.mod m) (CoreModule.imports m) (CoreModule.exports m) =
      none := he
  rw [he']

end Silmaril.Proofs.Wasm.Component.Core3G
