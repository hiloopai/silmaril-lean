module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Refs

/-!
# The base's `TypingFacts` hold in every `simEnv B`

`typingFacts_simEnv`: the structural typing facts the generic forward assembly consumes. A typed
configuration is a typed state and typed code (`config`), a typed state a typed store and frame
(`state`), `instr*` is checked elementwise (`append`), every value sequence is a typed `val*`
(`vals`, now unconditionally: `typedV_val`), and the components of typed labels, handlers and
frames are typed. All are inversions of closed IL types (`config`, `state`, `instr`), whose
typing does not depend on a term-only scope.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Typing

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d572 Original.d573)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-- A type whose typing is the same in every term-only scope. -/
def ClosedT (B : Builtins) (τ : Typ) : Prop :=
  ∀ {ρ ρ' : VarEnv} {u : Value}, ValsOnly ρ → ValsOnly ρ' → HasTyp (simEnv B) ρ τ u →
    HasTyp (simEnv B) ρ' τ u

theorem closedT_var (x : IL.Id) : ClosedT B (.varT x []) := fun hρ hρ' h =>
  IntNumeric.hasTyp_varT_nil_congr hρ hρ' h

theorem closedT_list (x : IL.Id) : ClosedT B (.iterT (.varT x []) .list) := fun hρ hρ' h => by
  obtain ⟨l, rfl, hl⟩ := hasTyp_iterT_list_iff.1 h
  exact hasTyp_iterT_list_iff.2 ⟨l, rfl, hasTypList_iff.2 fun u hu =>
    IntNumeric.hasTyp_varT_nil_congr hρ hρ' (hasTypList_iff.1 hl u hu)⟩

/-- A closed type's `TypedV` is its typing in the empty scope. -/
theorem typedV_iff_empty {τ : Typ} (hc : ClosedT B τ) {u : Value} :
    TypedV (simEnv B) τ u ↔ HasTyp (simEnv B) VarEnv.empty τ u :=
  ⟨fun h => h _ ⟨rfl, rfl, rfl⟩, fun h _ hρ => hc ⟨rfl, rfl, rfl⟩ hρ h⟩

/-- A typed closed one-instance variant is a typed case of it, in the empty scope. -/
theorem hasTypCase_of_closedVariant {x op : IL.Id} {cs : List TypCase} {w : Value}
    (htd : (simEnv B).findTyp? x = some ([], [.instD [] [] (.variantT cs)]))
    (h : HasTyp (simEnv B) VarEnv.empty (.varT x []) (.case op w)) :
    HasTypCase (simEnv B) VarEnv.empty cs op w := by
  obtain ⟨td, ws, htd', -, hi⟩ := (hasTyp_varT_global_iff rfl).1 h
  rw [htd] at htd'
  obtain rfl := (Option.some.inj htd').symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hrest
  · obtain rfl := IntNumeric.matchArgs_nil_scope hm
    obtain ⟨op', w', he, hc⟩ := hasTypDef_variantT_iff.1 hd
    cases he
    exact hc
  · exact absurd hrest not_hasTypInsts_nil

/-- The components of a typed pair. -/
theorem hasTyp_pair_inv {σ : VarEnv} {a b : IL.Id} {τ₁ τ₂ : Typ} {u v : Value}
    (h : HasTyp (simEnv B) σ (.tupT [.mk a τ₁, .mk b τ₂]) (.tuple [u, v])) :
    HasTyp (simEnv B) σ τ₁ u ∧ HasTyp (simEnv B) (σ.bindVal a u) τ₂ v := by
  obtain ⟨_, he, htt⟩ := hasTyp_tupT_iff.1 h
  obtain rfl := (Value.tuple.inj he).symm
  obtain ⟨_, _, he₁, h₁, ht₁⟩ := hasTypTup_cons_iff.1 htt
  obtain ⟨rfl, rfl⟩ := List.cons.inj he₁
  obtain ⟨_, _, he₂, h₂, -⟩ := hasTypTup_cons_iff.1 ht₁
  obtain ⟨rfl, -⟩ := List.cons.inj he₂
  exact ⟨h₁, h₂⟩

/-- A typed one-case pair variant (`config`, `state`): its two components are typed. -/
theorem typedV_pair_iff {x op a b : IL.Id} {τ₁ τ₂ : Typ} {cs : List TypCase}
    (htd : (simEnv B).findTyp? x = some ([], [.instD [] [] (.variantT cs)]))
    (hf : IntNumeric.findCase cs op = some (.tupT [.mk a τ₁, .mk b τ₂], []))
    (c₁ : ClosedT B τ₁) (c₂ : ClosedT B τ₂) {u v : Value} :
    HasTyp (simEnv B) VarEnv.empty (.varT x []) (.case op (.tuple [u, v])) ↔
      TypedV (simEnv B) τ₁ u ∧ TypedV (simEnv B) τ₂ v := by
  constructor
  · intro h
    have hp := hasTyp_pair_inv (IntNumeric.hasTyp_of_hasTypCase
      (hasTypCase_of_closedVariant htd h) hf)
    exact ⟨fun _ hρ => c₁ ⟨rfl, rfl, rfl⟩ hρ hp.1, fun _ hρ => c₂ ⟨rfl, rfl, rfl⟩ hρ hp.2⟩
  · rintro ⟨h₁, h₂⟩
    exact hasTyp_varT_case rfl htd Equiv.evalArgs_nil matchArgs_nil
      (IntNumeric.hasTypCase_of_findCase hf (hasTyp_tupT_iff.2 ⟨_, rfl,
        hasTypTup_cons_iff.2 ⟨_, _, rfl, h₁ _ ⟨rfl, rfl, rfl⟩,
          hasTypTup_cons_iff.2 ⟨_, _, rfl, h₂ _ ⟨rfl, rfl, rfl⟩, hasTypTup_nil_iff.2 rfl⟩⟩⟩)
        premsOk_nil (IntNumeric.quantFreeAt_of_findCase_nil hf))

set_option maxRecDepth 100000 in
theorem findTyp_config : (simEnv B).findTyp? "config" =
    some ([], [.instD [] [] (.variantT (IntNumeric.instCases Original.d573 0))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_state : (simEnv B).findTyp? "state" =
    some ([], [.instD [] [] (.variantT (IntNumeric.instCases Original.d572 0))]) := rfl

set_option maxRecDepth 100000 in
/-- The components of a typed three-field `instr` case `n; τ; instr*`. -/
theorem typedV_admin3 {op : MixopS} {y : IL.Id} {τ : Typ} (hτ : ClosedT B τ) {k : Nat}
    {u : Value} {l : List Value}
    (hf : IntNumeric.findCase (IntNumeric.recCases
      Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d271 0 0) op =
      some (.tupT [.mk "n" nT, .mk y τ, .mk "instr*" instrsT], []))
    (h : TypedV (simEnv B) instrsT (.list [.case op (.tuple [.num (.natN k), u, .list l])])) :
    TypedV (simEnv B) nT (.num (.natN k)) ∧ TypedV (simEnv B) τ u ∧
      TypedV (simEnv B) instrsT (.list l) := by
  have hi := IntNumeric.hasTyp_instr_inv ⟨rfl, rfl, rfl⟩ (hasTyp_instr_of_single h) hf
  obtain ⟨_, he, ht⟩ := hasTyp_tupT_iff.1 hi
  obtain rfl := (Value.tuple.inj he).symm
  obtain ⟨_, _, he₁, h₁, ht₁⟩ := hasTypTup_cons_iff.1 ht
  obtain ⟨rfl, rfl⟩ := List.cons.inj he₁
  obtain ⟨_, _, he₂, h₂, ht₂⟩ := hasTypTup_cons_iff.1 ht₁
  obtain ⟨rfl, rfl⟩ := List.cons.inj he₂
  obtain ⟨_, _, he₃, h₃, -⟩ := hasTypTup_cons_iff.1 ht₂
  obtain ⟨rfl, -⟩ := List.cons.inj he₃
  exact ⟨fun _ hρ => closedT_var "n" ⟨rfl, rfl, rfl⟩ hρ h₁,
    fun _ hρ => hτ ⟨rfl, rfl, rfl⟩ hρ h₂, fun _ hρ => closedT_list "instr" ⟨rfl, rfl, rfl⟩ hρ h₃⟩

set_option maxRecDepth 100000 in
/-- **The base's typing facts hold in every `simEnv B`.** -/
theorem typingFacts_simEnv {H : Type} (B : Builtins) (hn : H → String) :
    TypingFacts (simEnv B) hn where
  config c := by
    unfold Typed configV
    rw [typedV_pair_iff findTyp_config rfl (closedT_var _) (closedT_list _)]
  state s f := by
    unfold stateV
    rw [typedV_iff_empty (closedT_var _), typedV_pair_iff findTyp_state rfl (closedT_var _)
      (closedT_var _)]
  append a b := typedV_list_append
  vals vs _ := by
    rw [adminsToV_vals]
    exact typedV_list_iff.2 fun v hv => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hv
      exact typedV_val w
  label n cont body h := typedV_admin3 (closedT_list "instr") rfl h
  handler n cs body h := typedV_admin3 (closedT_list "catch") rfl h
  frame n f body h := typedV_admin3 (closedT_var "frame") rfl h

end Silmaril.Wasm.SpecTec.Sim.Typing
