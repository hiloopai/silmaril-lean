module

public import Silmaril.Wasm.Unified.Versions.FXSim.Defs
public import Silmaril.Wasm.Execution.Core.Properties

/-!
# FX code that reads as Core code: list lemmas (unrefined)

Splitting, joining and inverting `LiftAs` (`Silmaril.Wasm.Unified.Versions.FXSim`), and the code
without structured instructions (`Struct`), whose only reading is the embedding. Used by the
simulation proofs of this directory; re-exported through
`Silmaril.Wasm.Unified.Versions.FXSim.Thms`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.Unified.FXSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Unified.Versions

/-- FX administrative instructions that can read as Core ones. -/
def Liftable : AdminFX → Prop
  | .core _ | .block _ _ | .loop _ _ | .if_ _ _ _ | .label _ _ _ => True
  | _ => False

theorem liftAs_map_core : ∀ cs : List Admin, LiftAs (cs.map .core) cs
  | [] => .nil
  | c :: cs => .cons (.core c) (liftAs_map_core cs)

theorem LiftAs.eq_of_map_core : ∀ {cs₀ cs : List Admin}, LiftAs (cs₀.map .core) cs → cs = cs₀
  | [], _, h => by cases h; rfl
  | c :: cs₀, _, h => by
    cases h with
    | cons ha ht =>
      cases ha
      rw [LiftAs.eq_of_map_core ht]

theorem LiftAs.append : ∀ {A : List AdminFX} {C : List Admin} {B : List AdminFX} {D : List Admin},
    LiftAs A C → LiftAs B D → LiftAs (A ++ B) (C ++ D)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons ha ht, h => .cons ha (LiftAs.append ht h)

theorem LiftAs.length_eq : ∀ {A : List AdminFX} {C : List Admin}, LiftAs A C → A.length = C.length
  | _, _, .nil => rfl
  | _, _, .cons _ ht => by rw [List.length_cons, List.length_cons, LiftAs.length_eq ht]

theorem LiftAs.append_left : ∀ {A B : List AdminFX} {cs : List Admin}, LiftAs (A ++ B) cs →
    ∃ C D, cs = C ++ D ∧ LiftAs A C ∧ LiftAs B D
  | [], _, cs, h => ⟨[], cs, rfl, .nil, h⟩
  | a :: A, B, _, h => by
    cases h with
    | cons ha ht =>
      obtain ⟨C, D, rfl, hC, hD⟩ := LiftAs.append_left ht
      exact ⟨_ :: C, D, rfl, .cons ha hC, hD⟩

theorem LiftAs.append_right : ∀ {C D : List Admin} {es : List AdminFX}, LiftAs es (C ++ D) →
    ∃ A B, es = A ++ B ∧ LiftAs A C ∧ LiftAs B D
  | [], _, es, h => ⟨[], es, rfl, .nil, h⟩
  | c :: C, D, _, h => by
    cases h with
    | cons ha ht =>
      obtain ⟨A, B, rfl, hA, hB⟩ := LiftAs.append_right ht
      exact ⟨_ :: A, B, rfl, .cons ha hA, hB⟩

theorem LiftAs.singleton_left {a : AdminFX} {cs : List Admin} (h : LiftAs [a] cs) :
    ∃ c, cs = [c] ∧ LiftA a c := by
  cases h with
  | cons ha ht =>
    cases ht
    exact ⟨_, rfl, ha⟩

theorem LiftAs.singleton_right {c : Admin} {es : List AdminFX} (h : LiftAs es [c]) :
    ∃ a, es = [a] ∧ LiftA a c := by
  cases h with
  | cons ha ht =>
    cases ht
    exact ⟨_, rfl, ha⟩

theorem LiftAs.liftable : ∀ {es : List AdminFX} {cs : List Admin}, LiftAs es cs →
    ∀ a ∈ es, Liftable a
  | _, _, .nil => fun _ h => absurd h List.not_mem_nil
  | _, _, .cons ha ht => by
    intro a hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · cases ha <;> trivial
    · exact LiftAs.liftable ht a hm'

theorem LiftA.eq_core {a : AdminFX} {c : Admin} (h : LiftA a c) (hc : ¬ Struct c) :
    a = .core c := by
  cases h with
  | core => rfl
  | block _ => exact absurd trivial hc
  | loop _ => exact absurd trivial hc
  | if_ _ _ => exact absurd trivial hc
  | label _ _ => exact absurd trivial hc

/-- Code without structured instructions reads only as its embedding. -/
theorem LiftAs.eq_map_core : ∀ {es : List AdminFX} {cs : List Admin}, LiftAs es cs →
    (∀ c ∈ cs, ¬ Struct c) → es = cs.map .core
  | _, _, .nil, _ => rfl
  | _, _, .cons ha ht, hn => by
    rw [List.map_cons, LiftA.eq_core ha (hn _ (List.mem_cons_self ..)),
      LiftAs.eq_map_core ht fun c hc => hn c (List.mem_cons_of_mem _ hc)]

theorem not_struct_toAdmin (v : Val) : ¬ Struct v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, Struct]

@[simp] theorem noStruct_vals (vs : List Val) : ∀ c ∈ vals vs, ¬ Struct c := by
  intro c hc
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hc
  exact not_struct_toAdmin v

theorem LiftAs.vals_right {vs : List Val} {es : List AdminFX} (h : LiftAs es (vals vs)) :
    es = cvals vs :=
  LiftAs.eq_map_core h (noStruct_vals vs)

theorem liftAs_cvals (vs : List Val) : LiftAs (cvals vs) (vals vs) := liftAs_map_core _

theorem LiftI.toAdmin {x : InstrFX} {i : Instr} (h : LiftI x i) :
    LiftA x.toAdmin (.plain i) := by
  cases h with
  | core => exact .core _
  | block h => exact .block h
  | loop h => exact .loop h
  | if_ h₁ h₂ => exact .if_ h₁ h₂

theorem LiftIs.toAdmin : ∀ {b : List InstrFX} {is : List Instr}, LiftIs b is →
    LiftAs (b.map InstrFX.toAdmin) (expression is)
  | _, _, .nil => .nil
  | _, _, .cons hx ht => .cons (LiftI.toAdmin hx) (LiftIs.toAdmin ht)

theorem LiftAs.hne {vs : List Val} {A : List AdminFX} {C : List Admin} (h : LiftAs A C)
    (hne : vs ≠ [] ∨ A ≠ []) : vs ≠ [] ∨ C ≠ [] := by
  rcases hne with hv | hA
  · exact Or.inl hv
  · refine Or.inr fun hC => hA ?_
    have hl := LiftAs.length_eq h
    rw [hC, List.length_nil] at hl
    exact List.eq_nil_of_length_eq_zero hl

theorem LiftAs.hne' {vs : List Val} {A : List AdminFX} {C : List Admin} (h : LiftAs A C)
    (hne : vs ≠ [] ∨ C ≠ []) : vs ≠ [] ∨ A ≠ [] := by
  rcases hne with hv | hC
  · exact Or.inl hv
  · refine Or.inr fun hA => hC ?_
    have hl := LiftAs.length_eq h
    rw [hA, List.length_nil] at hl
    exact List.eq_nil_of_length_eq_zero hl.symm

end Silmaril.Raw.Wasm.Unified.FXSim
