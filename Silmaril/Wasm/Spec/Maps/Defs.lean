module

public import Silmaril.Wasm.Spec.Format.Thms

@[expose] public section

/-!
# Comorphisms of the trace-institution format

* `Logic.ofTrace Fm holds`: the logic of a per-trace property (`T ⊨ φ` iff every trace of `T`
  satisfies `φ`); the simple specification logics are of this form. `Logic.Antitone`: satisfaction
  is inherited by subsets of traces (true of every per-trace logic, `Logic.ofTrace_antitone`);
  these are the logics for which verifying more behaviours is harder.
* `LogicMap.coHom S : Inst.CoHom (inst L S) (inst L' S)` for a logic map `L → L'`: identity on
  interfaces and models, formulas translated, model-expansive (`LogicMap.coHom_modelExpansive`),
  hence borrowing (`LogicMap.entails_iff`).
* `SemMap.coHom L : Inst.CoHom (inst L S') (inst L S)` for a semantics map `S → S'`: identity on
  interfaces and sentences, programs translated.
-/

namespace Silmaril.Wasm.Spec

open CategoryTheory Silmaril.Logic.Institution

variable {Ty A R : Type}

/-! ## Per-trace logics -/

/-- The logic of a per-trace property: a trace set satisfies `φ` when each of its traces does. -/
abbrev Logic.ofTrace (Fm : Iface Ty → Type)
    (holds : ∀ {X : Iface Ty}, Fm X → List (Event A R X) → Prop) : Logic Ty A R :=
  ⟨Fm, fun T φ => ∀ t ∈ T, holds φ t⟩

/-- Satisfaction is inherited by subsets of traces. -/
def Logic.Antitone (L : Logic Ty A R) : Prop :=
  ∀ {X : Iface Ty} {T T' : Set (List (Event A R X))} (φ : L.Fm X), T ⊆ T' → L.Sat T' φ → L.Sat T φ

/-- Per-trace logics are antitone. -/
theorem Logic.ofTrace_antitone (Fm : Iface Ty → Type)
    (holds : ∀ {X : Iface Ty}, Fm X → List (Event A R X) → Prop) :
    (Logic.ofTrace Fm holds).Antitone :=
  fun _ hTT' h t ht => h t (hTT' ht)

/-- A logic map between per-trace logics from a formula translation preserving the property on
every trace. -/
def LogicMap.ofTrace {Fm Fm' : Iface Ty → Type}
    {holds : ∀ {X : Iface Ty}, Fm X → List (Event A R X) → Prop}
    {holds' : ∀ {X : Iface Ty}, Fm' X → List (Event A R X) → Prop}
    (fm : ∀ {X : Iface Ty}, Fm X → Fm' X) (h : ∀ {X : Iface Ty} (φ : Fm X) t, holds' (fm φ) t ↔ holds φ t) :
    LogicMap (Logic.ofTrace Fm holds) (Logic.ofTrace Fm' holds') :=
  ⟨fm, fun _ _ φ => forall₂_congr fun t _ => h φ t⟩

/-! ## Logic maps as comorphisms -/

/-- The corridor of a logic map at an interface: formulas translated, models unchanged. -/
def LogicMap.corridor {L L' : Logic Ty A R} (f : LogicMap L L') (S : Semantics Ty A R)
    (X : Iface Ty) : room L S X ⟶ room L' S X :=
  ⟨f.sen, 𝟭 _, fun M s => f.sat_fm _ ((S.good M.prog).reduct (s.obs ≫ M.obs)) s.φ⟩

/-- **The comorphism of a logic map** (identity on interfaces and models). -/
def LogicMap.coHom {L L' : Logic Ty A R} (f : LogicMap L L') (S : Semantics Ty A R) :
    Inst.CoHom (inst L S) (inst L' S) where
  Φ := 𝟭 _
  ρ :=
    { app := fun X => f.corridor S X
      naturality := fun _ _ _ => rfl }

/-- The comorphism of a logic map is model-expansive. -/
theorem LogicMap.coHom_modelExpansive {L L' : Logic Ty A R} (f : LogicMap L L')
    (S : Semantics Ty A R) : (f.coHom S).ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

/-- **Borrowing along a logic map**: consequence in `L` is consequence of the translated
sentences in `L'`. -/
theorem LogicMap.entails_iff {L L' : Logic Ty A R} (f : LogicMap L L') (S : Semantics Ty A R)
    (X : Iface Ty) (Γ : Set (Sen L X)) (s : Sen L X) :
    (room L S X).Entails Γ s ↔ (room L' S X).Entails (f.sen '' Γ) (f.sen s) :=
  (f.coHom S).entails_iff (f.coHom_modelExpansive S) X Γ s

/-- A program satisfies a translated formula iff it satisfies the formula. -/
theorem LogicMap.models_iff {L L' : Logic Ty A R} (f : LogicMap L L') (S : Semantics Ty A R)
    {X : Iface Ty} (p : S.Prog X) (φ : L.Fm X) : Models L' S p (f.fm φ) ↔ Models L S p φ := by
  rw [Spec.models_iff, Spec.models_iff]
  exact f.sat_fm _ (S.good p) φ

/-! ## Semantics maps as comorphisms -/

/-- The corridor of a semantics map at an interface: sentences unchanged, models translated. -/
def SemMap.corridor {S S' : Semantics Ty A R} (m : SemMap S S') (L : Logic Ty A R)
    (X : Iface Ty) : room L S' X ⟶ room L S X where
  sen s := s
  mod :=
    { obj := m.model
      map := fun h => ⟨congrArg m.model h.down⟩ }
  sat M s := by
    show L.Sat (reduct (s.obs ≫ M.obs) (S.traces M.prog)) s.φ ↔
      L.Sat (reduct (s.obs ≫ M.obs) (S'.traces (m.prog M.prog))) s.φ
    rw [m.traces_prog]

/-- **The comorphism of a semantics map** (identity on interfaces and sentences). -/
def SemMap.coHom {S S' : Semantics Ty A R} (m : SemMap S S') (L : Logic Ty A R) :
    Inst.CoHom (inst L S') (inst L S) where
  Φ := 𝟭 _
  ρ :=
    { app := fun X => m.corridor L X
      naturality := fun _ _ _ => rfl }

/-- A program satisfies a formula iff its translation does. -/
theorem SemMap.models_iff {S S' : Semantics Ty A R} (m : SemMap S S') (L : Logic Ty A R)
    {X : Iface Ty} (p : S.Prog X) (φ : L.Fm X) : Models L S' (m.prog p) φ ↔ Models L S p φ := by
  rw [Spec.models_iff, Spec.models_iff, m.traces_prog]

end Silmaril.Wasm.Spec
