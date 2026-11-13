module

public import Silmaril.Proofs.Wasm.Models.FXResumeT.Runs

/-!
# Renaming continuation slots, and the relation that ignores consumed slots

Bind-then-resume and the direct resume reach the same code, but the bind leaves one more
consumed slot in the continuation store, so later continuations get different indices. This
module sets up the relation between two configurations whose stores differ in consumed slots:

* `rnA ρ`, `rnL ρ`, `rnV ρ`, `rnE ρ`: rename the continuation references `ref.cont k` of code,
  FX values and suspension contexts by `ρ : Nat → Nat`;
* `avA B`, `avL B`, `avV B`, `avE B`: the code (values, context) mentions no slot in `B`, the
  *ignored* slots;
* `ContR ρ B C₁ C₂`: the continuation `C₂` is `C₁` renamed: it commutes with `rnL ρ` on code
  avoiding `B`, and `C₁` keeps such code avoiding `B`;
* **`KRel ρ B K₁ K₂`**: the store `K₂` is `K₁` with the slots in `B` ignored and the others
  renamed by `ρ`: live slots go to live slots with renamed continuations, consumed slots to
  consumed slots, `ρ` is injective off `B`, and the next allocations correspond
  (`ρ (|K₁| + j) = |K₂| + j`, never in `B`).

The lemmas show that renaming commutes with the code constructors used by `StepFXR` and that
`KRel` survives consuming a slot (`kRel_set`) and allocating one (`kRel_append`).

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXResumeT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV

/-! ## Renaming and avoidance -/

mutual
/-- Rename the continuation references of an administrative instruction. -/
@[simp] def rnA (ρ : Nat → Nat) : AdminFX → AdminFX
  | .core a => .core a
  | .fx i => .fx i
  | .block bt b => .block bt b
  | .loop bt b => .loop bt b
  | .if_ bt b₁ b₂ => .if_ bt b₁ b₂
  | .label n k b => .label n k (rnL ρ b)
  | .frame n f b => .frame n f (rnL ρ b)
  | .handler hs b => .handler hs (rnL ρ b)
  | .contRef k => .contRef (ρ k)
/-- Rename the continuation references of code. -/
@[simp] def rnL (ρ : Nat → Nat) : List AdminFX → List AdminFX
  | [] => []
  | a :: l => rnA ρ a :: rnL ρ l
end

mutual
/-- The instruction mentions no slot in `B`. -/
@[simp] def avA (B : Nat → Prop) : AdminFX → Prop
  | .core _ => True
  | .fx _ => True
  | .block _ _ => True
  | .loop _ _ => True
  | .if_ _ _ _ => True
  | .label _ _ b => avL B b
  | .frame _ _ b => avL B b
  | .handler _ b => avL B b
  | .contRef k => ¬ B k
/-- The code mentions no slot in `B`. -/
@[simp] def avL (B : Nat → Prop) : List AdminFX → Prop
  | [] => True
  | a :: l => avA B a ∧ avL B l
end

/-- Rename an FX value. -/
@[simp] def rnF (ρ : Nat → Nat) : FVal → FVal
  | .val v => .val v
  | .cont k => .cont (ρ k)

/-- Rename FX values. -/
def rnV (ρ : Nat → Nat) (vs : List FVal) : List FVal := vs.map (rnF ρ)

/-- Rename a suspension context. -/
@[simp] def rnE (ρ : Nat → Nat) : CtxV → CtxV
  | .hole => .hole
  | .seq vs E rest => .seq (rnV ρ vs) (rnE ρ E) (rnL ρ rest)
  | .label n k E => .label n k (rnE ρ E)
  | .frame n f E => .frame n f (rnE ρ E)
  | .handler hs E => .handler hs (rnE ρ E)

/-- The context mentions no slot in `B`. -/
@[simp] def avE (B : Nat → Prop) : CtxV → Prop
  | .hole => True
  | .seq vs E rest => avL B (fvals vs) ∧ avE B E ∧ avL B rest
  | .label _ _ E => avE B E
  | .frame _ _ E => avE B E
  | .handler _ E => avE B E

variable {ρ : Nat → Nat} {B : Nat → Prop}

@[simp] theorem rnL_append (a b : List AdminFX) : rnL ρ (a ++ b) = rnL ρ a ++ rnL ρ b := by
  induction a with
  | nil => rfl
  | cons x a ih => simp [ih]

@[simp] theorem avL_append (a b : List AdminFX) : avL B (a ++ b) ↔ avL B a ∧ avL B b := by
  induction a with
  | nil => simp
  | cons x a ih => simp [ih, and_assoc]

@[simp] theorem rnV_append (a b : List FVal) : rnV ρ (a ++ b) = rnV ρ a ++ rnV ρ b := by
  simp [rnV]

@[simp] theorem rnV_nil : rnV ρ [] = [] := rfl

@[simp] theorem length_rnV (vs : List FVal) : (rnV ρ vs).length = vs.length := by
  simp [rnV]

@[simp] theorem rnV_eq_nil (vs : List FVal) : rnV ρ vs = [] ↔ vs = [] := by
  simp [rnV]

@[simp] theorem rnL_eq_nil (l : List AdminFX) : rnL ρ l = [] ↔ l = [] := by
  cases l <;> simp

@[simp] theorem rnL_fvals (vs : List FVal) : rnL ρ (fvals vs) = fvals (rnV ρ vs) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    cases v <;> simp_all [fvals, rnV, FVal.toAdmin]

@[simp] theorem rnL_map_core (cs : List Admin) : rnL ρ (cs.map AdminFX.core) = cs.map .core := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [ih]

@[simp] theorem avL_map_core (cs : List Admin) : avL B (cs.map AdminFX.core) := by
  induction cs with
  | nil => trivial
  | cons c cs ih => exact ⟨trivial, ih⟩

@[simp] theorem rnL_cvals (vs : List Val) : rnL ρ (cvals vs) = cvals vs := rnL_map_core _

@[simp] theorem avL_cvals (vs : List Val) : avL B (cvals vs) := avL_map_core _

@[simp] theorem rnL_cthrowing (a : Nat) : rnL ρ (cthrowing a) = cthrowing a := rnL_map_core _

@[simp] theorem avL_cthrowing (a : Nat) : avL B (cthrowing a) := avL_map_core _

@[simp] theorem rnL_toAdmin (is : List InstrFX) :
    rnL ρ (is.map InstrFX.toAdmin) = is.map InstrFX.toAdmin := by
  induction is with
  | nil => rfl
  | cons i is ih => cases i <;> simp_all [InstrFX.toAdmin]

@[simp] theorem avL_toAdmin (is : List InstrFX) : avL B (is.map InstrFX.toAdmin) := by
  induction is with
  | nil => trivial
  | cons i is ih => cases i <;> simp_all [InstrFX.toAdmin]

@[simp] theorem rnE_plug (E : CtxV) (c : List AdminFX) :
    (rnE ρ E).plug (rnL ρ c) = rnL ρ (E.plug c) := by
  induction E with
  | hole => rfl
  | seq vs E rest ih => simp [CtxV.plug, ih]
  | label n k E ih => simp [CtxV.plug, ih]
  | frame n f E ih => simp [CtxV.plug, ih]
  | handler hs E ih => simp [CtxV.plug, ih]

@[simp] theorem avL_plug (E : CtxV) (c : List AdminFX) :
    avL B (E.plug c) ↔ avE B E ∧ avL B c := by
  induction E with
  | hole => simp [CtxV.plug]
  | seq vs E rest ih => simp [CtxV.plug, ih]; tauto
  | label n k E ih => simp [CtxV.plug, ih]
  | frame n f E ih => simp [CtxV.plug, ih]
  | handler hs E ih => simp [CtxV.plug, ih]

@[simp] theorem frameAt_rnE (f : Frame) (E : CtxV) : (rnE ρ E).frameAt f = E.frameAt f := by
  induction E generalizing f with
  | hole => rfl
  | seq vs E rest ih => exact ih f
  | label n k E ih => exact ih f
  | frame n fi E ih => exact ih fi
  | handler hs E ih => exact ih f

@[simp] theorem handles_rnE (ta : Nat) (E : CtxV) : (rnE ρ E).Handles ta ↔ E.Handles ta := by
  induction E with
  | hole => rfl
  | seq vs E rest ih => exact ih
  | label n k E ih => exact ih
  | frame n f E ih => exact ih
  | handler hs E ih => simp [CtxV.Handles, ih]

/-! ## Continuations and stores -/

/-- `C₂` is `C₁` renamed by `ρ`, on code avoiding `B`. -/
def ContR (ρ : Nat → Nat) (B : Nat → Prop) (C₁ C₂ : ContFX) : Prop :=
  ∀ c, avL B c → avL B (C₁.plug c) ∧ C₂.plug (rnL ρ c) = rnL ρ (C₁.plug c)

/-- Optional continuations related by `ContR`: both consumed, or both live and related. -/
def OContR (ρ : Nat → Nat) (B : Nat → Prop) : Option ContFX → Option ContFX → Prop
  | none, none => True
  | some C₁, some C₂ => ContR ρ B C₁ C₂
  | _, _ => False

/-- **`K₂` is `K₁` with the slots in `B` ignored and the others renamed by `ρ`.** -/
structure KRel (ρ : Nat → Nat) (B : Nat → Prop) (K₁ K₂ : List (Option ContFX)) : Prop where
  slot : ∀ i c₁, ¬ B i → K₁[i]? = some c₁ → ∃ c₂, K₂[ρ i]? = some c₂ ∧ OContR ρ B c₁ c₂
  alloc : ∀ j, ρ (K₁.length + j) = K₂.length + j
  fresh : ∀ j, ¬ B (K₁.length + j)
  inj : ∀ i i', ¬ B i → ¬ B i' → ρ i = ρ i' → i = i'

theorem kRel_live {K₁ K₂ : List (Option ContFX)} (hK : KRel ρ B K₁ K₂) {k : Nat} {C₁ : ContFX}
    (hB : ¬ B k) (hk : K₁[k]? = some (some C₁)) :
    ∃ C₂, K₂[ρ k]? = some (some C₂) ∧ ContR ρ B C₁ C₂ := by
  obtain ⟨c₂, hc₂, hr⟩ := hK.slot k _ hB hk
  cases c₂ with
  | none => exact hr.elim
  | some C₂ => exact ⟨C₂, hc₂, hr⟩

theorem kRel_used {K₁ K₂ : List (Option ContFX)} (hK : KRel ρ B K₁ K₂) {k : Nat}
    (hB : ¬ B k) (hk : K₁[k]? = some none) : K₂[ρ k]? = some none := by
  obtain ⟨c₂, hc₂, hr⟩ := hK.slot k _ hB hk
  cases c₂ with
  | none => exact hc₂
  | some C₂ => exact hr.elim

theorem getElem?_set_of_ne {K : List (Option ContFX)} {i k : Nat} (h : i ≠ k) :
    (K.set k none)[i]? = K[i]? := by
  simp [Ne.symm h]

/-- **Consuming a slot keeps the relation.** -/
theorem kRel_set {K₁ K₂ : List (Option ContFX)} (hK : KRel ρ B K₁ K₂) {k : Nat} {c₁ : Option ContFX}
    (hB : ¬ B k) (hk : K₁[k]? = some c₁) : KRel ρ B (K₁.set k none) (K₂.set (ρ k) none) := by
  obtain ⟨c₂, hc₂, -⟩ := hK.slot k _ hB hk
  have hlt₂ : ρ k < K₂.length := (List.getElem?_eq_some_iff.mp hc₂).1
  refine ⟨?_, by simpa using hK.alloc, by simpa using hK.fresh, hK.inj⟩
  intro i c hi hc
  by_cases hik : i = k
  · subst hik
    have hlt₁ : i < K₁.length := (List.getElem?_eq_some_iff.mp hk).1
    simp only [List.getElem?_set_self hlt₁, Option.some.injEq] at hc
    subst hc
    exact ⟨none, List.getElem?_set_self hlt₂, trivial⟩
  · rw [getElem?_set_of_ne hik] at hc
    have hne : ρ i ≠ ρ k := fun he => hik (hK.inj i k hi hB he)
    rw [getElem?_set_of_ne hne]
    exact hK.slot i c hi hc

/-- **Allocating related slots keeps the relation.** -/
theorem kRel_append {K₁ K₂ : List (Option ContFX)} (hK : KRel ρ B K₁ K₂) {c₁ c₂ : Option ContFX}
    (hc : OContR ρ B c₁ c₂) : KRel ρ B (K₁ ++ [c₁]) (K₂ ++ [c₂]) := by
  refine ⟨?_, fun j => by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hK.alloc (j + 1),
    fun j => by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hK.fresh (j + 1), hK.inj⟩
  intro i c hi hci
  rcases Nat.lt_or_ge i K₁.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hci
    obtain ⟨c', hc', hr⟩ := hK.slot i c hi hci
    have hlt₂ : ρ i < K₂.length := (List.getElem?_eq_some_iff.mp hc').1
    exact ⟨c', by rw [List.getElem?_append_left hlt₂]; exact hc', hr⟩
  · have hlt : i < K₁.length + 1 := by
      have := (List.getElem?_eq_some_iff.mp hci).1
      simpa using this
    have hi : i = K₁.length := by omega
    subst hi
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.some.injEq] at hci
    subst hci
    have hρ : ρ K₁.length = K₂.length := by simpa using hK.alloc 0
    exact ⟨c₂, by rw [hρ]; simp, hc⟩

theorem kRel_append_some {K₁ K₂ : List (Option ContFX)} (hK : KRel ρ B K₁ K₂) {C₁ C₂ : ContFX}
    (hc : ContR ρ B C₁ C₂) : KRel ρ B (K₁ ++ [some C₁]) (K₂ ++ [some C₂]) :=
  kRel_append hK (c₁ := some C₁) (c₂ := some C₂) hc

theorem fresh_length {K₁ K₂ : List (Option ContFX)} (hK : KRel ρ B K₁ K₂) : ¬ B K₁.length := by
  simpa using hK.fresh 0

theorem alloc_length {K₁ K₂ : List (Option ContFX)} (hK : KRel ρ B K₁ K₂) :
    ρ K₁.length = K₂.length := by
  simpa using hK.alloc 0

end Silmaril.Proofs.Wasm.Models.FXResumeT
