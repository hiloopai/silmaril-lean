module

public import Silmaril.Wasm.Binaryen.InlAssemble
public import Silmaril.Wasm.Binaryen.EffectRun

@[expose] public section

/-! # Unwrapping a branch-free block: the simulation relation

`block bt R` and `R` run in lockstep when `R` neither branches out of itself nor returns
(`Binaryen/InlUnwrap.lean`). The relation relates a configuration of the module with the
block (left) to one of the module with the bare region (right): the frames are equal, the
stores differ only in the code of one function (`SR`), and the codes are related by `UL`,
which is equality up to

* the site: the plain `block bt R` (left) against the instructions of `R` (right),
  inside instruction sequences of any nesting depth (`UIL.site`, `UL.site`);
* a running site: the label `label n [] X` (left) against `X'` spliced into the
  surrounding sequence (right), where `X` and `X'` are related and `X` never branches or
  returns out of the label (`NoEsc`, an effect budget without `return` and an empty label
  predicate, both kept by every step: `Step.bud`, `Step.admsLab`).

The left side takes the extra steps (entering the block, leaving the label, and bubbling
a trap or exception out of it); they decrease the size `aszs` of the left code.

The same relation also carries **code folding** (`Pass/CodeFolding.lean`): an `if` whose
arms end with the same escape-free tail `X` (left) against the `if` without the tail,
followed by `X` (right), inside instruction sequences of any nesting depth (`UIL.fold`,
`UL.foldIf`). At run time the left arm runs `C ++ X` inside the `if`'s label and the right
arm runs `C'` inside it and `X` after it (`UL.foldLabel`); once `C` is done, the right side
leaves its label and the pair becomes a running site (`UL.run`). A trap or exception that
bubbles out of the left arm through part of `X` is reached by the right side as it leaves
its label (`UL.foldExit`).
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type}

/-- The budget of an unwrapped region: anything but `return`, tail calls and handlers. -/
def budU : Bud := ⟨fun _ => True, fun _ => True, True, True, True, False⟩

/-- Code that never branches or returns out of its own scope. -/
def NoEsc (X : List Admin) : Prop := (∃ S, AdmsB budU S X) ∧ AdmsLab (fun _ => False) X

/-- An arm of a folded `if`: inside the region budget, with no free branch target. -/
def FoldOk (L : List Instr) : Prop := (∃ S, ∀ j ∈ L, InstrB budU S j) ∧ instrsLabels L = []

variable (R : List Instr)

mutual
/-- Instructions: equal up to sites in their bodies. -/
inductive UI : Instr → Instr → Prop where
  | flat (i : Instr) : UI i i
  | block {bt : BlockType} {b b' : List Instr} (h : UIL b b') : UI (.block bt b) (.block bt b')
  | loop {bt : BlockType} {b b' : List Instr} (h : UIL b b') : UI (.loop bt b) (.loop bt b')
  | if_ {bt : BlockType} {t t' e e' : List Instr} (h₁ : UIL t t') (h₂ : UIL e e') :
      UI (.if_ bt t e) (.if_ bt t' e')
  | tryTable {bt : BlockType} {cs : List Catch} {b b' : List Instr} (h : UIL b b') :
      UI (.tryTable bt cs b) (.tryTable bt cs b')
/-- Instruction sequences: the site `block bt R` against `R`. -/
inductive UIL : List Instr → List Instr → Prop where
  | nil : UIL [] []
  | cons {i i' : Instr} {is is' : List Instr} (h : UI i i') (t : UIL is is') :
      UIL (i :: is) (i' :: is')
  | site (bt : BlockType) {is is' : List Instr} (t : UIL is is') : UIL (.block bt R :: is) (R ++ is')
  /-- A folded `if`: the common tail `X` of the arms is hoisted after the `if`. -/
  | fold (bt : BlockType) {T T' E E' X is is' : List Instr} (h₁ : UIL T T') (h₂ : UIL E E')
      (hT : FoldOk (T ++ X)) (hE : FoldOk (E ++ X)) (t : UIL is is') :
      UIL (.if_ bt (T ++ X) (E ++ X) :: is) (.if_ bt T' E' :: (X ++ is'))
end

mutual
/-- Administrative instructions. -/
inductive UA : Admin → Admin → Prop where
  | plain {i i' : Instr} (h : UI R i i') : UA (.plain i) (.plain i')
  | ref (r : Ref) : UA (.ref r) (.ref r)
  | callRef (d : DefType) : UA (.callRefType d) (.callRefType d)
  | retCallRef (d : DefType) : UA (.returnCallRefType d) (.returnCallRefType d)
  | label {n : Nat} {c c' : List Instr} {b b' : List Admin} (hc : UIL R c c') (h : UL b b') :
      UA (.label n c b) (.label n c' b')
  | handler {n : Nat} {cs : List Catch} {b b' : List Admin} (h : UL b b') :
      UA (.handler n cs b) (.handler n cs b')
  | frame {n : Nat} {F : Frame} {b b' : List Admin} (h : UL b b') :
      UA (.frame n F b) (.frame n F b')
  | trap : UA .trap .trap
/-- Administrative sequences, with sites and running sites. -/
inductive UL : List Admin → List Admin → Prop where
  | nil : UL [] []
  | cons {a b : Admin} {os ns : List Admin} (h : UA a b) (t : UL os ns) : UL (a :: os) (b :: ns)
  | site (bt : BlockType) {os ns : List Admin} (t : UL os ns) :
      UL (.plain (.block bt R) :: os) (expression R ++ ns)
  | run {n : Nat} {X X' os ns : List Admin} (h : UL X X') (hX : NoEsc X) (t : UL os ns) :
      UL (.label n [] X :: os) (X' ++ ns)
  /-- A folded `if`. -/
  | foldIf (bt : BlockType) {T T' E E' X : List Instr} {os ns : List Admin} (h₁ : UIL R T T')
      (h₂ : UIL R E E') (hT : FoldOk (T ++ X)) (hE : FoldOk (E ++ X)) (t : UL os ns) :
      UL (.plain (.if_ bt (T ++ X) (E ++ X)) :: os) (.plain (.if_ bt T' E') :: (expression X ++ ns))
  /-- The chosen arm of a folded `if`. -/
  | foldBlock (bt : BlockType) {T T' X : List Instr} {os ns : List Admin} (h : UIL R T T')
      (hT : FoldOk (T ++ X)) (t : UL os ns) :
      UL (.plain (.block bt (T ++ X)) :: os) (.plain (.block bt T') :: (expression X ++ ns))
  /-- A running folded arm: `C ++ Xa` inside the label (left) against `C'` inside it and
  `Xa` after it (right), while `C` is not done. -/
  | foldLabel {n : Nat} {C C' Xa os ns : List Admin} (h : UL C C') (hX : NoEsc (C ++ Xa))
      (hv : C.all Admin.isVal = false) (t : UL os ns) :
      UL (.label n [] (C ++ Xa) :: os) (.label n [] C' :: (Xa ++ ns))
  /-- A trap or exception bubbling out of a folded arm (left), reached by the right side. -/
  | foldExit {n : Nat} {ws : List Val} {K J os ns : List Admin} (hK : Det.IsBubble K)
      (t : UL os ns) : UL (.label n [] (vals ws ++ K ++ J) :: os) (K ++ ns)
end

variable {R}

/-! ## Reflexivity and sequences -/

theorem UIL.refl : ∀ is : List Instr, UIL R is is
  | [] => .nil
  | i :: is => .cons (.flat i) (UIL.refl is)

mutual
theorem UA.refl : ∀ a : Admin, UA R a a
  | .plain i => .plain (.flat i)
  | .ref r => .ref r
  | .callRefType d => .callRef d
  | .returnCallRefType d => .retCallRef d
  | .label _ c b => .label (UIL.refl c) (UL.refl b)
  | .handler _ _ b => .handler (UL.refl b)
  | .frame _ _ b => .frame (UL.refl b)
  | .trap => .trap
theorem UL.refl : ∀ l : List Admin, UL R l l
  | [] => .nil
  | a :: l => .cons (UA.refl a) (UL.refl l)
end

theorem UL.of_UIL : ∀ {is is' : List Instr}, UIL R is is' → UL R (expression is) (expression is')
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (.plain h) (UL.of_UIL t)
  | _, _, .site bt t => by
    have := UL.site (R := R) bt (UL.of_UIL t)
    simpa [expression] using this
  | _, _, .fold bt h₁ h₂ hT hE t => by
    have := UL.foldIf (R := R) bt h₁ h₂ hT hE (UL.of_UIL t)
    simpa [expression] using this

theorem UL.append : ∀ {A B nA nB : List Admin}, UL R A nA → UL R B nB → UL R (A ++ B) (nA ++ nB)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h t, h' => .cons h (UL.append t h')
  | _, _, _, _, .site bt t, h' => by
    simpa [List.append_assoc] using UL.site bt (UL.append t h')
  | _, _, _, _, .run h hX t, h' => by
    simpa [List.append_assoc] using UL.run h hX (UL.append t h')
  | _, _, _, _, .foldIf bt h₁ h₂ hT hE t, h' => by
    simpa [List.append_assoc] using UL.foldIf bt h₁ h₂ hT hE (UL.append t h')
  | _, _, _, _, .foldBlock bt h hT t, h' => by
    simpa [List.append_assoc] using UL.foldBlock bt h hT (UL.append t h')
  | _, _, _, _, .foldLabel h hX hv t, h' => by
    simpa [List.append_assoc] using UL.foldLabel h hX hv (UL.append t h')
  | _, _, _, _, .foldExit hK t, h' => by
    simpa [List.append_assoc] using UL.foldExit hK (UL.append t h')

theorem UL.append_inv : ∀ {A B ns : List Admin}, UL R (A ++ B) ns →
    ∃ n₁ n₂, ns = n₁ ++ n₂ ∧ UL R A n₁ ∧ UL R B n₂
  | [], _, ns, h => ⟨[], ns, rfl, .nil, h⟩
  | a :: A, B, ns, h => by
    simp only [List.cons_append] at h
    cases h with
    | cons h t =>
      obtain ⟨n₁, n₂, rfl, h₁, h₂⟩ := UL.append_inv t
      exact ⟨_ :: n₁, n₂, rfl, .cons h h₁, h₂⟩
    | site bt t =>
      obtain ⟨n₁, n₂, rfl, h₁, h₂⟩ := UL.append_inv t
      exact ⟨expression R ++ n₁, n₂, by simp, .site bt h₁, h₂⟩
    | run h hX t =>
      obtain ⟨n₁, n₂, rfl, h₁, h₂⟩ := UL.append_inv t
      exact ⟨_ ++ n₁, n₂, by simp, .run h hX h₁, h₂⟩
    | foldIf bt h₁' h₂' hT hE t =>
      obtain ⟨n₁, n₂, rfl, h₁, h₂⟩ := UL.append_inv t
      exact ⟨_ :: (_ ++ n₁), n₂, by simp, .foldIf bt h₁' h₂' hT hE h₁, h₂⟩
    | foldBlock bt h hT t =>
      obtain ⟨n₁, n₂, rfl, h₁, h₂⟩ := UL.append_inv t
      exact ⟨_ :: (_ ++ n₁), n₂, by simp, .foldBlock bt h hT h₁, h₂⟩
    | foldLabel h hX hv t =>
      obtain ⟨n₁, n₂, rfl, h₁, h₂⟩ := UL.append_inv t
      exact ⟨_ :: (_ ++ n₁), n₂, by simp, .foldLabel h hX hv h₁, h₂⟩
    | foldExit hK t =>
      obtain ⟨n₁, n₂, rfl, h₁, h₂⟩ := UL.append_inv t
      exact ⟨_ ++ n₁, n₂, by simp, .foldExit hK h₁, h₂⟩

theorem UI.eq_of_flat {i i' : Instr} (h : UI R i i') (hs : structuredInstr i = false) : i' = i := by
  cases h with
  | flat => rfl
  | _ => simp [structuredInstr] at hs

theorem UA.val_inv {v : Val} {b : Admin} (h : UA R v.toAdmin b) : b = v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp only [Val.toAdmin] at h ⊢ <;>
    first
    | (cases h with | plain h => exact congrArg Admin.plain (UI.eq_of_flat h rfl))
    | (cases h; rfl)

theorem val_ne_site {v : Val} {bt : BlockType} : v.toAdmin ≠ .plain (.block bt R) := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin]

theorem val_ne_label {v : Val} {n : Nat} {c : List Instr} {X : List Admin} :
    v.toAdmin ≠ .label n c X := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin]

theorem val_ne_structured {v : Val} {i : Instr} (hi : structuredInstr i = true) :
    v.toAdmin ≠ .plain i := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] <;> rintro rfl <;>
    simp [structuredInstr] at hi

theorem UL.vals_inv : ∀ {vs : List Val} {ns : List Admin}, UL R (vals vs) ns → ns = vals vs
  | [], _, h => by simp only [vals, List.map_nil] at h; cases h; rfl
  | v :: vs, ns, h => by
    simp only [vals, List.map_cons] at h
    generalize ha : v.toAdmin = a at h
    cases h with
    | cons h t =>
      subst ha
      rw [UA.val_inv h, UL.vals_inv t]; rfl
    | site bt t => exact absurd ha val_ne_site
    | run h hX t => exact absurd ha val_ne_label
    | foldIf bt _ _ _ _ t => exact absurd ha (val_ne_structured rfl)
    | foldBlock bt _ _ t => exact absurd ha (val_ne_structured rfl)
    | foldLabel _ _ _ t => exact absurd ha val_ne_label
    | foldExit _ t => exact absurd ha val_ne_label

theorem UL.vals_append_inv {vs : List Val} {B ns : List Admin} (h : UL R (vals vs ++ B) ns) :
    ∃ nB, ns = vals vs ++ nB ∧ UL R B nB := by
  obtain ⟨n₁, n₂, rfl, h₁, h₂⟩ := UL.append_inv h
  exact ⟨n₂, by rw [UL.vals_inv h₁], h₂⟩

theorem UL.of_vals (vs : List Val) : UL R (vals vs) (vals vs) := UL.refl _

/-- An atomic administrative instruction is related only to itself. -/
theorem UA.eq_of_flat {a b : Admin} (h : UA R a b) (hL : ∀ n c b, a ≠ .label n c b)
    (hH : ∀ n cs b, a ≠ .handler n cs b) (hF : ∀ n F b, a ≠ .frame n F b)
    (hs : ∀ i, a = .plain i → structuredInstr i = false) : b = a := by
  cases h with
  | plain h => rw [UI.eq_of_flat h (hs _ rfl)]
  | label _ _ => exact absurd rfl (hL _ _ _)
  | handler _ => exact absurd rfl (hH _ _ _)
  | frame _ => exact absurd rfl (hF _ _ _)
  | _ => rfl

/-- One atomic instruction after values. -/
theorem UL.flat_inv {vs : List Val} {y : Admin} {rest ns : List Admin}
    (hL : ∀ n c b, y ≠ .label n c b) (hH : ∀ n cs b, y ≠ .handler n cs b)
    (hF : ∀ n F b, y ≠ .frame n F b) (hs : ∀ i, y = .plain i → structuredInstr i = false)
    (h : UL R (vals vs ++ y :: rest) ns) :
    ∃ rest', ns = vals vs ++ y :: rest' ∧ UL R rest rest' := by
  obtain ⟨nB, rfl, hB⟩ := UL.vals_append_inv h
  cases hB with
  | cons ha t =>
    rw [UA.eq_of_flat ha hL hH hF hs]
    exact ⟨_, rfl, t⟩
  | site bt t => exact absurd (hs _ rfl) (by simp [structuredInstr])
  | run hX' hX t => exact absurd rfl (hL _ _ _)
  | foldIf bt _ _ _ _ t => exact absurd (hs _ rfl) (by simp [structuredInstr])
  | foldBlock bt _ _ t => exact absurd (hs _ rfl) (by simp [structuredInstr])
  | foldLabel _ _ _ t => exact absurd rfl (hL _ _ _)
  | foldExit _ t => exact absurd rfl (hL _ _ _)

theorem UL.result_inv {r : Result} {ns : List Admin} (h : UL R r.toAdmin ns) : ns = r.toAdmin := by
  cases r with
  | values vs => exact UL.vals_inv h
  | trap =>
    simp only [Result.toAdmin] at h ⊢
    cases h with
    | cons h t => cases h; cases t; rfl
  | throw a =>
    simp only [Result.toAdmin] at h ⊢
    cases h with
    | cons h t =>
      cases h
      cases t with
      | cons h' t' =>
        cases h' with
        | plain h' => rw [UI.eq_of_flat h' rfl]; cases t'; rfl

/-! ## Escape-free code -/

/-- Steps keep code escape-free. -/
theorem NoEsc.step {P : Numerics.Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hX : NoEsc c.code) : NoEsc c'.code := by
  obtain ⟨⟨S, hB⟩, hL⟩ := hX
  exact ⟨⟨S, (Step.bud h hB).ab⟩, Step.admsLab h hL⟩

theorem NoEsc.no_br {X : List Admin} (hX : NoEsc X) {vs : List Val} {l : LabelIdx}
    {rest : List Admin} (h : X = vals vs ++ .plain (.br l) :: rest) : False := by
  have := AdmsLab_mem hX.2 (a := .plain (.br l)) (by rw [h]; simp)
  simp at this

theorem NoEsc.no_return {X : List Admin} (hX : NoEsc X) {vs : List Val} {rest : List Admin}
    (h : X = vals vs ++ .plain .return_ :: rest) : False := by
  obtain ⟨⟨S, hB⟩, -⟩ := hX
  have := AdmsB_mem hB (a := .plain .return_) (by rw [h]; simp)
  simp [budU] at this

theorem NoEsc.no_retCall {X : List Admin} (hX : NoEsc X) {vs : List Val} {c : Admin}
    {rest : List Admin} (hc : c.IsReturnCallRef) (h : X = vals vs ++ c :: rest) : False := by
  obtain ⟨⟨S, hB⟩, -⟩ := hX
  exact not_AdmB_retCall hc (AdmsB_mem hB (by rw [h]; simp))

end Silmaril.Wasm.Binaryen.Unwrap
