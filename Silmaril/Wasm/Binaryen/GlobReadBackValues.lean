module

public import Silmaril.Wasm.Binaryen.GlobReadSim

@[expose] public section

/-! # Immutable-global substitution: preparing the original value prefix

The literal side may be ready to consume a value while the original side still has
`global.get`. These reads are executable, store-preserving steps for every numerical
profile. Preparing them is the synchronization needed for a backward simulation;
it does not choose a deterministic floating-point or memory-growth policy.
-/

namespace Silmaril.Wasm.Binaryen.GlobRead

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {P : Numerics.Profile} {lk : GlobalIdx → Option Instr} {mi : ModuleInst}

theorem GL.append_inv_right {cur : ModuleInst} : ∀ {A B os : List Admin},
    GL lk mi cur os (A ++ B) →
      ∃ o₁ o₂, os = o₁ ++ o₂ ∧ GL lk mi cur o₁ A ∧ GL lk mi cur o₂ B
  | [], _, os, h => ⟨[], os, rfl, .nil _, h⟩
  | _ :: _, _, _, .cons h t => by
    obtain ⟨o₁, o₂, rfl, h₁, h₂⟩ := GL.append_inv_right t
    exact ⟨_ :: o₁, o₂, rfl, .cons h h₁, h₂⟩

/-- Lifting a finite host-free run through a value prefix and an arbitrary suffix. -/
theorem prepare_context {c c' : Config H} (h : Steps P Det.noHost c c')
    (vs : List Val) (rest : List Admin) :
    Steps P Det.noHost ⟨c.store, c.frame, vals vs ++ c.code ++ rest⟩
      ⟨c'.store, c'.frame, vals vs ++ c'.code ++ rest⟩ :=
  h.lift (fun c => (⟨c.store, c.frame, vals vs ++ c.code ++ rest⟩ : Config H))
    (fun a b hab => Det.lift_instrs vs rest a b hab)

/-- A related original instruction produces the literal value, without changing state. -/
theorem GA.prepare_value {s : Store H} {f : Frame} {a : Admin} {v : Val}
    (hinv : GInv lk mi s) (h : GA lk mi f.module a v.toAdmin) :
    Steps P Det.noHost ⟨s, f, [a]⟩ ⟨s, f, [v.toAdmin]⟩ := by
  cases v with
  | num n =>
    rcases n with ⟨ty, b⟩
    cases ty with
    | int t =>
      cases h with
      | plain h =>
        cases h with
        | flat => exact .refl
        | @site x _ _ hq hx =>
          obtain ⟨ag, g, ha, hg, _, hv⟩ := hinv _ _ _ hx
          have hget : s.global? f x = some (ag, g) := by
            simp [Store.global?, hq, ha, hg]
          simpa [hv, Val.toAdmin] using
            (Relation.ReflTransGen.single (Step.variable (P := P) (host := Det.noHost)
              (VariableStep.globalGet hget)))
    | float t =>
      cases h with
      | plain h => cases h; exact .refl
  | vec b =>
    simp only [Val.toAdmin] at h ⊢
    cases h with
    | plain h => cases h; exact .refl
  | ref r =>
    simp only [Val.toAdmin] at h ⊢
    cases h; exact .refl

/-- Prepare all original reads corresponding to an already evaluated value sequence. -/
theorem GL.prepare_values {s : Store H} {f : Frame} (hinv : GInv lk mi s) :
    ∀ {vs : List Val} {os : List Admin}, GL lk mi f.module os (vals vs) →
      Steps P Det.noHost ⟨s, f, os⟩ ⟨s, f, vals vs⟩
  | [], _, h => by cases h; exact .refl
  | v :: vs, _ :: os, .cons h t => by
    have h₁ := prepare_context (P := P) (GA.prepare_value hinv h) [] os
    have h₂ := prepare_context (P := P) (GL.prepare_values hinv t) [v] []
    simp only [vals, List.map_nil, List.map_cons, List.nil_append, List.cons_append,
      List.append_nil] at h₁ h₂ ⊢
    exact h₁.trans h₂

/-- Prepare only the value prefix, preserving the unevaluated suffix and its relation. -/
theorem GL.prepare_prefix {s : Store H} {f : Frame} {vs : List Val} {os ns : List Admin}
    (hinv : GInv lk mi s) (h : GL lk mi f.module os (vals vs ++ ns)) :
    ∃ rest, Steps P Det.noHost ⟨s, f, os⟩ ⟨s, f, vals vs ++ rest⟩ ∧
      GL lk mi f.module rest ns := by
  obtain ⟨pre, rest, rfl, hp, hr⟩ := GL.append_inv_right h
  exact ⟨rest, by simpa using prepare_context (GL.prepare_values hinv hp) [] rest, hr⟩

/-- A nonvalue atomic target has exactly the same original instruction. -/
theorem GA.atomic_back {cur : ModuleInst} {a b : Admin} (h : GA lk mi cur a b)
    (hv : b.val? = none) (hL : ∀ n c b', b ≠ .label n c b')
    (hH : ∀ n cs b', b ≠ .handler n cs b') (hF : ∀ n F b', b ≠ .frame n F b')
    (hs : ∀ i, b = .plain i → Rigid i) : a = b := by
  cases h with
  | plain h =>
    cases h with
    | flat => rfl
    | site => simp [Admin.val?] at hv
    | _ => simp [Rigid, structuredInstr] at hs
  | label _ _ => exact (hL _ _ _ rfl).elim
  | handler _ => exact (hH _ _ _ rfl).elim
  | frame _ => exact (hF _ _ _ rfl).elim
  | _ => rfl

/-- Prepare a target's value prefix up to an unchanged atomic instruction. -/
theorem GL.prepare_flat {s : Store H} {f : Frame} {vs : List Val} {y : Admin}
    {os rest : List Admin} (hinv : GInv lk mi s)
    (h : GL lk mi f.module os (vals vs ++ y :: rest))
    (hv : y.val? = none) (hL : ∀ n c b, y ≠ .label n c b)
    (hH : ∀ n cs b, y ≠ .handler n cs b) (hF : ∀ n F b, y ≠ .frame n F b)
    (hs : ∀ i, y = .plain i → Rigid i) :
    ∃ rest', Steps P Det.noHost ⟨s, f, os⟩ ⟨s, f, vals vs ++ y :: rest'⟩ ∧
      GL lk mi f.module rest' rest := by
  obtain ⟨_, hp, hr⟩ := GL.prepare_prefix (P := P) hinv h
  cases hr with
  | cons ha hr =>
    rw [GA.atomic_back ha hv hL hH hF hs] at hp
    exact ⟨_, hp, hr⟩

theorem GL.prepare_plain {s : Store H} {f : Frame} {vs : List Val} {i : Instr}
    {os rest : List Admin} (hinv : GInv lk mi s)
    (h : GL lk mi f.module os (vals vs ++ .plain i :: rest))
    (hv : (Admin.plain i).val? = none) (hi : Rigid i) :
    ∃ rest', Steps P Det.noHost ⟨s, f, os⟩ ⟨s, f, vals vs ++ .plain i :: rest'⟩ ∧
      GL lk mi f.module rest' rest :=
  GL.prepare_flat hinv h hv (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
    (fun _ _ _ h => by cases h) (fun _ h => by cases h; exact hi)

/-- A trap or thrown exception cannot hide a substituted integer literal. -/
theorem GL.abrupt_back {cur : ModuleInst} {r : Result} {os : List Admin}
    (hr : ∀ vs, r ≠ .values vs) (h : GL lk mi cur os r.toAdmin) : os = r.toAdmin := by
  cases r with
  | values vs => exact (hr vs rfl).elim
  | trap => cases h with
    | cons h t => cases h; cases t; rfl
  | throw a => cases h with
    | cons h t =>
      cases h
      cases t with
      | cons h t =>
        cases h with
        | plain h => cases h; cases t; rfl

end Silmaril.Wasm.Binaryen.GlobRead
