module

public import Silmaril.Wasm.Models.FunCloCompile.Thms
public import Silmaril.Wasm.Logic.Hoare.Thms
public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Logic.Instr.Thms

/-!
# Divergence in the every-run logic: total prefixes, conditionals and behaviours

Generic lemmas for proving that code runs forever with the step-indexed safety predicate
`Hoare.Safe`, for every profile and host relation:

* `thenSafe`, `safe_of_twp`: a **total prefix** followed by a partial continuation. If `c₁`
  falls through, totally correctly, into configurations from which `c₂` is safe for `n` steps,
  then `c₁ ++ c₂` is safe for `n` steps. This is how the total-correctness proofs of
  terminating subterms are reused around a diverging one;
* `safe_if`, `safe_ifBlock`: `if` at a given step index;
* `behaviours_eq_diverges`: a valid function specification whose postcondition never holds
  makes `diverges` the only behaviour of `$invoke`: no run ends (in values, a trap or an
  exception), and an infinite run exists (`InfiniteTrace.coinduct`).

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunCloDiv

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Post Outcome)
open Silmaril.Wasm.Models.FunCompile (anyref)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The postcondition of a total prefix: it falls through, and `c₂` is then safe for `n`
steps. -/
def thenSafe (P : Profile) (host : HostSemantics H) (Q : Post H) (n : Nat) (c₂ : List Admin) :
    Post H :=
  fun s f o => ∃ vs, o = .normal vs ∧ Safe P host Q n ⟨s, f, vals vs ++ c₂⟩

/-- **A total prefix, then a partial continuation.** -/
theorem safe_of_twp {n : Nat} {s : Store H} {f : Frame} {c₁ c₂ : List Admin} {Q : Post H}
    (h : TWP P host s f c₁ (thenSafe P host Q n c₂)) : Safe P host Q n ⟨s, f, c₁ ++ c₂⟩ := by
  refine Safe.seq (k := n) le_rfl (Safe.post_mono (fun s' f' o ho => ?_) (TSafe.safe h n))
  obtain ⟨vs, rfl, hs⟩ := ho
  exact hs

/-- Falling through into a safe continuation. -/
theorem twp_thenSafe {n : Nat} {s : Store H} {f : Frame} {vs : List Val} {c₂ : List Admin}
    {Q : Post H} (h : Safe P host Q n ⟨s, f, vals vs ++ c₂⟩) :
    TWP P host s f (vals vs) (thenSafe P host Q n c₂) :=
  Wp.of_vals (m := .total) ⟨vs, rfl, h⟩

/-- `twp_thenSafe` with an empty code after the values. -/
theorem twp_thenSafe' {n : Nat} {s : Store H} {f : Frame} {vs : List Val} {c₂ : List Admin}
    {Q : Post H} (h : Safe P host Q n ⟨s, f, vals vs ++ c₂⟩) :
    TWP P host s f (vals vs ++ []) (thenSafe P host Q n c₂) := by
  rw [List.append_nil]
  exact twp_thenSafe h

/-- **`if`** at a step index. -/
theorem safe_if {n : Nat} {s : Store H} {f : Frame} {us : List Val} {c : BitVec 32}
    {bt : BlockType} {b₁ b₂ : List Instr} {rest : List Admin} {Q : Post H}
    (h₁ : c ≠ 0 → Safe P host Q n ⟨s, f, vals us ++ .plain (.block bt b₁) :: rest⟩)
    (h₂ : c = 0 → Safe P host Q n ⟨s, f, vals us ++ .plain (.block bt b₂) :: rest⟩) :
    Safe P host Q (n + 1) ⟨s, f, vals (us ++ [.i32 c]) ++ .plain (.if_ bt b₁ b₂) :: rest⟩ := by
  have hp : ∃ vs args c₀, us ++ [Val.i32 c] = vs ++ args ∧
      Head P s f args (.plain (.if_ bt b₁ b₂)) c₀ := by
    by_cases hc : c = 0
    · exact ⟨us, _, _, rfl, .ifFalse hc⟩
    · exact ⟨us, _, _, rfl, .ifTrue hc⟩
  refine Safe.head ⟨rfl, by simp, rfl⟩ hp ?_
  intro us' args c₀ hW hh
  obtain ⟨c', rfl, ⟨hc, rfl⟩ | ⟨hc, rfl⟩⟩ := head_if hh <;>
    obtain ⟨rfl, hv⟩ := split_one hW <;> obtain rfl := i32_inj hv.symm
  · simpa using h₁ hc
  · simpa using h₂ hc

/-- **An `if` with result `anyref`** whose selected branch is safe for `n` steps. -/
theorem safe_ifBlock {n : Nat} {s : Store H} {f : Frame} {us : List Val} {c : BitVec 32}
    {b₁ b₂ : List Instr} {rest : List Admin} {Q : Post H}
    (h : Safe P host (labelPostK P host 1 [] us (seqPostK P host rest Q n) n) n
      ⟨s, f, vals [] ++ expression (if c ≠ 0 then b₁ else b₂)⟩) :
    Safe P host Q n
      ⟨s, f, vals (us ++ [.i32 c]) ++ .plain (.if_ (.value anyref) b₁ b₂) :: rest⟩ := by
  have hb : Safe P host Q (n + 1) ⟨s, f, vals (us ++ []) ++
      .plain (.block (.value anyref) (if c ≠ 0 then b₁ else b₂)) :: rest⟩ :=
    Safe.block (k := n) (t₁ := []) (t₂ := [f.module.instVal anyref]) le_rfl rfl rfl h
  have hb' : Safe P host Q (n + 1) ⟨s, f, vals us ++
      .plain (.block (.value anyref) (if c ≠ 0 then b₁ else b₂)) :: rest⟩ := by
    simpa using hb
  refine Safe.mono (Nat.le_add_right n 2) (safe_if (fun hc => ?_) (fun hc => ?_))
  · have hsel : (if c ≠ 0 then b₁ else b₂) = b₁ := by
      simp only [ne_eq, hc, not_false_eq_true, ↓reduceIte]
    exact hsel ▸ hb'
  · have hsel : (if c ≠ 0 then b₁ else b₂) = b₂ := by
      simp only [hc, ne_eq, not_true_eq_false, ↓reduceIte]
    exact hsel ▸ hb'

/-! ## Behaviours -/

/-- A configuration whose code is a result cannot step. -/
theorem not_step_result {c c' : Config H} {r : Result} (hc : c.code = r.toAdmin) :
    ¬ Step P host c c' := by
  obtain ⟨s, f, code⟩ := c
  have hcode : code = r.toAdmin := hc
  subst hcode
  cases r with
  | values vs => exact not_step_vals
  | throw a => exact not_step_throwing
  | trap => exact not_step_trap

/-- **A valid specification that never returns makes `$invoke` diverge**, and nothing else. -/
theorem behaviours_eq_diverges {a : Nat} {S : FSpec H} {s : Store H} {args : List Val}
    (h : FSpecValid P host a S) (hpre : S.pre s args) (hpost : ∀ s' o, ¬ S.post s args s' o) :
    behaviours P host s a args = {.diverges} := by
  have hnx : ∀ c', Steps P host (invoke s a args) c' → ∃ c'', Step P host c' c'' := by
    intro c' hs
    refine (h.invoke_safe hpre hs).resolve_right ?_
    rintro ⟨o, -, -, ⟨res, -, hr⟩ | ⟨-, hr⟩ | ⟨_, -, hr⟩⟩ <;> exact hpost _ _ hr
  have hdiv : Diverges P host (invoke s a args) :=
    Silmaril.InfiniteTrace.coinduct (Steps P host (invoke s a args))
      (fun c hc => (hnx c hc).imp fun c'' hst => ⟨hst, hc.tail hst⟩) Relation.ReflTransGen.refl
  ext b
  constructor
  · rintro (⟨c', r, hs, hc, -⟩ | ⟨rfl, -⟩)
    · exact absurd (hnx c' hs).choose_spec (not_step_result hc)
    · rfl
  · rintro rfl
    exact Or.inr ⟨rfl, hdiv⟩

end Silmaril.Proofs.Wasm.Models.FunCloDiv
