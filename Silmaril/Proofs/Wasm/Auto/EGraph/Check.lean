module

public import Silmaril.Proofs.Wasm.Auto.EGraph.Comp

/-! # Soundness of the e-graph certificate checker: steps, chains and the bridge

* `fold?_eval`: constant folding keeps the value;
* `rewriteAt_spec`: a rule application at a path, as a matched subterm, its
  replacement and the valuation of the pattern variables;
* `applyStep_sound`, `runSteps_sound`: a step and a chain of steps refine (and, when
  every step is an equation, preserve) the value;
* `exec_compile`, `exec_compileL`: the straight-line interpreter on compiled terms.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.EGraph

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.EGraph
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core

/-! ## Constant folding -/

theorem ofNat_toNat_eq {w : Nat} (x : BitVec w) : BitVec.ofNat w x.toNat = x := by simp

theorem fold_un_eval {f : Frame} {t t' : IntType} {op : IntUnOp} {n : Nat} {b : Term}
    (h : (if t = t' then some (Term.const t (intUnOp t op (BitVec.ofNat _ n)).toNat)
      else none) = some b) : (Term.un t op (.const t' n)).eval f = b.eval f := by
  split at h
  · rename_i ht; subst ht; cases h
    simp only [Term.eval, unV, Option.bind_some, asInt_intVal, Option.map_some, ofNat_toNat_eq]
  · cases h

theorem fold_test_eval {f : Frame} {t t' : IntType} {n : Nat} {b : Term}
    (h : (if t = t' then some (Term.const .i32 (intTestOp t .eqz (BitVec.ofNat _ n)).toNat)
      else none) = some b) : (Term.test t (.const t' n)).eval f = b.eval f := by
  split at h
  · rename_i ht; subst ht; cases h
    simp only [Term.eval, testV, Option.bind_some, asInt_intVal, Option.map_some,
      i32_eq_intVal]
    exact congrArg (fun z => some (intVal .i32 z)) (ofNat_toNat_eq _).symm
  · cases h

theorem fold_bin_eval {f : Frame} {t t₁ t₂ : IntType} {op : IntBinOp} {n₁ n₂ : Nat} {b : Term}
    (h : (if t = t₁ ∧ t = t₂ then
      match intBinOp t op (BitVec.ofNat _ n₁) (BitVec.ofNat _ n₂) with
      | .ok z => some (Term.const t z.toNat)
      | .error _ => none
    else none) = some b) : (Term.bin t op (.const t₁ n₁) (.const t₂ n₂)).eval f = b.eval f := by
  split at h
  · rename_i ht; obtain ⟨rfl, rfl⟩ := ht
    split at h
    · rename_i z hz; cases h
      simp only [Term.eval, binV, Option.bind_some, asInt_intVal, hz, ofNat_toNat_eq]
    · cases h
  · cases h

theorem fold_rel_eval {f : Frame} {t t₁ t₂ : IntType} {op : IntRelOp} {n₁ n₂ : Nat} {b : Term}
    (h : (if t = t₁ ∧ t = t₂ then
      some (Term.const .i32 (intRelOp t op (BitVec.ofNat _ n₁) (BitVec.ofNat _ n₂)).toNat)
    else none) = some b) : (Term.rel t op (.const t₁ n₁) (.const t₂ n₂)).eval f = b.eval f := by
  split at h
  · rename_i ht; obtain ⟨rfl, rfl⟩ := ht
    cases h
    simp only [Term.eval, relV, Option.bind_some, asInt_intVal, Option.map_some,
      i32_eq_intVal]
    exact congrArg (fun z => some (intVal .i32 z)) (ofNat_toNat_eq _).symm
  · cases h

/-- **Constant folding keeps the value.** -/
theorem fold?_eval {f : Frame} {a b : Term} (h : a.fold? = some b) : a.eval f = b.eval f := by
  unfold Term.fold? at h
  split at h
  · exact fold_un_eval h
  · exact fold_test_eval h
  · exact fold_bin_eval h
  · exact fold_rel_eval h
  · cases h

/-! ## Rule applications -/

/-- What `bindsOk` gives. -/
theorem bindsOk_spec {Γ : List IntType} {f : Frame} {p : Pat} {σ : Subst} (hf : FrameOk Γ f)
    (h : bindsOk Γ p σ = true) :
    (∀ tn ∈ p.vars, TypedV tn.1 (σ.val f tn.2)) ∧
      (∀ tn ∈ p.tvars, TotalV tn.1 (σ.val f tn.2)) := by
  simp only [bindsOk, Bool.and_eq_true, List.all_eq_true] at h
  constructor
  · intro tn hm
    have k := h.1 tn hm
    split at k
    · rename_i e he
      have ht : e.typeOf Γ = some tn.1 := by simpa using k
      have hv : σ.val f tn.2 = e.eval f := by simp [Subst.val, he]
      rw [hv]; exact typeOf_sound hf ht
    · cases k
  · intro tn hm
    have k := h.2 tn hm
    split at k
    · rename_i e he
      have ht : e.typeOf Γ = some tn.1 ∧ e.noTrap = true := by simpa using k
      have hv : σ.val f tn.2 = e.eval f := by simp [Subst.val, he]
      rw [hv]; exact noTrap_total hf ht.1 ht.2
    · cases k

/-- The valuation of a successful match satisfies the hypotheses of the source pattern. -/
theorem matched_hyps {Γ : List IntType} {f : Frame} {src : Pat} {a : Term} {σ₀ σ : Subst}
    (hf : FrameOk Γ f) (hm : src.match Γ a σ₀ = some σ) :
    (∀ tn ∈ src.vars, TypedV tn.1 (σ.val f tn.2)) ∧
      (∀ tn ∈ src.tvars, TotalV tn.1 (σ.val f tn.2)) := by
  constructor
  · intro tn hmem
    obtain ⟨e₀, he₀, ht⟩ := match_typed hm tn hmem
    have hv : σ.val f tn.2 = e₀.eval f := by simp [Subst.val, he₀]
    rw [hv]; exact typeOf_sound hf ht
  · intro tn hmem
    obtain ⟨e₀, he₀, ht, hn⟩ := match_total hm tn hmem
    have hv : σ.val f tn.2 = e₀.eval f := by simp [Subst.val, he₀]
    rw [hv]; exact noTrap_total hf ht hn

/-- What a rule application at a path consists of. -/
theorem rewriteAt_spec {Γ : List IntType} {f : Frame} {e e' : Term} {path : List Nat}
    {src dst : Pat} {σ₀ : Subst} (hf : FrameOk Γ f)
    (h : rewriteAt Γ e path src dst σ₀ = some e') :
    ∃ a b ρ, e.get? path = some a ∧ e.set? path b = some e' ∧ a.eval f = src.eval ρ ∧
      b.eval f = dst.eval ρ ∧ RuleHyps src dst ρ := by
  obtain ⟨a, hg, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨σ, hm, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i hb
    obtain ⟨b, hi, hs⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hty, hto⟩ := matched_hyps hf hm
    obtain ⟨dty, dto⟩ := bindsOk_spec hf hb
    refine ⟨a, b, σ.val f, hg, hs, inst_eval (match_inst hm), inst_eval hi, ?_, ?_⟩
    · intro tn hmem
      rcases List.mem_append.mp hmem with hm' | hm'
      · exact hty tn hm'
      · exact dty tn hm'
    · intro tn hmem
      rcases List.mem_append.mp hmem with hm' | hm'
      · exact hto tn hm'
      · exact dto tn hm'
  · cases h

/-- The hypotheses of a rule, read in either direction. -/
theorem RuleHyps.swap {ρ : Nat → Option Val} {p q : Pat} (h : RuleHyps p q ρ) :
    RuleHyps q p ρ :=
  ⟨fun tn hm => h.1 tn (List.mem_append.mpr (List.mem_append.mp hm).symm),
    fun tn hm => h.2 tn (List.mem_append.mpr (List.mem_append.mp hm).symm)⟩

/-- Value of a step's result, from the matched and replaced subterms. -/
theorem step_of_spec {Γ : List IntType} {f : Frame} {e e' : Term} {path : List Nat}
    {src dst : Pat} {σ₀ : Subst} (hf : FrameOk Γ f) (h : rewriteAt Γ e path src dst σ₀ = some e')
    (hR : ∀ ρ, RuleHyps src dst ρ → Ref (src.eval ρ) (dst.eval ρ)) :
    Ref (e.eval f) (e'.eval f) := by
  obtain ⟨a, b, ρ, hg, hs, ha, hb, ht⟩ := rewriteAt_spec hf h
  have hab : Ref (a.eval f) (b.eval f) := by rw [ha, hb]; exact hR ρ ht
  exact set_ref hab hg hs

/-- `step_of_spec` for equations. -/
theorem step_of_spec_eq {Γ : List IntType} {f : Frame} {e e' : Term} {path : List Nat}
    {src dst : Pat} {σ₀ : Subst} (hf : FrameOk Γ f) (h : rewriteAt Γ e path src dst σ₀ = some e')
    (hR : ∀ ρ, RuleHyps src dst ρ → src.eval ρ = dst.eval ρ) :
    e.eval f = e'.eval f := by
  obtain ⟨a, b, ρ, hg, hs, ha, hb, ht⟩ := rewriteAt_spec hf h
  have hab : a.eval f = b.eval f := by rw [ha, hb]; exact hR ρ ht
  exact set_eq hab hg hs

theorem StepOk.of_eq {f : Frame} {e e' : Term} (h : e.eval f = e'.eval f) :
    StepOk f e e' true :=
  ⟨Ref.of_eq h, fun _ => h⟩

/-- A rule step, given the rule's soundness. -/
theorem applyRule_sound {Γ : List IntType} {f : Frame} {e e' : Term} {b fwd : Bool}
    {path : List Nat} {σ₀ : Subst} {r : Rule} (hr : r.Sound) (hf : FrameOk Γ f)
    (h : (match r.kind, fwd with
      | .eq, true => (rewriteAt Γ e path r.lhs r.rhs σ₀).map (·, true)
      | .eq, false => (rewriteAt Γ e path r.rhs r.lhs σ₀).map (·, true)
      | .ref, true => (rewriteAt Γ e path r.lhs r.rhs σ₀).map (·, false)
      | .ref, false => none) = some (e', b)) :
    StepOk f e e' b := by
  unfold Rule.Sound at hr
  cases hk : r.kind <;> cases fwd <;> rw [hk] at hr h <;> simp only [] at h
  · obtain ⟨e₀, h₀, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact StepOk.of_eq (step_of_spec_eq hf h₀ fun ρ ht =>
      (hr ρ (RuleHyps.swap ht).1 (RuleHyps.swap ht).2).symm)
  · obtain ⟨e₀, h₀, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact StepOk.of_eq (step_of_spec_eq hf h₀ fun ρ ht => hr ρ ht.1 ht.2)
  · cases h
  · obtain ⟨e₀, h₀, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact ⟨step_of_spec hf h₀ fun ρ ht => hr ρ ht.1 ht.2, fun hb => by cases hb⟩

/-- **A step is sound.** -/
theorem applyStep_sound {Γ : List IntType} {rules : List Rule} {f : Frame} {e e' : Term}
    {b : Bool} (hR : ∀ r ∈ rules, r.Sound) (hf : FrameOk Γ f) :
    ∀ {s : Step}, applyStep Γ rules e s = some (e', b) → StepOk f e e' b
  | .rw i fwd path σ₀, h => by
    simp only [applyStep] at h
    split at h
    · cases h
    · rename_i r hr
      exact applyRule_sound (hR r (List.mem_of_getElem? hr)) hf h
  | .fold path, h => by
    obtain ⟨a, hg, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨e₀, hs, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact StepOk.of_eq (set_eq (fold?_eval hc) hg hs)
  | .comp path, h => by
    obtain ⟨a, hg, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨e₀, hs, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact StepOk.of_eq (set_eq (comp?_eval hc) hg hs)
  | .uncomp path c, h => by
    obtain ⟨a, hg, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hc
      obtain ⟨e₀, hs, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact StepOk.of_eq (set_eq (comp?_eval hc).symm hg hs)
    · cases h
  | .unfold path c, h => by
    obtain ⟨a, hg, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hc
      obtain ⟨e₀, hs, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact StepOk.of_eq (set_eq (fold?_eval hc).symm hg hs)
    · cases h

/-- **A chain of steps is sound.** -/
theorem runSteps_sound {Γ : List IntType} {rules : List Rule} {f : Frame}
    (hR : ∀ r ∈ rules, r.Sound) (hf : FrameOk Γ f) :
    ∀ {ss : List Step} {e e' : Term} {b : Bool}, runSteps Γ rules e ss = some (e', b) →
      StepOk f e e' b
  | [], e, e', b, h => by
    cases h; exact StepOk.of_eq rfl
  | s :: ss, e, e', b, h => by
    simp only [runSteps] at h
    split at h
    · cases h
    · rename_i e₁ b₁ h₁
      split at h
      · cases h
      · rename_i e₂ b₂ h₂
        cases h
        have k₁ : StepOk f e e₁ b₁ := applyStep_sound hR hf h₁
        have k₂ : StepOk f e₁ e' b₂ := runSteps_sound hR hf h₂
        refine ⟨Ref.trans k₁.1 k₂.1, fun hb => ?_⟩
        have hb' : b₁ = true ∧ b₂ = true := by simpa using hb
        exact (k₁.2 hb'.1).trans (k₂.2 hb'.2)

/-! ## The bridge to the straight-line interpreter -/

theorem popInt_cons (t : IntType) (v : Val) (rs : List Val) :
    popInt t (v :: rs) = (asInt t v).map (·, rs) := by
  cases t <;> rcases v with ⟨⟨(_ | _) | _⟩, b⟩ | _ | _ <;> rfl

theorem exec1_un {H : Type} (s : Store H) (f : Frame) (rs : List Val) (t : IntType)
    (op : IntUnOp) (va : Val) :
    exec1 s f (va :: rs) (.intUnOp t op) = pushed s f rs (unV t op (some va)) := by
  simp only [exec1, popInt_cons, unV, Option.bind_some, pushed]
  cases asInt t va <;> rfl

theorem exec1_test {H : Type} (s : Store H) (f : Frame) (rs : List Val) (t : IntType)
    (va : Val) :
    exec1 s f (va :: rs) (.intTestOp t .eqz) = pushed s f rs (testV t (some va)) := by
  simp only [exec1, popInt_cons, testV, Option.bind_some, pushed]
  cases asInt t va <;> rfl

theorem exec1_bin {H : Type} (s : Store H) (f : Frame) (rs : List Val) (t : IntType)
    (op : IntBinOp) (va vb : Val) :
    exec1 s f (vb :: va :: rs) (.intBinOp t op) = pushed s f rs (binV t op (some va) (some vb)) := by
  cases hy : asInt t vb <;> cases hx : asInt t va <;>
    simp only [exec1, popInt_cons, hx, hy, binV, Option.map_some, Option.map_none,
      Option.bind_some, Option.bind_none, pushed]
  split <;> rename_i heq <;> rw [heq] <;> rfl

theorem exec1_rel {H : Type} (s : Store H) (f : Frame) (rs : List Val) (t : IntType)
    (op : IntRelOp) (va vb : Val) :
    exec1 s f (vb :: va :: rs) (.intRelOp t op) = pushed s f rs (relV t op (some va) (some vb)) := by
  cases hy : asInt t vb <;> cases hx : asInt t va <;>
    simp only [exec1, popInt_cons, hx, hy, relV, Option.map_some, Option.map_none,
      Option.bind_some, Option.bind_none, pushed]

/-- One instruction at the end of a sequence. -/
theorem exec_single {H : Type} (s : Store H) (f : Frame) (rs : List Val) (i : Instr) :
    exec s f rs [i] = exec1 s f rs i := by
  rw [exec_cons]
  cases exec1 s f rs i <;> rfl

/-- Running the compiled code of a term pushes its value and changes nothing else. -/
theorem exec_compile {H : Type} (s : Store H) (f : Frame) :
    ∀ (e : Term) (rs : List Val), exec s f rs e.compile = pushed s f rs (e.eval f)
  | .const t n, rs => rfl
  | .lget i, rs => by
    rw [Term.compile, exec_single]
    rfl
  | .un t op a, rs => by
    rw [Term.compile, exec_append, exec_compile s f a]
    cases ha : a.eval f with
    | none => simp [Term.eval, ha, unV]
    | some va => rw [Term.eval, ha]; exact (exec_single ..).trans (exec1_un ..)
  | .test t a, rs => by
    rw [Term.compile, exec_append, exec_compile s f a]
    cases ha : a.eval f with
    | none => simp [Term.eval, ha, testV]
    | some va => rw [Term.eval, ha]; exact (exec_single ..).trans (exec1_test ..)
  | .bin t op a b, rs => by
    rw [Term.compile, List.append_assoc, exec_append, exec_compile s f a]
    cases ha : a.eval f with
    | none => simp [Term.eval, ha, binV]
    | some va =>
      rw [pushed, Option.map_some]
      simp only []
      rw [exec_append, exec_compile s f b]
      cases hb : b.eval f with
      | none => simp [Term.eval, ha, hb, binV]
      | some vb => rw [Term.eval, ha, hb]; exact (exec_single ..).trans (exec1_bin ..)
  | .rel t op a b, rs => by
    rw [Term.compile, List.append_assoc, exec_append, exec_compile s f a]
    cases ha : a.eval f with
    | none => simp [Term.eval, ha, relV]
    | some va =>
      rw [pushed, Option.map_some]
      simp only []
      rw [exec_append, exec_compile s f b]
      cases hb : b.eval f with
      | none => simp [Term.eval, ha, hb, relV]
      | some vb => rw [Term.eval, ha, hb]; exact (exec_single ..).trans (exec1_rel ..)

/-- Running the compiled code of a sequence of terms pushes their values. -/
theorem exec_compileL {H : Type} (s : Store H) (f : Frame) :
    ∀ (es : List Term) (rs : List Val),
      exec s f rs (compileL es) = (evalL f es).map fun vs => (s, f, vs.reverse ++ rs)
  | [], rs => rfl
  | e :: es, rs => by
    simp only [compileL, exec_append, exec_compile s f e]
    cases he : e.eval f with
    | none => simp [evalL, he]
    | some v =>
      simp only [Option.map_some, exec_compileL s f es]
      cases hs : evalL f es <;> simp [evalL, he, hs]

end Silmaril.Proofs.Wasm.Auto.EGraph