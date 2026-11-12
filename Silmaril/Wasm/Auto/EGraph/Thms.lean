module

public import Silmaril.Wasm.Auto.EGraph.Defs
public import Silmaril.Wasm.Logic.Core.Thms
import Silmaril.Proofs.Wasm.Auto.EGraph.Check

/-! # Proof-producing equality saturation for Wasm: soundness

The checker of `Silmaril.Wasm.Auto.EGraph.Defs` turns a certificate into a theorem:

* `checkEq_sound`, `checkRef_sound`: a checked chain of rule applications preserves
  (refines) the value of a term in every frame typed by `Γ`, given that every rule of
  the library is sound (`Rule.Sound`, proved once per rule);
* `segEquiv_of_checkEqL`, `segRefines_of_checkRefL`: the same for the compiled Core 3.0
  instruction sequences, as `SegEquiv` / `SegRefines` of the straight-line interpreter
  `exec` (from every store, frame typed by `Γ` and operand stack);
* contexts: `SegEquiv.append_right` (any suffix), `SegEquiv.append_left` (a prefix that
  keeps the frame typed, e.g. any pure segment), and the transitivity and symmetry
  lemmas, so one segment proof is reused in any surrounding code;
* `SegEquiv.steps`, `SegRefines.steps`: the small-step reading. When one side runs (by
  `exec`), the other has a run of silmaril-lean's `Steps` to the same configuration,
  in any profile and for any host.

Proofs: `Silmaril.Proofs.Wasm.Auto.EGraph.{Sound,Check}`.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.EGraph

/-! ## Results proved in `Silmaril.Proofs.Wasm.Auto.EGraph` -/

section
-- from Silmaril/Proofs/Wasm/Auto/EGraph/Check.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.EGraph
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core

/-- The hypotheses of a rule, read in either direction. -/
theorem RuleHyps.swap {ρ : Nat → Option Val} {p q : Pat} (h : RuleHyps p q ρ) :
    RuleHyps q p ρ :=
  Silmaril.Proofs.Wasm.Auto.EGraph.RuleHyps.swap (ρ := ρ) (p := p) (q := q) (h := h)

theorem StepOk.of_eq {f : Frame} {e e' : Term} (h : e.eval f = e'.eval f) :
    StepOk f e e' true :=
  Silmaril.Proofs.Wasm.Auto.EGraph.StepOk.of_eq (f := f) (e := e) (e' := e') (h := h)

/-- **A step is sound.** -/
theorem applyStep_sound {Γ : List IntType} {rules : List Rule} {f : Frame} {e e' : Term}
    {b : Bool} (hR : ∀ r ∈ rules, r.Sound) (hf : FrameOk Γ f) :
    ∀ {s : Step}, applyStep Γ rules e s = some (e', b) → StepOk f e e' b :=
  Silmaril.Proofs.Wasm.Auto.EGraph.applyStep_sound (Γ := Γ) (rules := rules) (f := f) (e := e)
    (e' := e') (b := b) (hR := hR) (hf := hf)

/-- **A chain of steps is sound.** -/
theorem runSteps_sound {Γ : List IntType} {rules : List Rule} {f : Frame}
    (hR : ∀ r ∈ rules, r.Sound) (hf : FrameOk Γ f) :
    ∀ {ss : List Step} {e e' : Term} {b : Bool}, runSteps Γ rules e ss = some (e', b) →
      StepOk f e e' b :=
  Silmaril.Proofs.Wasm.Auto.EGraph.runSteps_sound (Γ := Γ) (rules := rules) (f := f) (hR := hR)
    (hf := hf)

theorem popInt_cons (t : IntType) (v : Val) (rs : List Val) :
    popInt t (v :: rs) = (asInt t v).map (·, rs) :=
  Silmaril.Proofs.Wasm.Auto.EGraph.popInt_cons (t := t) (v := v) (rs := rs)

theorem exec1_un {H : Type} (s : Store H) (f : Frame) (rs : List Val) (t : IntType)
    (op : IntUnOp) (va : Val) :
    exec1 s f (va :: rs) (.intUnOp t op) = pushed s f rs (unV t op (some va)) :=
  Silmaril.Proofs.Wasm.Auto.EGraph.exec1_un (H := H) (s := s) (f := f) (rs := rs) (t := t) (op := op)
    (va := va)

theorem exec1_test {H : Type} (s : Store H) (f : Frame) (rs : List Val) (t : IntType)
    (va : Val) :
    exec1 s f (va :: rs) (.intTestOp t .eqz) = pushed s f rs (testV t (some va)) :=
  Silmaril.Proofs.Wasm.Auto.EGraph.exec1_test (H := H) (s := s) (f := f) (rs := rs) (t := t) (va := va)

theorem exec1_bin {H : Type} (s : Store H) (f : Frame) (rs : List Val) (t : IntType)
    (op : IntBinOp) (va vb : Val) :
    exec1 s f (vb :: va :: rs) (.intBinOp t op) = pushed s f rs (binV t op (some va) (some vb)) :=
  Silmaril.Proofs.Wasm.Auto.EGraph.exec1_bin (H := H) (s := s) (f := f) (rs := rs) (t := t) (op := op)
    (va := va) (vb := vb)

theorem exec1_rel {H : Type} (s : Store H) (f : Frame) (rs : List Val) (t : IntType)
    (op : IntRelOp) (va vb : Val) :
    exec1 s f (vb :: va :: rs) (.intRelOp t op) = pushed s f rs (relV t op (some va) (some vb)) :=
  Silmaril.Proofs.Wasm.Auto.EGraph.exec1_rel (H := H) (s := s) (f := f) (rs := rs) (t := t) (op := op)
    (va := va) (vb := vb)

/-- Running the compiled code of a sequence of terms pushes their values. -/
theorem exec_compileL {H : Type} (s : Store H) (f : Frame) :
    ∀ (es : List Term) (rs : List Val),
      exec s f rs (compileL es) = (evalL f es).map fun vs => (s, f, vs.reverse ++ rs) :=
  Silmaril.Proofs.Wasm.Auto.EGraph.exec_compileL (H := H) (s := s) (f := f)

end

section
-- from Silmaril/Proofs/Wasm/Auto/EGraph/Comp.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.EGraph
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

theorem pow2Exp?_spec {w n k : Nat} (h : pow2Exp? w n = some k) : k < w ∧ 2 ^ k = n :=
  Silmaril.Proofs.Wasm.Auto.EGraph.pow2Exp?_spec (w := w) (n := n) (k := k) (h := h)

theorem toNat_ofNat_lt {w k : Nat} (hk : k < w) : (BitVec.ofNat w k).toNat = k :=
  Silmaril.Proofs.Wasm.Auto.EGraph.toNat_ofNat_lt (w := w) (k := k) (hk := hk)

theorem toNat_ofNat_pow {w k : Nat} (hk : k < w) : (BitVec.ofNat w (2 ^ k)).toNat = 2 ^ k :=
  Silmaril.Proofs.Wasm.Auto.EGraph.toNat_ofNat_pow (w := w) (k := k) (hk := hk)

theorem umod_pow2 {w k : Nat} (hk : k < w) (x : BitVec w) :
    x % BitVec.ofNat w (2 ^ k) = x &&& BitVec.ofNat w (2 ^ k - 1) :=
  Silmaril.Proofs.Wasm.Auto.EGraph.umod_pow2 (w := w) (k := k) (hk := hk) (x := x)

theorem pow2_ne_zero {w k : Nat} (hk : k < w) : BitVec.ofNat w (2 ^ k) ≠ 0 :=
  Silmaril.Proofs.Wasm.Auto.EGraph.pow2_ne_zero (w := w) (k := k) (hk := hk)

end

section
-- from Silmaril/Proofs/Wasm/Auto/EGraph/Sound.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.EGraph
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core

theorem Ref.refl {α : Type} (o : Option α) : Ref o o :=
  Silmaril.Proofs.Wasm.Auto.EGraph.Ref.refl (α := α) (o := o)

theorem Ref.trans {α : Type} {a b c : Option α} (h₁ : Ref a b) (h₂ : Ref b c) : Ref a c :=
  Silmaril.Proofs.Wasm.Auto.EGraph.Ref.trans (α := α) (a := a) (b := b) (c := c) (h₁ := h₁) (h₂ := h₂)

theorem Ref.of_eq {α : Type} {a b : Option α} (h : a = b) : Ref a b :=
  Silmaril.Proofs.Wasm.Auto.EGraph.Ref.of_eq (α := α) (a := a) (b := b) (h := h)

theorem Ref.antisymm {α : Type} {a b : Option α} (h₁ : Ref a b) (h₂ : Ref b a) : a = b :=
  Silmaril.Proofs.Wasm.Auto.EGraph.Ref.antisymm (α := α) (a := a) (b := b) (h₁ := h₁) (h₂ := h₂)

@[simp] theorem asInt_intVal (t : IntType) (x : BitVec t.width) :
    asInt t (intVal t x) = some x :=
  Silmaril.Proofs.Wasm.Auto.EGraph.asInt_intVal (t := t) (x := x)

@[simp] theorem i32_eq_intVal (x : BitVec 32) : Val.i32 x = intVal .i32 x :=
  Silmaril.Proofs.Wasm.Auto.EGraph.i32_eq_intVal (x := x)

/-- **Typing is sound**: in a frame typed by `Γ`, a term of type `t` traps or has a
value of type `t`. -/
theorem typeOf_sound {Γ : List IntType} {f : Frame} (hf : FrameOk Γ f) :
    ∀ {e : Term} {t : IntType}, e.typeOf Γ = some t → TypedV t (e.eval f) :=
  Silmaril.Proofs.Wasm.Auto.EGraph.typeOf_sound (Γ := Γ) (f := f) (hf := hf)

/-- **Terms without division cannot trap**: in a frame typed by `Γ`, a term of type `t`
without division or remainder has an integer value of type `t`. -/
theorem noTrap_total {Γ : List IntType} {f : Frame} (hf : FrameOk Γ f) :
    ∀ {e : Term} {t : IntType}, e.typeOf Γ = some t → e.noTrap = true → TotalV t (e.eval f) :=
  Silmaril.Proofs.Wasm.Auto.EGraph.noTrap_total (Γ := Γ) (f := f) (hf := hf)

theorem Subst.Ext.refl (σ : Subst) : σ.Ext σ :=
  Silmaril.Proofs.Wasm.Auto.EGraph.Subst.Ext.refl (σ := σ)

theorem Subst.Ext.trans {a b c : Subst} (h₁ : a.Ext b) (h₂ : b.Ext c) : a.Ext c :=
  Silmaril.Proofs.Wasm.Auto.EGraph.Subst.Ext.trans (a := a) (b := b) (c := c) (h₁ := h₁) (h₂ := h₂)

theorem Subst.Ext.cons {σ : Subst} {n : Nat} {e : Term} (h : σ.find? n = none) :
    σ.Ext ((n, e) :: σ) :=
  Silmaril.Proofs.Wasm.Auto.EGraph.Subst.Ext.cons (σ := σ) (n := n) (e := e) (h := h)

theorem Subst.Typed.ext {Γ : List IntType} {σ σ' : Subst} {vs : List (IntType × Nat)}
    (h : σ.Typed Γ vs) (hx : σ.Ext σ') : σ'.Typed Γ vs :=
  Silmaril.Proofs.Wasm.Auto.EGraph.Subst.Typed.ext (Γ := Γ) (σ := σ) (σ' := σ') (vs := vs) (h := h)
    (hx := hx)

theorem Subst.Total.ext {Γ : List IntType} {σ σ' : Subst} {vs : List (IntType × Nat)}
    (h : σ.Total Γ vs) (hx : σ.Ext σ') : σ'.Total Γ vs :=
  Silmaril.Proofs.Wasm.Auto.EGraph.Subst.Total.ext (Γ := Γ) (σ := σ) (σ' := σ') (vs := vs) (h := h)
    (hx := hx)

/-- After a replacement, the path holds the new subterm, and replacing it back restores
the term. -/
theorem get_set {a b : Term} :
    ∀ {e e' : Term} {p : List Nat}, e.get? p = some a → e.set? p b = some e' →
      e'.get? p = some b ∧ e'.set? p a = some e :=
  Silmaril.Proofs.Wasm.Auto.EGraph.get_set (a := a) (b := b)

/-- Congruence for equal values. -/
theorem set_eq {f : Frame} {a b e e' : Term} {p : List Nat} (hab : a.eval f = b.eval f)
    (hg : e.get? p = some a) (hs : e.set? p b = some e') : e.eval f = e'.eval f :=
  Silmaril.Proofs.Wasm.Auto.EGraph.set_eq (f := f) (a := a) (b := b) (e := e) (e' := e') (p := p)
    (hab := hab) (hg := hg) (hs := hs)

end

end Silmaril.Wasm.Auto.EGraph

namespace Silmaril.Wasm.Auto.EGraph

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core

/-- **Soundness of the equivalence checker.** -/
theorem checkEq_sound {Γ : List IntType} {rules : List Rule} {e₁ e₂ : Term}
    {steps : List Step} (hR : ∀ r ∈ rules, r.Sound) (h : checkEq Γ rules e₁ e₂ steps = true)
    {f : Frame} (hf : FrameOk Γ f) : e₁.eval f = e₂.eval f := by
  unfold checkEq at h
  split at h
  · rename_i e hrun
    have he : e = e₂ := by simpa using h
    rw [← he]
    exact (runSteps_sound hR hf hrun).2 rfl
  · cases h

/-- **Soundness of the refinement checker.** -/
theorem checkRef_sound {Γ : List IntType} {rules : List Rule} {e₁ e₂ : Term}
    {steps : List Step} (hR : ∀ r ∈ rules, r.Sound) (h : checkRef Γ rules e₁ e₂ steps = true)
    {f : Frame} (hf : FrameOk Γ f) : ∀ v, e₁.eval f = some v → e₂.eval f = some v := by
  unfold checkRef at h
  split at h
  · rename_i e b hrun
    have he : e = e₂ := by simpa using h
    rw [← he]
    exact (runSteps_sound hR hf hrun).1
  · cases h

theorem evalL_eq_of_checkEqL {Γ : List IntType} {rules : List Rule} (hR : ∀ r ∈ rules, r.Sound)
    {f : Frame} (hf : FrameOk Γ f) :
    ∀ {es₁ es₂ : List Term} {cs : List (List Step)}, checkEqL Γ rules es₁ es₂ cs = true →
      evalL f es₁ = evalL f es₂
  | [], [], [], _ => rfl
  | e₁ :: es₁, e₂ :: es₂, c :: cs, h => by
    simp only [checkEqL, Bool.and_eq_true] at h
    simp only [evalL, checkEq_sound hR h.1 hf, evalL_eq_of_checkEqL hR hf h.2]
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by
    simp [checkEqL] at h

theorem evalL_ref_of_checkRefL {Γ : List IntType} {rules : List Rule}
    (hR : ∀ r ∈ rules, r.Sound) {f : Frame} (hf : FrameOk Γ f) :
    ∀ {es₁ es₂ : List Term} {cs : List (List Step)}, checkRefL Γ rules es₁ es₂ cs = true →
      ∀ vs, evalL f es₁ = some vs → evalL f es₂ = some vs
  | [], [], [], _, _, h => h
  | e₁ :: es₁, e₂ :: es₂, c :: cs, h, vs, hv => by
    simp only [checkRefL, Bool.and_eq_true] at h
    obtain ⟨v, hv₁, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨ws, hw, rfl⟩ := Option.map_eq_some_iff.mp hv
    simp only [evalL, checkRef_sound hR h.1 hf v hv₁, Option.bind_some,
      evalL_ref_of_checkRefL hR hf h.2 ws hw, Option.map_some]
  | [], _ :: _, _, h, _, _ | [], [], _ :: _, h, _, _ | _ :: _, [], _, h, _, _
  | _ :: _, _ :: _, [], h, _, _ => by simp [checkRefL] at h

/-- **Segment equivalence from a certificate.** The sequences of terms compile to
equivalent Core 3.0 instruction sequences. -/
theorem segEquiv_of_checkEqL {Γ : List IntType} {rules : List Rule} {es₁ es₂ : List Term}
    (cs : List (List Step)) (hR : ∀ r ∈ rules, r.Sound)
    (h : checkEqL Γ rules es₁ es₂ cs = true) : SegEquiv Γ (compileL es₁) (compileL es₂) := by
  intro H s f rs hf
  rw [exec_compileL, exec_compileL, evalL_eq_of_checkEqL hR hf h]

/-- **Segment refinement from a certificate.** -/
theorem segRefines_of_checkRefL {Γ : List IntType} {rules : List Rule} {es₁ es₂ : List Term}
    (cs : List (List Step)) (hR : ∀ r ∈ rules, r.Sound)
    (h : checkRefL Γ rules es₁ es₂ cs = true) :
    SegRefines Γ (compileL es₁) (compileL es₂) := by
  intro H s f rs r hf hr
  rw [exec_compileL] at hr ⊢
  obtain ⟨vs, hv, rfl⟩ := Option.map_eq_some_iff.mp hr
  rw [evalL_ref_of_checkRefL hR hf h vs hv, Option.map_some]

/-! ## Contexts -/

theorem SegEquiv.refl (Γ : List IntType) (is : List Instr) : SegEquiv Γ is is :=
  fun _ _ _ _ => rfl

theorem SegEquiv.symm {Γ : List IntType} {a b : List Instr} (h : SegEquiv Γ a b) :
    SegEquiv Γ b a :=
  fun s f rs hf => (h s f rs hf).symm

theorem SegEquiv.trans {Γ : List IntType} {a b c : List Instr} (h₁ : SegEquiv Γ a b)
    (h₂ : SegEquiv Γ b c) : SegEquiv Γ a c :=
  fun s f rs hf => (h₁ s f rs hf).trans (h₂ s f rs hf)

theorem SegEquiv.refines {Γ : List IntType} {a b : List Instr} (h : SegEquiv Γ a b) :
    SegRefines Γ a b :=
  fun s f rs _ hf hr => (h s f rs hf) ▸ hr

theorem SegRefines.trans {Γ : List IntType} {a b c : List Instr} (h₁ : SegRefines Γ a b)
    (h₂ : SegRefines Γ b c) : SegRefines Γ a c :=
  fun s f rs r hf hr => h₂ s f rs r hf (h₁ s f rs r hf hr)

/-- Any code after an equivalent segment. -/
theorem SegEquiv.append_right {Γ : List IntType} {a b : List Instr} (h : SegEquiv Γ a b)
    (q : List Instr) : SegEquiv Γ (a ++ q) (b ++ q) := by
  intro H s f rs hf
  rw [exec_append, exec_append, h s f rs hf]

/-- A segment that keeps the frame typed by `Γ` (for example, any code without
`local.set` and `local.tee`). -/
def KeepsFrame (Γ : List IntType) (p : List Instr) : Prop :=
  ∀ {H : Type} (s : Store H) (f : Frame) (rs : List Val) s' f' rs', FrameOk Γ f →
    exec s f rs p = some (s', f', rs') → FrameOk Γ f'

/-- Any code before an equivalent segment that keeps the frame typed. -/
theorem SegEquiv.append_left {Γ : List IntType} {a b p : List Instr} (h : SegEquiv Γ a b)
    (hp : KeepsFrame Γ p) : SegEquiv Γ (p ++ a) (p ++ b) := by
  intro H s f rs hf
  rw [exec_append, exec_append]
  split
  · rename_i s' f' rs' he
    exact h s' f' rs' (hp s f rs s' f' rs' hf he)
  · rfl

/-- Compiled terms keep the frame. -/
theorem keepsFrame_compileL (Γ : List IntType) (es : List Term) :
    KeepsFrame Γ (compileL es) := by
  intro H s f rs s' f' rs' hf he
  rw [exec_compileL] at he
  obtain ⟨vs, -, he⟩ := Option.map_eq_some_iff.mp he
  cases he
  exact hf

/-- The refinement form of `SegEquiv.append_right`. -/
theorem SegRefines.append_right {Γ : List IntType} {a b : List Instr} (h : SegRefines Γ a b)
    (q : List Instr) : SegRefines Γ (a ++ q) (b ++ q) := by
  intro H s f rs r hf hr
  rw [exec_append] at hr ⊢
  split at hr
  · rename_i s' f' rs' he
    rw [h s f rs _ hf he]
    exact hr
  · cases hr

/-! ## The small-step reading -/

/-- **A run of one side is a run of the other**: if `exec` runs `a`, the code `b` has a
run of silmaril-lean's small-step semantics to the same configuration. -/
theorem SegRefines.steps {Γ : List IntType} {a b : List Instr} (h : SegRefines Γ a b)
    {H : Type} {P : Profile} {host : HostSemantics H} {s s' : Store H} {f f' : Frame}
    {rs rs' : List Val} (rest : List Admin) (hf : FrameOk Γ f)
    (ha : exec s f rs a = some (s', f', rs')) :
    Steps P host ⟨s, f, vals rs.reverse ++ expression b ++ rest⟩
      ⟨s', f', vals rs'.reverse ++ rest⟩ :=
  exec_sound rest (h s f rs _ hf ha)

/-- `SegRefines.steps` for equivalent segments. -/
theorem SegEquiv.steps {Γ : List IntType} {a b : List Instr} (h : SegEquiv Γ a b)
    {H : Type} {P : Profile} {host : HostSemantics H} {s s' : Store H} {f f' : Frame}
    {rs rs' : List Val} (rest : List Admin) (hf : FrameOk Γ f)
    (ha : exec s f rs a = some (s', f', rs')) :
    Steps P host ⟨s, f, vals rs.reverse ++ expression b ++ rest⟩
      ⟨s', f', vals rs'.reverse ++ rest⟩ :=
  SegRefines.steps (SegEquiv.refines h) rest hf ha

/-! ## Results used by `Silmaril.Wasm.Auto2` -/

section
-- A lemma of `Silmaril.Proofs.Wasm.Auto.EGraph` that the proofs of `Silmaril.Wasm.Auto2` use.

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.EGraph
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core

theorem asInt_eq_some {t : IntType} {v : Val} {x : BitVec t.width} (h : asInt t v = some x) :
    v = intVal t x :=
  Silmaril.Proofs.Wasm.Auto.EGraph.asInt_eq_some h

end

end Silmaril.Wasm.Auto.EGraph
