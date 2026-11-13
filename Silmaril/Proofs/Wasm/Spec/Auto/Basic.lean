module

public import Silmaril.Wasm.Spec.Auto.Defs

@[expose] public section

/-!
# Automation: soundness of reductions, and the `wasm_spec` simp set

* `neverCallFrom_of_neverCall`: "never called" implies "never called while `e` is active";
* `ModReduces.sound`, **`Reduces.sound`**: every reduction is sound (`t'` holds ⟹ `t` holds),
  the harness step by `wasm_harness_iff`; `ModReduces.reduce`, `Reduces.reduce`,
  **`Task.reduce_sound`**: the normaliser is a reduction;
* `@[wasm_spec]` lemmas: satisfaction of the simple logics at a program as trace conditions
  (`models_neverCall_iff`, …), and the temporal images of simple sentences back to the simple
  logics (`models_ltlMax_neverCall_iff`, …, from the logic maps of `Silmaril.Wasm.Spec.Embed`).
-/

namespace Silmaril.Wasm.Spec.Auto

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {Ty A R : Type}

/-! ## Reductions -/

/-- "Never called" implies "never called while `e` is active". -/
theorem neverCallFrom_of_neverCall {S : Semantics Ty A R} {X : Iface Ty} {p : S.Prog X}
    {i : X.Imp} (h : Models (neverCall Ty A R) S p i) (e : X.Exp) :
    Models (neverCallFrom Ty A R) S p (i, e) := by
  rw [models_iff] at h ⊢
  intro t ht hpre ev r hdec a hev
  have hmem : Event.icall i a ∈ t := by
    rw [hdec, ← hev]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  exact absurd hmem (h t ht a)

/-- Module-property reductions are sound. -/
theorem ModReduces.sound {P : Profile} {X : WIface} {p : WasmProg X} :
    ∀ {φ φ' : ModProp X}, ModReduces φ φ' → φ'.Satisfies P p → φ.Satisfies P p
  | _, _, .refl _, h => h
  | _, _, .ncf _ e, h => neverCallFrom_of_neverCall h e
  | _, _, .and h₁ h₂, ⟨k₁, k₂⟩ => ⟨h₁.sound k₁, h₂.sound k₂⟩

/-- **Every reduction of tasks is sound.** -/
theorem Reduces.sound : ∀ {t t' : Task}, Reduces t t' → t'.Holds → t.Holds
  | _, _, .module _ _ h, k => h.sound k
  | _, _, .harness _ p H hQ hpl hol hph hinj, k => (wasm_harness_iff H hQ hpl hol hph hinj p).1 k
  | _, _, .trans h₁ h₂, k => h₁.sound (h₂.sound k)

/-- The normaliser of module properties is a reduction. -/
theorem ModReduces.reduce {X : WIface} : ∀ φ : ModProp X, ModReduces φ φ.reduce
  | .neverCallFrom i e => .ncf i e
  | .and φ ψ => .and (ModReduces.reduce φ) (ModReduces.reduce ψ)
  | .neverCall _ => .refl _
  | .assertNeverFalse _ => .refl _
  | .callPre _ _ => .refl _
  | .retPost _ _ => .refl _
  | .hist _ => .refl _
  | .terminates _ => .refl _
  | .ltl _ => .refl _
  | .ctl _ => .refl _
  | .tla _ => .refl _

/-- The normaliser of tasks is a reduction. -/
theorem Reduces.reduce : ∀ t : Task, Reduces t t.reduce ∨ t.reduce = t
  | .module P p φ => .inl (.module P p (ModReduces.reduce φ))
  | .component .. => .inr rfl
  | .joint .. => .inr rfl
  | .linked .. => .inr rfl

/-- **The normaliser is sound.** -/
theorem Task.reduce_sound (t : Task) (h : t.reduce.Holds) : t.Holds := by
  rcases Reduces.reduce t with hr | heq
  · exact hr.sound h
  · exact heq ▸ h

/-! ## The `wasm_spec` simp set -/

@[wasm_spec] theorem models_neverCall_iff {S : Semantics Ty A R} {X : Iface Ty} (p : S.Prog X)
    (i : X.Imp) : Models (neverCall Ty A R) S p i ↔ ∀ t ∈ S.traces p, ∀ a, Event.icall i a ∉ t :=
  models_iff _ _ _ _

@[wasm_spec] theorem models_callPre_iff {S : Semantics Ty A R} {X : Iface Ty} (p : S.Prog X)
    (φ : CallPre.Fm A X) :
    Models (callPre Ty A R) S p φ ↔ ∀ t ∈ S.traces p, ∀ a, Event.icall φ.imp a ∈ t → φ.pre a :=
  models_iff _ _ _ _

@[wasm_spec] theorem models_retPost_iff {S : Semantics Ty A R} {X : Iface Ty} (p : S.Prog X)
    (φ : RetPost.Fm R X) :
    Models (retPost Ty A R) S p φ ↔ ∀ t ∈ S.traces p, ∀ r, Event.ret φ.exp r ∈ t → φ.post r :=
  models_iff _ _ _ _

@[wasm_spec] theorem models_neverCallFrom_iff {S : Semantics Ty A R} {X : Iface Ty}
    (p : S.Prog X) (φ : X.Imp × X.Exp) :
    Models (neverCallFrom Ty A R) S p φ ↔ ∀ t ∈ S.traces p,
      EveryPos (fun h ev => ∀ a, ev = Event.icall φ.1 a → activeExport h ≠ some φ.2) t :=
  models_iff _ _ _ _

@[wasm_spec] theorem models_assertNeverFalse_iff {R : Type} {S : Semantics Ty (List Val) R}
    {X : Iface Ty} (p : S.Prog X) (i : X.Imp) :
    Models (assertNeverFalse Ty R) S p i ↔
      ∀ t ∈ S.traces p, ∀ a, Event.icall i a ∈ t → a.head? ≠ some (Val.i32 0) :=
  models_iff _ _ _ _

@[wasm_spec] theorem models_exportHist_iff {S : Semantics Ty A R} {X : Iface Ty} (p : S.Prog X)
    (Φ : Multi.Hist A R X → Prop) :
    Models (Multi.exportHist Ty A R) S p Φ ↔ ∀ t ∈ S.traces p, Φ (exportEvents t) :=
  models_iff _ _ _ _

@[wasm_spec] theorem models_act_iff {S : Semantics Ty A R} {X : Iface Ty} (p : S.Prog X)
    (q : PosPred A R X) : Models (act Ty A R) S p q ↔ ∀ t ∈ S.traces p, EveryPos q t :=
  models_iff _ _ _ _

/-- `□ (no call of i)` over maximal behaviours is "never called". -/
@[wasm_spec] theorem models_ltlMax_neverCall_iff {S : Semantics Ty A R} {X : Iface Ty}
    (p : S.Prog X) (i : X.Imp) :
    Models (ltlMax Ty A R) S p (LTL.alw (LTL.atom fun _ e => ∀ a, e ≠ Event.icall i a)) ↔
      Models (neverCall Ty A R) S p i :=
  ((NeverCall.toAct Ty A R).comp (Act.toLtlMax Ty A R)).models_iff S p i

/-- `□ (no call of i)` on finite traces is "never called". -/
@[wasm_spec] theorem models_ltlFin_neverCall_iff {S : Semantics Ty A R} {X : Iface Ty}
    (p : S.Prog X) (i : X.Imp) :
    Models (ltlFin Ty A R) S p (LTL.alw (LTL.atom fun _ e => ∀ a, e ≠ Event.icall i a)) ↔
      Models (neverCall Ty A R) S p i :=
  ((NeverCall.toAct Ty A R).comp (Act.toLtlFin Ty A R)).models_iff S p i

/-- `□[no call of i]` in TLA is "never called". -/
@[wasm_spec] theorem models_tla_neverCall_iff {S : Semantics Ty A R} {X : Iface Ty}
    (p : S.Prog X) (i : X.Imp) :
    Models (tla Ty A R) S p (TLA.box fun _ e => ∀ a, e ≠ Event.icall i a) ↔
      Models (neverCall Ty A R) S p i :=
  ((NeverCall.toAct Ty A R).comp (Act.toTla Ty A R)).models_iff S p i

/-- `□ (every call of i passes)` over maximal behaviours is "assert never false". -/
@[wasm_spec] theorem models_ltlMax_assert_iff {R : Type} {S : Semantics Ty (List Val) R}
    {X : Iface Ty} (p : S.Prog X) (i : X.Imp) :
    Models (ltlMax Ty (List Val) R) S p
        (LTL.alw (LTL.atom fun _ e => ∀ a, e = Event.icall i a → assertOk a)) ↔
      Models (assertNeverFalse Ty R) S p i :=
  ((AssertNeverFalse.toAct Ty R).comp (Act.toLtlMax Ty (List Val) R)).models_iff S p i

/-- `□[every call of i passes]` in TLA is "assert never false". -/
@[wasm_spec] theorem models_tla_assert_iff {R : Type} {S : Semantics Ty (List Val) R}
    {X : Iface Ty} (p : S.Prog X) (i : X.Imp) :
    Models (tla Ty (List Val) R) S p (TLA.box fun _ e => ∀ a, e = Event.icall i a → assertOk a) ↔
      Models (assertNeverFalse Ty R) S p i :=
  ((AssertNeverFalse.toAct Ty R).comp (Act.toTla Ty (List Val) R)).models_iff S p i

end Silmaril.Wasm.Spec.Auto
