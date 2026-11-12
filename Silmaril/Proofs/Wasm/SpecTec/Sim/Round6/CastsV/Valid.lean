module

public import Silmaril.Wasm.SpecTec.Sim.Round6.CastsV.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Thms

/-!
# Round 6: the validity of cast types, from `ConfigOk`

* `castsInv_of_configOk`: in a valid configuration, the store is valid and every top-level cast
  (under labels, handlers and frames) has an instantiated type valid in `{}`. Typing gives
  `TyOk C (C.closeRef rt)` at each cast (`tyOk_castTy`); the context's types are the frame
  module's and are valid in `{}` (`FrameOk.types_eq`, `FrameOk.typesOkEmptyCast`), so
  `closeRef_okEmptyCast` closes it. Labels, `initLocals` and `RETURN` keep the types; a frame
  instruction brings its own `FrameOk`.
* `castsInv_closed`: `CastsInv` is closed under SpecTec's context decompositions
  (`Target.CtxClosedVals`), and `castsInv_of_configEq`: it transfers along `ConfigEq`, since a
  `CALL_REF` is not a cast.
* `castRefOk_of_refOkBV`: `RefOkBV` gives `CastRefOk` at every predicate that implies `CastsInv`
  and a bounded frame module (`ModuleBnd`, for `tyBnd` of the instantiated type).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.CastsV

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open _root_.Silmaril.Wasm.SpecTec.Sim.Bwd (AdminEq CodeEq ConfigEq)

variable {H : Type}

/-! ## `CastsOkL` -/

@[simp] theorem castsOkL_nil (M : ModuleInst) : CastsOkL M [] := by simp [CastsOkL]

@[simp] theorem castsOkL_cons {M : ModuleInst} {a : Admin} {l : List Admin} :
    CastsOkL M (a :: l) ↔ CastsOkA M a ∧ CastsOkL M l := by simp [CastsOkL]

/-- `CastsOkL` along an append. -/
theorem castsOkL_append {M : ModuleInst} : ∀ {a b : List Admin},
    CastsOkL M (a ++ b) ↔ CastsOkL M a ∧ CastsOkL M b
  | [], _ => by simp
  | x :: a, b => by simp [castsOkL_append (a := a) (b := b), and_assoc]

@[simp] theorem castsOkA_label {M : ModuleInst} {n : Nat} {cont : List Instr} {b : List Admin} :
    CastsOkA M (.label n cont b) ↔ CastsOkL M b := by simp [CastsOkA]

@[simp] theorem castsOkA_handler {M : ModuleInst} {n : Nat} {cs : List Catch} {b : List Admin} :
    CastsOkA M (.handler n cs b) ↔ CastsOkL M b := by simp [CastsOkA]

@[simp] theorem castsOkA_frame {M : ModuleInst} {n : Nat} {fr : Frame} {b : List Admin} :
    CastsOkA M (.frame n fr b) ↔ CastsOkL fr.module b := by simp [CastsOkA]

/-- Values have no cast. -/
theorem castsOkL_vals (M : ModuleInst) : ∀ vs : List Val, CastsOkL M (vals vs)
  | [] => by simp [vals]
  | v :: vs => by
    refine castsOkL_cons.2 ⟨?_, castsOkL_vals M vs⟩
    rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [CastsOkA, Val.toAdmin, castTy?]

/-- A `CALL_REF` has no cast. -/
theorem castsOkA_of_isCallRef {M : ModuleInst} {a : Admin} (h : a.IsCallRef) : CastsOkA M a := by
  rcases Bwd.isCallRef_cases h with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;> simp [CastsOkA, castTy?]

/-- The cast at a cast pair. -/
theorem tyOk_of_castsOkL {M : ModuleInst} {r : Ref} {i : Instr} {rt : RefType}
    (h : CastsOkL M [.ref r, .plain i]) (hi : castTy? i = some rt) : TyOk {} (M.instRef rt) := by
  simp only [castsOkL_cons, CastsOkA] at h
  exact h.2.1 rt hi

/-! ## Along `ConfigEq` -/

mutual
/-- `CastsOkA` transfers along `AdminEq`. -/
theorem castsOkA_of_adminEq : ∀ {M : ModuleInst} {a b : Admin}, AdminEq a b → CastsOkA M a →
    CastsOkA M b
  | _, _, _, .refl _, h => h
  | _, _, _, .call _ hb, _ => castsOkA_of_isCallRef hb
  | _, _, _, .label he, h => castsOkA_label.2 (castsOkL_of_codeEq he (castsOkA_label.1 h))
  | _, _, _, .handler he, h => castsOkA_handler.2 (castsOkL_of_codeEq he (castsOkA_handler.1 h))
  | _, _, _, .frame he, h => castsOkA_frame.2 (castsOkL_of_codeEq he (castsOkA_frame.1 h))

/-- `CastsOkL` transfers along `CodeEq`. -/
theorem castsOkL_of_codeEq : ∀ {M : ModuleInst} {l k : List Admin}, CodeEq l k → CastsOkL M l →
    CastsOkL M k
  | _, _, _, .nil, h => h
  | _, _, _, .cons ha hl, h =>
    castsOkL_cons.2 ⟨castsOkA_of_adminEq ha (castsOkL_cons.1 h).1,
      castsOkL_of_codeEq hl (castsOkL_cons.1 h).2⟩
end

/-- **`CastsInv` transfers along `ConfigEq`.** -/
theorem castsInv_of_configEq {c d : Config H} (he : ConfigEq c d) (h : CastsInv c) :
    CastsInv d := by
  obtain ⟨hs, hf, hc⟩ := he
  exact ⟨hs ▸ h.1, hf ▸ castsOkL_of_codeEq hc h.2⟩

/-! ## Closure under SpecTec's context decompositions -/

/-- **`CastsInv` is closed under SpecTec's context decompositions.** -/
theorem castsInv_closed : Target.CtxClosedVals (CastsInv (H := H)) where
  mid _ _ _ _ _ h := ⟨h.1, (castsOkL_append.1 (castsOkL_append.1 h.2).1).2⟩
  label _ _ _ _ _ h := ⟨h.1, castsOkA_label.1 (castsOkL_cons.1 h.2).1⟩
  handler _ _ _ _ _ h := ⟨h.1, castsOkA_handler.1 (castsOkL_cons.1 h.2).1⟩
  frame _ _ _ _ _ h := ⟨h.1, castsOkA_frame.1 (castsOkL_cons.1 h.2).1⟩

/-! ## From `ConfigOk` -/

/-- **A typed cast has a type valid in its context.** -/
theorem tyOk_castTy {C : Context} {i : Instr} {it : InstrType} {rt : RefType}
    (h : InstrOk C i it) (hi : castTy? i = some rt) : TyOk C.toTypeCtx (C.closeRef rt) := by
  cases h with
  | reference h =>
    cases h <;> simp only [castTy?, reduceCtorEq, Option.some.injEq] at hi
    all_goals (subst hi; assumption)
  | brOnCast _ _ h₂ =>
    simp only [castTy?, Option.some.injEq] at hi
    exact hi ▸ h₂
  | brOnCastFail _ _ h₂ =>
    simp only [castTy?, Option.some.injEq] at hi
    exact hi ▸ h₂
  | parametric h => cases h <;> simp [castTy?] at hi
  | numeric h => cases h <;> simp [castTy?] at hi
  | vector h => cases h <;> simp [castTy?] at hi
  | «variable» h => cases h <;> simp [castTy?] at hi
  | memory h => cases h <;> simp [castTy?] at hi
  | table h => cases h <;> simp [castTy?] at hi
  | _ => simp [castTy?] at hi

/-- The context types are those of a module whose types are valid in `{}`. -/
def TypesFit (C : Context) (M : ModuleInst) : Prop :=
  C.types = M.types ∧ ∀ d ∈ C.types, TyOk {} d

/-- `TypesFit` survives `initLocals`. -/
theorem TypesFit.initLocals {C : Context} {M : ModuleInst} (h : TypesFit C M) (xs : List Nat) :
    TypesFit (C.initLocals xs) M := by
  have e : (C.initLocals xs).types = C.types :=
    congrArg TypeCtx.types (Context.initLocals_toTypeCtx C xs)
  exact ⟨e.trans h.1, e ▸ h.2⟩

/-- A typed plain instruction has `CastsOkA`, in a fitting context. -/
theorem castsOkA_plain {C : Context} {M : ModuleInst} {i : Instr} {it : InstrType}
    (hT : TypesFit C M) (h : InstrOk C i it) : CastsOkA M (.plain i) := by
  intro rt hi
  have hc : C.closeRef rt = M.instRef rt := by
    simp [Context.closeRef, ModuleInst.instRef, hT.1]
  exact hc ▸ closeRef_okEmptyCast hT.2 (tyOk_castTy h hi)

/-- **Typed administrative code has `CastsOkL`, in a fitting context.** -/
theorem castsOkL_of_adminsOk {s : Store H} {C : Context} {code : List Admin} {it : InstrType}
    (h : AdminsOk s C code it) : ∀ M, TypesFit C M → CastsOkL M code := by
  refine AdminsOk.rec (motive_1 := fun C a _ _ => ∀ M, TypesFit C M → CastsOkA M a)
    (motive_2 := fun C l _ _ => ∀ M, TypesFit C M → CastsOkL M l)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  case refine_1 => intro _ _ _ h M hT; exact castsOkA_plain hT h
  case refine_2 => intros; simp [CastsOkA]
  case refine_3 => intros; simp [CastsOkA]
  case refine_4 => intros; simp [CastsOkA]
  case refine_5 =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ ihb M hT
    exact castsOkA_label.2 (ihb M hT)
  case refine_6 =>
    intro _ _ _ fr _ _ hf _ _ _ ihb _ _
    exact castsOkA_frame.2 (ihb fr.module ⟨hf.types_eq, hf.typesOkEmptyCast⟩)
  case refine_7 =>
    intro _ _ _ _ _ _ _ _ ihb M hT
    exact castsOkA_handler.2 (ihb M hT)
  case refine_8 => intros; simp [CastsOkA]
  case refine_9 => intros; simp [CastsOkA, castTy?]
  case refine_10 => intros; simp
  case refine_11 =>
    intro _ _ _ _ ih M hT
    exact castsOkL_cons.2 ⟨ih M hT, by simp⟩
  case refine_12 =>
    intro _ _ _ _ _ _ xs _ _ _ _ ih₁ ih₂ M hT
    exact castsOkL_append.2 ⟨ih₁ M hT, ih₂ M (hT.initLocals xs)⟩
  case refine_13 =>
    intro _ _ _ _ _ _ xs _ _ _ _ ih₁ ih₂ M hT
    exact castsOkL_cons.2 ⟨ih₁ M hT, ih₂ M (hT.initLocals xs)⟩
  case refine_14 => intro _ _ _ _ _ _ _ ih; exact ih
  case refine_15 => intro _ _ _ _ _ _ _ _ ih; exact ih

/-- **A valid configuration satisfies `CastsInv`.** -/
theorem castsInv_of_configOk {c : Config H} {ts : List CValType} (h : ConfigOk c ts) :
    CastsInv c := by
  obtain ⟨C, ⟨hs, hf⟩, hc⟩ := h
  exact ⟨hs, castsOkL_of_adminsOk hc _ ⟨hf.types_eq, hf.typesOkEmptyCast⟩⟩

/-! ## `CastRefOk` -/

/-- **`RefOkBV` gives `CastRefOk`** at every predicate that implies `CastsInv` and a bounded
frame module. -/
theorem castRefOk_of_refOkBV {env : Env} {hn : H → String} {V : Config H → Prop}
    (KV : RefOkB.RefOkBV env) (hM : ∀ c, V c → Round4.ModuleBnd c.frame.module)
    (hI : ∀ c, V c → CastsInv c) : CastRefOk env hn V where
  refOk s _ _ _ rt hi hv hs := KV.refOk hn s _ hs (hI _ hv).1
    (Round5.Fwd.tyBnd_instRef (hM _ hv) rt) (tyOk_of_castsOkL (hI _ hv).2 hi)

end Silmaril.Wasm.SpecTec.Sim.Round6.CastsV
