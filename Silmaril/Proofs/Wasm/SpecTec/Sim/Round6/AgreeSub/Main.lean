module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeSub.Def
public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.Thms

/-!
# Round 6: `AgreeTy.subIntro` from `Sem`'s normal form

`Sem` (`RefOkV/Sem.lean`) reads `Heaptype_sub {}` between coherent types
as a normal form whose only middle types are abstract, plus chains along declared supertypes.
Every `Sem` fact between bounded types is derivable under `DDerivesB`, in
`simEnv (BI P hn host)`:

* `dderivesB_expand_abs`: a defined type is below every abstract type above its kind
  (`struct`/`array`/`func`, then the abstract order through the kind);
* `dderivesB_useAbs`, `dderivesB_absUse`: `UseAbs`, and abstract bottoms below defined types;
* `dderivesB_of_sem`: **`Sem a b` gives `Heaptype_sub` at the images**;
* `dderivesB_reftypeSub`: `Reftype_sub` from `Heaptype_sub`, at every pair of nullabilities
  allowed (`nonnull`, `null`);
* `subIntro`: **`AgreeTy.subIntro`**: Core's `Sub {}` between bounded, Core-valid reference types
  gives SpecTec's `Reftype_sub {}` (through `subS_empty`, `semK_of_subS` and `cohH_of_tyOk`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV absV nullV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core (HostSemantics)
open Silmaril.Wasm.Numerics (Profile)
open Round6.Reading
open Round6.RefOkV (Sem UseAbs)
open Round4Int (BI)
open Round4 (tyBnd)

variable {B : Builtins} {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **A defined type is below every abstract type above its kind.** -/
theorem dderivesB_expand_abs (O : ElseI) {c : Value} (hc : CtxT (BI P hn host) c) {d : DefType}
    {ct : CCompType} {b : AbsHeapType} (hd : tyBnd d = true) (h : Expand d ct)
    (hb : absSub (compAbs ct) b = true) : HSub (BI P hn host) O c (tyV d) (absV b) := by
  have hk : HSub (BI P hn host) O c (tyV d) (absV (compAbs ct)) := by
    cases ct with
    | struct fs => exact dderivesB_defStruct O hc hd h
    | array f => exact dderivesB_defArray O hc hd h
    | func ps rs => exact dderivesB_defFunc O hc hd h
  exact dderivesB_transAbs O (compAbs ct) hc (heapT_def hd) (heapT_abs b) hk
    (dderivesB_absSub O hc _ _ hb)

/-- **`UseAbs`**: a type use whose kind is below `b` is below `b`. -/
theorem dderivesB_useAbs (O : ElseI) {c : Value} (hc : CtxT (BI P hn host) c) {u : CTypeUse}
    {b : AbsHeapType} (hu : tyBnd u = true) (h : UseAbs u b) :
    HSub (BI P hn host) O c (tyV u) (absV b) := by
  obtain ⟨d, k, rfl, hk, hkb⟩ := h
  unfold defKind at hk
  cases hun : unrolldt d with
  | none => simp [hun] at hk
  | some st =>
    cases st with
    | sub fin sups ct =>
      simp only [hun, Option.map_some, Option.some.injEq, Ty.body] at hk
      subst hk
      exact dderivesB_expand_abs O hc hu ⟨hun⟩ hkb

/-- A defined type is not `BOT`. -/
theorem tyV_use_ne_bot {u : CTypeUse} {b : AbsHeapType} (h : UseAbs u b) :
    tyV u ≠ .case "BOT" (.tuple []) := by
  obtain ⟨d, k, rfl, -, -⟩ := h
  cases d
  simp [tyV]

/-- **An abstract bottom is below a defined type below its top.** -/
theorem dderivesB_absUse (O : ElseI) {c : Value} (hc : CtxT (BI P hn host) c) {a t : AbsHeapType}
    {u : CTypeUse} (hu : tyBnd u = true) (ht : botTop a = some t) (h : UseAbs u t) :
    HSub (BI P hn host) O c (absV a) (tyV u) := by
  have hs := dderivesB_useAbs O hc hu h
  have hT : HeapT (BI P hn host) (tyV u) := typedV_heaptype (h := .use u) hu
  cases a <;> simp [botTop] at ht <;> subst ht
  · exact dderivesB_botRule O hc hT ruleAt_none (tyV_use_ne_bot h) hs
  · exact dderivesB_botRule O hc hT ruleAt_nofunc (tyV_use_ne_bot h) hs
  · exact dderivesB_botRule O hc hT ruleAt_noexn (tyV_use_ne_bot h) hs
  · exact dderivesB_botRule O hc hT ruleAt_noextern (tyV_use_ne_bot h) hs

/-- Two type uses related by `Sem`. -/
theorem dderivesB_useUse (O : ElseI) {c : Value} (hc : CtxT (BI P hn host) c) {u₁ u₂ : CTypeUse}
    (hb₁ : tyBnd u₁ = true) (hb₂ : tyBnd u₂ = true) (h : Sem (.use u₁) (.use u₂)) :
    HSub (BI P hn host) O c (tyV u₁) (tyV u₂) := by
  rcases (h : _ ∨ _) with rfl | ⟨d₁, d₂, rfl, rfl, hr⟩
  · exact dderivesB_refl O hc (typedV_heaptype (h := .use u₁) hb₁)
  · exact dderivesB_reach O hc hr hb₂ hb₁

/-- **`Sem` is derivable**: `Sem a b` between bounded heap types gives `Heaptype_sub` at their
images, in every typed context. -/
theorem dderivesB_of_sem (O : ElseI) {c : Value} (hc : CtxT (BI P hn host) c) :
    ∀ {a b : CHeapType}, tyBnd a = true → tyBnd b = true → Sem a b →
      HSub (BI P hn host) O c (tyV a) (tyV b)
  | .bot, _, _, hb, _ => dderivesB_heaptypeSub_bot O hc (typedV_heaptype hb)
  | .abs _, .abs _, _, _, h => dderivesB_absSub O hc _ _ h
  | .abs _, .use _, _, hb, h => by
    obtain ⟨t, ht, hu⟩ := h
    exact dderivesB_absUse O hc hb ht hu
  | .use _, .abs _, ha, _, h => dderivesB_useAbs O hc ha h
  | .use _, .use _, ha, hb, h => dderivesB_useUse O hc ha hb h
  | .abs _, .bot, _, _, h => h.elim
  | .use _, .bot, _, _, h => h.elim

/-- **`Reftype_sub/nonnull`**, from `Heaptype_sub`. -/
theorem dderivesB_nonnull (O : ElseI) {c h₁ h₂ : Value} (hc : CtxT B c) (hh₁ : HeapT B h₁)
    (hh₂ : HeapT B h₂) (hd : HSub B O c h₁ h₂) :
    DDerivesB (simEnv B) O "Reftype_sub" "%|-%<:%" []
      (.tuple [c, .case "REF" (.tuple [nullV false, h₁]), .case "REF" (.tuple [nullV false, h₂])]) :=
  dderivesB_of_ruleAt ruleAt_nonnull (self_mem_conclAlts _) [("C", c), ("ht_1", h₁), ("ht_2", h₂)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (hh₁ _ (valsOnly_bind _))
      (QuantsOk.cons rfl (hh₂ _ (valsOnly_bind _)) QuantsOk.nil)))
    (evalExp_tup3 (evalExp_var rfl)
      (evalExp_case (evalExp_tup2 (evalExp_optE_none_iff.2 rfl) (evalExp_var rfl)))
      (evalExp_case (evalExp_tup2 (evalExp_optE_none_iff.2 rfl) (evalExp_var rfl))))
    (premsB_one (.rulePr (evalArgs_nil _ _)
      (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl)) hd))

/-- **`Reftype_sub`** at the images of two bounded reference types, from `Heaptype_sub` between
their heap types, when the nullabilities allow it. -/
theorem dderivesB_reftypeSub (O : ElseI) {c : Value} (hc : CtxT B c) {n₁ n₂ : Bool}
    {h₁ h₂ : CHeapType} (hb₁ : tyBnd h₁ = true) (hb₂ : tyBnd h₂ = true)
    (hn : n₁ = true → n₂ = true) (hd : HSub B O c (tyV h₁) (tyV h₂)) :
    DDerivesB (simEnv B) O "Reftype_sub" "%|-%<:%" []
      (.tuple [c, tyV (Ty.ref n₁ h₁ : CRefType), tyV (Ty.ref n₂ h₂ : CRefType)]) := by
  cases n₂ with
  | true =>
    exact dderivesB_reftypeSub_null O hc (typedV_heaptype hb₁) (typedV_heaptype hb₂) n₁ hd
  | false =>
    cases n₁ with
    | true => exact absurd (hn rfl) nofun
    | false => exact dderivesB_nonnull O hc (typedV_heaptype hb₁) (typedV_heaptype hb₂) hd

/-- **`AgreeTy.subIntro`, proved**: in `simEnv (BI P hn host)` (every profile, so in particular
`Profile.spec nd r`), Core's `Sub {}` between bounded, Core-valid reference types gives SpecTec's
`Reftype_sub {}` under `DDerivesB`, under every reading of `otherwise`. -/
theorem subIntro (O : ElseI) (p rt : CRefType) (hbp : tyBnd p = true) (hbr : tyBnd rt = true)
    (hp : TyOk {} p) (hr : TyOk {} rt) (hs : Sub {} p rt) :
    DDerivesB (simEnv (BI P hn host)) O "Reftype_sub" "%|-%<:%" []
      (.tuple [RefOkV.ctxEmptyV, tyV p, tyV rt]) := by
  cases p with
  | ref n₁ h₁ =>
    cases rt with
    | ref n₂ h₂ =>
      have hc₁ : RefOkV.CohH h₁ := by cases hp with | ref hh => exact RefOkV.cohH_of_tyOk hh
      have hc₂ : RefOkV.CohH h₂ := by cases hr with | ref hh => exact RefOkV.cohH_of_tyOk hh
      obtain ⟨hn, hsem⟩ := RefOkV.semK_of_subS (RefOkV.subS_empty hs) rfl
      exact dderivesB_reftypeSub O typedV_ctx0 hbp hbr hn
        (dderivesB_of_sem O typedV_ctx0 hbp hbr (hsem hc₁ hc₂))

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub
