module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8MonoEnv

/-!
# What monotonicity moves across the 2.0 `$utf8` erratum

The fuel-free consequences of `extMonoAt` and `extMonoTypAt`, for any `EnvExt e₁ e₂ x₀`:

* values, arguments and iteration domains (`evalExp_ext`, `evalArgs_ext`, `evalDoms_ext`);
* typing (`hasTyp_ext`, `typedV_ext`, `quantsOk_ext`);
* **positive derivations** (`dderivesB_ext`): a `DDerivesB` derivation in `e₁` is one in `e₂`,
  for any two readings `O ≤ O'` of `otherwise`;
* **steps, given `otherwise`** (`sstepB_ext`): a step `SStepB e₁ c c'` is a step `SStepB e₂ c c'`
  when every `otherwise` premise of `e₁` holds in `e₂` (`ElseMono e₁ e₂`). Monotonicity gives no
  more: `otherwiseB e₂` is a negative premise (no earlier rule fires in `e₂`), and `e₂` derives
  at least what `e₁` derives.

The 2.0 instances, at primitives `B` that leave `$utf8` uninterpreted (`storeB_utf8`):

* `typedV_utf8_20`, `typedV_utf8_20T`: typing in `simEnv20 B` (`simEnv20T B`) holds in
  `utf8Env20 B` (`utf8Env20T B`);
* **`good20BU_of_good20B`**: every `Good20B` configuration is `Good20BU`;
* **`typed20U_of_good20B`**: the image of a `Good20B` configuration is a `config` of
  `utf8Env20T (storeB P)`;
* **`fwd_good20B_utf8T`**: every V2 step from a `Good20B` configuration is a step of
  `utf8Env20T (storeB P)` between the images, given `ElseMono (simEnv20T (storeB P))
  (utf8Env20T (storeB P))`; its successor is `Good20B`, hence `Good20BU`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Mono

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim (TypedV QuantsOk ElseI noElse stateT EvalDoms)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (DDerivesB DPremB SStepB otherwiseB)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (utf8Env20 Good20B fwd_good20B good20B_steps
  typed20T_of_good20B)

/-! ## Generic consequences -/

section Generic

variable {e₁ e₂ : Env} {x₀ : IL.Id}

theorem evalExp_ext (hS : EnvExt e₁ e₂ x₀) {ρ : VarEnv} {e : Exp} {v : Value}
    (h : EvalExp e₁ ρ e v) : EvalExp e₂ ρ e v := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, (Res.Le.eq_of_ne_oof ((extMonoAt hS n).exp ρ e) (by rw [hn]; simp)).trans hn⟩

theorem evalArgs_ext (hS : EnvExt e₁ e₂ x₀) {ρ : VarEnv} {as₀ : List Arg} {ws : List ArgV}
    (h : EvalArgs e₁ ρ as₀ ws) : EvalArgs e₂ ρ as₀ ws := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, (Res.Le.eq_of_ne_oof ((extMonoAt hS n).args ρ as₀) (by rw [hn]; simp)).trans hn⟩

theorem evalDoms_ext (hS : EnvExt e₁ e₂ x₀) {ρ : VarEnv} {ds : List Dom}
    {xvs : List (IL.Id × Value)} (h : EvalDoms e₁ ρ ds xvs) : EvalDoms e₂ ρ ds xvs := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, (Res.Le.eq_of_ne_oof ((extMonoAt hS n).doms ρ ds) (by rw [hn]; simp)).trans hn⟩

theorem hasTyp_ext (hS : EnvExt e₁ e₂ x₀) {ρ : VarEnv} {t : Typ} {v : Value}
    (h : HasTyp e₁ ρ t v) : HasTyp e₂ ρ t v := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, (Res.Le.eq_of_ne_oof ((extMonoTypAt hS n).typ ρ t v) (by rw [hn]; simp)).trans hn⟩

theorem typedV_ext (hS : EnvExt e₁ e₂ x₀) {t : Typ} {v : Value} (h : TypedV e₁ t v) :
    TypedV e₂ t v :=
  fun ρ hρ => hasTyp_ext hS (h ρ hρ)

theorem quantsOk_ext (hS : EnvExt e₁ e₂ x₀) {ρ : VarEnv} {qs : List Param}
    (h : QuantsOk e₁ ρ qs) : QuantsOk e₂ ρ qs := fun x t hx => by
  obtain ⟨w, hw, ht⟩ := h x t hx
  exact ⟨w, hw, hasTyp_ext hS ht⟩

mutual
/-- **Positive derivations move from `e₁` to `e₂`**, along any inclusion of the readings of
`otherwise`. -/
theorem dderivesB_ext (hS : EnvExt e₁ e₂ x₀) {O O' : ElseI}
    (hO : ∀ x args i v, O x args i v → O' x args i v) :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value},
      DDerivesB e₁ O x op args v → DDerivesB e₂ O' x op args v
  | _, _, _, _, .rule hrel hrule halt hps hq he hp =>
      .rule (by rw [hS.rels]; exact hrel) hrule halt hps (quantsOk_ext hS hq)
        (evalExp_ext hS he) fun pr hpr => dpremB_ext hS hO (hO _ _ _ _) (hp pr hpr)

/-- `dderivesB_ext` for premises. -/
theorem dpremB_ext (hS : EnvExt e₁ e₂ x₀) {O O' : ElseI}
    (hO : ∀ x args i v, O x args i v → O' x args i v) {els els' : Prop} (hels : els → els') :
    ∀ {ρ : VarEnv} {pr : Prem}, DPremB e₁ O els ρ pr → DPremB e₂ O' els' ρ pr
  | _, _, .ifPr h => .ifPr (evalExp_ext hS h)
  | _, _, .elsePr h => .elsePr (hels h)
  | _, _, .letPr h₂ h₁ => .letPr (evalExp_ext hS h₂) (evalExp_ext hS h₁)
  | _, _, .rulePr ha he hd =>
      .rulePr (evalArgs_ext hS ha) (evalExp_ext hS he) (dderivesB_ext hS hO hd)
  | _, _, .iterOptNone hd hne hall => .iterOptNone (evalDoms_ext hS hd) hne hall
  | _, _, .iterOptSome hd hne hs hp =>
      .iterOptSome (evalDoms_ext hS hd) hne hs (dpremB_ext hS hO hels hp)
  | _, _, .iterList hit hd hne hl hk hp =>
      .iterList hit (evalDoms_ext hS hd) hne hl hk fun r hr =>
        dpremB_ext hS hO hels (hp r hr)
  | _, _, .iterListN hd he hk hl hlen hp =>
      .iterListN (evalDoms_ext hS hd) (evalExp_ext hS he) hk hl hlen fun r hr =>
        dpremB_ext hS hO hels (hp r hr)
end

/-- Derivations without `otherwise` move from `e₁` to `e₂`. -/
theorem dderivesB_noElse_ext (hS : EnvExt e₁ e₂ x₀) {x : IL.Id} {op : MixopS}
    {args : List ArgV} {v : Value} (h : DDerivesB e₁ noElse x op args v) :
    DDerivesB e₂ noElse x op args v :=
  dderivesB_ext hS (fun _ _ _ _ h => h) h

/-- Every `otherwise` premise of `e₁` holds in `e₂`. -/
def ElseMono (e₁ e₂ : Env) : Prop :=
  ∀ x args i v, otherwiseB e₁ x args i v → otherwiseB e₂ x args i v

/-- **A step moves from `e₁` to `e₂` when its `otherwise` premises do.** -/
theorem sstepB_ext (hS : EnvExt e₁ e₂ x₀) (hO : ElseMono e₁ e₂) {c c' : Value}
    (h : SStepB e₁ c c') : SStepB e₂ c c' :=
  dderivesB_ext hS hO h

end Generic

/-! ## The 2.0 instances -/

variable {B : Builtins}

theorem typedV_utf8_20 (hB : ∀ ws, B.call "utf8" ws = none) {t : Typ} {v : Value}
    (h : TypedV (simEnv20 B) t v) : TypedV (utf8Env20 B) t v :=
  typedV_ext (envExt20 B hB) h

theorem typedV_utf8_20T (hB : ∀ ws, B.call "utf8" ws = none) {t : Typ} {v : Value}
    (h : TypedV (simEnv20T B) t v) : TypedV (utf8Env20T B) t v :=
  typedV_ext (envExt20T B hB) h

theorem hasTyp_utf8_20T (hB : ∀ ws, B.call "utf8" ws = none) {ρ : VarEnv} {t : Typ} {v : Value}
    (h : HasTyp (simEnv20T B) ρ t v) : HasTyp (utf8Env20T B) ρ t v :=
  hasTyp_ext (envExt20T B hB) h

variable {H : Type} {hn : H → String}

/-- `TypF` gives `TypFU`. -/
theorem typFU_of_typF (hB : ∀ ws, B.call "utf8" ws = none) {c : Config H}
    (h : StoreFn.TypF B hn c) : TypFU B hn c :=
  ⟨typedV_utf8_20 hB h.state, typedV_utf8_20 hB h.code⟩

/-- **Every `Good20B` configuration is `Good20BU`.** -/
theorem good20BU_of_good20B {P : Profile} {c : Config H} (hg : Good20B hn P c) :
    Good20BU hn P c :=
  ⟨typFU_of_typF (storeB_utf8 P) hg.typ, hg.plain, hg.ok, hg.store, hg.small⟩

/-- **The image of a `Good20B` configuration is a `config` of `utf8Env20T (storeB P)`.** -/
theorem typed20U_of_good20B {P : Profile} {c : Config H} (hg : Good20B hn P c) :
    Typed20 (utf8Env20T (Whole.storeB P)) hn c :=
  hasTyp_utf8_20T (storeB_utf8 P) (typed20T_of_good20B hg)

/-- **The forward theorem in `utf8Env20T`, from `Good20B`, given `otherwise`.** Every V2 step from
a `Good20B` configuration is a step of `utf8Env20T (storeB P)` between the images when the
`otherwise` premises of `simEnv20T (storeB P)` hold in `utf8Env20T (storeB P)`; the successor is
`Good20B`, hence `Good20BU`. -/
theorem fwd_good20B_utf8T {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (hO : ElseMono (simEnv20T (Whole.storeB P)) (utf8Env20T (Whole.storeB P)))
    (hg : Good20B hn P c) (h : Step P host c c') :
    Good20B hn P c' ∧ Good20BU hn P c' ∧
      SStepB (utf8Env20T (Whole.storeB P)) (configV hn c) (configV hn c') := by
  obtain ⟨hg', hs⟩ := fwd_good20B hg h
  exact ⟨hg', good20BU_of_good20B hg', sstepB_ext (envExt20T _ (storeB_utf8 P)) hO hs⟩

/-- Runs, under the same condition. -/
theorem runU_good20B {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (hO : ElseMono (simEnv20T (Whole.storeB P)) (utf8Env20T (Whole.storeB P)))
    (h : Steps P host c c') (hg : Good20B hn P c) :
    Relation.ReflTransGen (SStepB (utf8Env20T (Whole.storeB P))) (configV hn c)
      (configV hn c') := by
  induction h with
  | refl => exact .refl
  | tail h₁ h₂ ih => exact .tail ih (fwd_good20B_utf8T hO (good20B_steps h₁ hg) h₂).2.2

end Silmaril.Wasm.SpecTec.Sim20.Utf8Mono
