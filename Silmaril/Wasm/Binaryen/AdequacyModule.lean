module

public import Silmaril.Wasm.Binaryen.NativeProfileBridge
public import Silmaril.Wasm.Binaryen.AdequacyReduce
public import Silmaril.Wasm.Binaryen.Profile
public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc
public import Silmaril.Wasm.Behaviour.Refinement.Interpreter

@[expose] public section

/-! # Instantiated profile modules satisfy the adequacy hypotheses

`nbehModule_eq` (a separate interpreter-adequacy development (not included in this package)) applies `lower_adequate` at every
store an instantiation of a closed profile module can leave. This file supplies
the three hypotheses that needs:

* `ready_det`: instantiation followed by the start function is deterministic
  under the deterministic profile and the closed host. Initialisers and the start
  run reach value normal forms, which are unique (`eq_of_steps_of_nf`). So every
  `Ready` outcome is the one an `Ok` witness describes, and its `InvokeOk` applies.
* `ready_storeOk`: the resulting store is typed. This is `Instantiate.ok` for the
  always-diverging host `divHost`, which satisfies `HostOk` and contains the closed
  host, followed by preservation along the closed-host run (`closed_preserves`).
* `ready_funcs`: every function of the resulting store is profile Wasm code with a
  function type. Allocation creates the functions; the start run does not change
  them (`okAdmins_steps`).
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Numerics Validation

variable {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool}

/-! ## Determinism of instantiation -/

theorem steps_det_nf {c c₁ c₂ : Config H}
    (h₁ : Steps (Profile.deterministic o) closedHost c c₁)
    (h₂ : Steps (Profile.deterministic o) closedHost c c₂)
    (n₁ : ∀ x, ¬ Step (Profile.deterministic o) closedHost c₁ x)
    (n₂ : ∀ x, ¬ Step (Profile.deterministic o) closedHost c₂ x) : c₁ = c₂ :=
  SingleThreaded.Exec.BehaviourRefinement.eq_of_steps_of_nf (o := o) h₁ h₂ n₁ n₂

theorem not_step_vals' {s : Store H} {f : Frame} {W : List Val} {c : Config H} :
    ¬ Step (Profile.deterministic o) closedHost ⟨s, f, vals W⟩ c :=
  fun h => SingleThreaded.Det.not_step_vals (P := Profile.deterministic o) h

theorem evalExpr_det {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {e : Expr} {v₁ v₂ : List Val}
    (h₁ : EvalExpr (Profile.deterministic o) closedHost s f e s₁ f₁ v₁)
    (h₂ : EvalExpr (Profile.deterministic o) closedHost s f e s₂ f₂ v₂) :
    s₁ = s₂ ∧ f₁ = f₂ ∧ v₁ = v₂ := by
  have := steps_det_nf h₁ h₂ (fun _ => not_step_vals') (fun _ => not_step_vals')
  simp only [Config.mk.injEq, SingleThreaded.Det.vals_inj] at this
  exact this

theorem evalGlobals_det {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {gs : List CGlobalType}
    {es : List Expr} {vs₁ vs₂ : List Val}
    (h₁ : EvalGlobals (Profile.deterministic o) closedHost s f gs es s₁ f₁ vs₁)
    (h₂ : EvalGlobals (Profile.deterministic o) closedHost s f gs es s₂ f₂ vs₂) :
    s₁ = s₂ ∧ f₁ = f₂ ∧ vs₁ = vs₂ := by
  induction h₁ generalizing s₂ f₂ vs₂ with
  | nil => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | cons he _ ih =>
    cases h₂ with
    | cons he' hs' =>
      obtain ⟨rfl, rfl, h⟩ := evalExpr_det he he'
      simp only [List.cons.injEq, and_true] at h
      subst h
      obtain ⟨rfl, rfl, rfl⟩ := ih hs'
      exact ⟨rfl, rfl, rfl⟩

theorem evalExprs_det {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {es : List Expr}
    {rs₁ rs₂ : List Ref}
    (h₁ : EvalExprs (Profile.deterministic o) closedHost s f es s₁ f₁ rs₁)
    (h₂ : EvalExprs (Profile.deterministic o) closedHost s f es s₂ f₂ rs₂) :
    s₁ = s₂ ∧ f₁ = f₂ ∧ rs₁ = rs₂ := by
  induction h₁ generalizing s₂ f₂ rs₂ with
  | nil => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | cons he _ ih =>
    cases h₂ with
    | cons he' hs' =>
      obtain ⟨rfl, rfl, h⟩ := evalExpr_det he he'
      simp only [List.cons.injEq, and_true, Val.ref.injEq] at h
      subst h
      obtain ⟨rfl, rfl, rfl⟩ := ih hs'
      exact ⟨rfl, rfl, rfl⟩

theorem evalExprss_det {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {ess : List (List Expr)}
    {rss₁ rss₂ : List (List Ref)}
    (h₁ : EvalExprss (Profile.deterministic o) closedHost s f ess s₁ f₁ rss₁)
    (h₂ : EvalExprss (Profile.deterministic o) closedHost s f ess s₂ f₂ rss₂) :
    s₁ = s₂ ∧ f₁ = f₂ ∧ rss₁ = rss₂ := by
  induction h₁ generalizing s₂ f₂ rss₂ with
  | nil => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | cons he _ ih =>
    cases h₂ with
    | cons he' hs' =>
      obtain ⟨rfl, rfl, rfl⟩ := evalExprs_det he he'
      obtain ⟨rfl, rfl, rfl⟩ := ih hs'
      exact ⟨rfl, rfl, rfl⟩

/-- Instantiation under the deterministic profile and the closed host is a
function of the store, module and imports. -/
theorem instantiate_det {s : Store H} {M : Module} {xas : List ExternAddr} {c₁ c₂ : Config H}
    (h₁ : Instantiate (Profile.deterministic o) closedHost s M xas c₁)
    (h₂ : Instantiate (Profile.deterministic o) closedHost s M xas c₂) : c₁ = c₂ := by
  obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, vG, rT, rE, mi, hg, ht, he, ha, rfl⟩ := h₁.run
  obtain ⟨s₁', s₂', s₃', s₄', f₁', f₂', f₃', vG', rT', rE', mi', hg', ht', he', ha', rfl⟩ := h₂.run
  obtain ⟨rfl, rfl, rfl⟩ := evalGlobals_det hg hg'
  obtain ⟨rfl, rfl, rfl⟩ := evalExprs_det ht ht'
  obtain ⟨rfl, rfl, rfl⟩ := evalExprss_det he he'
  rw [ha] at ha'
  cases ha'
  rfl

/-- **Determinism of `Ready`**: instantiation and the start function leave a
unique store and module instance. -/
theorem ready_det {s : Store H} {M : Module} {xas : List ExternAddr} {s₁ s₂ : Store H}
    {mi₁ mi₂ : ModuleInst}
    (h₁ : Ready (Profile.deterministic o) closedHost s M xas s₁ mi₁)
    (h₂ : Ready (Profile.deterministic o) closedHost s M xas s₂ mi₂) : s₁ = s₂ ∧ mi₁ = mi₂ := by
  obtain ⟨c, c', hi, hst, hcode, rfl, rfl⟩ := h₁
  obtain ⟨d, d', hi', hst', hcode', rfl, rfl⟩ := h₂
  obtain rfl := instantiate_det hi hi'
  have hnf : ∀ {x : Config H}, x.code = [] → ∀ y, ¬ Step (Profile.deterministic o) closedHost x y := by
    intro x hx y hy
    rcases x with ⟨s, f, code⟩
    simp only at hx
    subst hx
    exact not_step_vals' (W := []) hy
  obtain rfl := steps_det_nf hst hst' (hnf hcode) (hnf hcode')
  exact ⟨rfl, rfl⟩

/-! ## The resulting store is typed -/

theorem steps_of_closed {P : Profile} (host : HostSemantics H) {c c' : Config H}
    (h : Steps P closedHost c c') : Steps P host c c' := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (Step.of_noHost host hs)

theorem evalGlobals_of_closed {P : Profile} (host : HostSemantics H) {s s' : Store H}
    {f f' : Frame} {gs : List CGlobalType} {es : List Expr} {vs : List Val}
    (h : EvalGlobals P closedHost s f gs es s' f' vs) : EvalGlobals P host s f gs es s' f' vs := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (steps_of_closed host he) ih

theorem evalExprs_of_closed {P : Profile} (host : HostSemantics H) {s s' : Store H}
    {f f' : Frame} {es : List Expr} {rs : List Ref}
    (h : EvalExprs P closedHost s f es s' f' rs) : EvalExprs P host s f es s' f' rs := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (steps_of_closed host he) ih

theorem evalExprss_of_closed {P : Profile} (host : HostSemantics H) {s s' : Store H}
    {f f' : Frame} {ess : List (List Expr)} {rss : List (List Ref)}
    (h : EvalExprss P closedHost s f ess s' f' rss) : EvalExprss P host s f ess s' f' rss := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (evalExprs_of_closed host he) ih

theorem instantiate_of_closed {P : Profile} (host : HostSemantics H) {s : Store H} {M : Module}
    {xas : List ExternAddr} {c : Config H} (h : Instantiate P closedHost s M xas c) :
    Instantiate P host s M xas c where
  valid := h.valid
  bounded := h.bounded
  run := by
    obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, vG, rT, rE, mi, hg, ht, he, ha, hc⟩ := h.run
    exact ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, vG, rT, rE, mi, evalGlobals_of_closed host hg,
      evalExprs_of_closed host ht, evalExprss_of_closed host he, ha, hc⟩

theorem storeOk_empty : StoreOk ({} : Store H) := by
  constructor <;> simp

/-- The store a closed instantiation leaves is typed. -/
theorem ready_storeOk {P : Profile} {M : Module} {s : Store H} {mi : ModuleInst}
    (h : Ready P closedHost ({} : Store H) M [] s mi) : StoreOk s := by
  obtain ⟨c, c', hi, hst, -, rfl, -⟩ := h
  have hc : ConfigOk c [] :=
    Instantiate.ok SingleThreaded.divHost_ok storeOk_empty (instantiate_of_closed SingleThreaded.divHost hi)
  obtain ⟨C, ⟨hs, -⟩, -⟩ := closed_preserves hc hst
  exact hs

/-! ## The resulting store holds profile functions -/

theorem forall₂_mem_zip {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a b}, (b, a) ∈ l₂.zip l₁ → R a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hab hs, _, _, h => by
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact hab
    · exact forall₂_mem_zip hs h

theorem funcOk_funcType {C : Context} {fn : Func} {d : DefType} (h : FuncOk C fn d) :
    ∃ ps rs, DefType.funcType? d = some (ps, rs) := by
  cases h with
  | mk _ he _ _ => exact ⟨_, _, by unfold DefType.funcType?; rw [Expand.iff.mp he]⟩

theorem alloc_funcs {P : Profile} {host : HostSemantics H} {M : Module} {xas : List ExternAddr}
    {dts : List DefType} {xtI : List CExternType} {jts : List DefType}
    {gts : List CGlobalType} {tts : List CTableType} {fdts : List DefType}
    {rts : List CRefType} {C' C : Context}
    (htypes : TypesOk {} M.types dts)
    (himports : List.Forall₂ (ImportOk { types := dts }) M.imports xtI)
    (hC' : C' = { types := dts, globals := CExternType.globals xtI,
                  funcs := CExternType.funcs xtI ++ fdts, refs := funcIdxNonFuncs M })
    (hC : C = { C' with
                tags := CExternType.tags xtI ++ jts, globals := C'.globals ++ gts,
                mems := CExternType.mems xtI ++ M.memories,
                tables := CExternType.tables xtI ++ tts,
                datas := M.data.map fun _ => (), elems := rts })
    (htags : List.Forall₂ (TagOk C') M.tags jts)
    (hglobals : GlobalsOk C' M.globals gts)
    (htables : List.Forall₂ (TableOk C') M.tables tts)
    (hfuncs : List.Forall₂ (FuncOk C) M.funcs fdts)
    (helems : List.Forall₂ (ElemOk C) M.elems rts)
    (hxas : List.Forall₂ (ExternAddrOk ({} : Store H)) xas xtI)
    {s₁ s₂ s₃ s₄ : Store H} {f₁ f₂ f₃ : Frame} {valsG : List Val} {refsT : List Ref}
    {refsE : List (List Ref)} {mi : ModuleInst}
    (hg : EvalGlobals P host {} ⟨[], ModuleInst.initial ({} : Store H) M xas⟩
      (M.globals.map fun g => ⟨g.type.mutability,
        (liftVal g.type.value).substAll ((allocTypes M.types).map .dt)⟩)
      (M.globals.map Global.init) s₁ f₁ valsG)
    (ht : EvalExprs P host s₁ f₁ (M.tables.map Table.init) s₂ f₂ refsT)
    (he : EvalExprss P host s₂ f₂ (M.elems.map Elem.init) s₃ f₃ refsE)
    (ha : allocModule? s₃ M xas valsG refsT refsE = some (s₄, mi)) :
    s₄.funcs = (fdts.zip M.funcs).map fun p => ⟨p.1, mi, .wasm p.2⟩ := by
  obtain ⟨hsh, -⟩ := initEval_ok (storeOk_empty (H := H)) htypes himports hC' hC htags hglobals htables
    hfuncs helems hxas hg ht he
  obtain ⟨tagTypes, funcTypes, xi, -, hft, -, -, hs₄⟩ := allocModule?_inv ha
  have hdts : allocTypes M.types = dts := allocTypes_eq htypes
  have hCT : C.types = dts := by subst hC hC'; rfl
  have hfunT : funcTypes = fdts := by
    refine mapM_eq_of_forall₂ hft (hfuncs.imp fun fn d h => ?_)
    cases h with
    | mk hd _ _ _ => rw [hdts, ← hCT]; exact hd
  subst hfunT hs₄
  simp only [hsh.funcs]
  rfl

/-- A closed native-profile instantiation leaves native Wasm functions with
function types. The native profile excludes data segments and element segments. -/
theorem ready_funcs {P : Profile} {m : BModule} (hip : InNativeProfile m) {s : Store H}
    {mi : ModuleInst} (h : Ready P closedHost ({} : Store H) m.lower [] s mi) :
    ∀ fi ∈ s.funcs, ∃ fn ps rs, fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧ ∀ i ∈ fn.body, instrInNativeProfile i := by
  obtain ⟨c, c', hi, hst, -, rfl, -⟩ := h
  obtain ⟨_, _, hm, hxas⟩ := hi.valid
  obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi', hg, ht, he, ha, rfl⟩ := hi.run
  cases hm with
  | mk htypes himports hC' hC htags hglobals _ htables hfuncs _ helems _ _ _ =>
  have hF := alloc_funcs htypes himports hC' hC htags hglobals htables hfuncs helems hxas
    hg ht he ha
  have hmem : ∀ fi ∈ s₄.funcs, ∃ fn ps rs, fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧ ∀ i ∈ fn.body, instrInNativeProfile i := by
    intro fi hfi
    rw [hF] at hfi
    obtain ⟨⟨fd, fn⟩, hp, rfl⟩ := List.mem_map.mp hfi
    obtain ⟨ps, rs, hft⟩ := funcOk_funcType (forall₂_mem_zip hfuncs hp)
    exact ⟨fn, ps, rs, rfl, hft, hip.code fn (List.of_mem_zip hp).2⟩
  have hFok : FuncsOk s₄.funcs := fun fi hfi =>
    let ⟨fn, _, _, h₁, _, h₃⟩ := hmem fi hfi
    ⟨fn, h₁, fun i hi => instrInNativeProfile_profile i (h₃ i hi)⟩
  have hcode : OkAdmins (⟨s₄, { module := mi' },
      expression ((List.range m.lower.elems.length).zip m.lower.elems |>.flatMap
        fun (i, e) => runElem i e) ++
      expression ((List.range m.lower.data.length).zip m.lower.data |>.flatMap
        fun (i, d) => runData i d) ++
      (match m.lower.start with | some x => [.plain (.call x)] | none => [])⟩ : Config H).code := by
    simp only [hip.elems, hip.data, List.length_nil, List.range_zero, List.zip_nil_right,
      List.flatMap_nil, expression, List.map_nil, List.nil_append]
    cases m.lower.start with
    | none => exact okAdmins_nil
    | some x =>
      show OkAdmins [.plain (.call x)]
      exact ⟨Or.inl ((instrInProfile_flat' (by simp) (by simp) (by simp)).2 rfl), trivial⟩
  rw [(okAdmins_steps hst hcode hFok).2]
  exact hmem

/-! ## Backward simulation from the forward ones

`BwdSim` needs no simulation of its own. If the native interpreter terminates at
some fuel, `FwdSim` gives a Core run to its result. Core has a unique normal form
(`steps_det_nf`), so that result is the one Core reaches. If no fuel suffices,
`DivSim` makes Core diverge, which `NoDivOfTerm` forbids once Core reaches a
result. -/

/-- Fuel-indexed divergence transfer: if no fuel suffices, Core diverges. -/
def DivSim (P : Profile) (s : Store H) (a : Nat) (vs : List Val) : Prop :=
  (∀ fuel, invokeRun fuel s a vs = none) → Diverges P closedHost (invoke s a vs)

theorem result_toAdmin_inj {r₁ r₂ : Result} (h : r₁.toAdmin = r₂.toAdmin) : r₁ = r₂ := by
  have h₁ := SingleThreaded.Exec.BehaviourRefinement.codeOutcome?_toAdmin r₁
  rw [h, SingleThreaded.Exec.BehaviourRefinement.codeOutcome?_toAdmin r₂] at h₁
  exact Option.some.inj h₁.symm

theorem not_step_terminal' {c c' : Config H} (h : c.Terminal) :
    ¬ Step (Profile.deterministic o) closedHost c c' :=
  SingleThreaded.Exec.BehaviourRefinement.not_step_of_terminal h

/-- `BwdSim` from `FwdSim`, `DivSim` and `NoDivOfTerm`. -/
theorem bwdSim_of {s : Store H} {a : Nat} {vs : List Val}
    (fwd : FwdSim (Profile.deterministic o) s a vs) (div : DivSim (Profile.deterministic o) s a vs)
    (sn : NoDivOfTerm (Profile.deterministic o) s a vs) :
    BwdSim (Profile.deterministic o) s a vs := by
  intro c r hst hc
  by_cases hex : ∃ fuel s' fl, invokeRun fuel s a vs = some (s', fl)
  · obtain ⟨fuel, s', fl, hrun⟩ := hex
    obtain ⟨b, hb⟩ := invokeRun_flowBeh hrun
    obtain ⟨c₂, r₂, hst₂, hc₂, rfl⟩ := fwd fuel s' fl b hrun hb
    obtain rfl := steps_det_nf hst hst₂ (fun _ => not_step_terminal' ⟨r, hc⟩)
      (fun _ => not_step_terminal' ⟨r₂, hc₂⟩)
    obtain rfl := result_toAdmin_inj (hc.symm.trans hc₂)
    exact ⟨fuel, s', fl, hrun, hb⟩
  · have hnone : ∀ fuel, invokeRun fuel s a vs = none := by
      intro fuel
      rcases h : invokeRun fuel s a vs with _ | ⟨s', fl⟩
      · rfl
      · exact absurd ⟨fuel, s', fl, h⟩ hex
    exact absurd (div hnone) (sn ⟨c, hst, r, hc⟩)

end Silmaril.Wasm.Binaryen
