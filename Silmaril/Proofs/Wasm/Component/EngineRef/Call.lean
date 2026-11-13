module

public import Silmaril.Proofs.Wasm.Component.EngineRef.CallPath
public import Silmaril.Proofs.Wasm.Component.Reference.RefToSpec

/-!
# The call phase over any engine, and the reference-machine half from the engine facts

`Silmaril.Proofs.Wasm.Component.Reference.CallPath` and the `core3P`-specific sections of
`Silmaril.Proofs.Wasm.Component.Reference.CallRun` over an arbitrary engine `E` (provenance:
copies of `Param.Core3R.Call`, with `core3R P V IR` replaced by `E`). The core activation is
`E.invoke a xs` at the core address `a` of the lifted export. What `Core3R.Call` derives from
Core 3.0 typing and the image of the store (`no_callout`, `values_coreOut`, `trap_coreOut`,
`diverges_core`) is the hypothesis `EngineRef.RunFacts` here, read on the machine's core runs
through `coreSteps_steps`; the target is `EngineRef.specOut x Out Div` instead of
`exportSpec P c x`.

* `callPhaseE`: from `afterInstE`, every behaviour of a call of the `j`-th lifted function is in
  `specOut`;
* `refToSpecE_of_facts`: with the instantiation phase (`EngineRef.Inst`), every behaviour of
  calling export `x` of `c.toRef.map ofCore` over `E` is in `specOut`.

New proofs (copied structure).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.EngineRef

open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.EngineRef Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower)

/-! ## Outcomes -/

section Outcomes


variable {E : Engine} [∀ a b, Decidable (E.ExternSub a b)] {prof : ProfileKind}

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- A trapped configuration has only the trap outcome. -/
theorem holds_trapCfg {m : Machine.Config E Unit} {out : CallOutcome}
    (ho : out.Holds (refHostE E).hr ⟨0⟩ (trapCfg m)) : out = .trap := by
  cases out with
  | resolved r => exact absurd ho.2.1 (by simp)
  | trap => rfl
  | deadlock => exact absurd ho.1.2.1 (by simp)

/-- After a resolving suffix, the only outcome is the resolution. -/
theorem out_of_resolves {m₁ m' : Machine.Config E Unit} {rs : List Silmaril.Wasm.Component.Reference.Val}
    {tr : List (Label E Unit)} {out : CallOutcome} (hR : Resolves prof m₁ rs)
    (hs : Steps prof (refHostE E).hr (D E) m₁ tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨0⟩ ev)
    (ho : out.Holds (refHostE E).hr ⟨0⟩ m') : out = .resolved (some rs) := by
  obtain ⟨tr₃, mE, hlr, hctl, hlock, hres, htick⟩ := hR
  rcases hlr.inv hs with hl | ⟨tr₄, e, r⟩
  · exact absurd ho (hl.not_holds _ _)
  have hev' : ∀ ev, Label.host ev ∈ tr₄ → CallHostEvent ⟨0⟩ ev :=
    fun ev hm => hev ev (e ▸ List.mem_append_right _ hm)
  have hq := quiet hctl (by rw [hres]; simp) htick _ tr₄ m' le_rfl r hev'
  rcases hq with rfl | hl
  · cases out with
    | resolved r => exact congrArg _ (Option.some.inj (ho.2.2.symm.trans hres))
    | trap => exact absurd (ho.symm.trans hlock) (by decide)
    | deadlock => exact absurd (ho.2.symm.trans hres) (by simp)
  · exact absurd ho (hl.not_holds _ _)

/-- After a trapping suffix, the only outcome is the trap. -/
theorem out_of_trapsNext {m₁ m' : Machine.Config E Unit}
    {tr : List (Label E Unit)} {out : CallOutcome} (hT : TrapsNext prof m₁)
    (hs : Steps prof (refHostE E).hr (D E) m₁ tr m')
    (ho : out.Holds (refHostE E).hr ⟨0⟩ m') : out = .trap := by
  obtain ⟨mT, r, hlr, hlive, hu⟩ := hT
  rcases hlr.inv hs with hl | ⟨tr₄, -, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  cases r' with
  | refl => exact absurd ho (hlive.not_holds _ _)
  | cons s r'' =>
    obtain ⟨rfl, rfl⟩ := hu.2 _ _ s
    rw [steps_of_locked rfl rfl r''] at ho
    exact holds_trapCfg ho

/-- A resolving suffix does not diverge. -/
theorem resolves_not_diverges {m₁ : Machine.Config E Unit} {rs : List Silmaril.Wasm.Component.Reference.Val}
    (hR : Resolves prof m₁ rs) : ¬ Diverges prof (refHostE E).hr (D E) m₁ := by
  obtain ⟨tr₃, mE, hlr, hctl, -⟩ := hR
  exact fun hd => not_diverges_of_ctl_nil hctl (hlr.diverges hd)

/-- A trapping suffix does not diverge. -/
theorem trapsNext_not_diverges {m₁ : Machine.Config E Unit} (hT : TrapsNext prof m₁) :
    ¬ Diverges prof (refHostE E).hr (D E) m₁ := by
  obtain ⟨mT, r, hlr, -, hu⟩ := hT
  intro hd
  obtain ⟨m', ⟨l, -, s⟩, hd'⟩ := (hlr.diverges hd).unfold
  obtain ⟨-, rfl⟩ := hu.2 _ _ s
  exact not_diverges_trapCfg _ hd'

end Outcomes

/-! ## The call phase -/

section Call

variable {E : Engine} [∀ a b, Decidable (E.ExternSub a b)] {prof : ProfileKind}
  {cs : E.Store (CanonHost E)} {x : SimpleExport} {vs : List Silmaril.Wasm.Component.Val}
  {a : E.FuncAddr} {Out : Set (Option (List Flat))} {Div : Prop}

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- Runs of the core activation allowed by the machine are engine runs. -/
theorem coreSteps_steps {x₀ y : CoreSt E} (hy : Relation.ReflTransGen (CoreStep E) x₀ y) :
    CoreEngine.Steps E x₀ y :=
  Relation.ReflTransGen.mono (fun _ _ h => h.2) _ _ hy

/-- The run facts of the call of export `x` on `vs` at address `a`. -/
abbrev CallFacts (E : Engine) (cs : E.Store (CanonHost E)) (a : E.FuncAddr) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) (Out : Set (Option (List Flat))) (Div : Prop) : Prop :=
  RunFacts E cs a (lowerArgs x.ty.params vs) (ValTy.flatList x.ty.results) Out Div

/-- **Calls after the core activation left it.** -/
theorem exit_spec (hRF : CallFacts E cs a x vs Out Div) {M₀ : Machine.Config E Unit}
    {th : Option ThreadId} {K : List FlatValue → Canon.P E Unit (Ret E)}
    {segs : List (Seg E Unit)} {rest : List (Activation E Unit)}
    (hat : CallAt prof cs x a vs M₀ th K segs rest) {y : CoreSt E}
    (hy : Relation.ReflTransGen (CoreStep E) (cs, E.invoke a (lowerArgs x.ty.params vs)) y)
    {l : Label E Unit} {m₁ m' : Machine.Config E Unit} {tr : List (Label E Unit)}
    {out : CallOutcome} (hx : CoreExit M₀ th K segs rest y l m₁)
    (hs : Steps prof (refHostE E).hr (D E) m₁ tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨0⟩ ev)
    (ho : out.Holds (refHostE E).hr ⟨0⟩ m') : Outcome.ofCall out ∈ specOut x Out Div := by
  have hy' := coreSteps_steps hy
  rcases hx with ⟨ys, hst, -, rfl⟩ | ⟨hst, -, rfl⟩ | ⟨h, args, hst⟩
  · obtain ⟨hout, hty⟩ := hRF.values ys hy' hst
    cases hl : liftArgs x.ty.results ys with
    | some ws =>
      rw [out_of_resolves (hat.ret y ys ws hty hl) hs hev ho]
      exact Or.inl ⟨_, hout, by simp only [Outcome.ofCall, liftOutcome, hl]⟩
    | none =>
      rw [out_of_trapsNext (hat.trap y ys hty hl) hs ho]
      exact Or.inl ⟨_, hout, by simp only [Outcome.ofCall, liftOutcome, hl]⟩
  · rw [steps_of_locked rfl rfl hs] at ho
    rw [holds_trapCfg ho]
    exact Or.inl ⟨_, hRF.trap hy' hst, rfl⟩
  · exact (hRF.no_callout h args hy' hst).elim

/-- **Divergence after the core activation left it** is impossible. -/
theorem exit_not_diverges (hRF : CallFacts E cs a x vs Out Div) {M₀ : Machine.Config E Unit}
    {th : Option ThreadId} {K : List FlatValue → Canon.P E Unit (Ret E)}
    {segs : List (Seg E Unit)} {rest : List (Activation E Unit)}
    (hat : CallAt prof cs x a vs M₀ th K segs rest) {y : CoreSt E}
    (hy : Relation.ReflTransGen (CoreStep E) (cs, E.invoke a (lowerArgs x.ty.params vs)) y)
    {l : Label E Unit} {m₁ : Machine.Config E Unit}
    (hx : CoreExit M₀ th K segs rest y l m₁) : ¬ Diverges prof (refHostE E).hr (D E) m₁ := by
  have hy' := coreSteps_steps hy
  rcases hx with ⟨ys, hst, -, rfl⟩ | ⟨hst, -, rfl⟩ | ⟨h, args, hst⟩
  · obtain ⟨-, hty⟩ := hRF.values ys hy' hst
    cases hl : liftArgs x.ty.results ys with
    | some ws => exact resolves_not_diverges (hat.ret y ys ws hty hl)
    | none => exact trapsNext_not_diverges (hat.trap y ys hty hl)
  · exact not_diverges_trapCfg _
  · exact (hRF.no_callout h args hy' hst).elim

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- The host invocation from `afterInstE`. -/
theorem invoke_inv {fs : List (CFuncInst E)} {j : Nat} {args : List Silmaril.Wasm.Component.Reference.Val}
    {m : Machine.Config E Unit} {hr : HostReady Unit} {d : Call E → Canon.P E Unit (Ret E)}
    (h : Step prof hr d (afterInstE cs fs) (.host (.invoke ⟨0⟩ ⟨j⟩ args)) m) :
    m = invokedCfg cs fs j args := by
  cases h
  rfl

variable {fs : List (CFuncInst E)} {j : Nat} {M₀ : Machine.Config E Unit} {th : Option ThreadId}
  {K : List FlatValue → Canon.P E Unit (Ret E)} {segs : List (Seg E Unit)}
  {rest : List (Activation E Unit)} {tr₁ : List (Label E Unit)}

/-- **Terminating calls** are in `specOut`. -/
theorem calls_spec (hRF : CallFacts E cs a x vs Out Div)
    (hpre : LRun prof (refHostE E).hr (D E) (invokedCfg cs fs j (vs.map toRefVal)) tr₁ M₀)
    (hat : CallAt prof cs x a vs M₀ th K segs rest)
    {m' : Machine.Config E Unit} {out : CallOutcome}
    (hcalls : Calls prof (refHostE E).hr (D E) (afterInstE cs fs) ⟨0⟩ ⟨j⟩ (vs.map toRefVal) m'
      out) : Outcome.ofCall out ∈ specOut x Out Div := by
  obtain ⟨tr, hs, hev, -, ho⟩ := hcalls
  obtain ⟨m₂, s, r⟩ := Steps.cons_iff.mp hs
  rw [invoke_inv s] at r
  rcases hpre.inv r with hl | ⟨tr'', e, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  rw [eq_coreCfg hat.ctl, hat.core] at r'
  rcases coreCfg_steps_inv r' with ⟨y, -, rfl, -⟩ | ⟨y, pre, l, m₁, tr₂, hy, -, e', hx, r''⟩
  · have hl : Live (coreCfg M₀ th K segs rest y) := ⟨List.cons_ne_nil _ _, hat.lock⟩
    exact absurd ho (hl.not_holds _ _)
  · have hev' : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨0⟩ ev := fun ev hm =>
      hev ev (by rw [e, e']; exact List.mem_append_right _ (List.mem_append_right _
        (List.mem_cons_of_mem _ hm)))
    exact exit_spec hRF hat hy hx r'' hev' ho

/-- **Divergent calls** need `Div`. -/
theorem diverges_spec (hRF : CallFacts E cs a x vs Out Div)
    (hpre : LRun prof (refHostE E).hr (D E) (invokedCfg cs fs j (vs.map toRefVal)) tr₁ M₀)
    (hat : CallAt prof cs x a vs M₀ th K segs rest)
    (hd : CallDiverges prof (refHostE E).hr (D E) (afterInstE cs fs) ⟨0⟩ ⟨j⟩
      (vs.map toRefVal)) : Div := by
  obtain ⟨m₂, s, hd⟩ := hd
  rw [invoke_inv s] at hd
  have hd₀ := hpre.diverges hd
  rw [eq_coreCfg hat.ctl, hat.core] at hd₀
  rcases coreCfg_diverges_inv hd₀ with hi | ⟨y, l, m₁, hy, hx, hd'⟩
  · exact hRF.diverges (Silmaril.InfiniteTrace.map id (fun _ _ h => h.2) hi)
  · exact (exit_not_diverges hRF hat hy hx hd').elim

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- The `j`-th lifted function. -/
theorem liftedFuncsE_get? (c : Simple) (addr : Nat → E.FuncAddr) {j : Nat}
    (hj : j < c.exports.length) :
    (liftedFuncsE addr c)[j]? =
      some (.lifted (addr c.exports[j].core) (liftedFt c.exports[j]) {} ⟨0⟩) := by
  simp only [liftedFuncsE, List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some]

/-- **The call phase over `E`.** -/
theorem callPhaseE (prof : ProfileKind) (c : Simple) (hf : c.FloatFree) (ha : c.Arity)
    (cs : E.Store (CanonHost E)) (addr : Nat → E.FuncAddr) (j : Nat) (hj : j < c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (hRF : CallFacts E cs (addr c.exports[j].core) c.exports[j] vs Out Div) :
    callBehaviours prof (refHostE E) (afterInstE cs (liftedFuncsE addr c)) ⟨0⟩ ⟨j⟩
        (vs.map toRefVal) ⊆ specOut c.exports[j] Out Div := by
  intro b hb
  have hx : c.exports[j] ∈ c.exports := List.getElem_mem hj
  obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
  obtain ⟨hff, hffr⟩ := hf _ hx
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_at prof cs _ j _ c.exports[j] vs hff hvs
    hmax hres hmaxr hffr (liftedFuncsE_get? c addr hj)
  rcases hb with ⟨m', out, hcalls, rfl⟩ | ⟨rfl, hd⟩
  · exact calls_spec hRF hpre hat hcalls
  · exact Or.inr ⟨rfl, diverges_spec hRF hpre hat hd⟩

end Call

/-! ## The reference-machine half from the engine facts -/

/-- **The reference-machine half over any engine, from the instantiation and run facts.** -/
theorem refToSpecE_of_facts {E : Engine} [∀ a b, Decidable (E.ExternSub a b)]
    {ofCore : Silmaril.Wasm.Module → E.Module} (prof : ProfileKind) (c : Simple) (hc : c.Good)
    (hf : c.FloatFree) (ha : c.Arity) {cs : E.Store (CanonHost E)} {ci : E.Inst}
    {addr : Nat → E.FuncAddr} (hF : InstFacts E ofCore c cs ci addr) (x : SimpleExport)
    (hx : x ∈ c.exports) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList x.ty.params vs = true) {Out : Set (Option (List Flat))} {Div : Prop}
    (hRF : CallFacts E cs (addr x.core) x vs Out Div) :
    exportBehaviours prof (refHostE E) ()
        (Silmaril.Wasm.Component.Syntax.Component.map ofCore c.toRef) [] x.name
        (vs.map toRefVal) ⊆ specOut x Out Div := by
  obtain ⟨j, hj, rfl⟩ : ∃ j, ∃ hj : j < c.exports.length, c.exports[j] = x :=
    List.getElem_of_mem hx
  have hinst := instBehaviours_toRef hF prof
  have hcall := callPhaseE prof c hf ha cs addr j hj vs hvs hRF
  intro b hb
  rcases hb with ⟨m₁, inst, es, f, hr, hl, hb⟩ | ⟨-, hr⟩ | ⟨-, hr⟩
  · have he : InstResult.instance m₁ inst es =
        .instance (afterInstE cs (liftedFuncsE addr c)) ⟨0⟩ (exportMap c) := hinst _ hr
    obtain ⟨rfl, rfl, rfl⟩ : m₁ = afterInstE cs (liftedFuncsE addr c) ∧ inst = ⟨0⟩ ∧
        es = exportMap c := by
      simpa only [InstResult.instance.injEq] using he
    have hf' : f = ⟨j⟩ := Option.some.inj (hl.symm.trans (exportMap_lookup hc j hj))
    exact hcall (hf' ▸ hb)
  · exact absurd (hinst _ hr) (by simp)
  · exact absurd (hinst _ hr) (by simp)

end Silmaril.Proofs.Wasm.Component.EngineRef
