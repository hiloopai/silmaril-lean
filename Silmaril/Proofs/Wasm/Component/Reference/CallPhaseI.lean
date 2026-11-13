module

public import Silmaril.Proofs.Wasm.Component.Reference.CallI
public import Silmaril.Proofs.Wasm.Component.Reference.CalloutPath

/-!
# The call phase of a component with imports

`callPhaseI : CallPhaseI`: from the configuration after instantiation
(`afterInst P cs (c.afterFuncs P addr)`: one host function per import, then the lifted
exports; the core store `cs` renames to the instance's store under `trampIdx`, and its host
functions are the `canon lower` trampolines of the imports, `SimpleI.TrampOk`), every behaviour of a call of export `j` over `core3P P` with the host
`answerHostS P g` (a stateful host; `answerHost P g` is its stateless instance) is what the IR must exhibit (`IRObsI`): the reference run is a segmented run
of the core activation (`segs_inv`), which is a play of the core instance with import calls
related by `ImpRel` and answered by `g` (`CalloutPath`), and `simpleI_specToIR` turns it into a
play of the IR denotation.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN)

variable {P : Profile} {σ : Type} {g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)}
  {prof : ProfileKind}
  {c : SimpleI} {I : Silmaril.Wasm.Game.ScalarInstance}

/-! ## The configuration after instantiation -/

theorem afterFuncs_host (addr : Nat → Nat) {k : Nat} (hk : k < c.imports.length) :
    (SimpleI.afterFuncs P addr c)[k]? = some (.host (witFt c.imports[k].2) ⟨k⟩) := by
  rw [SimpleI.afterFuncs, List.getElem?_append_left (by rw [List.length_mapIdx]; exact hk),
    List.getElem?_mapIdx, List.getElem?_eq_getElem hk]
  rfl

theorem afterFuncs_lifted (addr : Nat → Nat) {j : Nat} (hj : j < c.exports.length) :
    (SimpleI.afterFuncs P addr c)[c.imports.length + j]? =
      some (.lifted (addr c.exports[j].core) (liftedFt c.exports[j]) {} ⟨0⟩) := by
  rw [SimpleI.afterFuncs, List.getElem?_append_right (by rw [List.length_mapIdx]; omega), List.length_mapIdx,
    Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_eq_getElem hj]
  rfl

/-! ## Outcomes under `answerHostS P g` -/

theorem holds_trapCfgA {m : Machine.Config (E3 P) σ} {out : CallOutcome}
    (ho : out.Holds (answerHostS P g).hr ⟨0⟩ (trapCfg m)) : out = .trap :=
  holds_trapCfg' (g := g) ho

theorem out_of_resolvesA {m₁ m' : Machine.Config (E3 P) σ} {rs : List Silmaril.Wasm.Component.Reference.Val}
    {tr : List (Label (E3 P) σ)} {out : CallOutcome} (hR : ResolvesA prof P g m₁ rs)
    (hs : Steps prof (answerHostS P g).hr (DA P g) m₁ tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨0⟩ ev)
    (ho : out.Holds (answerHostS P g).hr ⟨0⟩ m') : out = .resolved (some rs) := by
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

theorem out_of_trapsNextA {m₁ m' : Machine.Config (E3 P) σ}
    {tr : List (Label (E3 P) σ)} {out : CallOutcome} (hT : TrapsNextA prof P g m₁)
    (hs : Steps prof (answerHostS P g).hr (DA P g) m₁ tr m')
    (ho : out.Holds (answerHostS P g).hr ⟨0⟩ m') : out = .trap := by
  obtain ⟨mT, r, hlr, hlive, hu⟩ := hT
  rcases hlr.inv hs with hl | ⟨tr₄, -, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  cases r' with
  | refl => exact absurd ho (hlive.not_holds _ _)
  | cons s r'' =>
    obtain ⟨rfl, rfl⟩ := hu.2 _ _ s
    rw [steps_of_locked rfl rfl r''] at ho
    exact holds_trapCfgA ho

theorem invoke_invA {cs : (core3P P).Store (CanonHost (core3P P))} {fs : List (CFuncInst (core3P P))}
    {h₀ : σ} {j : Nat} {args : List Silmaril.Wasm.Component.Reference.Val} {m : Machine.Config (E3 P) σ}
    (h : Step prof (answerHostS P g).hr (DA P g) (afterInstH P cs fs h₀)
      (.host (.invoke ⟨0⟩ ⟨j⟩ args)) m) :
    m = invokedCfgH P cs fs h₀ j args := by
  cases h
  rfl

theorem extSC_nil (B : Machine.Config (E3 P) σ) : extSC B [] [] = B := by
  simp only [extSC, List.append_nil]

theorem withH_self (B : Machine.Config (E3 P) σ) : withH B B.host = B := rfl

/-! ## Rounds to component import calls -/

/-- The host states recorded by a segmented run are consecutive, from `s` to `s'`. -/
def Chain : σ → List (σ × CallRec × σ) → σ → Prop
  | s, [], s' => s = s'
  | s, (a, _, b) :: l, s' => a = s ∧ Chain b l s'

theorem ASeg.chain {Q : LowerSite P → Prop} {B : CStore (E3 P)} {th : Option ThreadId}
    {s s' : σ} {x z : CoreSt (E3 P)} {calls : List (σ × CallRec × σ)}
    (h : ASeg g Q B th s x calls s' z) : Chain s calls s' := by
  induction h with
  | done => rfl
  | call _ _ _ _ _ _ _ ih => exact ⟨rfl, ih⟩

theorem _root_.Silmaril.Wasm.Component.Reference.HostRun.append {n : Nat} {s s₁ s₂ : σ} {ds₁ ds₂ : List (Σ _ : (sigN n).Op, Option Payload)}
    (h₁ : HostRun g s ds₁ s₁) (h₂ : HostRun g s₁ ds₂ s₂) : HostRun g s (ds₁ ++ ds₂) s₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons hd _ ih => exact .cons hd (ih h₂)

/-- **The rounds of a segmented run are component import calls answered by `g`**, the host
state threaded along the recorded states. -/
theorem rounds_dss {calls : List (σ × CallRec × σ)} {rounds : List (Round I.E)}
    (h : List.Forall₂ (RoundOf c I g) calls rounds) :
    ∀ {s s' : σ}, Chain s calls s' →
      ∃ dss, List.Forall₂ (ImpRel c I) rounds dss ∧ HostRun g s dss.flatten s' := by
  induction h with
  | nil => intro s s' hc; exact ⟨[], .nil, (show s = s' from hc) ▸ .nil _⟩
  | @cons cl r calls rounds hcl _ ih =>
    intro s s' hc
    obtain ⟨a, x, b⟩ := cl
    obtain ⟨rfl, hc'⟩ := hc
    obtain ⟨ds, hr, hds⟩ := impRel_of_round hcl
    obtain ⟨dss, hrs, hdss⟩ := ih hc'
    exact ⟨ds :: dss, .cons hr hrs, by rw [List.flatten_cons]; exact hds.append hdss⟩

/-! ## The callouts of the core activation -/

theorem coreStep_funcs {s s' : Silmaril.Wasm.Execution.Core.Store (CanonHost (E3 P))}
    {t t' : Silmaril.Wasm.SingleThreaded.Thread} (h : CoreStep (E3 P) (s, t) (s', t')) :
    s'.funcs = s.funcs := by
  obtain ⟨-, f', code', -, hs⟩ := h
  have hl := (Silmaril.Wasm.SingleThreaded.Step.framesLocal hs).1
  rw [Silmaril.Wasm.SingleThreaded.Thread.config_store] at hl
  exact hl

theorem coreSteps_funcs {x y : CoreSt (E3 P)} (h : Relation.ReflTransGen (CoreStep (E3 P)) x y) :
    (y.1 : Silmaril.Wasm.Execution.Core.Store (CanonHost (E3 P))).funcs =
      (x.1 : Silmaril.Wasm.Execution.Core.Store (CanonHost (E3 P))).funcs := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact (coreStep_funcs hs).trans ih

/-- Segmented runs keep the functions of the core store. -/
theorem aseg_funcs {B : CStore (E3 P)} {th : Option ThreadId} {x z : CoreSt (E3 P)}
    {calls : List (σ × CallRec × σ)} {s s' : σ}
    (h : ASeg g (SiteI c) B th s x calls s' z) :
    (z.1 : Silmaril.Wasm.Execution.Core.Store (CanonHost (E3 P))).funcs =
      (x.1 : Silmaril.Wasm.Execution.Core.Store (CanonHost (E3 P))).funcs := by
  induction h with
  | done hy => exact coreSteps_funcs hy
  | call hy _ _ _ _ _ _ ih =>
    have h₁ := coreSteps_funcs hy
    exact ih.trans h₁

/-- A host-call redex of the core store, in the renamed configuration. -/
theorem decompose_mapped {s : Silmaril.Wasm.Execution.Core.Store (CanonHost (E3 P))}
    {t : Silmaril.Wasm.SingleThreaded.Thread} {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : Nat}
    {h : CanonHost (E3 P)} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hd : Silmaril.Wasm.SingleThreaded.decompose? s (t.config s).code = some (E, a, h, args)) :
    Silmaril.Wasm.SingleThreaded.decompose? (t.config (Store.mapH trampIdx s)).store
      (t.config (Store.mapH trampIdx s)).code = some (E, a, trampIdx h, args) := by
  rw [Silmaril.Wasm.SingleThreaded.Thread.config_store, decompose?_config_mapH, hd]
  rfl

/-- The facts about the frame of the core activation that the callouts use. -/
structure FrameOk (c : SimpleI) (B : CStore (E3 P)) (th : Option ThreadId) : Prop where
  funcs : B.funcs = SimpleI.afterFuncs P (fun k => I.addrs.getD k 0) c
  entry : ∀ f ft opts, calloutEntry B th (.lowered f ft opts ⟨0⟩) = none
  inst : ∃ st, ArenaField.insts.get? B ⟨0⟩ = some st ∧ st.mayLeave = true

/-- **The callouts of the core activation are the trampolines of the imports** (at a later store), at the types
of the imports, typed and answered by `g` as the IR prescribes. -/
theorem calloutsOk_ofAt {s : Silmaril.Wasm.Execution.Core.Store Nat} {cs : (core3P P).Store (CanonHost (core3P P))} {f : I.F.Op} {a : Nat}
    {xs : List Flat} (C : CallStartAt c I s cs f a xs) (hff : c.FloatFree) (har : c.Arity)
    (htr : c.TrampOk cs) (hg : c.HostOkS g) {B : CStore (E3 P)} {th : Option ThreadId}
    (hB : FrameOk (I := I) c B th) {s₀ : σ} :
    CalloutsOk g (SiteI c) B th s₀ (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) := by
  intro calls s' y h ys hs hst
  obtain ⟨-, -, post⟩ := aseg_rounds C.good C.inst C.wf (f := f) hs (C.pre s₀)
  obtain ⟨E, a', args, hd, hm⟩ := status_callout_redex hst
  obtain ⟨fi, -, -, -, hfi, hcode, -⟩ := Silmaril.Wasm.SingleThreaded.decompose?_sound hd
  have hfi' : (cs : Silmaril.Wasm.Execution.Core.Store (CanonHost (E3 P))).funcs[a']? = some fi := by
    rw [← aseg_funcs hs]
    exact hfi
  obtain ⟨k, hk, rfl⟩ := htr a' fi h hfi' hcode
  obtain ⟨e, he⟩ := callout_typed C.wf post (decompose_mapped hd)
  have hek := ifaceOp?_some he
  have htyped : ys.map (·.type) = ValTy.flatList c.imports[k].2.params := by
    have ht : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal
        ((ValTy.flatList c.imports[k].2.params).map .num) args := by
      have h₀ : (I.imports.get e.1).params = (ValTy.flatList c.imports[k].2.params).map .num := by
        rw [imports_get C.good C.inst e k hk hek.1]
        rfl
      have h₁ : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (I.imports.get e.1).params args :=
        hek.2 ▸ e.2.2
      exact h₀ ▸ h₁
    exact toFlat?_types _ _ _ ht hm
  obtain ⟨st, hst', hleave⟩ := hB.inst
  have hmem : c.imports[k] ∈ c.imports := List.getElem_mem hk
  let L : LowerSite P := ⟨⟨k⟩, ⟨0⟩, st, witFt c.imports[k].2, ⟨k⟩, c.imports[k].2⟩
  refine ⟨L, ⟨k, hk, rfl, rfl, rfl⟩, rfl, ?_⟩
  exact { entry := hB.entry _ _ _, inst := hst', leave := hleave
          func := by
            show (B.funcs)[k]? = _
            rw [hB.funcs, afterFuncs_host _ hk]
          pff := (hff.2 _ hmem).1, rff := (hff.2 _ hmem).2, typed := htyped
          maxp := (har.2 _ hmem).1, res := (har.2 _ hmem).2.2, maxr := (har.2 _ hmem).2.1
          answers := fun s ws rs s' h => hg s k hk ws rs s' h }

/-- **The callouts of the core activation are the trampolines of the imports**, at the types
of the imports, typed and answered by `g` as the IR prescribes. -/
theorem calloutsOk_of {cs : (core3P P).Store (CanonHost (core3P P))} {f : I.F.Op} {a : Nat}
    {xs : List Flat} (C : CallStart c I cs f a xs) (hff : c.FloatFree) (har : c.Arity)
    (htr : c.TrampOk cs) (hg : c.HostOkS g) {B : CStore (E3 P)} {th : Option ThreadId}
    (hB : FrameOk (I := I) c B th) {s₀ : σ} :
    CalloutsOk g (SiteI c) B th s₀ (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) :=
  calloutsOk_ofAt C.toAt hff har htr hg hB

/-! ## Assembly -/

/-- **A play of the core instance with related import calls is a play of the IR**, with the
lifted answer `R`. -/
theorem ir_play (hc : c.Good) (hI : c.mod.IsInst I) (j : Fin c.exports.length)
    {vs : List Silmaril.Wasm.Component.Val} {xs : List Flat}
    (hxs : checkLower c.exports[j].ty.params vs = some xs) {f : I.F.Op}
    (hf₁ : f.1.val = c.exports[j].core) (hf₂ : f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat)
    {rounds : List (Round I.E)} {w : I.F.Ar f} {q : I.HState}
    (hpath : I.Path P (.idle I.store) (.inr (.ask f) :: callMoves rounds ++ [.inr (.ans f w)]) q)
    {dss : List (List (Σ _ : (sigN c.imports.length).Op, Option Payload))}
    (hrel : List.Forall₂ (ImpRel c I) rounds dss) {R : Option Payload}
    (hR : (answerPayload w).bind (Silmaril.Wasm.Component.Adapter.up (.lift c.exports[j].ty)) = R) :
    (.inr (.ask (⟨j, by simp [SimpleI.toComp]⟩, .vals vs)) :: callMoves dss.flatten ++
        [.inr (.ans (m := (⟨j, by simp [SimpleI.toComp]⟩, .vals vs)) R)] :
        List (Move (sigN c.imports.length) (sigN c.toComp.exports.length))) ∈
        c.toComp.den (impSem P) := by
  have h := (simpleI_specToIR P c hc I hI j vs).2 xs hxs f hf₁ hf₂ rounds w q hpath dss hrel
  rw [hR] at h
  exact h

/-- The returned values of the export call are typed by its flat result types. -/
theorem results_typed {x : SimpleExport} {f : I.F.Op}
    (hft : I.exports.get f.1 = fnOf x.ty.flat) {vs : List Silmaril.Wasm.Execution.Core.Val}
    {ys : List Flat} {w : I.F.Ar f}
    (hw : Silmaril.Wasm.Game.Answer.ofResult? (I.exports.get f.1) (.values vs) = some w)
    (hm : vs.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys) :
    ys.map (·.type) = ValTy.flatList x.ty.results := by
  have ht : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (I.exports.get f.1).results vs := by
    by_contra hn
    have hnone : Silmaril.Wasm.Game.Answer.ofResult? (I.exports.get f.1) (.values vs) = none := by
      simp only [Silmaril.Wasm.Game.Answer.ofResult?, hn, dite_false]
    rw [hnone] at hw
    cases hw
  rw [hft] at ht
  exact toFlat?_types _ _ _ ht hm

/-- The lifted answer of returned flat values. -/
theorem lifted_answer {x : SimpleExport} {f : I.F.Op} {vs : List Silmaril.Wasm.Execution.Core.Val}
    {ys : List Flat} {w : I.F.Ar f}
    (hw : Silmaril.Wasm.Game.Answer.ofResult? (I.exports.get f.1) (.values vs) = some w)
    (hm : vs.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys) :
    (answerPayload w).bind (Silmaril.Wasm.Component.Adapter.up (.lift x.ty)) =
      (liftArgs x.ty.results ys).map .vals := by
  rw [answerPayload_of_ofResult? hw]
  simp only [hm, Option.map_some, Option.bind_some, Silmaril.Wasm.Component.Adapter.up]

/-- The lifted answer of a trap or an exception. -/
theorem lifted_trap {x : SimpleExport} {f : I.F.Op} {r : Silmaril.Wasm.Execution.Core.Result}
    (hr : ∀ vs, r ≠ .values vs) {w : I.F.Ar f}
    (hw : Silmaril.Wasm.Game.Answer.ofResult? (I.exports.get f.1) r = some w) :
    (answerPayload w).bind (Silmaril.Wasm.Component.Adapter.up (.lift x.ty)) = none := by
  rw [answerPayload_of_ofResult? hw]
  cases r with
  | values vs => exact absurd rfl (hr vs)
  | trap => rfl
  | throw _ => rfl

/-- The static facts of an export call of `c` from the configuration after instantiation. -/
structure CallCtxI (P : Profile) (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3P P).Store (CanonHost (core3P P))) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (f : I.F.Op) (a : Nat) : Prop where
  start : CallStart c I cs f a (lowerArgs c.exports[j].ty.params vs)
  typed : ValTy.checkList c.exports[j].ty.params vs = true
  core : f.1.val = c.exports[j].core
  ty : I.exports.get f.1 = fnOf c.exports[j].ty.flat

theorem CallCtxI.lowered {cs : (core3P P).Store (CanonHost (core3P P))} {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} {f : I.F.Op} {a : Nat} (C : CallCtxI P c I cs j vs f a) :
    checkLower c.exports[j].ty.params vs = some (lowerArgs c.exports[j].ty.params vs) := by
  simp only [checkLower, C.typed, ↓reduceIte]

/-- **The reference outcome of an ending core phase is what the IR exhibits.** -/
theorem obs_of_end {cs : (core3P P).Store (CanonHost (core3P P))} {fs : List (CFuncInst (core3P P))}
    {j : Fin c.exports.length} {vs : List Silmaril.Wasm.Component.Val} {f : I.F.Op} {a : Nat}
    (C : CallCtxI P c I cs j vs f a) {M₀ : Machine.Config (E3 P) σ} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)} {s₀ : σ}
    (hat : CallAtA prof P g cs fs c.exports[j] a vs M₀ th K segs rest)
    {tr : List (Label (E3 P) σ)} {m' : Machine.Config (E3 P) σ} {out : CallOutcome}
    (hend : CoreEnd (prof := prof) g (SiteI c) M₀ s₀ th K segs rest
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs c.exports[j].ty.params vs))
      tr m' out)
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨0⟩ ev)
    (ho : out.Holds (answerHostS P g).hr ⟨0⟩ m') :
    IRObsIS (c.toComp.den (impSem P)) ⟨j, by simp [SimpleI.toComp]⟩ vs g s₀
      (Outcome.ofCall out) := by
  obtain ⟨calls, s', y, hs, hexit | hfail⟩ := hend
  · obtain ⟨ST, CL, pre, l, m₁, tr₂, rfl, hco, hx, r₂⟩ := hexit
    have hev' : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨0⟩ ev :=
      fun ev hm => hev ev (List.mem_append_right _ hm)
    rcases hx with ⟨ys, hst, -, rfl⟩ | ⟨hst, -, rfl⟩ | ⟨h, ys, hst⟩
    · show IRObsIS _ _ vs g s₀ (Outcome.ofCall out)
      obtain ⟨cvs, hcode, hm⟩ := status_values hst
      obtain ⟨rounds, w, q, hrs, hpath, hw⟩ := path_returned C.start hs (.values cvs) hcode
      obtain ⟨dss, hrel, hrun⟩ := rounds_dss hrs hs.chain
      have hty := results_typed C.ty hw hm
      have hR := lifted_answer (x := c.exports[j]) hw hm
      cases hl : liftArgs c.exports[j].ty.results ys with
      | some ws =>
        rw [out_of_resolvesA (hat.ret s' ST CL y ys ws hty hl) r₂ hev' ho]
        rw [hl] at hR
        exact ⟨ws, dss.flatten, s', rfl, hrun, ir_play C.start.good C.start.inst j C.lowered C.core
          C.start.args hpath hrel hR⟩
      | none =>
        rw [out_of_trapsNextA (hat.trap s' ST CL y ys hty hl) r₂ ho]
        rw [hl] at hR
        exact ⟨dss.flatten, s', hrun, ir_play C.start.good C.start.inst j C.lowered C.core
          C.start.args hpath hrel hR⟩
    · show IRObsIS _ _ vs g s₀ (Outcome.ofCall out)
      rw [steps_of_locked rfl rfl r₂] at ho
      rw [holds_trapCfgA ho]
      have hr : ∃ r : Silmaril.Wasm.Execution.Core.Result, (∀ vs, r ≠ .values vs) ∧
          (y.2.config y.1).code = r.toAdmin := by
        rcases status_trap hst with hc' | ⟨e, hc'⟩
        · exact ⟨.trap, (fun _ h => by cases h), hc'⟩
        · exact ⟨.throw e, (fun _ h => by cases h), hc'⟩
      obtain ⟨r, hrv, hcode⟩ := hr
      obtain ⟨rounds, w, q, hrs, hpath, hw⟩ := path_returned C.start hs r hcode
      obtain ⟨dss, hrel, hrun⟩ := rounds_dss hrs hs.chain
      exact ⟨dss.flatten, s', hrun, ir_play C.start.good C.start.inst j C.lowered C.core
        C.start.args hpath hrel (lifted_trap (x := c.exports[j]) hrv hw)⟩
    · exact absurd hst (hco h ys)
  · obtain ⟨L, ys, E, a', args, hst, hq, hok, hf, hd, rfl⟩ := hfail
    show IRObsIS _ _ vs g s₀ .traps
    obtain ⟨rounds, e, q, hrs, he, hpath⟩ := path_callout_trap C.start hs (decompose_mapped hd)
    have hek := ifaceOp?_some he
    have hys : e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys := by
      obtain ⟨E', a'', args', hd', hm⟩ := status_callout_redex hst
      have hargs : args' = args := by
        have e' := hd'.symm.trans hd
        simp only [Option.some.injEq, Prod.mk.injEq] at e'
        exact e'.2.2.2
      rw [hek.2, ← hargs]
      exact filterMap_of_mapM hm
    obtain ⟨ds, hds, hrun₁⟩ := impRel_fail (I := I) (e := e) hq hek.1 hys hf
    obtain ⟨dss, hrel, hrun⟩ := rounds_dss hrs hs.chain
    have hrel' : List.Forall₂ (ImpRel c I) (rounds ++ [⟨e, .trap⟩]) (dss ++ [ds]) :=
      List.rel_append hrel (.cons hds .nil)
    refine ⟨(dss ++ [ds]).flatten, s', ?_, ir_play C.start.good C.start.inst j C.lowered C.core
      C.start.args hpath hrel' rfl⟩
    rw [List.flatten_append, List.flatten_singleton]
    exact hrun.append hrun₁

/-- The configuration after instantiation is the frame of the core activation, with no callout
records yet. -/
theorem coreCfg_start {cs : (core3P P).Store (CanonHost (core3P P))} {fs : List (CFuncInst (core3P P))}
    {x : SimpleExport} {a : Nat} {vs : List Silmaril.Wasm.Component.Val} {M₀ : Machine.Config (E3 P) σ}
    {th : Option ThreadId} {K : List FlatValue → Canon.P (E3 P) σ (Ret (E3 P))}
    {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)}
    (hat : CallAtA prof P g cs fs x a vs M₀ th K segs rest) :
    M₀ = coreCfg (extSC (withH M₀ M₀.host) [] []) th K segs rest
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs x.ty.params vs)) := by
  rw [withH_self, extSC_nil, ← hat.core]
  exact eq_coreCfg hat.ctl

/-- **The call phase with imports answered by a stateful host**: from the configuration after
instantiation in host state `s₀`, every behaviour of a call of export `j` of `c` on the images of
well-typed values, over `core3P P` with the host answering by the stateful `g`, is what the IR
denotation over `impSem P` must exhibit, the host state threaded from `s₀`. -/
def CallPhaseIS : Prop :=
  ∀ (P : Profile) (prof : ProfileKind) (c : SimpleI), c.Good → c.FloatFree → c.Arity →
    ∀ (I : Silmaril.Wasm.Game.ScalarInstance), c.mod.IsInst I →
    ∀ (cs : (core3P P).Store (CanonHost (core3P P))), Store.mapH trampIdx cs = I.store →
      c.TrampOk cs →
    ∀ (σ : Type) (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)), c.HostOkS g →
    ∀ (s₀ : σ) (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val),
      ValTy.checkList c.exports[j].ty.params vs = true →
      ∀ b ∈ callBehaviours prof (answerHostS P g)
          (afterInstH P cs (c.afterFuncs P fun k => I.addrs.getD k 0) s₀) ⟨0⟩
          ⟨c.imports.length + j⟩ (vs.map toRefVal),
        IRObsIS (c.toComp.den (impSem P)) ⟨j, by simp [SimpleI.toComp]⟩ vs g s₀ b

/-- The call phase with imports answered by a stateful host, in components. -/
theorem callPhaseIS_of (P : Profile) (prof : ProfileKind) (c : SimpleI) (hc : c.Good)
    (hff : c.FloatFree) (har : c.Arity) (I : Silmaril.Wasm.Game.ScalarInstance) (hI : c.mod.IsInst I)
    (cs : (core3P P).Store (CanonHost (core3P P))) (hcs : Store.mapH trampIdx cs = I.store)
    (htr : c.TrampOk cs) (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ))
    (hg : c.HostOkS g) (s₀ : σ)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) :
    ∀ b ∈ callBehaviours prof (answerHostS P g)
        (afterInstH P cs (SimpleI.afterFuncs P (fun k => I.addrs.getD k 0) c) s₀) ⟨0⟩
        ⟨c.imports.length + j⟩ (vs.map toRefVal),
      IRObsIS (c.toComp.den (impSem P)) ⟨j, by simp [SimpleI.toComp]⟩ vs g s₀ b := by
  have hx : c.exports[j] ∈ c.exports := List.getElem_mem j.isLt
  obtain ⟨nm, hcore⟩ := hc.core _ hx
  have hk : c.exports[j].core < c.mod.exports.length := (List.getElem?_eq_some_iff.mp hcore).1
  have hflat : c.mod.exports[c.exports[j].core] = (nm, c.exports[j].ty.flat) :=
    (List.getElem?_eq_some_iff.mp hcore).2
  have hxs : (lowerArgs c.exports[j].ty.params vs).map (·.type) =
      c.mod.exports[c.exports[j].core].2.params := by
    rw [hflat]
    exact lowerList_types _ _ hvs
  obtain ⟨f, hf₁, hf₂, hft⟩ := typedCallI hI hk hxs
  have C : CallCtxI P c I cs j vs f (I.addrs.getD c.exports[j].core 0) :=
    { start := ⟨hc, hI, hcs, by rw [← hf₁]; rfl, hf₂⟩, typed := hvs, core := hf₁
      ty := by rw [hft, hflat] }
  obtain ⟨hmax, hmaxr, hres⟩ := har.1 _ hx
  obtain ⟨hpf, hrf⟩ := hff.1 _ hx
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat, hhost⟩ := call_atA (g := g) prof cs
    (SimpleI.afterFuncs P (fun k => I.addrs.getD k 0) c) s₀ (c.imports.length + j) _ c.exports[j]
    vs hpf hvs hmax hres hmaxr hrf (afterFuncs_lifted _ j.isLt)
  have hok : CalloutsOk g (SiteI c) M₀.store th M₀.host
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
        (I.addrs.getD c.exports[j].core 0) (lowerArgs c.exports[j].ty.params vs)) :=
    calloutsOk_of C.start hff har htr hg ⟨hat.funcs, hat.entry, hat.inst⟩
  intro b hb
  rcases hb with ⟨m', out, hcalls, rfl⟩ | ⟨rfl, -⟩
  · show IRObsIS _ _ vs g s₀ (Outcome.ofCall out)
    obtain ⟨tr, hs, hev, -, ho⟩ := hcalls
    obtain ⟨m₂, s, r⟩ := Steps.cons_iff.mp hs
    have r₀ : Steps prof (answerHostS P g).hr (DA P g) (invokedCfgH P cs
        (SimpleI.afterFuncs P (fun k => I.addrs.getD k 0) c) s₀ (c.imports.length + j)
          (vs.map toRefVal)) tr m' :=
      invoke_invA s ▸ r
    rcases hpre.inv r₀ with hl | ⟨tr'', e, r'⟩
    · exact absurd ho (hl.not_holds _ _)
    have r'' : Steps prof (answerHostS P g).hr (DA P g) (coreCfg (extSC (withH M₀ M₀.host) [] [])
        th K segs rest (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
          (I.addrs.getD c.exports[j].core 0) (lowerArgs c.exports[j].ty.params vs))) tr'' m' :=
      coreCfg_start hat ▸ r'
    have hend : CoreEnd (prof := prof) g (SiteI c) M₀ M₀.host th K segs rest
        (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD c.exports[j].core 0)
          (lowerArgs c.exports[j].ty.params vs)) tr'' m' out :=
      segs_inv hat.lock tr''.length _ _ [] [] tr'' m' out le_rfl hok r'' ho
    have hev' : ∀ ev, Label.host ev ∈ tr'' → CallHostEvent ⟨0⟩ ev :=
      fun ev hm => hev ev (e ▸ List.mem_append_right _ hm)
    rw [← hhost]
    exact obs_of_end C hat hend hev' ho
  · trivial

/-- **The call phase with imports answered by a stateful host** (proved). -/
theorem callPhaseIS : CallPhaseIS :=
  fun P prof c hc hff har I hI cs hcs htr _ g hg s₀ j vs hvs =>
    callPhaseIS_of P prof c hc hff har I hI cs hcs htr g hg s₀ j vs hvs

/-! ## Stateless hosts -/

/-- A component import call answered by the stateless `statelessG g₀` is answered by `g₀`. -/
theorem hostAnswers_of_step {τ : Type} {g₀ : HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val)} {n : Nat}
    {s s' : τ} {d : Σ _ : (sigN n).Op, Option Payload}
    (hd : HostAnswersS (statelessG g₀) s d s') : HostAnswers g₀ d := by
  obtain ⟨k, ws, h1, h2⟩ := hd
  refine ⟨k, ws, h1, ?_⟩
  obtain ⟨op, R⟩ := d
  match R, h2 with
  | none, h2 => simpa [statelessG] using h2.1
  | some (.vals us), h2 =>
    simp only [statelessG, Option.map_eq_some_iff, Prod.mk.injEq] at h2
    obtain ⟨rs, hrs, hrs', -⟩ := h2
    rw [hrs, hrs']
  | some (.flat _), h2 => exact h2.elim

/-- Component import calls answered by the stateless `statelessG g₀` are answered by `g₀`. -/
theorem hostAnswers_of_run {τ : Type} {g₀ : HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val)} {n : Nat}
    {s s' : τ} {ds : List (Σ _ : (sigN n).Op, Option Payload)}
    (h : HostRun (statelessG g₀) s ds s') : ∀ d ∈ ds, HostAnswers g₀ d := by
  induction h with
  | nil => exact fun d hd => nomatch hd
  | cons hd _ ih =>
    intro d' hd'
    rcases List.mem_cons.mp hd' with rfl | hd'
    · exact hostAnswers_of_step hd
    · exact ih d' hd'

/-- A stateless host answering in the IR's types, as a stateful one. -/
theorem hostOkS_stateless {τ : Type} {c : SimpleI} {g₀ : HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val)}
    (hg : c.HostOk g₀) : c.HostOkS (σ := τ) (statelessG g₀) := by
  intro s k hk ws rs s' h
  simp only [statelessG, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨rs', hrs, rfl, -⟩ := h
  exact hg k hk ws rs' hrs

/-- `IRObsIS` of the stateless `statelessG g₀` is `IRObsI` of `g₀`. -/
theorem irObsI_of_S {n m : Nat} {σI : Silmaril.Games.Strategy (sigN n) (sigN m)} {j : Fin m}
    {vs : List Silmaril.Wasm.Component.Val} {g₀ : HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val)}
    {b : Silmaril.Wasm.Component.Reference.Outcome} (h : IRObsIS σI j vs (statelessG g₀) () b) :
    IRObsI σI j vs g₀ b := by
  cases b with
  | returns r =>
    cases r with
    | none => trivial
    | some rs =>
      obtain ⟨ws, ds, _, hrs, hrun, hp⟩ := h
      exact ⟨ws, ds, hrs, hostAnswers_of_run hrun, hp⟩
  | traps =>
    obtain ⟨ds, _, hrun, hp⟩ := h
    exact ⟨ds, hostAnswers_of_run hrun, hp⟩
  | deadlocks => trivial
  | diverges => trivial

/-- **The call phase with imports**: from the configuration after instantiation, every
behaviour of a call of export `j` of `c` on the images of well-typed values, over `core3P P`
with the host answering by `g`, is what the IR denotation over `impSem P` must exhibit. -/
def CallPhaseI : Prop :=
  ∀ (P : Profile) (prof : ProfileKind) (c : SimpleI), c.Good → c.FloatFree → c.Arity →
    ∀ (I : Silmaril.Wasm.Game.ScalarInstance), c.mod.IsInst I →
    ∀ (cs : (core3P P).Store (CanonHost (core3P P))), Store.mapH trampIdx cs = I.store →
      c.TrampOk cs →
    ∀ (g : HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val)), c.HostOk g →
    ∀ (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val),
      ValTy.checkList c.exports[j].ty.params vs = true →
      ∀ b ∈ callBehaviours prof (answerHost P g)
          (afterInst P cs (c.afterFuncs P fun k => I.addrs.getD k 0)) ⟨0⟩ ⟨c.imports.length + j⟩
          (vs.map toRefVal),
        IRObsI (c.toComp.den (impSem P)) ⟨j, by simp [SimpleI.toComp]⟩ vs g b

/-- **The call phase with imports** (proved, from `callPhaseIS`). -/
theorem callPhaseI : CallPhaseI :=
  fun P prof c hc hff har I hI cs hcs htr g hg j vs hvs b hb =>
    irObsI_of_S (callPhaseIS_of P prof c hc hff har I hI cs hcs htr (statelessG g)
      (hostOkS_stateless hg) () j vs hvs b hb)

end Silmaril.Proofs.Wasm.Component.Reference
