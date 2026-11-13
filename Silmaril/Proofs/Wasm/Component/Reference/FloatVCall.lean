module

public import Silmaril.Proofs.Wasm.Component.Reference.FloatVPath
public import Silmaril.Proofs.Wasm.Component.Reference.FloatCall

/-!
# The call phase with floats

`floatCallPhaseV : FloatCallPhaseV` (`FloatCall` with floats at every type, variant payloads
included; no hypothesis on the types): every behaviour of calling function `j` from
`afterInst` on the reference
images of well-typed IR values `vs` is an outcome of `exportSpecFV` on some admissible argument
list `vs'` (`NanAtVList prof ts vs vs'`, the NaN lowerings the component choice profile `prof`
admits), where `exportSpecFV` is `exportSpec` with the returned values canonicalised
(`liftOutcomeFV`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower FuncTy)

/-! ## The specification with canonicalised results -/

/-- `liftOutcome` with the returned values canonicalised. -/
def liftOutcomeFV (ft : FuncTy) : Option (List Flat) → Silmaril.Wasm.Component.Reference.Outcome
  | some ys =>
    match liftArgs ft.results ys with
    | some ws => .returns (some ((canonAtVList ft.results ws).map toRefVal))
    | none => .traps
  | none => .traps

/-- `exportSpec` with the returned values canonicalised. -/
def exportSpecFV (P : Profile) (c : Simple) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) : Set Silmaril.Wasm.Component.Reference.Outcome :=
  match checkLower x.ty.params vs with
  | none => {.traps}
  | some xs =>
    {b | ∃ r ∈ coreOut P c.mod x.core xs, b = liftOutcomeFV x.ty r} ∪
      {b | b = .diverges ∧ coreDiverges P c.mod x.core xs}

/-- **The call phase with floats.** -/
def FloatCallPhaseV : Prop :=
  ∀ (P : Profile) (prof : ProfileKind) (c : Simple), c.Good → c.Arity →
    ∀ (I : Silmaril.Wasm.Game.ScalarInstance) (cs : (core3P P).Store (CanonHost (core3P P))),
      c.mod.IsInst I → Store.mapH (fun _ => 0) cs = I.store →
      ∀ (j : Nat) (hj : j < c.exports.length) (vs : List Silmaril.Wasm.Component.Val),
        ValTy.checkList c.exports[j].ty.params vs = true →
        callBehaviours prof (refHost P)
            (afterInst P cs (liftedFuncs P (fun k => I.addrs.getD k 0) c)) ⟨0⟩ ⟨j⟩
            (vs.map toRefVal) ⊆
          {b | ∃ vs', NanAtVList prof c.exports[j].ty.params vs vs' ∧
            ValTy.checkList c.exports[j].ty.params vs' = true ∧
            b ∈ exportSpecFV P c c.exports[j] vs'}

/-! ## The branching run of a call -/

variable {P : Profile}

/-- The configurations running the core activation of an admissible argument list. -/
def QFV (prof : ProfileKind) (P : Profile) (cs : (core3P P).Store (CanonHost (core3P P)))
    (x : SimpleExport) (a : Nat) (vs : List Silmaril.Wasm.Component.Val)
    (m : Machine.Config (E3 P) Unit) : Prop :=
  ∃ vs' th K segs rest, NanAtVList prof x.ty.params vs vs' ∧
    ValTy.checkList x.ty.params vs' = true ∧
    CallAtFV prof P cs x a (lowerArgs x.ty.params vs') m th K segs rest

/-- **The branching run of a call with floats**: every run from the host's invocation stays
live until it reaches the core activation of an admissible argument list. -/
theorem call_trunV (prof : ProfileKind) (cs : (core3P P).Store (CanonHost (core3P P)))
    (fs : List (CFuncInst (core3P P))) (j a : Nat) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) (hck : ValTy.checkList x.ty.params vs = true)
    (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨0⟩)) :
    TRun prof (refHost P).hr (D P) (QFV prof P cs x a vs)
      (invokedCfg P cs fs j (vs.map toRefVal)) := by
  obtain ⟨Mℓ, th, cx, f, segs, rest, tr₁, hpre, hc, hl, hpost⟩ :=
    call_at_floatV prof cs fs j a x vs hres hmaxr hf
  have hc' : Mℓ.ctl = ⟨th, .prog (.op (S := Eff (E3 P) Unit) .get fun s =>
      lowerFlatTypes Limits.spec Quirks.none cx (ptrTypeIn s cx) (toRefVals vs)
        (toClosedList x.ty.params) >>= f), segs⟩ :: rest := by
    rw [hc, paramTypes_liftedFt, lowerFlatValues_float (max := ABI.maxFlatParams) _ _ _ hmax]
    rfl
  have hch := lowerFlatTypesV (E := E3 P) (σ := Unit) Limits.spec Quirks.none cx
    (ptrTypeIn Mℓ.store cx) prof x.ty.params vs hck
  have ht := ChoiceProg.trun (hr := (refHost P).hr) (dispatch := D P) hch
    { Mℓ with ctl := ⟨th, .prog (lowerFlatTypes Limits.spec Quirks.none cx (ptrTypeIn Mℓ.store cx)
      (toRefVals vs) (toClosedList x.ty.params) >>= f), segs⟩ :: rest } f th segs rest rfl hl
  refine TRun.of_lrun hpre (TRun.of_lrun (uniqueStep_get hc' hl) (ht.bind ?_))
  rintro m ⟨out, ⟨vs', hn, hck', rfl⟩, rfl⟩
  obtain ⟨M₀, th', K, segs', rest', hl₁, hat⟩ := hpost (lowerArgs x.ty.params vs')
  exact TRun.of_lrun hl₁ (.done ⟨vs', th', K, segs', rest', hn, hck', hat⟩)

/-! ## Outcomes -/

section Call

variable {prof : ProfileKind} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
  {cs : (core3P P).Store (CanonHost (core3P P))} {x : SimpleExport}
  {vs : List Silmaril.Wasm.Component.Val}

/-- The specification of a call with typed arguments. -/
theorem CallCtx.specFV (C : CallCtx P c I cs x vs) {b : Silmaril.Wasm.Component.Reference.Outcome}
    (h : ∃ r ∈ coreOut P c.mod x.core (lowerArgs x.ty.params vs), b = liftOutcomeFV x.ty r) :
    b ∈ exportSpecFV P c x vs := by
  have hl : checkLower x.ty.params vs = some (lowerArgs x.ty.params vs) := by
    unfold checkLower
    rw [ite_eq_left_iff.mpr (fun h => absurd C.typed h)]
  unfold exportSpecFV
  rw [hl]
  exact .inl h

/-- The specification of a divergent call with typed arguments. -/
theorem CallCtx.specF_divergesV (C : CallCtx P c I cs x vs)
    (h : coreDiverges P c.mod x.core (lowerArgs x.ty.params vs)) :
    .diverges ∈ exportSpecFV P c x vs := by
  have hl : checkLower x.ty.params vs = some (lowerArgs x.ty.params vs) := by
    unfold checkLower
    rw [ite_eq_left_iff.mpr (fun h => absurd C.typed h)]
  unfold exportSpecFV
  rw [hl]
  exact .inr ⟨rfl, h⟩

/-- **Calls after the core activation left it**, with floats. -/
theorem exit_specFV (C : CallCtx P c I cs x vs) {M₀ : Machine.Config (E3 P) Unit}
    {th : Option ThreadId} {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))}
    {segs : List (Seg (E3 P) Unit)} {rest : List (Activation (E3 P) Unit)}
    (hat : CallAtFV prof P cs x (I.addrs.getD x.core 0) (lowerArgs x.ty.params vs) M₀ th K segs
      rest) {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
      (I.addrs.getD x.core 0) (lowerArgs x.ty.params vs)) y)
    {l : Label (E3 P) Unit} {m₁ m' : Machine.Config (E3 P) Unit} {tr : List (Label (E3 P) Unit)}
    {out : CallOutcome} (hx : CoreExit M₀ th K segs rest y l m₁)
    (hs : Steps prof (refHost P).hr (D P) m₁ tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨0⟩ ev)
    (ho : out.Holds (refHost P).hr ⟨0⟩ m') : Outcome.ofCall out ∈ exportSpecFV P c x vs := by
  obtain ⟨nm, hcore⟩ := C.core
  rcases hx with ⟨ys, hst, -, rfl⟩ | ⟨hst, -, rfl⟩ | ⟨h, args, hst⟩
  · obtain ⟨hout, hty⟩ := values_coreOut C.inst C.store rfl hcore C.lowered hy hst
    cases hl : liftArgs x.ty.results ys with
    | some ws =>
      rw [out_of_resolves (hat.ret y ys ws hty hl) hs hev ho]
      exact C.specFV ⟨_, hout, by simp only [Outcome.ofCall, liftOutcomeFV, hl]⟩
    | none =>
      rw [out_of_trapsNext (hat.trap y ys hty hl) hs ho]
      exact C.specFV ⟨_, hout, by simp only [Outcome.ofCall, liftOutcomeFV, hl]⟩
  · rw [steps_of_locked rfl rfl hs] at ho
    rw [holds_trapCfg ho]
    exact C.specFV ⟨_, trap_coreOut C.inst C.store rfl hy hst, rfl⟩
  · exact (no_callout C.inst C.store rfl hcore C.lowered hy hst).elim

/-- **Divergence after the core activation left it** is impossible. -/
theorem exit_not_divergesFV (C : CallCtx P c I cs x vs) {M₀ : Machine.Config (E3 P) Unit}
    {th : Option ThreadId} {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))}
    {segs : List (Seg (E3 P) Unit)} {rest : List (Activation (E3 P) Unit)}
    (hat : CallAtFV prof P cs x (I.addrs.getD x.core 0) (lowerArgs x.ty.params vs) M₀ th K segs
      rest) {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
      (I.addrs.getD x.core 0) (lowerArgs x.ty.params vs)) y)
    {l : Label (E3 P) Unit} {m₁ : Machine.Config (E3 P) Unit}
    (hx : CoreExit M₀ th K segs rest y l m₁) : ¬ Diverges prof (refHost P).hr (D P) m₁ := by
  obtain ⟨nm, hcore⟩ := C.core
  rcases hx with ⟨ys, hst, -, rfl⟩ | ⟨hst, -, rfl⟩ | ⟨h, args, hst⟩
  · obtain ⟨-, hty⟩ := values_coreOut C.inst C.store rfl hcore C.lowered hy hst
    cases hl : liftArgs x.ty.results ys with
    | some ws => exact resolves_not_diverges (hat.ret y ys ws hty hl)
    | none => exact trapsNext_not_diverges (hat.trap y ys hty hl)
  · exact not_diverges_trapCfg _
  · exact (no_callout C.inst C.store rfl hcore C.lowered hy hst).elim

/-- **Terminating runs from the core activation** follow the specification. -/
theorem core_calls_specFV (C : CallCtx P c I cs x vs) {M₀ : Machine.Config (E3 P) Unit}
    {th : Option ThreadId} {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))}
    {segs : List (Seg (E3 P) Unit)} {rest : List (Activation (E3 P) Unit)}
    (hat : CallAtFV prof P cs x (I.addrs.getD x.core 0) (lowerArgs x.ty.params vs) M₀ th K segs
      rest) {m' : Machine.Config (E3 P) Unit} {tr : List (Label (E3 P) Unit)} {out : CallOutcome}
    (r : Steps prof (refHost P).hr (D P) M₀ tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨0⟩ ev)
    (ho : out.Holds (refHost P).hr ⟨0⟩ m') : Outcome.ofCall out ∈ exportSpecFV P c x vs := by
  rw [eq_coreCfg hat.ctl, hat.core] at r
  rcases coreCfg_steps_inv r with ⟨y, -, rfl, -⟩ | ⟨y, pre, l, m₁, tr₂, hy, -, e', hx, r''⟩
  · have hl : Live (coreCfg M₀ th K segs rest y) := ⟨List.cons_ne_nil _ _, hat.lock⟩
    exact absurd ho (hl.not_holds _ _)
  · have hev' : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨0⟩ ev := fun ev hm =>
      hev ev (by rw [e']; exact List.mem_append_right _ (List.mem_cons_of_mem _ hm))
    exact exit_specFV C hat hy hx r'' hev' ho

/-- **Divergent runs from the core activation** diverge in the core. -/
theorem core_diverges_specFV (C : CallCtx P c I cs x vs) {M₀ : Machine.Config (E3 P) Unit}
    {th : Option ThreadId} {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))}
    {segs : List (Seg (E3 P) Unit)} {rest : List (Activation (E3 P) Unit)}
    (hat : CallAtFV prof P cs x (I.addrs.getD x.core 0) (lowerArgs x.ty.params vs) M₀ th K segs
      rest) (hd : Diverges prof (refHost P).hr (D P) M₀) :
    coreDiverges P c.mod x.core (lowerArgs x.ty.params vs) := by
  rw [eq_coreCfg hat.ctl, hat.core] at hd
  rcases coreCfg_diverges_inv hd with hi | ⟨y, l, m₁, hy, hx, hd'⟩
  · exact diverges_core C.inst C.store rfl hi
  · exact (exit_not_divergesFV C hat hy hx hd').elim

end Call

/-- The admissible outcomes of a call of export `x` on `vs`. -/
def FloatOutV (prof : ProfileKind) (P : Profile) (c : Simple) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) : Set Silmaril.Wasm.Component.Reference.Outcome :=
  {b | ∃ vs', NanAtVList prof x.ty.params vs vs' ∧ ValTy.checkList x.ty.params vs' = true ∧
    b ∈ exportSpecFV P c x vs'}

section Main

variable {prof : ProfileKind} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
  {cs : (core3P P).Store (CanonHost (core3P P))} {x : SimpleExport}
  {vs : List Silmaril.Wasm.Component.Val} {fs : List (CFuncInst (core3P P))} {j : Nat}

/-- **Terminating calls with floats.** -/
theorem calls_specFV (hI : c.mod.IsInst I) (hcs : Store.mapH (fun _ => 0) cs = I.store)
    (hcore : ∃ nm, c.mod.exports[x.core]? = some (nm, x.ty.flat))
    (ht : TRun prof (refHost P).hr (D P) (QFV prof P cs x (I.addrs.getD x.core 0) vs)
      (invokedCfg P cs fs j (vs.map toRefVal)))
    {m' : Machine.Config (E3 P) Unit} {out : CallOutcome}
    (hcalls : Calls prof (refHost P).hr (D P) (afterInst P cs fs) ⟨0⟩ ⟨j⟩ (vs.map toRefVal) m'
      out) : Outcome.ofCall out ∈ FloatOutV prof P c x vs := by
  obtain ⟨tr, hs, hev, -, ho⟩ := hcalls
  obtain ⟨m₂, s, r⟩ := Steps.cons_iff.mp hs
  rw [invoke_inv s] at r
  rcases ht.inv r with hl | ⟨mq, tr₁, tr₂, ⟨vs', th, K, segs, rest, hn, hck, hat⟩, e, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  have C : CallCtx P c I cs x vs' := ⟨hI, hcs, hcore, hck⟩
  have hev' : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨0⟩ ev :=
    fun ev hm => hev ev (by rw [e]; exact List.mem_append_right _ hm)
  exact ⟨vs', hn, hck, core_calls_specFV C hat r' hev' ho⟩

/-- **Divergent calls with floats.** -/
theorem diverges_specFV (hI : c.mod.IsInst I) (hcs : Store.mapH (fun _ => 0) cs = I.store)
    (hcore : ∃ nm, c.mod.exports[x.core]? = some (nm, x.ty.flat))
    (ht : TRun prof (refHost P).hr (D P) (QFV prof P cs x (I.addrs.getD x.core 0) vs)
      (invokedCfg P cs fs j (vs.map toRefVal)))
    (hd : CallDiverges prof (refHost P).hr (D P) (afterInst P cs fs) ⟨0⟩ ⟨j⟩ (vs.map toRefVal)) :
    .diverges ∈ FloatOutV prof P c x vs := by
  obtain ⟨m₂, s, hd⟩ := hd
  rw [invoke_inv s] at hd
  obtain ⟨mq, ⟨vs', th, K, segs, rest, hn, hck, hat⟩, hd'⟩ := ht.diverges hd
  have C : CallCtx P c I cs x vs' := ⟨hI, hcs, hcore, hck⟩
  exact ⟨vs', hn, hck, C.specF_divergesV (core_diverges_specFV C hat hd')⟩

end Main

/-- **The call phase with floats.** -/
theorem floatCallPhaseV : FloatCallPhaseV := by
  intro P prof c hc ha I cs hI hcs j hj vs hvs b hb
  have hx : c.exports[j] ∈ c.exports := List.getElem_mem hj
  obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
  have ht := call_trunV prof cs _ j _ c.exports[j] vs hvs hmax hres hmaxr
    (liftedFuncs_get? c (fun k => I.addrs.getD k 0) hj)
  rcases hb with ⟨m', out, hcalls, rfl⟩ | ⟨rfl, hd⟩
  · exact calls_specFV hI hcs (hc.core _ hx) ht hcalls
  · exact diverges_specFV hI hcs (hc.core _ hx) ht hd

end Silmaril.Proofs.Wasm.Component.Reference
