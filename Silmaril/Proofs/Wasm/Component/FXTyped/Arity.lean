module

public import Silmaril.Proofs.Wasm.Component.FXTyped.Enter
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# Result arity of calls of FX functions in the engine with suspension

`StepFX'` is untyped, but the FX rule `invoke` puts the body of an FX function `F` in a frame of
arity `F.nresults`, and the frame rules return exactly that many values. This module follows a
call of an FX function in `fxEV P` from its invocation and shows that a returned call returns
`F.nresults` values, whatever FX code runs (`suspend`, `resume`, `switch`, `cont.bind`,
`resume_throw`):

* `FXAt s a F ft`: the store holds the FX function `F` at `a`, as `allocFX` allocates it
  (a host function of flat type `ft` with code `fx F`, `F.nparams = |ft.params|`);
* `decompose?_invokeFX`: its invocation is a host-call redex;
* `ArInv`: every thread reached from the invocation is the invocation itself, or an FX thread
  in a host-free store whose code is `FrameOut F.nresults` (`arInv_step`: the Core thread can
  only enter `F`, by `step_enter`; an FX thread at the outer frame steps to `FrameOut` by
  `stepFX'_frame`; quiet code does not step, `stepFX'_not_quiet`; nothing parks in a host-free
  store);
* **`fx_results_length`**: a returned call of the FX function returns `F.nresults` values.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXTyped

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded (decompose? Thread)
open Silmaril.Wasm.Models.FX (AdminFX ContFX ConfigFX FuncFX InstrFX cvals cthrowing ofCore)
open Silmaril.Wasm.Models.FXV (StepFX' FVal fvals)
open Silmaril.Wasm.Component.FXEngine (FXCode fxOf noHostFX fxResult liftR)
open Silmaril.Wasm.Component.FXEngineV (fxEV ThreadV InternalV statusV)
open Silmaril.Proofs.Wasm.Component.FXRefV (HostFree)
open Silmaril.Wasm.Component.Engine.CoreEngine (Steps)
open Silmaril.Wasm.Component (Flat)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- **The FX function `F` of flat type `ft` at address `a`**, as `allocFX` allocates it. -/
def FXAt (s : Store (FXCode H)) (a : Nat) (F : FuncFX) (ft : V1.FuncType) : Prop :=
  s.funcs[a]? = some ⟨SingleThreaded.ofFlatType ft, {}, .host (.fx F)⟩ ∧
    F.nparams = ft.params.length

/-- The code of the invocation of `a` on `args`. -/
theorem invoke_code {s : Store (FXCode H)} {a : Nat} {F : FuncFX} {ft : V1.FuncType}
    (hA : FXAt s a F ft) (args : List Val) :
    (invoke s a args).code =
      vals args ++ [.ref (.func a), .callRefType (SingleThreaded.ofFlatType ft)] := by
  simp [invoke, hA.1]

/-- **The invocation of an FX function is a host-call redex.** -/
theorem decompose?_invokeFX {s : Store (FXCode H)} {a : Nat} {F : FuncFX} {ft : V1.FuncType}
    (hA : FXAt s a F ft) {args : List Val} (hn : args.length = ft.params.length) :
    decompose? s (vals args ++ [.ref (.func a), .callRefType (SingleThreaded.ofFlatType ft)]) =
      some (.top [] [], a, .fx F, args) := by
  have har : SingleThreaded.hostArity? s a = some (.fx F, args.length) := by
    simp [SingleThreaded.hostArity?, hA.1, SingleThreaded.funcType?_ofFlatType, hn]
  have e : vals args ++ [.ref (.func a), .callRefType (SingleThreaded.ofFlatType ft)] =
      vals (args ++ [.ref (.func a)]) ++ (Admin.callRefType (SingleThreaded.ofFlatType ft)) :: [] := by
    simp [vals, Val.toAdmin]
  rw [e, SingleThreaded.decompose?_top (n := args.length) (by rfl) har le_rfl]
  simp

/-! ## The invariant -/

/-- **The threads reached from the invocation of the FX function `a` on `xs`**: the invocation
itself, or an FX thread in a host-free store at `FrameOut n`. -/
def ArInv (s₀ : Store (FXCode H)) (a : Nat) (xs : List Flat) (n : Nat)
    (y : Store (FXCode H) × ThreadV H) : Prop :=
  y = (s₀, .core (Thread.invokeFlat a xs)) ∨
    (HostFree y.1 ∧ ∃ K f code, y.2 = .fx K f code ∧ FrameOut n code)

/-- The configuration of the invocation thread. -/
theorem config_invokeFlat (s : Store (FXCode H)) (a : Nat) (xs : List Flat) :
    (Thread.invokeFlat a xs).config s = invoke s a (xs.map SingleThreaded.ofFlat) := rfl

/-- The invocation code of an FX function, as Core code of the thread. -/
theorem invokeFlat_code {s₀ : Store (FXCode H)} {a : Nat} {F : FuncFX} {ft : V1.FuncType}
    (hA : FXAt s₀ a F ft) (xs : List Flat) :
    ((Thread.invokeFlat a xs).config s₀).code = vals (xs.map SingleThreaded.ofFlat) ++
      [.ref (.func a), .callRefType (SingleThreaded.ofFlatType ft)] :=
  invoke_code hA _

/-- The invocation thread of an FX function takes no Core step. -/
theorem no_internalP_invoke {s₀ : Store (FXCode H)} {a : Nat} {F : FuncFX} {ft : V1.FuncType}
    (hA : FXAt s₀ a F ft) {xs : List Flat} (hxs : xs.length = ft.params.length)
    {y : Store (FXCode H) × Thread} (h : Silmaril.Wasm.Game.InternalP P (s₀, Thread.invokeFlat a xs) y) :
    False := by
  obtain ⟨f', code', -, hstep⟩ := h
  have hnr : decompose? s₀ (vals [] ++ ((Thread.invokeFlat a xs).config s₀).code ++ []) = none :=
    Silmaril.Wasm.SingleThreaded.Step.noRedex hstep [] []
  have hd := decompose?_invokeFX hA (args := xs.map SingleThreaded.ofFlat)
    (by rw [List.length_map, hxs])
  rw [invokeFlat_code hA] at hnr
  simp only [show vals ([] : List Val) = [] from rfl, List.nil_append, List.append_nil, hd] at hnr
  cases hnr

/-- The FX step from the invocation thread is the entry into the FX function. -/
theorem enter_eq {s₀ : Store (FXCode H)} {a : Nat} {F : FuncFX} {ft : V1.FuncType}
    (hA : FXAt s₀ a F ft) {xs : List Flat} (hxs : xs.length = ft.params.length)
    {y : ConfigFX (FXCode H)}
    (h : StepFX' P (noHostFX H) fxOf (ofCore ((Thread.invokeFlat a xs).config s₀)) y) :
    y = ⟨s₀, [], {}, [enterCode F (xs.map SingleThreaded.ofFlat)]⟩ := by
  have hn : (xs.map SingleThreaded.ofFlat).length = ft.params.length := by
    rw [List.length_map, hxs]
  have hcfg : ofCore ((Thread.invokeFlat a xs).config s₀) =
      ⟨s₀, [], {}, (vals (xs.map SingleThreaded.ofFlat) ++
        [Admin.ref (.func a), Admin.callRefType (SingleThreaded.ofFlatType ft)]).map
          AdminFX.core⟩ := by
    rw [← invokeFlat_code hA]
    rfl
  rw [hcfg] at h
  exact step_enter (P := P) (c := .callRefType (SingleThreaded.ofFlatType ft)) trivial hA.1
    rfl rfl (hn.trans hA.2.symm) (by rw [decompose?_invokeFX hA hn]; simp) h

/-- The step from the invocation thread enters the FX function. -/
theorem arInv_core {s₀ : Store (FXCode H)} (hs : HostFree s₀) {a : Nat} {F : FuncFX}
    {ft : V1.FuncType} (hA : FXAt s₀ a F ft) {xs : List Flat} (hxs : xs.length = ft.params.length)
    {z : Store (FXCode H) × ThreadV H}
    (h : InternalV P (s₀, .core (Thread.invokeFlat a xs)) z) : ArInv s₀ a xs F.nresults z := by
  rcases h with ⟨t', -, hP⟩ | ⟨-, K, f, code, hz, hstep⟩
  · exact (no_internalP_invoke hA hxs hP).elim
  · have e : (⟨z.1, K, f, code⟩ : ConfigFX (FXCode H)) =
        ⟨s₀, [], {}, [enterCode F (xs.map SingleThreaded.ofFlat)]⟩ := enter_eq hA hxs hstep
    have e1 : z.1 = s₀ := congrArg ConfigFX.store e
    have e4 : code = [enterCode F (xs.map SingleThreaded.ofFlat)] := congrArg ConfigFX.code e
    exact Or.inr ⟨e1 ▸ hs, K, f, code, hz, Or.inl ⟨_, _, e4⟩⟩

/-- Quiet `FrameOut` code. -/
theorem quiet_of_frameOut {n : Nat} {code : List AdminFX} (h : FrameOut n code)
    (hf : ∀ fi es, code ≠ [.frame n fi es]) : QuietFX code := by
  rcases h with ⟨fi, es, e⟩ | ⟨vs, rfl, -⟩ | rfl | ⟨a, rfl⟩
  · exact (hf fi es e).elim
  · exact Or.inl (all_isFV_fvals vs)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inr ⟨a, rfl⟩))

/-- A step of an FX thread at `FrameOut n` reaches `FrameOut n`. -/
theorem frameOut_step {s s' : Store (FXCode H)} {K K' : List (Option ContFX)} {f f' : Frame}
    {code code' : List AdminFX} {n : Nat} (h : FrameOut n code)
    (hstep : StepFX' P (noHostFX H) fxOf ⟨s, K, f, code⟩ ⟨s', K', f', code'⟩) :
    FrameOut n code' := by
  by_cases hf : ∃ fi es, code = [.frame n fi es]
  · obtain ⟨fi, es, e⟩ := hf
    exact stepFX'_frame hstep e
  · push Not at hf
    exact (stepFX'_not_quiet hstep (quiet_of_frameOut h hf)).elim

/-- **The invariant is kept by engine steps.** -/
theorem arInv_step {s₀ : Store (FXCode H)} (hs : HostFree s₀) {a : Nat} {F : FuncFX}
    {ft : V1.FuncType} (hA : FXAt s₀ a F ft) {xs : List Flat} (hxs : xs.length = ft.params.length)
    {y z : Store (FXCode H) × ThreadV H} (hy : ArInv s₀ a xs F.nresults y)
    (h : InternalV P y z) : ArInv s₀ a xs F.nresults z := by
  rcases hy with rfl | ⟨hsy, K, f, code, hy2, hout⟩
  · exact arInv_core hs hA hxs h
  · obtain ⟨s, t⟩ := y
    dsimp only at hy2 hsy
    subst hy2
    rcases h with ⟨K', f', code', hz, hstep⟩ | ⟨-, E, cs, Ec, b, hh, args, -, hd, -⟩
    · refine Or.inr ⟨?_, K', f', code', hz, frameOut_step hout hstep⟩
      exact Silmaril.Proofs.Wasm.Component.FXRefV.hostFree_of_funcs hsy
        (Silmaril.Proofs.Wasm.Component.FXRefV.stepFX'_funcs hstep)
    · exact (Silmaril.Proofs.Wasm.Component.FXRefV.decompose?_hostFree hsy hd).elim

/-- The invariant along runs. -/
theorem arInv_reach {s₀ : Store (FXCode H)} (hs : HostFree s₀) {a : Nat} {F : FuncFX}
    {ft : V1.FuncType} (hA : FXAt s₀ a F ft) {xs : List Flat} (hxs : xs.length = ft.params.length)
    {y : Store (FXCode H) × ThreadV H}
    (run : Steps (fxEV P) (s₀, (fxEV P).invoke a xs) y) : ArInv s₀ a xs F.nresults y := by
  induction run with
  | refl => exact Or.inl rfl
  | tail _ hstep ih => exact arInv_step hs hA hxs ih hstep

/-! ## Returned values -/

theorem mapM_length {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM g = some r → r.length = l.length
  | [], r, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | x :: l, r, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, -, r', hr', rfl⟩ := h
    simp [mapM_length hr']

/-- Core values at `FrameOut n` are `n` values. -/
theorem cvals_frameOut {n : Nat} {vs : List Val} (h : FrameOut n (cvals vs)) : vs.length = n := by
  rcases h with ⟨fi, es, e⟩ | ⟨ws, e, hl⟩ | e | ⟨b, e⟩
  · have hm : AdminFX.frame n fi es ∈ cvals vs := by rw [e]; simp
    simp [cvals, vals] at hm
  · have := congrArg List.length e
    simp only [cvals, vals, fvals, List.length_map] at this
    omega
  · have hm : AdminFX.core .trap ∈ cvals vs := by rw [e]; simp
    simp only [cvals, List.mem_map] at hm
    obtain ⟨x, hx, hx'⟩ := hm
    cases hx'
    exact (Silmaril.Wasm.SingleThreaded.Det.mem_vals hx rfl).elim
  · have hm : AdminFX.core (.plain .throwRef) ∈ cvals vs := by rw [e]; simp [cthrowing, throwing]
    simp only [cvals, List.mem_map] at hm
    obtain ⟨x, hx, hx'⟩ := hm
    cases hx'
    exact (Silmaril.Wasm.SingleThreaded.Det.mem_vals hx rfl).elim

/-- The status of an FX thread whose `fxResult` returns values. -/
theorem fxResult_values {code : List AdminFX} {ys : List Flat}
    (h : (fxResult code : Silmaril.Wasm.Component.Engine.Status H) = .returned (.values ys)) :
    ∃ vs, code = cvals vs ∧ vs.mapM SingleThreaded.toFlat? = some ys := by
  unfold fxResult at h
  split_ifs at h with h1
  · refine ⟨h1.choose, h1.choose_spec, ?_⟩
    cases hm : h1.choose.mapM SingleThreaded.toFlat? with
    | none => simp [hm] at h
    | some fvs =>
      simp only [hm, Silmaril.Wasm.Component.Engine.Status.returned.injEq,
        Silmaril.Wasm.Component.Engine.CallResult.values.injEq] at h
      rw [h]
  all_goals cases h

/-- The invocation code of an FX function is not final. -/
theorem invokeFlat_not_final {s₀ : Store (FXCode H)} {a : Nat} {F : FuncFX} {ft : V1.FuncType}
    (hA : FXAt s₀ a F ft) (xs : List Flat) :
    (¬ ∃ vs, ((Thread.invokeFlat a xs).config s₀).code = vals vs) ∧
      ¬ ((Thread.invokeFlat a xs).config s₀).code = [.trap] ∧
      ¬ ∃ b, ((Thread.invokeFlat a xs).config s₀).code = throwing b := by
  have hlast : ((Thread.invokeFlat a xs).config s₀).code.getLast? =
      some (.callRefType (SingleThreaded.ofFlatType ft)) := by
    rw [invokeFlat_code hA]
    simp
  refine ⟨fun ⟨vs, e⟩ => ?_, fun e => ?_, fun ⟨b, e⟩ => ?_⟩
  rotate_left
  · rw [e] at hlast
    cases hlast
  · rw [e] at hlast
    cases hlast
  have hm : Admin.callRefType (SingleThreaded.ofFlatType ft) ∈ vals vs := by
    rw [← e, invokeFlat_code hA]
    simp
  exact Silmaril.Wasm.SingleThreaded.Det.mem_vals hm rfl

/-- **The invocation of an FX function is a callout of it.** -/
theorem statusP_invokeFX {s₀ : Store (FXCode H)} {a : Nat} {F : FuncFX} {ft : V1.FuncType}
    (hA : FXAt s₀ a F ft) {xs : List Flat} (hxs : xs.length = ft.params.length) :
    Silmaril.Wasm.Game.statusP P s₀ (Thread.invokeFlat a xs) =
      .callout (.fx F) (xs.map SingleThreaded.ofFlat) := by
  have hd := decompose?_invokeFX hA (args := xs.map SingleThreaded.ofFlat)
    (by rw [List.length_map, hxs])
  obtain ⟨n₁, n₂, n₃⟩ := invokeFlat_not_final hA xs
  exact Silmaril.Proofs.Wasm.Component.FXRefV.statusP_of_decompose n₁ n₂ n₃
    (by rw [invokeFlat_code hA]; exact hd)

/-- The invocation thread is not returned. -/
theorem statusV_invoke_ne {s₀ : Store (FXCode H)} {a : Nat} {F : FuncFX} {ft : V1.FuncType}
    (hA : FXAt s₀ a F ft) {xs : List Flat} (hxs : xs.length = ft.params.length)
    {R : Silmaril.Wasm.Component.Engine.CallResult} :
    statusV P s₀ (.core (Thread.invokeFlat a xs)) ≠ .returned R := by
  intro e
  simp only [statusV, statusP_invokeFX hA hxs, liftR] at e
  cases e

/-- **The entry step**: the invocation thread of an FX function becomes the FX thread at its
outermost frame. -/
theorem internalV_enter {s : Store (FXCode H)} {a : Nat} {F : FuncFX} {ft : V1.FuncType}
    (hA : FXAt s a F ft) {xs : List Flat} (hxs : xs.length = ft.params.length) :
    InternalV P (s, .core (Thread.invokeFlat a xs))
      (s, .fx [] {} [enterCode F (xs.map SingleThreaded.ofFlat)]) := by
  have hcfg : ofCore ((Thread.invokeFlat a xs).config s) =
      ⟨s, [], {}, cvals (xs.map SingleThreaded.ofFlat) ++
        [.core (.ref (.func a)), .core (.callRefType (SingleThreaded.ofFlatType ft))]⟩ := by
    rw [config_invokeFlat]
    show (⟨_, [], _, (invoke s a (xs.map SingleThreaded.ofFlat)).code.map AdminFX.core⟩ :
      ConfigFX (FXCode H)) = _
    rw [invoke_code hA]
    simp [cvals, invoke]
  refine Or.inr ⟨⟨F, _, statusP_invokeFX hA hxs⟩, [], {}, _, rfl, ?_⟩
  rw [hcfg]
  exact StepFX'.invoke (c := .callRefType (SingleThreaded.ofFlatType ft)) trivial hA.1 rfl rfl
    (by rw [List.length_map, hxs, hA.2])

/-- **A returned call of an FX function returns `F.nresults` values.** -/
theorem fx_results_length {s₀ : Store (FXCode H)} (hs : HostFree s₀) {a : Nat} {F : FuncFX}
    {ft : V1.FuncType} (hA : FXAt s₀ a F ft) {xs : List Flat} (hxs : xs.length = ft.params.length)
    {s' : Store (FXCode H)} {t' : ThreadV H}
    (run : Steps (fxEV P) (s₀, (fxEV P).invoke a xs) (s', t')) {ys : List Flat}
    (hst : (fxEV P).status s' t' = .returned (.values ys)) : ys.length = F.nresults := by
  rcases arInv_reach hs hA hxs run with e | ⟨-, K, f, code, ht, hout⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact (statusV_invoke_ne hA hxs hst).elim
  · dsimp only at ht
    subst ht
    have hst' : statusV P s' (.fx K f code) = .returned (.values ys) := hst
    simp only [statusV] at hst'
    split_ifs at hst' with hex
    obtain ⟨vs, rfl, hm⟩ := fxResult_values hst'
    rw [mapM_length hm]
    exact cvals_frameOut hout

end Silmaril.Proofs.Wasm.Component.FXTyped
