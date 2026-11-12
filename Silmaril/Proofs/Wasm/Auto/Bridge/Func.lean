module

public import Silmaril.Proofs.Wasm.Auto.Bridge.Exec
public import Silmaril.Proofs.Wasm.Auto.Bridge.Beh
public import Silmaril.Wasm.Verify.Check.Thms
public import Silmaril.Wasm.Execution.Core.Typing.Store

/-!
# Function summaries: total specifications and behaviour sets

`tfspec_of_sumOf`: a function instance with a summary (`sumOf`) has the total specification
"called on typed arguments `vs` from the store `s₀`, it returns `fnOut F vs`" at every profile
and host relation. `behaviours_of_fnSum`: for function export `j` of a module with a summary
(`fnSum?`), the behaviour set of every accepted invocation is `{returns (fnOut F vs)}`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Bridge

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Post)
open Silmaril.Wasm.Game (ScalarType ScalarInstance FnType)
open Silmaril.Wasm.Verify (instance? instOf isInstance_of_instance?)
open Silmaril.Wasm.Auto.Front (addrOf)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Lists -/

theorem mapM_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.length = l.length
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, -, bs, hbs, rfl⟩ := h
    simp [mapM_length hbs]

theorem typedVals_nil : TypedVals [] [] := ⟨rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

theorem typedVals_cons {t : IntType} {ts : List IntType} {v : Val} {vs : List Val}
    (hv : ∃ x : BitVec t.width, v = .num ⟨.int t, x⟩) (h : TypedVals ts vs) :
    TypedVals (t :: ts) (v :: vs) := by
  obtain ⟨hl, hi⟩ := h
  refine ⟨by simp [hl], fun i hlt => ?_⟩
  cases i with
  | zero => simpa using hv
  | succ i => simpa using hi i (by simpa using hlt)

theorem valOk_int {s : Store H} {v : Val} {t : IntType} (h : ValOk s v (.num (.int t))) :
    ∃ x : BitVec t.width, v = .num ⟨.int t, x⟩ := by
  generalize hT : (Ty.num (.int t) : CValType) = T at h
  cases h with
  | num nv =>
    obtain ⟨ty, x⟩ := nv
    injection hT with hty
    subst hty
    exact ⟨x, rfl⟩
  | vec b => cases hT
  | ref _ => cases hT

/-- Values of the closed types of integer scalar types are typed. -/
theorem typedVals_of_forall₂ {s : Store H} :
    ∀ {ps : List ScalarType} {ts : List IntType} {vs : List Val},
      ps.mapM scalarInt? = some ts →
      List.Forall₂ (ValOk s) vs (ps.map ScalarType.toC) → TypedVals ts vs
  | [], ts, vs, h, hf => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    cases hf
    exact typedVals_nil
  | p :: ps, ts, vs, h, hf => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨t, ht, ts', hts, rfl⟩ := h
    rcases hf with _ | ⟨hv, hf⟩
    rename_i v vs'
    refine typedVals_cons ?_ (typedVals_of_forall₂ hts hf)
    rcases p with (_ | _) | _ | _
    · rename_i it
      simp only [scalarInt?, Option.some.injEq] at ht
      subst ht
      exact valOk_int hv
    all_goals simp [scalarInt?] at ht

/-! ## Frames -/

theorem den_const_zero (t : IntType) (ρ : Env) :
    den ρ (t, .const 0) = .num ⟨.int t, 0⟩ := by
  cases t <;> rfl

theorem locals_zero (σ : List CTypeUse) :
    ∀ {lts : List ValType} {ls : List IntType} (ρ : Env), lts.mapM intTy? = some ls →
      (ls.map fun t => (t, Term.const 0)).map (fun p => some (den ρ p)) =
        lts.map fun t => defaultVal? ((liftVal t).substAll σ)
  | [], ls, ρ, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | t :: lts, ls, ρ, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨it, hit, ls', hls, rfl⟩ := h
    simp only [List.map_cons, locals_zero σ ρ hls, List.cons.injEq, and_true]
    rcases t with (_ | _) | _ | _
    · rename_i it'
      simp only [intTy?, Option.some.injEq] at hit
      subst hit
      rw [den_const_zero]
      rfl
    all_goals simp [intTy?] at hit

/-- The initial symbolic state denotes the frame of the call. -/
theorem frameAt_fnInit {ps ls : List IntType} {lts : List ValType} {args : List Val}
    (hargs : TypedVals ps args) (hls : lts.mapM intTy? = some ls) (m : ModuleInst) :
    frameAt (Frame.forCall m args lts) (envOfVals args) (fnInit ps ls) =
      Frame.forCall m args lts := by
  have h₁ := map_den_envOfVals hargs [] []
  simp only [List.length_nil, Nat.zero_add, List.nil_append, List.append_nil] at h₁
  have h₂ : (ps.mapIdx fun i t => (t, Term.var i)).map (fun p => some (den (envOfVals args) p)) =
      args.map some := by
    have := congrArg (List.map some) h₁
    simp only [List.map_map] at this
    exact this
  simp only [frameAt, fnInit, List.map_append, h₂, Frame.forCall]
  rw [locals_zero (m.types.map .dt) (envOfVals args) hls]

/-! ## Total specifications -/

theorem fnOut_length (F : FnSum) (vs : List Val) :
    (fnOut F vs).length = F.final.stack.length := by
  simp [fnOut, stackAt]

/-- What a summary records. -/
theorem sumOf_inv {ft : FnType} {fi : FuncInst H} {F : FnSum} (h : sumOf ft fi = some F) :
    ∃ code ps rs ls A, fi.code = .wasm code ∧ ft.params.mapM scalarInt? = some ps ∧
      ft.results.mapM scalarInt? = some rs ∧ code.locals.mapM intTy? = some ls ∧
      xexec fnFuel (fnInit ps ls) code.body = some A ∧ A.stack.map (·.1) = rs.reverse ∧
      F = ⟨ps, rs, A⟩ := by
  unfold sumOf at h
  split at h
  · rename_i code hcode
    split at h
    · rename_i ps rs ls hps hrs hls
      split at h
      · rename_i A hA
        split at h
        · exact ⟨code, ps, rs, ls, A, hcode, hps, hrs, hls, hA, by assumption, (Option.some.inj h).symm⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- The final values of a summarised body satisfy the body postcondition of the total call
rule. -/
theorem bodyPost_of_sum {ft : FnType} {ps rs : List IntType} {A : SState} {s₀ s : Store H}
    {args vs₀ : List Val} {f F : Frame} (hrs : ft.results.mapM scalarInt? = some rs)
    (hty : A.stack.map (·.1) = rs.reverse) :
    bodyPostT P host (Ty.ofList (ft.results.map ScalarType.toC)).length f vs₀
      (callPost f vs₀ ((sumSpec ⟨ps, rs, A⟩ s₀).post s args)) s F
      (.normal (stackAt (envOfVals args) A).reverse) := by
  have hlen : (stackAt (envOfVals args) A).reverse.length =
      (Ty.ofList (ft.results.map ScalarType.toC)).length := by
    have h₁ : A.stack.length = rs.length := by
      simpa using congrArg List.length hty
    rw [Ty.length_ofList, List.length_map, ← mapM_length hrs, ← h₁]
    simp [stackAt]
  exact ⟨by simpa using hlen, rfl, Or.inl ⟨_, rfl, rfl⟩⟩

/-- **A summary is a total specification**, at every profile and host relation. -/
theorem tfspec_of_sumOf {ft : FnType} {fi : FuncInst H} {F : FnSum} (h : sumOf ft fi = some F)
    {s₀ : Store H} {a : Nat} (hfi : s₀.funcs[a]? = some fi) (he : Expand fi.type ft.toComp) :
    TFSpecAt P host a (sumSpec F s₀) := by
  obtain ⟨code, ps, rs, ls, A, hcode, hps, hrs, hls, hA, hty, rfl⟩ := sumOf_inv h
  refine TFSpecAt.of_body (fi := fi) (code := code) (hfi := fun s _ hp => hp.1 ▸ hfi)
    hcode he (fun _ args hp => ?_) (fun s args hp f vs₀ => ?_)
  · show args.length = (Ty.ofList (ft.params.map ScalarType.toC)).length
    rw [Ty.length_ofList, List.length_map, hp.2.1, ← mapM_length hps]
  · have hfin : TWP P host s (frameAt (Frame.forCall fi.module args code.locals)
        (envOfVals args) A) (vals ([] ++ (stackAt (envOfVals args) A).reverse) ++ [])
        (bodyPostT P host (Ty.ofList (ft.results.map ScalarType.toC)).length f vs₀
          (callPost f vs₀ ((sumSpec ⟨ps, rs, A⟩ s₀).post s args))) := by
      simpa using Wp.of_vals (m := .total) (bodyPost_of_sum hrs hty)
    have hw := twp_xexec (P := P) (host := host) (ρ := envOfVals args) fnFuel hA s
      (Frame.forCall fi.module args code.locals) [] [] _ hfin
    rw [frameAt_fnInit hp.2 hls fi.module] at hw
    simpa [codeAt, fnInit, stackAt, TWP] using hw

/-! ## Exports of computed instances -/

theorem fnSum?_inv {m : Module} {j : Nat} {F : FnSum} (h : fnSum? m j = some F) :
    ∃ mt I ft fi, instance? m = some (mt, I) ∧ I.exports[j]? = some ft ∧
      I.store.funcs[I.addrs.getD j 0]? = some fi ∧ sumOf ft fi = some F := by
  unfold fnSum? at h
  split at h
  · rename_i mt I hI
    unfold fnSumI at h
    split at h
    · rename_i ft fi hft hfi
      exact ⟨mt, I, ft, fi, hI, hft, hfi, h⟩
    · cases h
  · cases h

theorem export_expand {mt : CModuleType} {I : ScalarInstance} {m : Module}
    (hI : instance? m = some (mt, I)) {j : Nat} {ft : FnType} {fi : FuncInst Nat}
    (hft : I.exports[j]? = some ft) (hfi : I.store.funcs[I.addrs.getD j 0]? = some fi) :
    Expand fi.type ft.toComp := by
  have hw : I.WellFormed I.store := (isInstance_of_instance? hI).ok
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hft
  obtain ⟨fi', hfi', hex⟩ := hw.export_type ⟨j, hj⟩
  have : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
  subst this
  exact hex

/-- Accepted arguments of a summarised export are typed. -/
theorem typedVals_of_invokeOk {s : Store Nat} {a : Nat} {ft : FnType} {fi : FuncInst Nat}
    {F : FnSum} (h : sumOf ft fi = some F) (hfi : s.funcs[a]? = some fi)
    (he : Expand fi.type ft.toComp) {vs : List Val} (hvs : InvokeOk s a vs) :
    TypedVals F.params vs := by
  obtain ⟨fi', ps, rs, hfi', he', hf⟩ := hvs
  have : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
  subst this
  have hc := Expand.func_eq he' he
  simp only [FnType.toComp] at hc
  injection hc with hc₁ hc₂
  rw [hc₁, Ty.toList_ofList] at hf
  unfold sumOf at h
  split at h
  · split at h
    · rename_i ps' rs' ls hps hrs hls
      split at h
      · split at h
        · cases h
          exact typedVals_of_forall₂ hps hf
        · cases h
      · cases h
    · cases h
  · cases h

/-- **The behaviour set of a summarised export**: every accepted invocation terminates and
returns `fnOut F vs`, at every profile. -/
theorem behaviours_of_fnSum {m : Module} {j : Nat} {F : FnSum} (h : fnSum? m j = some F)
    {vs : List Val} (hvs : InvokeOk (instOf m).store (addrOf m j) vs) :
    behaviours P SingleThreaded.Det.noHost (instOf m).store (addrOf m j) vs = {.returns (fnOut F vs)} := by
  obtain ⟨mt, I, ft, fi, hI, hft, hfi, hs⟩ := fnSum?_inv h
  have hinst : instOf m = I := by simp [instOf, hI]
  have haddr : addrOf m j = I.addrs.getD j 0 := by simp [addrOf, hinst]
  rw [hinst, haddr] at hvs ⊢
  have he := export_expand hI hft hfi
  exact behaviours_eq_of_tfspec (tfspec_of_sumOf hs hfi he)
    ⟨rfl, typedVals_of_invokeOk hs hfi he hvs⟩ (fun _ _ ho => ho)

end Silmaril.Proofs.Wasm.Auto.Bridge