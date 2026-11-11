module

public import Silmaril.Proofs.Wasm.Auto.Bridge.Ext.Beh
public import Silmaril.Wasm.Auto.Bridge.Defs
public import Silmaril.Wasm.Auto.Equiv.Thms

/-!
# Summaries with memory, globals and traps: total specifications and behaviour sets

`tfspecX_of_sumOfX`: a function instance with a summary (`sumOfX`) has the total specification
"called from the store `s₀` on typed arguments `vs`, its outcome is that of `fnOutX F vs`" at
every profile and host relation: the extended executor's forward rule (`wp_xsexec`, track
equiv) in the total reading, started from the call frame, the store's globals and memory `0`.
`behaviours_of_fnSumX`: for function export `j` of a module with a summary (`fnSumX?`), the
behaviour set of every accepted invocation is `{(fnOutX F vs).toBehaviour}`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Bridge

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Equiv (Env envOfVals TypedVals den)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Post Outcome)
open Silmaril.Wasm.Game (ScalarType ScalarInstance FnType)
open Silmaril.Wasm.Verify (instance? instOf)
open Silmaril.Wasm.Auto.Front (addrOf)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Stores -/

theorem modify_self {α : Type} (l : List α) (a : Nat) (g : α → α)
    (h : ∀ x, l[a]? = some x → g x = x) : l.modify a g = l := by
  apply List.ext_getElem (by simp)
  intro j h₁ h₂
  rw [List.getElem_modify]
  split
  · rename_i hj
    subst hj
    exact h _ (List.getElem?_eq_getElem h₂)
  · rfl

theorem setGlobal_self {s : Store H} {a : Nat} {v : Val}
    (h : s.globals[a]?.map (·.value) = some v) : s.setGlobal a v = s := by
  have hm : s.globals.modify a (fun g => { g with value := v }) = s.globals := by
    refine modify_self _ _ _ fun x hx => ?_
    rw [hx] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    rfl
  simp only [Store.setGlobal, hm]

theorem setGlobals_self (s : Store H) :
    ∀ {ga : List Nat} {gv : List Val},
      ga.mapM (fun a => s.globals[a]?.map (·.value)) = some gv → setGlobals s ga gv = s
  | [], gv, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | a :: ga, gv, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, gv', hgv, rfl⟩ := h
    simp only [setGlobals, setGlobal_self hv]
    exact setGlobals_self s hgv

theorem setMem_self {s : Store H} {a : Nat} {mi : MemInst} (h : s.mems[a]? = some mi) :
    s.setMem a mi = s := by
  have hm : s.mems.set a mi = s.mems := by
    apply List.ext_getElem (by simp)
    intro j h₁ h₂
    rw [List.getElem_set]
    split
    · rename_i hj
      subst hj
      exact (Option.some.inj ((List.getElem?_eq_getElem h₂).symm.trans h)).symm
    · rfl
  simp only [Store.setMem, hm]

theorem mapM_some_lt {s : Store H} :
    ∀ {ga : List Nat} {gv : List Val},
      ga.mapM (fun a => s.globals[a]?.map (·.value)) = some gv →
        ∀ (k : Nat) (hk : k < ga.length), ga[k] < s.globals.length
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | a :: ga, gv, h, k, hk => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, gv', hgv, rfl⟩ := h
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero]
      cases ha : s.globals[a]? with
      | none => rw [ha] at hv; cases hv
      | some _ => exact (List.getElem?_eq_some_iff.mp ha).1
    | succ k => exact mapM_some_lt hgv k (by simpa using hk)

theorem typedVals_of_valInt : ∀ {gv : List Val} {gt : List IntType},
    gv.mapM valInt? = some gt → TypedVals gt gv
  | [], gt, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact Silmaril.Proofs.Wasm.Auto.Bridge.typedVals_nil
  | v :: gv, gt, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨t, ht, gt', hgt, rfl⟩ := h
    refine Silmaril.Proofs.Wasm.Auto.Bridge.typedVals_cons ?_ (typedVals_of_valInt hgt)
    rcases v with ⟨_ | _, x⟩ | _ | _
    all_goals simp only [valInt?, Option.some.injEq, reduceCtorEq] at ht
    subst ht
    exact ⟨x, rfl⟩

/-! ## The globals a summary uses -/

theorem globsUsed_ok (s : Store H) (mi : ModuleInst) :
    GlobsOk s mi (globsUsed s mi).1 (globsUsed s mi).2.1 (globsUsed s mi).2.2 := by
  unfold globsUsed globsOf
  split
  · rename_i gv hgv
    split
    · rename_i gt hgt
      split
      · rename_i hnd
        refine ⟨hnd, fun k hk => ⟨List.getElem?_eq_getElem hk, mapM_some_lt hgv k hk⟩, hgv,
          typedVals_of_valInt hgt⟩
      · exact ⟨List.nodup_nil, fun k hk => absurd hk (Nat.not_lt_zero _), rfl,
          Silmaril.Proofs.Wasm.Auto.Bridge.typedVals_nil⟩
    · exact ⟨List.nodup_nil, fun k hk => absurd hk (Nat.not_lt_zero _), rfl,
        Silmaril.Proofs.Wasm.Auto.Bridge.typedVals_nil⟩
  · exact ⟨List.nodup_nil, fun k hk => absurd hk (Nat.not_lt_zero _), rfl,
      Silmaril.Proofs.Wasm.Auto.Bridge.typedVals_nil⟩

/-! ## The context of a call -/

theorem bytes_ctxOf (s : Store H) (mi : ModuleInst) (args : List Val) (lts : List ValType)
    (ρ : Env) : (ctxOf s mi args lts ρ).mi.bytes = bytesOf (memOf s mi) := by
  simp only [ctxOf]
  cases memOf s mi <;> rfl

theorem module_forCall (mi : ModuleInst) (args : List Val) (lts : List ValType) :
    (Frame.forCall mi args lts).module = mi := rfl

theorem good_ctxOf (s : Store H) (mi : ModuleInst) (args : List Val) (lts : List ValType)
    (ρ : Env) : (ctxOf s mi args lts ρ).Good (memOf s mi).isSome := by
  have hg := globsUsed_ok s mi
  refine ⟨hg.nodup, fun k hk => hg.addr k hk, fun hm => ?_⟩
  cases h : memOf s mi with
  | none => rw [h] at hm; cases hm
  | some p =>
    simp only [ctxOf, h, Option.getD_some]
    exact h

theorem denX_var (ρ : Env) (B0 : ByteArray) (t : IntType) (n : Nat) :
    denX ρ B0 (t, .var n) = den ρ (t, .var n) := rfl

theorem denX_zero (ρ : Env) (B0 : ByteArray) (t : IntType) :
    denX ρ B0 (t, .const 0) = den ρ (t, .const 0) := rfl

theorem map_denX_vars (ρ : Env) (B0 : ByteArray) (ps : List IntType) (k : Nat) :
    (ps.mapIdx fun i t => (t, XT.var (k + i))).map (denX ρ B0) =
      (ps.mapIdx fun i t => (t, Silmaril.Wasm.Auto.Equiv.Term.var (k + i))).map (den ρ) := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp [denX_var]

theorem map_denX_zeros (ρ : Env) (B0 : ByteArray) (ls : List IntType) :
    (ls.map fun t => (t, XT.const 0)).map (fun p => some (denX ρ B0 p)) =
      (ls.map fun t => (t, Silmaril.Wasm.Auto.Equiv.Term.const 0)).map (fun p => some (den ρ p)) := by
  simp only [List.map_map, Function.comp_def, denX_zero]

/-- The initial symbolic state denotes the call frame. -/
theorem frameOf_init {ps ls gt : List IntType} {lts : List ValType} {args gv : List Val}
    (hargs : TypedVals ps args) (hls : lts.mapM intTy? = some ls) (s : Store H)
    (mi : ModuleInst) :
    (ctxOf s mi args lts (envOfVals (args ++ gv))).frameOf (fnInitX ps ls gt) =
      Frame.forCall mi args lts := by
  have h₁ := Silmaril.Wasm.Auto.Equiv.map_den_envOfVals hargs [] gv
  simp only [List.length_nil, Nat.zero_add, List.nil_append] at h₁
  have h₂ : ∀ B0, (ps.mapIdx fun i t => (t, XT.var i)).map
      (fun p => some (denX (envOfVals (args ++ gv)) B0 p)) = args.map some := by
    intro B0
    have := map_denX_vars (envOfVals (args ++ gv)) B0 ps 0
    simp only [Nat.zero_add] at this
    have := congrArg (List.map some) this
    simp only [List.map_map, h₁] at this
    exact this
  simp only [XCtx.frameOf, ctxOf, fnInitX, List.map_append, h₂, map_denX_zeros, Frame.forCall]
  rw [locals_zero (mi.types.map .dt) _ hls]

/-- The memory `memOf` finds is the store's memory at that address. -/
theorem setMem_memOf {s : Store H} {mi : ModuleInst} {ma : Nat} {m : MemInst}
    (h : memOf s mi = some (ma, m)) : s.setMem ma { type := m.type, bytes := m.bytes } = s := by
  apply setMem_self
  have hm : s.mem? { module := mi } ⟨0⟩ = some (ma, m) := h
  simp only [Store.mem?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨a, -, m', hm', rfl, rfl⟩ := hm
  exact hm'

/-- The initial symbolic state denotes the store. -/
theorem storeOf_init {ps ls : List IntType} {lts : List ValType} {args : List Val}
    (hargs : TypedVals ps args) (s : Store H) (mi : ModuleInst) :
    (ctxOf s mi args lts (envOfVals (args ++ (globsUsed s mi).2.1))).storeOf (memOf s mi).isSome
      (fnInitX ps ls (globsUsed s mi).2.2) = s := by
  have hg : GlobsOk s mi (globsUsed s mi).1 (globsUsed s mi).2.1 (globsUsed s mi).2.2 :=
    globsUsed_ok s mi
  have hl : args.length = ps.length := hargs.1
  have h₁ : List.map (den (envOfVals (args ++ (globsUsed s mi).2.1)))
      (List.mapIdx (fun i t => (t, Term.var (args.length + i))) (globsUsed s mi).2.2) =
      (globsUsed s mi).2.1 := by
    simpa only [List.append_nil] using Silmaril.Wasm.Auto.Equiv.map_den_envOfVals hg.typed args []
  have hgl : ∀ B0, (fnInitX ps ls (globsUsed s mi).2.2).globs.map
      (denX (envOfVals (args ++ (globsUsed s mi).2.1)) B0) = (globsUsed s mi).2.1 := by
    intro B0
    rw [fnInitX, map_denX_vars, ← hl]
    exact h₁
  simp only [XCtx.storeOf, ctxOf, hgl, setGlobals_self s hg.vals]
  cases h : memOf s mi with
  | none => rfl
  | some p =>
    obtain ⟨ma, m⟩ := p
    simp only [Option.isSome_some, ↓reduceIte, Option.getD_some, fnInitX, evM]
    exact setMem_memOf h

/-! ## Total specifications -/

/-- What a summary records. -/
theorem sumOfX_inv {s : Store H} {ft : FnType} {fi : FuncInst H} {F : FnSumX}
    (h : sumOfX s ft fi = some F) :
    ∃ code ps rs ls A, fi.code = .wasm code ∧ ft.params.mapM scalarInt? = some ps ∧
      ft.results.mapM scalarInt? = some rs ∧ code.locals.mapM intTy? = some ls ∧
      xsexec (memOf s fi.module).isSome (fnInitX ps ls (globsUsed s fi.module).2.2) code.body =
        some A ∧ A.stack.map (·.1) = rs.reverse ∧
      F = ⟨ps, rs, (globsUsed s fi.module).2.1, bytesOf (memOf s fi.module), A⟩ := by
  unfold sumOfX at h
  split at h
  · rename_i code hcode
    split at h
    · rename_i ps rs ls hps hrs hls
      dsimp only at h
      split at h
      · rename_i A hA
        split at h
        · exact ⟨code, ps, rs, ls, A, hcode, hps, hrs, hls, hA, by assumption,
            (Option.some.inj h).symm⟩
        · cases h
      · cases h
    · cases h
  · cases h

theorem guardsOk_iff {ρ : Env} {B0 : ByteArray} {G : List (Guard × XState)} :
    guardsOk ρ B0 G = true ↔ firstFail ρ B0 G = none := by
  rw [firstFail_none_iff]
  simp [guardsOk]

/-- **A summary is a total specification**, at every profile and host relation. -/
theorem tfspecX_of_sumOfX {s₀ : Store H} {ft : FnType} {fi : FuncInst H} {F : FnSumX}
    (h : sumOfX s₀ ft fi = some F) {a : Nat} (hfi : s₀.funcs[a]? = some fi)
    (he : Expand fi.type ft.toComp) : TFSpecAt P host a (sumSpecX F s₀) := by
  obtain ⟨code, ps, rs, ls, A, hcode, hps, hrs, hls, hA, hty, hF⟩ := sumOfX_inv h
  have hFp : F.params = ps := by rw [hF]
  have hFf : F.final = A := by rw [hF]
  have hFb : F.bytes = bytesOf (memOf s₀ fi.module) := by rw [hF]
  refine TFSpecAt.of_body (fi := fi) (code := code) (hfi := fun s _ hp => hp.1 ▸ hfi)
    hcode he (fun _ args hp => ?_) (fun s args hp f vs₀ => ?_)
  · show args.length = (Ty.ofList (ft.params.map ScalarType.toC)).length
    rw [Ty.length_ofList, List.length_map, hp.2.1, hFp, ← mapM_length hps]
  · show TSafe P host (bodyPostT P host _ f vs₀ (callPost f vs₀ ((sumSpecX F s₀).post s args)))
      ⟨s, Frame.forCall fi.module args code.locals, expression code.body⟩
    obtain ⟨rfl, htv₀⟩ := hp
    have htv : TypedVals ps args := hFp ▸ htv₀
    have hFg : F.gvals = (globsUsed s fi.module).2.1 := by rw [hF]
    let c := ctxOf s fi.module args code.locals (envX F args)
    have hc : c.Good (memOf s fi.module).isSome := good_ctxOf _ _ _ _ _
    have hgl : (fnInitX ps ls (globsUsed s fi.module).2.2).globs.length = c.ga.length := by
      have hg := globsUsed_ok s fi.module
      simp only [fnInitX, List.length_mapIdx, c, ctxOf]
      rw [← hg.typed.1, ← mapM_length hg.vals]
    have hw := wp_xsexec (m := .total) (P := P) (host := host) hc [] []
      (bodyPostT P host (Ty.ofList (ft.results.map ScalarType.toC)).length f vs₀
        (callPost f vs₀ ((sumSpecX F s).post s args))) code.body hgl rfl hA
    have hρ : envX F args = envOfVals (args ++ (globsUsed s fi.module).2.1) := by
      rw [envX, hFg]
    have hs : c.storeOf (memOf s fi.module).isSome (fnInitX ps ls (globsUsed s fi.module).2.2) =
        s := by
      simp only [c]
      rw [hρ]
      exact storeOf_init htv s fi.module
    have hf : c.frameOf (fnInitX ps ls (globsUsed s fi.module).2.2) =
        Frame.forCall fi.module args code.locals := by
      simp only [c]
      rw [hρ]
      exact frameOf_init htv hls s fi.module
    have hst : c.stackOf (fnInitX ps ls (globsUsed s fi.module).2.2) = [] := rfl
    rw [hs, hf, hst] at hw
    have hb : c.mi.bytes = F.bytes := (bytes_ctxOf _ _ _ _ _).trans hFb.symm
    have hx : XOut .total P host c (memOf s fi.module).isSome A [] []
        (bodyPostT P host (Ty.ofList (ft.results.map ScalarType.toC)).length f vs₀
          (callPost f vs₀ ((sumSpecX F s).post s args))) := by
      unfold XOut
      cases hT : firstFail c.ρ c.mi.bytes A.guards with
      | some T =>
        show bodyPostT P host _ f vs₀ _ (c.storeOf (memOf s fi.module).isSome T) (c.frameOf T) .trap
        have hng : guardsOk (envX F args) F.bytes A.guards = false := by
          cases hk : guardsOk (envX F args) F.bytes A.guards
          · rfl
          · rw [guardsOk_iff, ← hb] at hk
            exact absurd (hk.symm.trans hT) (by simp)
        refine ⟨rfl, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
        show Outcome.trap = resOutcome (fnOutX F args)
        simp only [fnOutX, outAt, hFf, hng]
        rfl
      | none =>
        show Wp .total P host (c.storeOf (memOf s fi.module).isSome A) (c.frameOf A)
          (vals ([] ++ (c.stackOf A).reverse) ++ []) _
        have hok : guardsOk (envX F args) F.bytes A.guards = true := by
          rw [guardsOk_iff, ← hb]
          exact hT
        rw [List.nil_append, List.append_nil]
        refine Wp.of_vals ?_
        have hlen : (c.stackOf A).reverse.length =
            (Ty.ofList (ft.results.map ScalarType.toC)).length := by
          have h₁ : A.stack.length = rs.length := by simpa using congrArg List.length hty
          rw [Ty.length_ofList, List.length_map, ← mapM_length hrs, ← h₁]
          simp [XCtx.stackOf]
        refine ⟨by simpa using hlen, rfl, Or.inl ⟨_, rfl, ?_⟩⟩
        show Outcome.normal _ = resOutcome (fnOutX F args)
        simp only [fnOutX, outAt, hFf, hok, ↓reduceIte, resOutcome, XCtx.stackOf, hb]
        rfl
    have hw' := hw.mpr hx
    simpa [expression, TWP] using hw'

/-! ## Exports of computed instances -/

theorem fnSumX?_inv {m : Module} {j : Nat} {F : FnSumX} (h : fnSumX? m j = some F) :
    ∃ mt I ft fi, instance? m = some (mt, I) ∧ I.exports[j]? = some ft ∧
      I.store.funcs[I.addrs.getD j 0]? = some fi ∧ sumOfX I.store ft fi = some F := by
  unfold fnSumX? at h
  split at h
  · rename_i mt I hI
    unfold fnSumXI at h
    split at h
    · rename_i ft fi hft hfi
      exact ⟨mt, I, ft, fi, hI, hft, hfi, h⟩
    · cases h
  · cases h

/-- Accepted arguments of a summarised export are typed. -/
theorem typedVals_of_invokeOkX {s : Store Nat} {a : Nat} {ft : FnType} {fi : FuncInst Nat}
    {F : FnSumX} (h : sumOfX s ft fi = some F) (hfi : s.funcs[a]? = some fi)
    (he : Expand fi.type ft.toComp) {vs : List Val} (hvs : InvokeOk s a vs) :
    TypedVals F.params vs := by
  obtain ⟨fi', ps, rs, hfi', he', hf⟩ := hvs
  have : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
  subst this
  have hc := Expand.func_eq he' he
  simp only [Silmaril.Wasm.Game.FnType.toComp] at hc
  injection hc with hc₁ hc₂
  rw [hc₁, Ty.toList_ofList] at hf
  obtain ⟨code, ps', rs', ls, A, -, hps, -, -, -, -, rfl⟩ := sumOfX_inv h
  exact typedVals_of_forall₂ hps hf

/-- The behaviour set of a summarised export on typed arguments. -/
theorem behaviours_of_fnSumX_typed {m : Module} {j : Nat} {F : FnSumX} (h : fnSumX? m j = some F)
    {vs : List Val} (htv : TypedVals F.params vs) :
    behaviours P SingleThreaded.Det.noHost (instOf m).store (addrOf m j) vs =
      {(fnOutX F vs).toBehaviour} := by
  obtain ⟨mt, I, ft, fi, hI, hft, hfi, hs⟩ := fnSumX?_inv h
  have hinst : instOf m = I := by simp [instOf, hI]
  have haddr : addrOf m j = I.addrs.getD j 0 := by simp [addrOf, hinst]
  rw [hinst, haddr]
  refine behaviours_eq_res_of_tfspec ?_ (tfspecX_of_sumOfX hs hfi (export_expand hI hft hfi))
    ⟨rfl, htv⟩ (fun _ _ ho => ho)
  intro x hx
  simp only [fnOutX, outAt] at hx
  split at hx <;> cases hx

/-- Typed arguments of a summarised export. -/
theorem typedVals_of_fnSumX {m : Module} {j : Nat} {F : FnSumX} (h : fnSumX? m j = some F)
    {vs : List Val} (hvs : InvokeOk (instOf m).store (addrOf m j) vs) :
    TypedVals F.params vs := by
  obtain ⟨mt, I, ft, fi, hI, hft, hfi, hs⟩ := fnSumX?_inv h
  have hinst : instOf m = I := by simp [instOf, hI]
  have haddr : addrOf m j = I.addrs.getD j 0 := by simp [addrOf, hinst]
  rw [hinst, haddr] at hvs
  exact typedVals_of_invokeOkX hs hfi (export_expand hI hft hfi) hvs

/-- **The behaviour set of a summarised export**: every accepted invocation terminates, and
returns or traps as `fnOutX F vs` says, at every profile. -/
theorem behaviours_of_fnSumX {m : Module} {j : Nat} {F : FnSumX} (h : fnSumX? m j = some F)
    {vs : List Val} (hvs : InvokeOk (instOf m).store (addrOf m j) vs) :
    behaviours P SingleThreaded.Det.noHost (instOf m).store (addrOf m j) vs =
      {(fnOutX F vs).toBehaviour} :=
  behaviours_of_fnSumX_typed h (typedVals_of_fnSumX h hvs)

end Silmaril.Proofs.Wasm.Auto.Bridge