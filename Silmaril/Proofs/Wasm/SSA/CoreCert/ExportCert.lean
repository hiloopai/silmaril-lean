module

public import Silmaril.Proofs.Wasm.SSA.CoreCert.Export
public import Silmaril.Proofs.Wasm.SSA.CoreCert.LocalCert
public import Silmaril.Wasm.Logic.Hoare.Thms

@[expose] public section

/-!
# The export certificate of the SSA optimiser (proofs)

`optimizeFuncExport m g = some bf'` (the local certificate `optimizeFuncLocal`, with source and
result strict leaf functions), together with `runCert` of `bf'` in a module `m'` holding it,
gives `LeafFun P dt (coreFunc bf) (coreFunc bf')` at the defined type `dt` that allocation
assigns, at every profile (`leafFun_of_export`): the canonical behaviours of the two callee
frames are the behaviours of invocations in the allocated stores of `m` and `m'`
(`invoke_entry`, `frame_behaviours`), which are the fragment outcomes of the two functions
(`runCert_spec`), equal by `optimizeFuncNative?_spec`. `replace_exportEquiv`: a module whose
functions are the originals or such replacements is export-equivalent to the source
(`exportEquiv_modRel`).
-/

namespace Silmaril.Proofs.Wasm.SSA.CoreCert

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SSA
open Silmaril.Wasm.SSA.CoreCert
open Silmaril.Wasm.Binaryen (closedHost ExportEquiv BModule BFunc)

variable {H : Type} {P : Numerics.Profile}

/-! ## Invocations enter the callee frame -/

/-- The only step of an invocation of a Wasm function enters its callee frame. -/
theorem invoke_step_entry {host : HostSemantics H} {s : Store H} {a : Nat} {vs : List Val}
    {fi : FuncInst H} {fn : Func} {ps rs : Validation.Ty (.list .val)}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (he : Validation.Expand fi.type (.func ps rs)) (hn : vs.length = ps.length) :
    Step P host (invoke s a vs) ⟨s, {}, [entry rs.length fi.module vs fn]⟩ ∧
      ∀ c', Step P host (invoke s a vs) c' → c' = ⟨s, {}, [entry rs.length fi.module vs fn]⟩ := by
  have hinv : invoke s a vs =
      ⟨s, {}, vals [] ++ vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ := by
    simp [invoke, hf, vals]
  refine ⟨?_, fun c' h => ?_⟩
  · rw [hinv]
    simpa [vals, entry] using Step.callRefFunc (P := P) (host := host) (s := s) (f := {})
      (c := .callRefType fi.type) (vs := vs) trivial hf he hn hcode
  · rw [hinv] at h
    have hc := Silmaril.Wasm.Logic.Hoare.call_step_inv (c := .callRefType fi.type) trivial hf hcode he
      hn h
    simpa [Silmaril.Wasm.Logic.Hoare.callFrame, entry, vals] using hc

/-- An invocation is not a result. -/
theorem invoke_ne_result {s : Store H} {a : Nat} {vs : List Val} (r : Result) :
    (invoke s a vs).code ≠ r.toAdmin := by
  intro hc
  have hl : (invoke s a vs).code.getLast? = r.toAdmin.getLast? := congrArg List.getLast? hc
  cases r with
  | values ws =>
    rcases List.eq_nil_or_concat ws with rfl | ⟨ws', w, rfl⟩
    · simp [invoke, Result.toAdmin, vals] at hl
    · rcases w with ⟨⟨t | t⟩, b⟩ | b | r <;> simp [invoke, Result.toAdmin, vals, Val.toAdmin] at hl
  | throw x => simp [invoke, Result.toAdmin] at hl
  | trap => simp [invoke, Result.toAdmin] at hl

/-- **The behaviours of an invocation of a Wasm function are those of its callee frame.** -/
theorem invoke_entry {host : HostSemantics H} {s : Store H} {a : Nat} {vs : List Val}
    {fi : FuncInst H} {fn : Func} {ps rs : Validation.Ty (.list .val)}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (he : Validation.Expand fi.type (.func ps rs)) (hn : vs.length = ps.length) :
    behaviours P host s a vs = behavioursOf P host ⟨s, {}, [entry rs.length fi.module vs fn]⟩ := by
  obtain ⟨hstep, huniq⟩ := invoke_step_entry (P := P) (host := host) hf hcode he hn
  refine Set.Subset.antisymm ?_ (behavioursOf_step_sub hstep)
  rintro b (⟨c', r, hs, hc, rfl⟩ | ⟨rfl, hd⟩)
  · rcases Relation.ReflTransGen.cases_head hs with rfl | ⟨c₁, h₁, h₂⟩
    · exact (invoke_ne_result r hc).elim
    · have h₂' : Steps P host ⟨s, {}, [entry rs.length fi.module vs fn]⟩ c' := huniq c₁ h₁ ▸ h₂
      exact mem_behavioursOf h₂' hc
  · obtain ⟨c₁, h₁, hd₁⟩ := hd.unfold
    have hd₁' : Diverges P host ⟨s, {}, [entry rs.length fi.module vs fn]⟩ := huniq c₁ h₁ ▸ hd₁
    exact .inr ⟨rfl, hd₁'⟩

/-! ## Types of the allocated function -/

/-- The allocated store holds each function at the defined type allocation assigns. -/
theorem prepare_type {M : Module} {c : Config H} {st : Option FuncIdx}
    (hp : prepare? evalConst? ({} : Store H) M [] = some (c, st))
    (hv : ((Validation.validate? M).map fun mt => mt.imports.isEmpty) = some true)
    {g : Nat} {fn : Func} (hg : M.funcs[g]? = some fn) :
    ∃ fi, c.store.funcs[g]? = some fi ∧ fi.code = .wasm fn ∧
      (allocTypes M.types)[fn.type.toNat]? = some fi.type := by
  have hi := prepare_instantiate hp hv (SingleThreaded.profile fun _ _ _ _ => false)
    SingleThreaded.divHost
  obtain ⟨_, _, hm, hxas⟩ := hi.valid
  obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi', hg', ht, he, ha, hc⟩ := hi.run
  have hstore : c.store = s₄ := by rw [← withStart_store c st, hc]
  cases hm with
  | mk htypes himports hC' hC htags hglobals _ htables hfuncs _ helems _ _ _ =>
  have hF := Binaryen.alloc_funcs htypes himports hC' hC htags hglobals htables hfuncs helems hxas
    hg' ht he ha
  rw [hstore, hF]
  obtain ⟨d, hd, hok⟩ := Sim.forall₂_getElem? hfuncs hg
  refine ⟨⟨d, mi', .wasm fn⟩, by simp [List.getElem?_zip_eq_some, hd, hg], rfl, ?_⟩
  cases hok with
  | mk hd' _ _ _ =>
    rw [allocTypes_eq htypes]
    subst hC hC'
    exact hd'

/-- The parameter and result lists of an expansion, from `funcType?`. -/
theorem expand_of_funcType {d : Validation.DefType} {a b : List Validation.CValType}
    {ps rs : Validation.Ty (.list .val)} (h : Validation.DefType.funcType? d = some (a, b))
    (he : Validation.Expand d (.func ps rs)) : ps.toList = a ∧ rs.toList = b := by
  unfold Validation.DefType.funcType? at h
  rw [Validation.Expand.iff.mp he] at h
  exact Prod.mk.inj (Option.some.inj h)

/-- What `runCert` gives about the allocated function: its code, the defined type allocation
assigns, and its integer function type. -/
theorem runCert_type {m : BModule} {g : Nat} {ft : FuncType} {bf : BFunc} {f : FragFunc}
    (hbf : m.funcs[g]? = some bf) (hf : ofBFunc? ft bf = some f)
    (hc : runCert m g ft bf = true) :
    ∃ s fi, allocStore? m = some s ∧ s.funcs[g]? = some fi ∧ fi.code = .wasm (coreFunc bf) ∧
      (allocTypes m.lower.types)[bf.type.toNat]? = some fi.type ∧
      Validation.DefType.funcType? fi.type = some
        (f.params.map fun t => Validation.liftVal (.num (.int t)),
          ft.results.map Validation.liftVal) := by
  obtain ⟨-, -, hv, hvst, s, u, hs, hu, hready, hsame⟩ := runCert_inv hc
  obtain ⟨-, -, -, fj, hfj, hcodej, htyj⟩ := checked_store (stub_lower_funcs hbf) hu hvst hready
  obtain ⟨c, st, hp, rfl⟩ := allocStore?_inv hs
  obtain ⟨fi, hfi, hcodei, htype⟩ := prepare_type hp (beq_iff_eq.mp hv) (lower_funcs hbf)
  have heq : u.funcs[g]? = c.store.funcs[g]? :=
    funcs_eq_of_same hsame hfi hfj (hcodei.trans hcodej.symm)
  have hfij : fi = fj := Option.some.inj (hfi.symm.trans (heq.symm.trans hfj))
  obtain ⟨hp', -⟩ : ft.params = f.params.map (fun t => .num (.int t)) ∧
      ft.results = resultTypes f.result := ofBFunc?_types hf
  have hlift : ft.params.map Validation.liftVal =
      f.params.map fun t => Validation.liftVal (.num (.int t)) := by
    rw [hp', List.map_map]
    rfl
  refine ⟨c.store, fi, hs, hfi, hcodei, htype, ?_⟩
  rw [hfij, htyj, hlift]

/-- Typed arguments of integer parameters are no references. -/
theorem valS_of_int {H' : Type} {u : Store H'} :
    ∀ {ts : List IntType} {vs : List Val},
      List.Forall₂ (ValOk u) vs (ts.map fun t => Validation.liftVal (.num (.int t))) →
      ∀ v ∈ vs, ValS v
  | _, _, h, v, hv => by
    obtain ⟨args, rfl, -⟩ := args_of_valOk h
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv
    cases w <;> trivial

theorem optimizeFuncNative?_type {ft : FuncType} {bf bf' : BFunc}
    (ho : optimizeFuncNative? ft bf = some bf') : bf'.type = bf.type := by
  have ho' : ∃ f, ofBFunc? ft bf = some f ∧ ∃ u, guard (f.native = true) = some u ∧
      ∃ g, optimize? f = some g ∧ ∃ v, guard (g.native = true) = some v ∧
        toBFunc? bf.type g = some bf' := by
    simpa only [optimizeFuncNative?, Option.bind_eq_bind, Option.bind_eq_some_iff] using ho
  obtain ⟨-, -, -, -, g, -, -, -, hb⟩ := ho'
  simp only [toBFunc?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hb
  obtain ⟨_, -, rfl⟩ := hb
  rfl

/-- What `optimizeFuncExport` checked. -/
theorem optimizeFuncExport_inv {m : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncExport m g = some bf') :
    ∃ bf, m.funcs[g]? = some bf ∧ optimizeFuncLocal m g = some bf' ∧
      strictFunc (coreFunc bf) = true ∧ strictFunc (coreFunc bf') = true := by
  simp only [optimizeFuncExport, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨bf, hbf, bf'', ho, hif⟩ := h
  split at hif
  · rename_i hs
    obtain rfl : bf'' = bf' := Option.some.inj hif
    simp only [Bool.and_eq_true] at hs
    exact ⟨bf, hbf, ho, hs.1, hs.2⟩
  · cases hif

/-! ## The per-function export certificate -/

/-- The fragment outcomes of `f` on `args`, as Core behaviours. -/
def fragBeh (f : FragFunc) (args : List WVal) : Set (Behaviour Val) :=
  {b | (∃ o, f.Run args o ∧ b = outBeh (some o)) ∨ (b = .diverges ∧ ∀ o, ¬ f.Run args o)}

/-- Integer arguments are no references. -/
theorem valS_args (args : List WVal) : ∀ v ∈ args.map WVal.toVal, ValS v := fun v hv => by
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv
  cases w <;> trivial

/-- **The canonical behaviours of the callee frame of a certified function** are its fragment
outcomes. -/
theorem lBeh_cert {m : BModule} {g : Nat} {ft : FuncType} {bf : BFunc} {f : FragFunc}
    (hbf : m.funcs[g]? = some bf) (hf : ofBFunc? ft bf = some f) (hnf : f.native = true)
    (hrc : runCert m g ft bf = true) (hs : strictFunc (coreFunc bf) = true) {dt : Validation.DefType}
    (hdt : (allocTypes m.lower.types)[bf.type.toNat]? = some dt) {ps rs : Validation.Ty (.list .val)}
    (he : Validation.Expand dt (.func ps rs)) {args : List WVal} (hargs : args.map WVal.type = f.params)
    (hn : (args.map WVal.toVal).length = ps.length) :
    LBeh P (entry rs.length {} (args.map WVal.toVal) (coreFunc bf)) = fragBeh f args := by
  obtain ⟨s, fi, hsA, hfi, hcode, hdt₀, -⟩ := runCert_type hbf hf hrc
  obtain ⟨s₂, hs₂, hinv, hbeh⟩ := runCert_spec hbf hf hnf hrc
  have hss : s₂ = s := Option.some.inj (hs₂.symm.trans hsA)
  subst hss
  have edt : fi.type = dt := Option.some.inj (hdt₀.symm.trans hdt)
  have e₁ : behaviours P closedHost s₂ g (args.map WVal.toVal) =
      LBeh P (entry rs.length {} (args.map WVal.toVal) (coreFunc bf)) := by
    rw [invoke_entry hfi hcode (edt ▸ he) hn, frame_behaviours (entry_lFrame hs (valS_args args)),
      lBeh_entry hs]
  obtain ⟨a₁, ha₁, -, hb₁⟩ := hbeh P _ (hinv args hargs)
  have ha : a₁ = args := map_toVal_inj' ha₁.symm
  rw [← e₁, hb₁, ha]
  rfl

/-- The parameters of the allocated type of a certified function are its integer
parameters. -/
theorem params_cert {m : BModule} {g : Nat} {ft : FuncType} {bf : BFunc} {f : FragFunc}
    (hbf : m.funcs[g]? = some bf) (hf : ofBFunc? ft bf = some f) (hrc : runCert m g ft bf = true)
    {dt : Validation.DefType} (hdt : (allocTypes m.lower.types)[bf.type.toNat]? = some dt)
    {ps rs : Validation.Ty (.list .val)} (he : Validation.Expand dt (.func ps rs)) :
    ps.toList = f.params.map fun t => Validation.liftVal (.num (.int t)) := by
  obtain ⟨s, fi, -, -, -, hdt₀, hfty⟩ := runCert_type hbf hf hrc
  have edt : fi.type = dt := Option.some.inj (hdt₀.symm.trans hdt)
  rw [edt] at hfty
  exact (expand_of_funcType hfty he).1

theorem args_length {ps : Validation.Ty (.list .val)} {ts : List IntType} {args : List WVal}
    (hps : ps.toList = ts.map fun t => Validation.liftVal (.num (.int t)))
    (hargs : args.map WVal.type = ts) : (args.map WVal.toVal).length = ps.length := by
  have h1 := congrArg List.length hps
  have h2 := congrArg List.length hargs
  simp [Validation.Ty.length] at h1 h2 ⊢
  omega

/-- **Equivalent strict leaf functions, from the certificates.** -/
theorem leafFun_of_export {m m' : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncExport m g = some bf') (hbf' : m'.funcs[g]? = some bf')
    (hr : ∀ bf ft, m.funcs[g]? = some bf → m.funcType? bf.type = some ft →
      runCert m' g ft bf' = true)
    (htypes : m'.lower.types = m.lower.types) :
    ∃ bf : BFunc, m.funcs[g]? = some bf ∧ bf'.type = bf.type ∧
      ∀ dt, (allocTypes m.lower.types)[bf.type.toNat]? = some dt →
        LeafFun P dt (coreFunc bf) (coreFunc bf') := by
  obtain ⟨bf, hbf, hloc, hs, hs'⟩ := optimizeFuncExport_inv h
  obtain ⟨bf₀, ft, hbf₀, hft, ho, hrc⟩ := optimizeFuncLocal_inv hloc
  obtain rfl : bf = bf₀ := (Option.some.inj (hbf₀.symm.trans hbf)).symm
  obtain ⟨hon, -, -⟩ := optimizeFuncCore?_inv ho
  have hty : bf'.type = bf.type := optimizeFuncNative?_type hon
  obtain ⟨f, f', hf, hnf, hf', hnf', gp, -, hrun⟩ := optimizeFuncNative?_spec hon
  have hrc' : runCert m' g ft bf' = true := hr bf ft hbf hft
  refine ⟨bf, hbf, hty, fun dt hd => ?_⟩
  have hd' : (allocTypes m'.lower.types)[bf'.type.toNat]? = some dt := by rw [htypes, hty, hd]
  refine ⟨fun ps rs he _ u vs hvs => ?_, hs, hs', fun ps rs vs he hv => ?_⟩
  · rw [params_cert hbf hf hrc hd he] at hvs
    exact valS_of_int hvs
  · show LBeh P (entry rs.length {} vs (coreFunc bf)) =
      LBeh P (entry rs.length {} vs (coreFunc bf'))
    obtain ⟨H', u, hvu⟩ := hv
    have hps : ps.toList = f.params.map fun t => Validation.liftVal (.num (.int t)) :=
      params_cert hbf hf hrc hd he
    obtain ⟨args, hvs, hargs⟩ : ∃ args : List WVal, vs = args.map WVal.toVal ∧
        args.map WVal.type = f.params := args_of_valOk (hps ▸ hvu)
    have hn : vs.length = ps.length := hvs ▸ args_length hps hargs
    rw [hvs] at hn ⊢
    rw [lBeh_cert hbf hf hnf hrc hs hd he hargs hn,
      lBeh_cert hbf' hf' hnf' hrc' hs' hd' he (hargs.trans gp.symm) hn]
    exact outcome_set_eq (hrun args)

/-! ## Modules -/

/-- **A module whose functions are the originals or export-certified replacements is
export-equivalent to the source**, at every profile, under the closed host. -/
theorem replace_exportEquiv {m m' : BModule} (hbase : m'.base = m.base)
    (hlen : m'.funcs.length = m.funcs.length) (hm : m.Ok) (hm' : m'.Ok)
    (hfun : ∀ g bf', m'.funcs[g]? = some bf' → m.funcs[g]? = some bf' ∨
      (optimizeFuncExport m g = some bf' ∧ ∀ bf ft, m.funcs[g]? = some bf →
        m.funcType? bf.type = some ft → runCert m' g ft bf' = true))
    (P : Numerics.Profile) :
    ExportEquiv (· = ·) P (closedHost (H := H)) m'.lower m.lower := by
  have htypes : m'.lower.types = m.lower.types := by
    simp [BModule.lower, hbase]
  have hrel : ModRel P m.lower m'.lower := by
    refine ⟨by simp [BModule.lower, hbase], ?_⟩
    simp only [BModule.lower]
    rw [List.forall₂_iff_get]
    refine ⟨by simp [hlen], fun i h₁ h₂ => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_map]
    have hi' : i < m'.funcs.length := by simpa using h₂
    have hi : i < m.funcs.length := by simpa using h₁
    rcases hfun i _ (List.getElem?_eq_getElem hi') with he | ⟨hex, hr⟩
    · rw [List.getElem?_eq_getElem hi, Option.some.injEq] at he
      rw [he]
      exact ⟨rfl, .inl rfl⟩
    · obtain ⟨bf, hbf, hty, hlf⟩ :=
        leafFun_of_export (P := P) hex (List.getElem?_eq_getElem hi') hr htypes
      rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hbf
      rw [hbf]
      exact ⟨hty.symm, .inr fun dt hd => hlf dt hd⟩
  exact exportEquiv_modRel hrel.symm hm' hm

end Silmaril.Proofs.Wasm.SSA.CoreCert
