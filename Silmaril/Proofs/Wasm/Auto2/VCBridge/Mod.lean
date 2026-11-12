module

public import Silmaril.Wasm.Auto2.VCBridge.Defs
public import Silmaril.Wasm.Auto2.VCGen.Thms
public import Silmaril.Wasm.Auto.Bridge.Thms

/-!
# The VC generator at the module level: soundness of the check

* `allValid_of_covered`: conditions that are among proved conditions are valid;
* `modTSpec_of_vcCheck`: `vcCheck e m j = true` gives the total every-run specification of the
  export (`Silmaril.Wasm.Auto2.VCGen.genFunc_tsound` on the instance's function);
* `argsOf_valEnv`: typed arguments are the arguments of their own placeholder environment;
* **`modMeets_of_vcCheck`**: with a precondition that holds for all arguments and a reference
  function that agrees with every result the postcondition allows, `ModMeets R P m j f` for every
  reflexive `R` and every profile `P`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCBridge

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Verify (instance? instOf isInstance_of_instance?)
open Silmaril.Wasm.Game (FnType)
open Silmaril.Wasm.Auto.Front (addrOf ModMeets specOfFn)
open Silmaril.Wasm.Auto.Bridge (scalarInt? export_expand mapM_length typedVals_of_forall₂ OrDiv
  meets_orDiv_of_fspecValid)
open Silmaril.Wasm.Auto.Equiv (TypedVals)

variable {P : Profile}

/-! ## Conditions -/

theorem allValid_iff {F : Fns} : ∀ {l : List Fm}, AllValid F l ↔ ∀ φ ∈ l, Valid F φ
  | [] => by simp [AllValid]
  | φ :: l => by simp [AllValid, allValid_iff]

theorem allValid_of_covered {F : Fns} {l conds : List Fm} (hc : covered l conds = true)
    (hv : AllValid F conds) : AllValid F l := by
  rw [allValid_iff] at hv ⊢
  intro φ hφ
  have hm : decide (φ ∈ conds) = true := (List.all_eq_true.mp hc) φ hφ
  exact hv φ (of_decide_eq_true hm)

/-! ## The function of an export -/

theorem fnCode?_inv {m : Module} {j : Nat} {ft : FnType} {code : Func}
    (h : fnCode? m j = some (ft, code)) :
    ∃ mt I fi, instance? m = some (mt, I) ∧ I.exports[j]? = some ft ∧
      I.store.funcs[I.addrs.getD j 0]? = some fi ∧ fi.code = .wasm code := by
  unfold fnCode? at h
  split at h
  · rename_i mt I hI
    split at h
    · rename_i ft' fi hft hfi
      split at h
      · rename_i code' hc
        cases h
        exact ⟨mt, I, fi, hI, hft, hfi, hc⟩
      · cases h
    · cases h
  · cases h

/-- What a successful check says about the export. -/
theorem vcCheck_inv {e : VcEntry} {m : Module} {j : Nat} (h : vcCheck e m j = true) :
    ∃ mt I ft fi code, instance? m = some (mt, I) ∧ I.exports[j]? = some ft ∧
      I.store.funcs[I.addrs.getD j 0]? = some fi ∧ fi.code = .wasm code ∧
      ft.params.mapM scalarInt? = some e.S.params ∧ ft.results.mapM scalarInt? = some e.S.results ∧
      AllValid e.F (genFunc e.S code e.fuel) := by
  unfold vcCheck at h
  split at h
  · rename_i ft code hfc
    obtain ⟨mt, I, fi, hI, hft, hfi, hc⟩ := fnCode?_inv hfc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨mt, I, ft, fi, code, hI, hft, hfi, hc, h.1.1, h.1.2,
      allValid_of_covered h.2 e.valid⟩
  · cases h

theorem instOf_eq {m : Module} {mt : CModuleType} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : instance? m = some (mt, I)) : instOf m = I := by
  simp [instOf, hI]

/-- **The check gives the total specification of the export**, at every profile. -/
theorem modTSpec_of_vcCheck {e : VcEntry} {m : Module} {j : Nat} (h : vcCheck e m j = true) :
    ModTSpec P e m j := by
  obtain ⟨mt, I, ft, fi, code, hI, hft, hfi, hc, hps, hrs, hvc⟩ := vcCheck_inv h
  intro fi' hfi'
  have haddr : addrOf m j = I.addrs.getD j 0 := by simp [addrOf, instOf_eq hI]
  rw [instOf_eq hI, haddr, hfi] at hfi'
  cases hfi'
  have he : Expand fi.type ft.toComp := export_expand hI hft hfi
  refine genFunc_tsound e.total hc he ?_ ?_ hvc ?_
  · rw [Ty.length_ofList, List.length_map, mapM_length hps]
  · rw [Ty.length_ofList, List.length_map, mapM_length hrs]
  · intro c hc'
    rw [e.calls] at hc'
    cases hc'

/-! ## Arguments -/

theorem get_valEnv {vs : List Val} {B : ByteArray} {i : Nat} {t : IntType} {x : BitVec t.width}
    (hv : vs[i]? = some (.num ⟨.int t, x⟩)) : (valEnv vs B).get t i = x := by
  cases t with
  | i32 => simp [Env.get, valEnv, hv]
  | i64 => simp [Env.get, valEnv, hv]

/-- Typed arguments are the arguments of their placeholder environment. -/
theorem argsOf_valEnv {S : FnSpec} {vs : List Val} (B : ByteArray) (h : TypedVals S.params vs) :
    argsOf S (valEnv vs B) = vs := by
  obtain ⟨hl, hi⟩ := h
  apply List.ext_getElem (by simp [argsOf, hl])
  intro i h₁ h₂
  have hi' : i < S.params.length := by simpa [argsOf] using h₁
  obtain ⟨x, hx⟩ := hi i hi'
  have hv : vs[i]? = some (.num ⟨.int S.params[i], x⟩) := by
    rw [List.getElem?_eq_getElem h₂, hx]
  simp only [argsOf, List.getElem_mapIdx, hx, get_valEnv hv]

/-- The memory condition of a function without memory. -/
theorem memOk_empty {H : Type} {S : FnSpec} (hm : S.mem = false) (s : Store H) (mi : ModuleInst) :
    Silmaril.Wasm.Auto2.VCGen.MemOk S s mi ByteArray.empty := by
  simp [Silmaril.Wasm.Auto2.VCGen.MemOk, hm]

theorem eq_empty_of_memOk {H : Type} {S : FnSpec} (hm : S.mem = false) {s : Store H}
    {mi : ModuleInst} {B : ByteArray} (h : Silmaril.Wasm.Auto2.VCGen.MemOk S s mi B) : B = ByteArray.empty := by
  simpa [Silmaril.Wasm.Auto2.VCGen.MemOk, hm] using h

/-- The globals condition of a function without globals. -/
theorem globOk_nil {H : Type} {S : FnSpec} (hg : S.globals = []) {s : Store H} {mi : ModuleInst}
    {ρ : Env} : GlobOk S s mi ρ :=
  ⟨fun g _ _ hg' => by simp [hg] at hg', fun g t ht => by simp [hg] at ht⟩

/-! ## Reference functions -/

/-- The precondition of the contract at the typed arguments of an accepted call. -/
theorem pre_of_invokeOk {e : VcEntry} {m : Module} {j : Nat} {mt : CModuleType}
    {I : Silmaril.Wasm.Game.ScalarInstance} {ft : FnType} {fi : FuncInst Nat}
    (hI : instance? m = some (mt, I)) (hft : I.exports[j]? = some ft)
    (hfi : I.store.funcs[I.addrs.getD j 0]? = some fi)
    (hps : ft.params.mapM scalarInt? = some e.S.params)
    (hpre : ∀ ρ : Env, ρ.mem 0 = ByteArray.empty → e.S.preF.den e.F ρ ρ) {vs : List Val}
    (hvs : InvokeOk I.store (I.addrs.getD j 0) vs) :
    TypedVals e.S.params vs ∧
      (fspec e.F e.S (I.addrs.getD j 0) fi).pre I.store vs := by
  have he : Expand fi.type ft.toComp := export_expand hI hft hfi
  obtain ⟨fi', ps, rs, hfi', he', hf⟩ := hvs
  have : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
  subst this
  have hcomp := Expand.func_eq he' he
  simp only [FnType.toComp] at hcomp
  injection hcomp with hc₁ hc₂
  rw [hc₁, Ty.toList_ofList] at hf
  have htv : TypedVals e.S.params vs := typedVals_of_forall₂ hps hf
  refine ⟨htv, hfi, fun c hc => ?_, valEnv vs ByteArray.empty,
    (argsOf_valEnv _ htv).symm, memOk_empty e.mem _ _, globOk_nil e.globals, hpre _ rfl⟩
  rw [e.calls] at hc
  cases hc

/-- A result the postcondition allows is allowed by the reference function. -/
theorem returns_mem_specOfFn {e : VcEntry} {f : List Val → Option Result} (hf : RefOK e f)
    {a : Nat} {fi : FuncInst Nat} {s s' : Store Nat} {vs : List Val}
    {o : Silmaril.Wasm.Logic.Core.Outcome} (htv : TypedVals e.S.params vs)
    (hpost : (fspec e.F e.S a fi).post s vs s' o) :
    ∃ res, o = .normal res ∧ Behaviour.returns res ∈ specOfFn f vs := by
  obtain ⟨B', G, -, hG, res, rfl, -, hty, hq⟩ := hpost
  obtain rfl : G = [] := by simpa [e.globals] using hG
  have hd : e.S.post.den e.F (valEnv vs ByteArray.empty) (valEnv res B') := by
    simpa using hq (valEnv vs ByteArray.empty) (argsOf_valEnv _ htv).symm (memOk_empty e.mem _ _)
      (globOk_nil e.globals)
  refine ⟨res, rfl, ?_⟩
  unfold specOfFn
  rcases hf vs res B' htv hty hd with hs | hs
  · rw [hs]
    rfl
  · rw [hs]
    trivial

theorem specOfFn_nonempty (f : List Val → Option Result) (vs : List Val) :
    (specOfFn f vs).Nonempty := by
  unfold specOfFn
  split
  · exact Set.singleton_nonempty _
  · exact Set.univ_nonempty

/-- What a check gives at the computed instance: the total specification of the export and the
precondition at every accepted call. -/
theorem tspec_of_vcCheck {e : VcEntry} {m : Module} {j : Nat} (h : vcCheck e m j = true)
    (hpre : ∀ ρ : Env, ρ.mem 0 = ByteArray.empty → e.S.preF.den e.F ρ ρ) :
    ∃ fi, TFSpecAt P SingleThreaded.Det.noHost (addrOf m j) (fspec e.F e.S (addrOf m j) fi) ∧
      ∀ vs, InvokeOk (instOf m).store (addrOf m j) vs → TypedVals e.S.params vs ∧
        (fspec e.F e.S (addrOf m j) fi).pre (instOf m).store vs := by
  obtain ⟨mt, I, ft, fi, code, hI, hft, hfi, hc, hps, hrs, hvc⟩ := vcCheck_inv h
  have haddr : addrOf m j = I.addrs.getD j 0 := by simp [addrOf, instOf_eq hI]
  have hfi' : (instOf m).store.funcs[addrOf m j]? = some fi := by rw [instOf_eq hI, haddr, hfi]
  refine ⟨fi, modTSpec_of_vcCheck h fi hfi', fun vs hvs => ?_⟩
  rw [instOf_eq hI, haddr] at hvs ⊢
  exact pre_of_invokeOk hI hft hfi hps hpre hvs

/-- **A checked contract meets a reference function** that agrees with every result its
postcondition allows (or leaves the result open), at every profile, for every reflexive
relation. -/
theorem modMeets_of_vcCheck {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {e : VcEntry} {m : Module} {j : Nat} {f : List Val → Option Result}
    (h : vcCheck e m j = true)
    (hpre : ∀ ρ : Env, ρ.mem 0 = ByteArray.empty → e.S.preF.den e.F ρ ρ) (hf : RefOK e f) :
    ModMeets R P m j f := by
  obtain ⟨fi, hts, hok⟩ := tspec_of_vcCheck (P := P) h hpre
  have hmeets : Equiv.Meets (entryPoints P SingleThreaded.Det.noHost) (OrDiv R)
      (instOf m).store (addrOf m j) (specOfFn f) :=
    meets_orDiv_of_fspecValid hR hts.valid (fun vs hvs => (hok vs hvs).2)
      (fun vs _ _ hvs hpost => returns_mem_specOfFn hf (hok vs hvs).1 hpost)
      (specOfFn_nonempty f)
  intro vs hvs b hb
  obtain ⟨b', hb', hr⟩ := hmeets vs hvs b hb
  refine ⟨b', hb', hr.resolve_left fun hd => ?_⟩
  have hdiv : Diverges P SingleThreaded.Det.noHost (invoke (instOf m).store (addrOf m j) vs) :=
    diverges_mem_behavioursOf_iff.mp (hd ▸ hb)
  exact hts.invoke_terminates (hok vs hvs).2 hdiv

/-- A proved reference contract, checked at export `j` of `m`. -/
theorem RefEntry.meets {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    (r : RefEntry) {m : Module} {j : Nat} (h : vcCheck r.e m j = true) : ModMeets R P m j r.f :=
  modMeets_of_vcCheck hR h r.pre r.ref

/-- **A `proved` verdict of the front end with the VC stage** is `ModMeets` at every profile. -/
theorem checkMeetsVC_proved {R : Silmaril.Wasm.Auto.Front.Rel} {r : RefEntry} {m : Module}
    {j n : Nat} (h : (checkMeetsVC R r m j n).verdict = .proved) : ModMeets R.toProp P m j r.f := by
  unfold checkMeetsVC at h
  by_cases hv : vcCheck r.e m j = true
  · exact r.meets (Silmaril.Wasm.Auto.Bridge.rel_refl R) hv
  · exfalso
    simp only [hv, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · rename_i hb
      rw [hb] at h
      cases h
    · cases h

end Silmaril.Wasm.Auto2.VCBridge
