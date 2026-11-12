module

public import Silmaril.Wasm.WatSpec.Defs
public import Silmaril.Wasm.Logic.VC.Thms
public import Silmaril.Wasm.Logic.VCTotal.Thms
public import Silmaril.Wasm.Verify.FnSpec.Thms

/-!
# Annotated WAT: soundness of the verification condition

`Annotated.sound`: a proof of `A.vc` gives the specification `A.spec fi a` for every function
instance `fi` running `A.func` with a matching type, at every profile and for every host
relation (by `Silmaril.Wasm.Logic.VC.FSpecValid.of_wpc`). `Annotated.invoke`: then every run of
the embedder's `$invoke` on arguments meeting the precondition can still step, or has returned
results meeting the postcondition with the store unchanged.

`Annotated.vc_toFnSpec`, `Annotated.verified`, `AnnotatedSt.toFnSpec_sound`: the annotated
forms as front-ends of `Silmaril.Wasm.Verify.FnSpec`.
-/

@[expose] public section

namespace Silmaril.Wasm.WatSpec

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare (FSpecValid)

variable {P : Profile} {host : HostSemantics Nat}

/-- **Soundness of annotated WAT**: the verification condition gives the specification. -/
theorem Annotated.sound (A : Annotated) (hvc : A.vc) {fi : FuncInst Nat} {a : Nat}
    {ps rs : Validation.Ty (.list .val)} (hc : fi.code = .wasm A.func)
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = A.nparams)
    (hrs : rs.length = A.nresults) : FSpecValid P host a (A.spec fi a) := by
  refine Silmaril.Wasm.Logic.VC.FSpecValid.of_wpc (fun args s => A.inv args s) (fun _ _ h => h.1)
    hc he (fun s args h => ((hvc fi.module s args h.2).1).trans hps.symm) (fun s args h => ?_)
  rw [hrs]
  exact (hvc fi.module s args h.2).2

/-- **Every run of `$invoke`** of a function meeting an annotated specification, on arguments
meeting the precondition, can still step or has returned results meeting the postcondition,
with the store unchanged. -/
theorem Annotated.invoke {A : Annotated} {fi : FuncInst Nat} {a : Nat} {s : Store Nat}
    {args : List Val} (hv : FSpecValid P host a (A.spec fi a)) (hfi : s.funcs[a]? = some fi)
    (hpre : A.pre args) {c' : Config Nat} (hs : Steps P host (invoke s a args) c') :
    (∃ c'', Step P host c' c'') ∨ ∃ res, A.post args res ∧ c' = ⟨s, {}, vals res⟩ := by
  rcases Silmaril.Wasm.Logic.Hoare.FSpecValid.invoke_safe hv ⟨hfi, hpre⟩ hs with h | ⟨o, he, hp⟩
  · exact .inl h
  · right
    obtain ⟨hf, hr⟩ := hp
    rcases hr with ⟨res', rfl, rfl, res, ho, hpost⟩ | ⟨rfl, -, res, ho, -⟩ | ⟨b, rfl, -, res, ho, -⟩
    · obtain ⟨cs, cf, cc⟩ := c'
      have hres : res' = res := by simpa using ho
      have hc : cc = vals res' := he
      refine ⟨res, hpost, ?_⟩
      simp_all
    · cases ho
    · cases ho

/-! ## The `FnSpec` forms -/

/-- **A `wat_spec!` condition is the condition of its `FnSpec` form.** -/
theorem Annotated.vc_toFnSpec {A : Annotated} (hvc : A.vc) : A.toFnSpec.vc A.func := by
  intro x mi s hp
  have h := (hvc mi s x.1 hp).2
  have e : (fun s' o => s' = s ∧ ∃ res, o = .normal res ∧ A.post x.1 res) =
      (fun s' (o : Silmaril.Wasm.Logic.Core.Outcome) =>
        ∃ res, o = .normal res ∧ (s' = s ∧ A.post x.1 res)) := by
    funext s' o
    exact propext ⟨fun ⟨h₁, res, h₂, h₃⟩ => ⟨res, h₂, h₁, h₃⟩,
      fun ⟨res, h₂, h₁, h₃⟩ => ⟨h₁, res, h₂, h₃⟩⟩
  rw [e] at h
  exact h

/-- An annotated function is a `Silmaril.Wasm.Verify.Verified` function of its module. -/
theorem Annotated.verified {A : Annotated} (hvc : A.vc) (hm : A.module.funcs ≠ []) :
    Silmaril.Wasm.Verify.Verified A.module 0 A.toFnSpec := by
  obtain ⟨fn, r, hf⟩ := List.exists_cons_of_ne_nil hm
  have h := Annotated.vc_toFnSpec hvc
  have e : A.func = fn := by simp [Annotated.func, hf]
  exact ⟨fn, by rw [hf]; rfl, e ▸ h⟩

/-- **The `FnSpec` form of a store-annotated function is sound**: a proof of its condition (no
`return`, no calls) gives, for each argument list, the call specification of
`Silmaril.Wasm.Verify.FnSpec.fspec` (the precondition and postcondition of `A.spec fi a` at those
arguments). -/
theorem AnnotatedSt.toFnSpec_sound (A : AnnotatedSt) (hvc : A.toFnSpec.vc A.func)
    {fi : FuncInst Nat} {a : Nat} {ps rs : Validation.Ty (.list .val)}
    (hc : fi.code = .wasm A.func) (he : Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = A.nparams) (hrs : rs.length = A.nresults) (x : Args A.nparams) :
    FSpecValid P host a (A.toFnSpec.fspec fi a x) :=
  Silmaril.Wasm.Verify.FnSpec.sound hvc hc he (fun x => x.2.trans hps.symm) hrs x

/-! ## Functions over the store -/

/-- **Soundness of store-annotated WAT**: the verification condition (with a spec context valid
at `P` and `host` for the calls of the body) gives the specification `A.spec fi a`. -/
theorem AnnotatedSt.sound (A : AnnotatedSt) {Γ : Silmaril.Wasm.Logic.VC.VCSpecs Nat}
    (hΓ : Γ.Valid P host) (hvc : A.vc Γ) {fi : FuncInst Nat} {a : Nat}
    {ps rs : Validation.Ty (.list .val)} (hc : fi.code = .wasm A.func)
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = A.nparams)
    (hrs : rs.length = A.nresults) : FSpecValid P host a (A.spec fi a) := by
  refine Silmaril.Wasm.Logic.VC.FSpecValid.of_wpc_fn hΓ (fun args s => A.inv fi.module args s)
    (fun _ _ h => h.1) hc he (fun s args h => ((hvc fi.module s args h.2).1).trans hps.symm)
    (fun s args h => ?_)
  rw [hrs]
  exact (hvc fi.module s args h.2).2

/-- `AnnotatedSt.sound` without calls (the empty spec context). -/
theorem AnnotatedSt.sound₀ (A : AnnotatedSt) (hvc : A.vc) {fi : FuncInst Nat} {a : Nat}
    {ps rs : Validation.Ty (.list .val)} (hc : fi.code = .wasm A.func)
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = A.nparams)
    (hrs : rs.length = A.nresults) : FSpecValid P host a (A.spec fi a) :=
  A.sound Silmaril.Wasm.Logic.VC.VCSpecs.valid_empty hvc hc he hps hrs

/-! ## Read-back lemmas for `gv` -/

section Gv

open Silmaril.Wasm.Logic.VC

variable {H : Type} {s : Store H} {mi : ModuleInst} {x k : Nat} {v : Val}

theorem gv_of_globalVal (h : globalVal s mi k = some v) : gv s mi k = valNum v := by
  simp [gv, h]

theorem gv_set_self (h : (globalVal s mi x).isSome) : gv (setGlobalIdx s mi x v) mi x = valNum v := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h
  simp [gv, globalVal_setGlobalIdx_self, hu]

theorem gv_set_ne (hnd : mi.globals.Nodup) (hk : k ≠ x) :
    gv (setGlobalIdx s mi x v) mi k = gv s mi k := by
  simp only [gv, globalVal_setGlobalIdx_ne hnd hk]

@[simp] theorem valNum_i64 (b : BitVec 64) : valNum (.num ⟨.int .i64, b⟩) = b := rfl
@[simp] theorem valNum_i32 (b : BitVec 32) : valNum (.num ⟨.int .i32, b⟩) = b.setWidth 64 := rfl

end Gv

end Silmaril.Wasm.WatSpec
