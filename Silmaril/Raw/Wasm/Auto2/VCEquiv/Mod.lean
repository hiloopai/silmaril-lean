module

public import Silmaril.Wasm.Auto2.VCEquiv.Defs
public import Silmaril.Wasm.Auto2.VCBridge.Thms
public import Silmaril.Wasm.Auto.Bridge.Thms

/-!
# Equivalence through a shared contract: soundness (unrefined)

* `pre_of_typed`: typed arguments meet the precondition of a contract without callees, memory
  or precondition;
* `behaviours_of_vcCheck_typed`: an export that passes `vcCheck e` has exactly the behaviour
  `returns res` on typed arguments, when the reference function determined by `e` gives `res`;
* **`modEquiv_of_vcEquivWith`**, **`modEquiv_of_vcEquiv`**, `modEquiv_of_vcEquivAny`: the checks
  of `Silmaril.Wasm.Auto2.VCEquiv.Defs` prove `ModEquiv` at every profile, for every reflexive
  relation.

New proofs (unrefined).
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCEquiv

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Auto2.VCBridge
open Silmaril.Wasm.Verify (instOf)
open Silmaril.Wasm.Auto.Front (addrOf ModRefines ModEquiv)
open Silmaril.Wasm.Auto.Equiv (TypedVals)

variable {P : Profile}

/-- Typed arguments meet the precondition of a checked contract. -/
theorem pre_of_typed {e : VcEntry} {m : Module} {j : Nat} {fi : FuncInst Nat}
    (hfi : (instOf m).store.funcs[addrOf m j]? = some fi)
    (hpre : ∀ ρ : Env, ρ.mem 0 = ByteArray.empty → e.S.preF.den e.F ρ ρ) {vs : List Val}
    (htv : TypedVals e.S.params vs) :
    (fspec e.F e.S (addrOf m j) fi).pre (instOf m).store vs := by
  refine ⟨hfi, fun c hc => ?_, valEnv vs ByteArray.empty, (argsOf_valEnv _ htv).symm,
    memOk_empty e.mem _ _, globOk_nil e.globals, hpre _ rfl⟩
  rw [e.calls] at hc
  cases hc

/-- **The behaviour of a checked export on typed arguments**: it returns `f`'s values. -/
theorem behaviours_of_vcCheck_typed {e : VcEntry} {f : List Val → Option Result} {m : Module}
    {j : Nat} (h : vcCheck e m j = true)
    (hpre : ∀ ρ : Env, ρ.mem 0 = ByteArray.empty → e.S.preF.den e.F ρ ρ) (hf : RefOK e f)
    {vs res : List Val} (htv : TypedVals e.S.params vs) (hres : f vs = some (.values res)) :
    behaviours P SingleThreaded.Det.noHost (instOf m).store (addrOf m j) vs = {.returns res} := by
  obtain ⟨mt, I, ft, fi, code, hI, hft, hfi, hc, hps, hrs, hvc⟩ := vcCheck_inv h
  have haddr : addrOf m j = I.addrs.getD j 0 := by simp [addrOf, instOf_eq hI]
  have hfi' : (instOf m).store.funcs[addrOf m j]? = some fi := by rw [instOf_eq hI, haddr, hfi]
  refine Silmaril.Wasm.Auto.Bridge.behaviours_eq_of_tfspec (modTSpec_of_vcCheck (P := P) h fi hfi')
    (pre_of_typed hfi' hpre htv) ?_
  intro s' o hpost
  obtain ⟨B', G, -, hG, res', rfl, -, hty, hq⟩ := hpost
  obtain rfl : G = [] := by simpa [e.globals] using hG
  have hd : e.S.post.den e.F (valEnv vs ByteArray.empty) (valEnv res' B') := by
    simpa using hq (valEnv vs ByteArray.empty) (argsOf_valEnv _ htv).symm (memOk_empty e.mem _ _)
      (globOk_nil e.globals)
  rcases hf vs res' B' htv hty hd with hs | hs
  · rw [hres] at hs
    cases hs
    rfl
  · rw [hres] at hs
    cases hs

/-- An accepted call of a checked export has typed arguments. -/
theorem typed_of_vcCheck {e : VcEntry} {m : Module} {j : Nat} (h : vcCheck e m j = true)
    (hpre : ∀ ρ : Env, ρ.mem 0 = ByteArray.empty → e.S.preF.den e.F ρ ρ) {vs : List Val}
    (hvs : InvokeOk (instOf m).store (addrOf m j) vs) : TypedVals e.S.params vs := by
  obtain ⟨mt, I, ft, fi, code, hI, hft, hfi, -, hps, -, -⟩ := vcCheck_inv h
  have haddr : addrOf m j = I.addrs.getD j 0 := by simp [addrOf, instOf_eq hI]
  rw [instOf_eq hI, haddr] at hvs
  exact (pre_of_invokeOk hI hft hfi hps hpre hvs).1

/-- The behaviour of `f`'s result. -/
def resBeh (f : List Val → Option Result) (vs : List Val) : Behaviour Val :=
  match f vs with
  | some r => r.toBehaviour
  | none => .traps

/-- The behaviour of a checked export, on every argument list it accepts. -/
theorem behaviours_of_vcCheck {F : EqFun} {e : VcEntry} (he : e ∈ F.es) {m : Module} {j : Nat}
    (h : vcCheck e m j = true) {vs : List Val} (htv : TypedVals e.S.params vs) :
    behaviours P SingleThreaded.Det.noHost (instOf m).store (addrOf m j) vs =
      {resBeh F.f vs} := by
  obtain ⟨res, hres⟩ := F.tot e he vs htv
  rw [behaviours_of_vcCheck_typed h (F.pre e he) (F.ref e he) htv hres]
  simp only [resBeh, hres]
  rfl

/-- Refinement from two checked contracts of one functional contract. -/
theorem modRefines_of_vcEquivWith {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {F : EqFun} {e₁ e₂ : VcEntry} (he₁ : e₁ ∈ F.es) (he₂ : e₂ ∈ F.es) {m₁ m₂ : Module}
    {j : Nat} (h : vcEquivWith e₁ e₂ m₁ m₂ j = true) : ModRefines R P m₁ m₂ j := by
  simp only [vcEquivWith, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hp, h₁⟩, h₂⟩ := h
  refine Silmaril.Wasm.Auto.Bridge.exportRefines_of_singletonB hR (resBeh F.f)
    (fun vs hvs => ?_) (fun vs hvs => ?_)
  · exact behaviours_of_vcCheck he₁ h₁ (typed_of_vcCheck h₁ (F.pre e₁ he₁) hvs)
  · have htv := typed_of_vcCheck h₁ (F.pre e₁ he₁) hvs
    rw [hp] at htv
    exact behaviours_of_vcCheck he₂ h₂ htv

theorem vcEquivWith_symm {e₁ e₂ : VcEntry} {m₁ m₂ : Module} {j : Nat}
    (h : vcEquivWith e₁ e₂ m₁ m₂ j = true) : vcEquivWith e₂ e₁ m₂ m₁ j = true := by
  simp only [vcEquivWith, Bool.and_eq_true, beq_iff_eq] at h ⊢
  exact ⟨⟨h.1.1.symm, h.2⟩, h.1.2⟩

/-- **Two checked contracts of one functional contract prove module equivalence**, every
profile, every reflexive relation. -/
theorem modEquiv_of_vcEquivWith {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {F : EqFun} {e₁ e₂ : VcEntry} (he₁ : e₁ ∈ F.es) (he₂ : e₂ ∈ F.es) {m₁ m₂ : Module}
    {j : Nat} (h : vcEquivWith e₁ e₂ m₁ m₂ j = true) : ModEquiv R P m₁ m₂ j :=
  ⟨modRefines_of_vcEquivWith hR he₁ he₂ h,
    modRefines_of_vcEquivWith (R := fun x y => R y x) hR he₂ he₁ (vcEquivWith_symm h)⟩

/-- **`vcEquiv` proves module equivalence**, every profile, every reflexive relation. -/
theorem modEquiv_of_vcEquiv {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {F : EqFun} {m₁ m₂ : Module} {j : Nat} (h : vcEquiv F m₁ m₂ j = true) :
    ModEquiv R P m₁ m₂ j := by
  simp only [vcEquiv, List.any_eq_true] at h
  obtain ⟨e₁, he₁, e₂, he₂, h⟩ := h
  exact modEquiv_of_vcEquivWith hR he₁ he₂ h

/-- `vcEquivAny` proves module equivalence. -/
theorem modEquiv_of_vcEquivAny {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {L : List EqFun} {m₁ m₂ : Module} {j : Nat} (h : vcEquivAny L m₁ m₂ j = true) :
    ModEquiv R P m₁ m₂ j := by
  simp only [vcEquivAny, List.any_eq_true] at h
  obtain ⟨F, -, h⟩ := h
  exact modEquiv_of_vcEquiv hR h

end Silmaril.Wasm.Auto2.VCEquiv
