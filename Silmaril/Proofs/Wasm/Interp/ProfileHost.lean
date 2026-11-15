module

public import Silmaril.Proofs.Wasm.Interp.Profile

@[expose] public section

/-!
# Native-profile configurations with host functions: closure and profile transfer (proofs)

`Silmaril.Proofs.Wasm.Interp.Profile` closes native-profile code (`NAdmins`) under Core steps for
stores without host functions (`Binaryen.NativeFuncsOk`). Here the store may contain host
functions: `NativeWasmFuncs` asks only that its Wasm functions be native-profile code, and the
explicit host side condition `HostNative` that host answers keep this and never throw (a thrown
host exception is a `throw_ref`, outside the native profile). Then `NHConfig` is closed under
Core steps of every profile (`NHConfig.step`), and runs, normal forms and divergence are the same
at every profile (`steps_profileH`, `normal_profile`, `diverges_profileH`): the profile
enters only through `step_profile`, which holds for every host.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen

variable {H : Type}

theorem NativeWasmFuncs.of_nativeFuncsOk {F : List (FuncInst H)} (h : NativeFuncsOk F) :
    NativeWasmFuncs F := by
  intro fi hfi fn hfn
  obtain ⟨fn', hfn', hb⟩ := h fi hfi
  rw [hfn] at hfn'
  cases hfn'
  exact hb

/-- The code a call of a native Wasm function enters. -/
theorem nAdmins_calleeW {F : List (FuncInst H)} (hF : NativeWasmFuncs F) {a n : Nat}
    {fi : FuncInst H} {code : Func} (hf : F[a]? = some fi) (hcode : fi.code = .wasm code)
    (fr : Frame) : NAdmins [.frame n fr [.label n [] (expression code.body)]] := by
  rw [nAdmins_frame_iff, nAdmins_label_iff]
  exact ⟨List.forall_mem_nil _, nAdmins_expression (hF fi (List.mem_of_getElem? hf) code hcode)⟩

/-- A non-throwing host result is native-profile code. -/
theorem nAdmins_result {r : Result} (hr : ∀ t, r ≠ .throw t) : NAdmins r.toAdmin := by
  cases r with
  | values vs => exact nAdmins_vals vs
  | throw t => exact (hr t rfl).elim
  | trap => simp [Result.toAdmin]

set_option linter.unusedTactic false in
/-- **Preservation with host functions**: a Core step, at any profile, keeps native-profile code
native-profile and the store's Wasm functions native-profile, for a `HostNative` host. -/
theorem nAdmins_stepH {P : Profile} {host : HostSemantics H} (hN : HostNative host)
    {c c' : Config H} (h : Step P host c c') (hc : NAdmins c.code)
    (hF : NativeWasmFuncs c.store.funcs) :
    NAdmins c'.code ∧ NativeWasmFuncs c'.store.funcs := by
  induction h with
  | parametric h | numeric h | vector h | «variable» h | table h | reference h | aggregate h =>
    cases h <;> n_simp
  | memory h => cases h <;> simp_all [aconst, load8u, store8, Store.setData, Store.setMem] <;> n_simp
  | ctxtInstrs _ _ ih => exact ⟨hc.replace_mid (ih hc.mid hF).1, (ih hc.mid hF).2⟩
  | ctxtLabel _ ih => exact ⟨hc.replace_label (ih hc.label hF).1, (ih hc.label hF).2⟩
  | ctxtHandler _ ih =>
    exact ⟨nAdmins_handler_iff.mpr (ih (nAdmins_handler_iff.mp hc) hF).1,
      (ih (nAdmins_handler_iff.mp hc) hF).2⟩
  | ctxtFrame _ ih =>
    exact ⟨nAdmins_frame_iff.mpr (ih (nAdmins_frame_iff.mp hc) hF).1,
      (ih (nAdmins_frame_iff.mp hc) hF).2⟩
  | callRefFunc _ hf _ _ hcode => exact ⟨nAdmins_calleeW hF hf hcode _, hF⟩
  | callRefHost _ _ _ _ _ hhost =>
    exact ⟨nAdmins_result fun t ht => hN.noThrow _ _ _ _ t (ht ▸ hhost),
      hN.funcs _ _ _ _ _ hhost hF⟩
  | callRefHostDiv => exact ⟨hc, hF⟩
  | returnCallRefFrameAddr hcr => exact ⟨nAdmins_retToCall hcr hc, hF⟩
  | _ => n_simp ; all_goals first | exact nAdmins_expression hc.2 | exact nAdmins_expression hc.1

/-- The native-profile invariant with host functions. -/
def NHConfig (c : Config H) : Prop := NAdmins c.code ∧ NativeWasmFuncs c.store.funcs

theorem NHConfig.step {P : Profile} {host : HostSemantics H} (hN : HostNative host)
    {c c' : Config H} (hc : NHConfig c) (h : Step P host c c') : NHConfig c' :=
  nAdmins_stepH hN h hc.1 hc.2

theorem NHConfig.steps {P : Profile} {host : HostSemantics H} (hN : HostNative host)
    {c c' : Config H} (hc : NHConfig c) (h : Steps P host c c') : NHConfig c' := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact ih.step hN hs

theorem nhConfig_invoke {s : Store H} (hF : NativeWasmFuncs s.funcs) (a : Nat) (vs : List Val) :
    NHConfig (invoke s a vs) :=
  ⟨nAdmins_invoke s a vs, hF⟩

/-- Runs transfer between profiles. -/
theorem steps_profileH {P P' : Profile} {host : HostSemantics H} (hN : HostNative host)
    {c c' : Config H} (h : Steps P host c c') (hc : NHConfig c) : Steps P' host c c' := by
  induction h with
  | refl => exact .refl
  | tail hst hs ih => exact ih.tail (step_profile hs (hc.steps hN hst).1)

/-- Divergence transfers between profiles. -/
theorem diverges_profileH {P P' : Profile} {host : HostSemantics H} (hN : HostNative host)
    {c : Config H} (h : Diverges P host c) (hc : NHConfig c) : Diverges P' host c := by
  refine Silmaril.InfiniteTrace.of_map (R := Step P' host) (S := Step P host) id NHConfig ?_ hc h
  intro a b ha hab
  exact ⟨b, step_profile hab ha.1, ha.step hN hab, rfl⟩

end Silmaril.Wasm.Interp
