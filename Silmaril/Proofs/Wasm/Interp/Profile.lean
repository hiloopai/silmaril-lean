module

public import Silmaril.Wasm.Interp.Defs
public import Silmaril.Wasm.Binaryen.AdequacyModule

@[expose] public section

/-!
# Native-profile Core configurations: closure and profile independence (proofs)

`NAdmins` (native-profile administrative code) is closed under Core steps of every profile and
host, as long as every function of the store is native-profile Wasm code
(`Binaryen.NativeFuncsOk`), and the store's functions never change (`nAdmins_step`,
`nAdmins_steps`). On such configurations a Core step at one profile is a step at every other
(`step_profile`): only the numeric, vector, table and memory rules of `Step` mention the profile,
and the only ones applicable to native code — the integer `NumericStep` rules — have no
profile premise. Consequently runs, divergence and behaviours are profile-independent
(`steps_profile_iff`, `diverges_profile_iff`, `behaviours_profile`).

Adapted from silmaril-lean's `Binaryen.okAdmins_step` (`Silmaril/Wasm/Binaryen/NoThrow.lean`)
and `Step.of_noHost`; the profile transfer is new. Summary in `Silmaril.Wasm.Interp.Thms`.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen

variable {H : Type}

/-! ## The invariant -/

@[simp] theorem nAdmins_nil : NAdmins ([] : List Admin) := trivial

@[simp] theorem nAdmins_cons {a : Admin} {as : List Admin} :
    NAdmins (a :: as) ↔ NAdmin a ∧ NAdmins as := Iff.rfl

@[simp] theorem nAdmins_append {as bs : List Admin} :
    NAdmins (as ++ bs) ↔ NAdmins as ∧ NAdmins bs := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih, and_assoc]

@[simp] theorem nAdmin_plain {i : Instr} : NAdmin (.plain i) ↔ NInstr i := Iff.rfl

@[simp] theorem nAdmin_label {n : Nat} {cont : List Instr} {body : List Admin} :
    NAdmin (.label n cont body) ↔ (∀ i ∈ cont, instrInNativeProfile i) ∧ NAdmins body :=
  Iff.rfl

@[simp] theorem nAdmin_handler {n : Nat} {cs : List Catch} {body : List Admin} :
    NAdmin (.handler n cs body) ↔ NAdmins body := Iff.rfl

@[simp] theorem nAdmin_frame {n : Nat} {f : Frame} {body : List Admin} :
    NAdmin (.frame n f body) ↔ NAdmins body := Iff.rfl

@[simp] theorem nAdmin_ref {r : Ref} : NAdmin (.ref r) := trivial

@[simp] theorem nAdmin_callRefType {d} : NAdmin (.callRefType d) := trivial

@[simp] theorem nAdmin_returnCallRefType {d} : NAdmin (.returnCallRefType d) := trivial

@[simp] theorem nAdmin_trap : NAdmin .trap := trivial

@[simp] theorem nAdmin_toAdmin (v : Val) : NAdmin v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;>
    simp only [Val.toAdmin, nAdmin_plain, nAdmin_ref, NInstr]
  all_goals first
    | exact Or.inl ((instrInNativeProfile_flat' (by simp) (by simp) (by simp)).2 rfl)
    | exact Or.inr (Or.inl ⟨_, _, rfl⟩)
    | exact Or.inr (Or.inr ⟨_, rfl⟩)

@[simp] theorem nAdmins_vals (vs : List Val) : NAdmins (vals vs) := by
  induction vs with
  | nil => trivial
  | cons v vs ih => exact ⟨nAdmin_toAdmin v, ih⟩

@[simp] theorem nAdmin_constI32 (b : BitVec 32) : NAdmin (constI32 b) := nAdmin_toAdmin _

theorem nAdmins_expression {is : List Instr} (h : ∀ i ∈ is, instrInNativeProfile i) :
    NAdmins (expression is) := by
  induction is with
  | nil => trivial
  | cons i is ih =>
    exact ⟨Or.inl (h i (List.mem_cons_self ..)), ih fun j hj => h j (List.mem_cons_of_mem _ hj)⟩

/-- The invoked configuration is native-profile code. -/
theorem nAdmins_invoke (s : Store H) (a : Nat) (vs : List Val) :
    NAdmins (invoke s a vs).code := by
  simp [invoke]

macro "n_simp" : tactic => `(tactic| simp_all [NInstr, instrInNativeProfile_block,
  instrInNativeProfile_loop, instrInNativeProfile_if, not_instrInNativeProfile_tryTable,
  instrInNativeProfile_flat', structuredInstr, nativeInstr, throwing, Store.setGlobal,
  Store.setMem])

theorem nAdmin_retToCallIn {m : ModuleInst} {c : Admin} (hc : c.IsReturnCallRef)
    (h : NAdmin c) : NAdmin (c.retToCallIn m) := by
  unfold Admin.IsReturnCallRef at hc
  split at hc
  · simp [NInstr, instrInNativeProfile_flat', nativeInstr] at h
  · simp [Admin.retToCallIn]
  · exact absurd hc id

/-- No host function is reachable in a native store. -/
theorem not_host_of_native {F : List (FuncInst H)} (hF : NativeFuncsOk F) {a : Nat}
    {fi : FuncInst H} (hf : F[a]? = some fi) {h : H} (hcode : fi.code = .host h) : False := by
  obtain ⟨fn, hfn, -⟩ := hF fi (List.mem_of_getElem? hf)
  rw [hcode] at hfn
  cases hfn

/-! ## Closure -/

/-! ### Contexts -/

section Contexts

variable {vs : List Val} {is is' rest : List Admin} {n : Nat}

theorem NAdmins.mid (h : NAdmins (vals vs ++ is ++ rest)) : NAdmins is := by
  simp only [nAdmins_append] at h
  exact h.1.2

theorem NAdmins.replace_mid (h : NAdmins (vals vs ++ is ++ rest)) (h' : NAdmins is') :
    NAdmins (vals vs ++ is' ++ rest) := by
  simp only [nAdmins_append] at h ⊢
  exact ⟨⟨h.1.1, h'⟩, h.2⟩

theorem nAdmins_label_iff {cont : List Instr} :
    NAdmins [.label n cont is] ↔ (∀ i ∈ cont, instrInNativeProfile i) ∧ NAdmins is := by
  simp

theorem nAdmins_handler_iff {cs : List Catch} : NAdmins [.handler n cs is] ↔ NAdmins is := by
  simp

theorem nAdmins_frame_iff {f : Frame} : NAdmins [.frame n f is] ↔ NAdmins is := by
  simp

theorem NAdmins.label {cont : List Instr} (h : NAdmins [.label n cont is]) : NAdmins is :=
  (nAdmins_label_iff.mp h).2

theorem NAdmins.replace_label {cont : List Instr} (h : NAdmins [.label n cont is])
    (h' : NAdmins is') : NAdmins [.label n cont is'] :=
  nAdmins_label_iff.mpr ⟨(nAdmins_label_iff.mp h).1, h'⟩

end Contexts

/-- The code a call of a native function enters. -/
theorem nAdmins_callee {F : List (FuncInst H)} (hF : NativeFuncsOk F) {a n : Nat}
    {fi : FuncInst H} {code : Func} (hf : F[a]? = some fi) (hcode : fi.code = .wasm code)
    (fr : Frame) : NAdmins [.frame n fr [.label n [] (expression code.body)]] := by
  obtain ⟨fn, hfn, hbody⟩ := hF fi (List.mem_of_getElem? hf)
  have hfc : Func.body fn = code.body := by
    rw [hcode] at hfn
    cases hfn
    rfl
  rw [nAdmins_frame_iff, nAdmins_label_iff]
  exact ⟨List.forall_mem_nil _, nAdmins_expression (hfc ▸ hbody)⟩

/-- The call a `return_call_ref` leaves behind. -/
theorem nAdmins_retToCall {vs' vs : List Val} {a k : Nat} {c : Admin} {fi' : Frame}
    {rest : List Admin} (hcr : c.IsReturnCallRef)
    (hc : NAdmins [.frame k fi' (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]) :
    NAdmins (vals vs ++ [.ref (.func a), c.retToCallIn fi'.module]) := by
  have hcc : NAdmin c := by simp_all
  simpa using nAdmin_retToCallIn (m := fi'.module) hcr hcc

set_option linter.unusedTactic false in
/-- **Preservation**: a Core step, at any profile and host, keeps native-profile code
native-profile and leaves the functions of a native store unchanged. -/
theorem nAdmins_step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hc : NAdmins c.code) (hF : NativeFuncsOk c.store.funcs) :
    NAdmins c'.code ∧ c'.store.funcs = c.store.funcs := by
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
  | callRefFunc _ hf _ _ hcode => exact ⟨nAdmins_callee hF hf hcode _, rfl⟩
  | callRefHost _ hf _ _ hcode _ => exact (not_host_of_native hF hf hcode).elim
  | callRefHostDiv _ hf _ _ hcode _ => exact (not_host_of_native hF hf hcode).elim
  | returnCallRefFrameAddr hcr => exact ⟨nAdmins_retToCall hcr hc, rfl⟩
  | _ => n_simp ; all_goals first | exact nAdmins_expression hc.2 | exact nAdmins_expression hc.1

/-- The native-profile invariant (code and store) of a configuration. -/
def NConfig (c : Config H) : Prop := NAdmins c.code ∧ NativeFuncsOk c.store.funcs

theorem NConfig.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (hc : NConfig c) (h : Step P host c c') : NConfig c' := by
  obtain ⟨h1, h2⟩ := nAdmins_step h hc.1 hc.2
  exact ⟨h1, h2 ▸ hc.2⟩

theorem NConfig.steps {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (hc : NConfig c) (h : Steps P host c c') : NConfig c' := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact ih.step hs

theorem nConfig_invoke {s : Store H} (hF : NativeFuncsOk s.funcs) (a : Nat) (vs : List Val) :
    NConfig (invoke s a vs) :=
  ⟨nAdmins_invoke s a vs, hF⟩

/-! ## Profile independence -/

/-- **Profile transfer of one step**: on native-profile code, a Core step at profile `P` is a
step at every profile `P'` (same host). -/
theorem step_profile {P P' : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hN : NAdmins c.code) : Step P' host c c' := by
  induction h with
  | parametric h => exact .parametric h
  | numeric h =>
    cases h with
    | intUnOp => exact .numeric .intUnOp
    | intBinOp hz => exact .numeric (.intBinOp hz)
    | intBinOpTrap he => exact .numeric (.intBinOpTrap he)
    | intTestOp => exact .numeric .intTestOp
    | intRelOp => exact .numeric .intRelOp
    | _ => exfalso; n_simp
  | vector h => exfalso; cases h <;> n_simp
  | «variable» h => exact .«variable» h
  | table h => exfalso; cases h <;> n_simp
  | memory h => exfalso; cases h <;> n_simp
  | reference h => exact .reference h
  | aggregate h => exact .aggregate h
  | ctxtInstrs _ hne ih => exact .ctxtInstrs (ih hN.mid) hne
  | ctxtLabel _ ih => exact .ctxtLabel (ih hN.label)
  | ctxtHandler _ ih => exact .ctxtHandler (ih (nAdmins_handler_iff.mp hN))
  | ctxtFrame _ ih => exact .ctxtFrame (ih (nAdmins_frame_iff.mp hN))
  | block hbt hm => exact .block hbt hm
  | loop hbt hm => exact .loop hbt hm
  | ifTrue hc => exact .ifTrue hc
  | ifFalse => exact .ifFalse
  | labelVals => exact .labelVals
  | brLabelZero hl hn => exact .brLabelZero hl hn
  | brLabelSucc hl => exact .brLabelSucc hl
  | brHandler => exact .brHandler
  | brIfTrue hc => exact .brIfTrue hc
  | brIfFalse => exact .brIfFalse
  | brTableLt hi => exact .brTableLt hi
  | brTableGe hi => exact .brTableGe hi
  | brOnNullNull => exact .brOnNullNull
  | brOnNullAddr hv => exact .brOnNullAddr hv
  | brOnNonNullNull => exact .brOnNonNullNull
  | brOnNonNullAddr hv => exact .brOnNonNullAddr hv
  | brOnCastSucceed h => exact .brOnCastSucceed h
  | brOnCastFail h => exact .brOnCastFail h
  | brOnCastFailSucceed h => exact .brOnCastFailSucceed h
  | brOnCastFailFail h => exact .brOnCastFailFail h
  | call hx hf => exact .call hx hf
  | callRefNull hc => exact .callRefNull hc
  | callRefFunc hc hf he hn hcode => exact .callRefFunc hc hf he hn hcode
  | callRefHost hc hf he hn hcode hhost => exact .callRefHost hc hf he hn hcode hhost
  | callRefHostDiv hc hf he hn hcode hhost => exact .callRefHostDiv hc hf he hn hcode hhost
  | returnCall hx hf => exact .returnCall hx hf
  | returnCallRefLabel hc => exact .returnCallRefLabel hc
  | returnCallRefHandler hc => exact .returnCallRefHandler hc
  | returnCallRefFrameNull hc => exact .returnCallRefFrameNull hc
  | returnCallRefFrameAddr hc hf he hn => exact .returnCallRefFrameAddr hc hf he hn
  | callIndirect => exact .callIndirect
  | returnCallIndirect => exact .returnCallIndirect
  | frameVals hn => exact .frameVals hn
  | returnFrame hn => exact .returnFrame hn
  | returnLabel => exact .returnLabel
  | returnHandler => exact .returnHandler
  | throw ht he hn => exact .throw ht he hn
  | throwRefNull => exact .throwRefNull
  | throwRefInstrs hne => exact .throwRefInstrs hne
  | throwRefLabel => exact .throwRefLabel
  | throwRefFrame => exact .throwRefFrame
  | throwRefHandlerEmpty => exact .throwRefHandlerEmpty
  | throwRefHandlerCatch he ht => exact .throwRefHandlerCatch he ht
  | throwRefHandlerCatchRef he ht => exact .throwRefHandlerCatchRef he ht
  | throwRefHandlerCatchAll => exact .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => exact .throwRefHandlerCatchAllRef
  | throwRefHandlerNext h => exact .throwRefHandlerNext h
  | tryTable hbt hm => exact .tryTable hbt hm
  | handlerVals => exact .handlerVals
  | trapInstrs hne => exact .trapInstrs hne
  | trapLabel => exact .trapLabel
  | trapHandler => exact .trapHandler
  | trapFrame => exact .trapFrame

/-- Runs of native configurations are profile-independent. -/
theorem steps_profile {P P' : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hc : NConfig c) : Steps P' host c c' := by
  induction h with
  | refl => exact .refl
  | tail hst hs ih => exact ih.tail (step_profile hs (hc.steps hst).1)

theorem steps_profile_iff {P P' : Profile} {host : HostSemantics H} {c c' : Config H}
    (hc : NConfig c) : Steps P host c c' ↔ Steps P' host c c' :=
  ⟨fun h => steps_profile h hc, fun h => steps_profile h hc⟩

/-- Divergence of native configurations is profile-independent. -/
theorem diverges_profile {P P' : Profile} {host : HostSemantics H} {c : Config H}
    (h : Diverges P host c) (hc : NConfig c) : Diverges P' host c := by
  refine Silmaril.InfiniteTrace.of_map (R := Step P' host) (S := Step P host) id NConfig ?_ hc h
  intro a b ha hab
  exact ⟨b, step_profile hab ha.1, ha.step hab, rfl⟩

theorem diverges_profile_iff {P P' : Profile} {host : HostSemantics H} {c : Config H}
    (hc : NConfig c) : Diverges P host c ↔ Diverges P' host c :=
  ⟨fun h => diverges_profile h hc, fun h => diverges_profile h hc⟩

/-- Normal forms of native configurations are profile-independent. -/
theorem normal_profile {P P' : Profile} {host : HostSemantics H} {c : Config H}
    (hc : NConfig c) (hn : ∀ x, ¬ Step P host c x) : ∀ x, ¬ Step P' host c x :=
  fun x hx => hn x (step_profile hx hc.1)

/-- **Behaviours of native stores are profile-independent.** -/
theorem behaviours_profile {P P' : Profile} {host : HostSemantics H} {s : Store H}
    (hF : NativeFuncsOk s.funcs) (a : Nat) (vs : List Val) :
    behaviours P host s a vs = behaviours P' host s a vs := by
  have hc : NConfig (invoke s a vs) := nConfig_invoke hF a vs
  ext b
  simp only [behaviours_eq, behavioursOf, Set.mem_union, Set.mem_ofPred_eq,
    steps_profile_iff (P := P) (P' := P') hc, diverges_profile_iff (P := P) (P' := P') hc]

/-! ## Unique normal forms at every profile -/

/-- **Unique normal forms at every profile**: two closed-host normal forms reachable from a
native configuration are equal. Transferred from silmaril-lean's deterministic-profile
`eq_of_steps_of_nf` (subcommutativity, `Det.DStep.join'`). -/
theorem eq_of_steps_nf {P : Profile} {c c₁ c₂ : Config H} (hc : NConfig c)
    (h₁ : Steps P closedHost c c₁) (h₂ : Steps P closedHost c c₂)
    (n₁ : ∀ x, ¬ Step P closedHost c₁ x) (n₂ : ∀ x, ¬ Step P closedHost c₂ x) : c₁ = c₂ := by
  let D : Profile := Profile.deterministic fun _ _ _ _ => false
  have d₁ : Steps D closedHost c c₁ := steps_profile h₁ hc
  have d₂ : Steps D closedHost c c₂ := steps_profile h₂ hc
  have m₁ : ∀ x, ¬ Step D closedHost c₁ x := normal_profile (hc.steps h₁) n₁
  have m₂ : ∀ x, ¬ Step D closedHost c₂ x := normal_profile (hc.steps h₂) n₂
  exact steps_det_nf d₁ d₂ m₁ m₂

end Silmaril.Wasm.Interp
