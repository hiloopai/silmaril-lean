module

public import Silmaril.Wasm.Component.Engine.Core3.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Typed.Store.Defs
public import Silmaril.Wasm.Component.Reference.Wasm.Execution.Core.Soundness.InstantiationOnce.Defs
public import Silmaril.Wasm.Component.Reference.Wasm.Execution.Core.Soundness.InstantiationOnceAlloc.Defs

/-!
# `Engine.Core3.Typed.Prepare`: the laws that definitions cite

The theorems of the component reference copy `Engine.Core3.Typed.Prepare` that definition parts cite
(engine records bundle such laws as fields). The other theorems stay in
`Silmaril.Raw.Wasm.Component.Engine.Core3.Typed.Prepare`, which imports this module.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3.Typed

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
variable {H : Type}

/-- Host-free runs never change the function instances. -/
theorem Steps.funcs_eq {P : Silmaril.Wasm.Numerics.Profile} {c c' : Config H}
    (h : Steps P (fun _ _ _ _ => False) c c') : c'.store.funcs = c.store.funcs := by
  induction h with
  | refl => rfl
  | tail _ hst ih => exact (SingleThreaded.Step.framesLocal hst).1.trans ih

/-- Runs from a typed configuration stay typed and extend the store. -/
theorem Steps.preserves {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    (hhost : HostOk host) {c c' : Config H} {ts : List CValType} (hc : ConfigOk c ts)
    (h : Steps P host c c') :
    ConfigOk c' ts ∧ Extend c.store c'.store := by
  induction h with
  | refl => exact ⟨hc, Extend.refl (SingleThreaded.ConfigOk.storeOk hc)⟩
  | tail _ hst ih =>
    obtain ⟨h₁, h₂⟩ := ih
    obtain ⟨h₃, h₄⟩ := Step.preservation hhost h₁ hst
    exact ⟨h₃, h₂.trans h₄⟩

/-- A function of a typed store whose type is a subtype of a valid function type `[] -> []` is
invoked with no arguments at `[]`. -/
theorem invoke_configOk_of_sub {s : Store H} {a : Nat} {fi : FuncInst H} {d : DefType}
    {ps rs : Silmaril.Wasm.Validation.Ty TKind.val.list} (hs : StoreOk s) (hfi : s.funcs[a]? = some fi)
    (hsubd : Validation.Sub {} fi.type d) (hdok : TyOk {} d) (he : Expand d (ps.func rs))
    (hps : ps.toList = []) (hrs : rs.toList = []) : ConfigOk (invoke s a []) [] := by
  have hfit : TyOk {} fi.type := by
    cases hs.funcs fi (List.mem_of_getElem? hfi) <;> assumption
  obtain ⟨ps', rs', he', hps', hrs'⟩ := PC.func_sub_data (.inr ⟨hdok, hsubd⟩) hfit he
  rw [hps] at hps'
  rw [hrs] at hrs'
  have hps'' : ps'.toList = [] := List.forall₂_nil_left_iff.mp hps'
  have hrs'' : rs'.toList = [] := List.forall₂_nil_right_iff.mp hrs'
  obtain ⟨fi₂, ps₂, rs₂, hfi₂, he₂, hok₂⟩ :=
    invoke_ok hs ⟨fi, ps', rs', hfi, he', by rw [hps'']; exact .nil⟩
  rw [hfi] at hfi₂
  cases hfi₂
  have := Expand.func_eq he' he₂
  simp only [Silmaril.Wasm.Validation.Ty.func.injEq] at this
  obtain ⟨-, rfl⟩ := this
  rw [hrs''] at hok₂
  exact hok₂

/-- A typed `call x` at `[] -> []` calls a function of type `[] -> []`: its invocation with no
arguments is typed at `[]`. -/
theorem start_configOk {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat}
    (h : ConfigOk ⟨s, f, [.plain (.call x)]⟩ []) (hx : f.module.funcs[x.toNat]? = some a) :
    ConfigOk (invoke s a []) [] := by
  obtain ⟨C, ⟨hs, hfr⟩, hadm⟩ := h
  have hΔ : C.toTypeCtx.Ok := FrameOk.toTypeCtx_okReg hs hfr
  obtain ⟨ts, it₀, ha, hp, hr, -⟩ := AdminsOk.single_inv hΔ hadm
  obtain ⟨d, ps, rs, hd, he, rfl⟩ := PC.inv_call ha
  have hps : ps.toList = [] :=
    (List.append_eq_nil_iff.mp (List.forall₂_nil_left_iff.mp hp)).2
  have hrs : rs.toList = [] :=
    (List.append_eq_nil_iff.mp (List.forall₂_nil_right_iff.mp hr)).2
  obtain ⟨a', ha', hea⟩ := FrameOk.func hfr hd
  have haa : a' = a := Option.some.inj (ha'.symm.trans hx)
  subst haa
  obtain ⟨xt', e, hsub, hok⟩ := ExternAddrOk.principal hs hea
  simp only [externAddrType?, Option.map_eq_some_iff] at e
  obtain ⟨fi, hfi, rfl⟩ := e
  cases hsub with
  | func hsubd =>
    cases hok with
    | func hdok _ => exact invoke_configOk_of_sub hs hfi hsubd hdok he hps hrs

/-- The parts of a successful `prepareE?`. -/
theorem prepareE?_inv {s s' : Store H} {m : Module} {xas : List ExternAddr} {i : ModuleInst}
    {st : Option Nat} (h : prepareE? s m xas = some (s', i, st)) :
    ∃ mt f' st₀, validate? m = some mt ∧ externAddrsOk? s xas mt.imports = true ∧
      instantiateOnce? s m xas = some (s', f', st₀) ∧ i = f'.module ∧
      ∀ a, st = some a → ∃ x, st₀ = some x ∧ f'.module.funcs[x.toNat]? = some a := by
  unfold prepareE? at h
  split at h
  · cases h
  · rename_i mt hv
    split at h
    · rename_i hx
      split at h
      · cases h
      · rename_i s₁ f₁ hi
        cases h
        exact ⟨mt, f₁, none, hv, hx, hi, rfl, fun a ha => by cases ha⟩
      · rename_i s₁ f₁ x hi
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨a, ha, rfl, rfl, rfl⟩ := h
        exact ⟨mt, f₁, some x, hv, hx, hi, rfl, fun a' ha' => by cases ha'; exact ⟨x, rfl, ha⟩⟩
    · cases h

/-- Instantiation by `prepareE?` keeps the store typed, extends it, appends only Wasm functions,
and returns a start function whose invocation with no arguments is typed at `[]`. -/
theorem prepareE?_typed {s s' : Store H} {m : Module} {xas : List ExternAddr} {i : ModuleInst}
    {st : Option Nat} (hs : StoreOk s) (h : prepareE? s m xas = some (s', i, st)) :
    StoreOk s' ∧ Extend s s' ∧
      (∃ new : List (FuncInst H), s'.funcs = s.funcs ++ new ∧
        ∀ fi ∈ new, ∃ code, fi.code = .wasm code) ∧
      ∀ a, st = some a → ConfigOk (invoke s' a []) [] := by
  obtain ⟨⟨xtI, xtE⟩, f', st₀, hv, hx, hi, -, hst⟩ := prepareE?_inv h
  have hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI :=
    ⟨xtE, xtI, validate?_sound hv, externAddrsOk?_sound hx⟩
  obtain ⟨s₁, f₁, vs, c, hg, hp, hS⟩ := instantiateOnce?_steps
    (P := SingleThreaded.profile SingleThreaded.neverFail) (host := SingleThreaded.divHost) hi
  have hfeq : s'.funcs = c.store.funcs := by
    obtain ⟨s₁', f₁', vs', c', hg', hp', hS'⟩ := instantiateOnce?_steps
      (P := SingleThreaded.profile SingleThreaded.neverFail) (host := fun _ _ _ _ => False) hi
    rw [hg] at hg'
    cases hg'
    rw [hp] at hp'
    cases hp'
    exact Steps.funcs_eq hS'
  obtain ⟨hc, hext, new, hnew, hwasm⟩ :=
    prepare?_globalResidue_ok (P := SingleThreaded.profile SingleThreaded.neverFail)
      SingleThreaded.divHost_ok hs hvalid hg hp
  have hS₂ : Steps (SingleThreaded.profile SingleThreaded.neverFail) SingleThreaded.divHost
      (c.withStart st₀) ⟨s', f', startCode st₀⟩ := by
    rw [← Config.withStart_nil]
    exact Steps.withStart hS
  have hws : (c.withStart st₀).store = c.store := by cases st₀ <;> rfl
  obtain ⟨hc', hext'⟩ := Steps.preserves SingleThreaded.divHost_ok hc hS₂
  have hext'' : Extend c.store s' := by
    rw [← hws]
    exact hext'
  refine ⟨SingleThreaded.ConfigOk.storeOk hc', hext.trans hext'', ⟨new, ?_, hwasm⟩, ?_⟩
  · exact hfeq.trans hnew
  · intro a ha
    obtain ⟨x, rfl, hxa⟩ := hst a ha
    exact start_configOk hc' hxa

end Silmaril.Wasm.Component.Engine.Core3.Typed
