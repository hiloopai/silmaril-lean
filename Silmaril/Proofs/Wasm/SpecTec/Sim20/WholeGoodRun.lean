module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeGoodCode
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdLoad
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdCoverP

/-!
# Covered runs: the forward 2.0 half on every step of a run from an invocation

`Good20C hn P c` is a single-configuration condition:

* the image of `c` is typed (at `storeB P`) and the store's pages are whole;
* `c` satisfies the plain-tail invariant `Plain20`;
* the code is `adminOk` and the store `StoreOk` (`WholeGoodCode`): every instruction, also in
  label continuations, frame bodies and the store's functions, is one the forward fragment
  covers, and every function of the store is a Wasm function.

* **`cover20C`**: every V2 step from code that is `Tail20`, `adminOk`, over an `StoreOk` store,
  is a step of `Nest20 (FwdStep20D P)`. The pure steps go through `pureStep_cover_tail`, whose
  remainder `PureRest20N` is excluded by `adminOk`; the read steps of the covered instructions
  are `block`, `loop`, `call`, `call_addr`, `local.get`, `global.get`, `ref.func` and the
  unpacked loads; the other
  base steps are `local.set` and `global.set`. Every other rule has an uncovered instruction on
  its left-hand side, and a host call needs a host function.
* **`fwd_good20C`**: every V2 step from a `Good20C` configuration is a corrected-script step
  between the images, and its successor is `Good20C`. **`good20C_steps`**: so is every
  configuration of a run.
* `good20C_invoke`: at an invocation `val* (CALL_ADDR a)`, `Good20C` asks only for a typed
  image, whole pages and a `StoreOk` store.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S)

variable {H : Type} {hn : H → String}

/-! ## Into the fragment -/

theorem fwdC_pure {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (h : PureFrag20 P is is') : FwdStep20D P ⟨s, f, is⟩ ⟨s, f, is'⟩ :=
  .fwd (.fwd (.fwd (.fwd (.base (.pure (.mk h))))))

theorem fwdC_pureB {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (h : PureFrag20B P is is') : FwdStep20D P ⟨s, f, is⟩ ⟨s, f, is'⟩ :=
  .fwd (.fwd (.fwd (.fwd (.pure (.mk h)))))

theorem fwdC_read {P : Profile} {c c' : Config H} (h : ReadFwd20 c c') : FwdStep20D P c c' :=
  .fwd (.fwd (.fwd (.fwd (.base (.read h)))))

theorem fwdC_call {P : Profile} {c c' : Config H} (h : CallFwd20 c c') : FwdStep20D P c c' :=
  .fwd (.fwd (.fwd (.fwd (.call h))))

theorem fwdC_top {P : Profile} {c c' : Config H} (h : TopVStep20 P c c') : FwdStep20D P c c' :=
  .fwd (.fwd (.fwd (.fwd (.base (.top h)))))

/-- `PureRest20N` has an uncovered instruction. -/
theorem not_pureRest20N_ok {is : List Admin} (h : PureRest20N is) (hok : is.all adminOk = true) :
    False := by
  cases h with
  | vec hm hv =>
    have hi : adminOk (.plain _) = true := List.all_eq_true.1 hok _ hm
    rw [adminOk_plain, ctrlOk_of_vecOp hv] at hi
    exact absurd hi (by decide)
  | unOpInvalid h => simp_all [ctrlOk]
  | cvtUndefined h => simp_all [ctrlOk]

/-- The pure steps from covered plain-tail code are in the fragment. -/
theorem cover20C_pure {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (hp : PureStep P is is') (ht : Tail20 s f is) (hok : is.all adminOk = true) :
    FwdStep20D P ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  rcases pureStep_cover_tail hp ht with h | h | h
  · exact fwdC_pure h
  · exact fwdC_pureB h
  · exact (not_pureRest20N_ok h hok).elim

/-- `global.get`'s lookup, taken apart. -/
theorem global?_some {s : Store H} {f : Frame} {x : GlobalIdx} {gi : GlobalInst}
    (h : (⟨s, f⟩ : State H).global? x = some gi) :
    ∃ a, f.module.globals[x.toNat]? = some a ∧ s.globals[a]? = some gi := by
  cases ha : f.module.globalAddr? x with
  | none => simp [State.global?, ha] at h
  | some a =>
    have hg : s.globalInst? a = some gi := by simpa [State.global?, ha] using h
    exact ⟨a, by simpa [ModuleInst.globalAddr?] using ha, by simpa [Store.globalInst?] using hg⟩

/-- The read steps from covered code over a covered store are in the fragment. -/
theorem cover20C_read {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (hr : ReadStep s f is is') (hok : is.all adminOk = true) :
    FwdStep20D P ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  cases hr with
  | block hbt hk => exact .fwd (.fwd (.block (.block hbt hk)))
  | loop hbt hk => exact .fwd (.fwd (.block (.loop hbt hk)))
  | call hx => exact fwdC_call (.call (by simpa [ModuleInst.funcAddr?] using hx))
  | callAddr hf hcode hk => exact .fwd (.callAddr (.mk hf hcode hk))
  | loadIntTrap hm h => exact .load (.intTrap hm h)
  | loadIntVal hm hb => exact .load (.intVal hm hb)
  | loadFloatTrap hm h => exact .load (.floatTrap hm h)
  | loadFloatVal hm hb => exact .load (.floatVal hm hb)
  | localGet h => exact fwdC_read (.localGet (by simpa [State.local?, Frame.local?] using h))
  | globalGet h =>
    obtain ⟨a, ha, hg⟩ := global?_some h
    exact fwdC_read (.globalGet ha hg)
  | refFunc hx => exact fwdC_read (.refFunc (by simpa [ModuleInst.funcAddr?] using hx))
  | _ => simp [ctrlOk] at hok

/-- **Every V2 step from covered plain-tail code over a covered store is in the nested
fragment.** -/
theorem cover20C {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : Step P host c c')
    (ht : Tail20 c.store c.frame c.code) (hok : c.code.all adminOk = true)
    (hs : StoreOk c.store) : Nest20 (FwdStep20D P) c c' := by
  induction h with
  | pure hp => exact .base (cover20C_pure hp ht hok)
  | read hr => exact .base (cover20C_read hr hok)
  | ctxtInstrs hstep hne ih =>
    refine .ctx (ih (tail20_ctx hstep.not_allVals ht) ?_ hs) hne
    simp only [List.all_append, Bool.and_eq_true] at hok
    exact hok.1.2
  | ctxtLabel _ ih =>
    refine .label (ih (tail20_label ht).tail ?_ hs)
    simp only [List.all_cons, List.all_nil, Bool.and_true, adminOk_label, Bool.and_eq_true] at hok
    exact hok.2
  | ctxtFrame _ ih => exact .frame (ih (tail20_frame ht).tail (by simpa using hok) hs)
  | callAddrHost hf hcode => exact (hs.not_host hf hcode).elim
  | callAddrHostDiv hf hcode => exact (hs.not_host hf hcode).elim
  | localSet hx => exact .base (fwdC_top (.var (.localSet hx)))
  | globalSet ha hg => exact .base (fwdC_top (.var (.globalSet ha hg)))
  | _ => simp [ctrlOk] at hok

/-! ## Covered runs -/

/-- **The covered configurations** at profile `P`. -/
structure Good20C (hn : H → String) (P : Profile) (c : Config H) : Prop where
  typed : Typed20 (simEnv20 (storeB P)) hn c
  whole : WholePages c.store
  plain : Plain20 c.store c.frame c.code
  ok : c.code.all adminOk = true
  store : StoreOk c.store

theorem WholePages.of_fm {s s' : Store H} (h : WholePages s) (e : StoreFM s s') :
    WholePages s' :=
  fun mi hm => h mi (e.2 ▸ hm)

/-- **Every V2 step from a covered configuration is a corrected-script step, and its successor
is covered.** -/
theorem fwd_good20C {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (hg : Good20C hn P c) (h : Step P host c c') :
    Good20C hn P c' ∧ SStepB (simEnv20S (storeB P)) (configV hn c) (configV hn c') := by
  have hN : Nest20 (FwdStep20D P) c c' := cover20C h hg.plain.tail hg.ok hg.store
  obtain ⟨ht, hst⟩ := wholeStepFwd20D H hn P c c' hg.typed hg.whole hN
  obtain ⟨hok, hm⟩ := adminOk_step h hg.ok hg.store
  exact ⟨⟨ht, hg.whole.of_fm hm, plain20_step h hg.plain, hok, hg.store.of_fm hm⟩, hst⟩

/-- **Every configuration of a run from a covered configuration is covered.** -/
theorem good20C_steps {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hg : Good20C hn P c) : Good20C hn P c' := by
  induction h with
  | refl => exact hg
  | tail _ h₂ ih => exact (fwd_good20C ih h₂).1

/-- **At an invocation**, `Good20C` asks for a typed image, whole pages and a covered store. -/
theorem good20C_invoke {P : Profile} {s : Store H} {f : Frame} {args : List Val} {a : FuncAddr}
    (ht : Typed20 (simEnv20 (storeB P)) hn ⟨s, f, vals args ++ [.callAddr a]⟩)
    (hw : WholePages s) (hs : StoreOk s) : Good20C hn P ⟨s, f, vals args ++ [.callAddr a]⟩ :=
  ⟨ht, hw, plain20_invoke args a, by simp [List.all_append], hs⟩

end Silmaril.Wasm.SpecTec.Sim20.Whole
