module

public import Silmaril.Wasm.Game.Shared.Defs
public import Silmaril.Proofs.Wasm.Game.Adequacy.RunTyping
public import Silmaril.Proofs.Wasm.Game.Adequacy.Progress

/-!
# Typing and progress against store-changing hosts

The run invariant `ShGood I s₀ ts c`: `c` is typed at `ts`, its store is
well formed for the instance, and it extends `s₀`. Unlike the store-preserving
invariant (`Good`, `RunInv`: same functions as the initial store), the store may
gain functions, as long as they are typed imports (`ScalarInstance.HostsTyped`).

* `shGood_shStep`: product steps preserve it, for a well-formed environment
  (`ShEnvOk`). An answer step is a Core step against the host replaying exactly
  that answer in its store (`answerHost`), which satisfies the host contract
  `HostOk` by `ShAnswerOk`, so Core preservation applies.
* `shGood_progress`: a configuration satisfying it is final or has a product
  step; its host-call redexes are valid import calls (`shGood_callout_valid`, read
  through Core progress against `typedDivHost`).
* `shGood_result`: final values are typed by the declared results.

New proofs; they follow `Silmaril.Proofs.Wasm.Game.Adequacy.{RunTyping,Progress}`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Shared

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

variable {I : Silmaril.Wasm.Game.ScalarInstance}

/-! ### Well-formed stores -/

/-- Well-formedness is the host typing on a store extending a well-formed store. -/
theorem wellFormed_of_extend {s s' : Store Nat} (hw : I.WellFormed s) (hs' : StoreOk s')
    (hext : Extend s s') (ht : I.HostsTyped s') : I.WellFormed s' := by
  refine ⟨hs', hw.addrs_length, fun j => ?_, ht⟩
  obtain ⟨fi, hfi, hexp⟩ := hw.export_type j
  obtain ⟨fi', hfi', hef⟩ := hext.funcs.get hfi
  exact ⟨fi', hfi', hef.1 ▸ hexp⟩

/-- Well-formedness transfers to a well-typed store with the same functions. -/
theorem wellFormed_of_funcs {s s' : Store Nat} (hw : I.WellFormed s) (hs' : StoreOk s')
    (hf : s'.funcs = s.funcs) : I.WellFormed s' := by
  refine ⟨hs', hw.addrs_length, fun j => ?_, fun a fi h ha hc => hw.host_type a fi h (hf ▸ ha) hc⟩
  rw [hf]
  exact hw.export_type j

/-! ### The run invariant -/

/-- The run invariant against store-changing hosts, from the store `s₀`. -/
structure ShGood (I : Silmaril.Wasm.Game.ScalarInstance) (s₀ : Store Nat) (ts : List CValType)
    (c : Config Nat) : Prop where
  ok : ConfigOk c ts
  wf : I.WellFormed c.store
  ext : Extend s₀ c.store

/-- The host replaying the answer `(s', r)` to host code `h₀` at store `s₀`, and otherwise
diverging. -/
def answerHost (s₀ : Store Nat) (h₀ : Nat) (s' : Store Nat) (r : Result) : HostSemantics Nat :=
  fun h s _ out => out = .diverged ∨ (s = s₀ ∧ h = h₀ ∧ out = .returned s' r)

theorem answerHost_ok {s₀ s' : Store Nat} {h₀ : Nat} {r : Result} (hs : StoreOk s')
    (hext : Extend s₀ s')
    (hr : ∀ fi ∈ s₀.funcs, fi.code = .host h₀ → ∀ ps rs, Expand fi.type (.func ps rs) →
      ResultTyped s' r rs.toList) : HostOk (answerHost s₀ h₀ s' r) := by
  intro s fi h vs ps rs _ hfi hcode hexp _
  refine ⟨⟨.diverged, Or.inl rfl⟩, fun out hout => ?_⟩
  rcases hout with rfl | ⟨rfl, rfl, rfl⟩
  · trivial
  · exact ⟨hs, hext, hr fi hfi hcode ps rs hexp⟩

/-- The result types of a host function of a well-formed store are those of its import. -/
theorem results_of_host {s : Store Nat} (hw : I.WellFormed s) {fi : FuncInst Nat} {i : Fin I.imports.length}
    (hfi : fi ∈ s.funcs) (hcode : fi.code = .host i.val) {ps rs : Ty (.list .val)}
    (hexp : Expand fi.type (.func ps rs)) :
    ps = Ty.ofList ((I.imports.get i).params.map ScalarType.toC) ∧
      rs = Ty.ofList ((I.imports.get i).results.map ScalarType.toC) := by
  obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hfi
  obtain ⟨hlt, hexp'⟩ := hw.host_type a fi i.val ha hcode
  have hfin : (⟨i.val, hlt⟩ : Fin I.imports.length) = i := Fin.ext rfl
  rw [hfin] at hexp'
  simpa only [FnType.toComp, Ty.func.injEq] using Expand.func_eq hexp hexp'

/-- A well-formed answer is a host satisfying the host contract. -/
theorem answerHost_answer_ok {s s' : Store Nat} (hw : I.WellFormed s) {i : Fin I.imports.length}
    {w : Answer (I.imports.get i)} (hok : I.ShAnswerOk s s' w) :
    HostOk (answerHost s i.val s' w.toResult) := by
  refine answerHost_ok hok.wf.storeOk hok.extend fun fi hfi hcode ps rs hexp => ?_
  rw [(results_of_host hw hfi hcode hexp).2, Ty.toList_ofList]
  exact resultTyped_toResult hok.throws (Nat.le_refl _)

/-- The host function called at a host-call redex. -/
theorem callout_host {c : Config Nat} {E : Ctx} {a hh : Nat} {args : List Val}
    {e : (ifaceSig I.imports).Op} (hd : decompose? c.store c.code = some (E, a, hh, args))
    (op : ifaceOp? I.imports hh args = some e) :
    ∃ fi ∈ c.store.funcs, fi.code = .host e.1.val := by
  obtain ⟨fi, -, -, -, hf, hcode, -⟩ := decompose?_sound hd
  exact ⟨fi, List.mem_of_getElem? hf, by rw [ifaceOp?_fst op]; exact hcode⟩

/-- Host-free steps preserve the invariant. -/
theorem shGood_internal {P : Profile} {s₀ : Store Nat} {ts : List CValType} {c c' : Config Nat}
    (hg : ShGood I s₀ ts c) (h : Step P (fun _ _ _ _ => False) c c') : ShGood I s₀ ts c' := by
  obtain ⟨hok', hext'⟩ :=
    Step.preservation (SingleThreaded.divHost_ok (H := Nat)) hg.ok (Step.of_noHost _ h)
  have hf : c'.store.funcs = c.store.funcs := (Step.framesLocal h).1
  exact ⟨hok', wellFormed_of_funcs hg.wf (SingleThreaded.ConfigOk.storeOk hok') hf,
    hg.ext.trans hext'⟩

/-- A well-formed answer step preserves the invariant. -/
theorem shGood_answer {P : Profile} {s₀ : Store Nat} {ts : List CValType} {c : Config Nat}
    {E : Ctx} {a hh : Nat} {args : List Val} {e : (ifaceSig I.imports).Op} {s' : Store Nat}
    {w : Answer (I.imports.get e.1)} (hg : ShGood I s₀ ts c)
    (hd : decompose? c.store c.code = some (E, a, hh, args))
    (op : ifaceOp? I.imports hh args = some e) (hok : I.ShAnswerOk c.store s' w) :
    ShGood I s₀ ts ⟨s', c.frame, E.fill w.toResult.toAdmin⟩ := by
  have hh' : hh = e.1.val := (ifaceOp?_fst op).symm
  have hstep : Step P (answerHost c.store e.1.val s' w.toResult) c
      ⟨s', c.frame, E.fill w.toResult.toAdmin⟩ :=
    ScalarInstance.step_of_callout_returned (hh' ▸ hd) (Or.inr ⟨rfl, rfl, rfl⟩)
  exact ⟨(Step.preservation (answerHost_answer_ok hg.wf hok) hg.ok hstep).1, hok.wf,
    hg.ext.trans hok.extend⟩

/-- **Product steps preserve the invariant**, against a well-formed environment. -/
theorem shGood_shStep {P : Profile} {s₀ : Store Nat} {L : SEnv I.shE} (hL : I.ShEnvOk s₀ L)
    {ts : List CValType} {x y : Config Nat × L.S} (hg : ShGood I s₀ ts x.1)
    (h : ShStep P L x y) : ShGood I s₀ ts y.1 := by
  cases h with
  | internal h0 => exact shGood_internal hg h0
  | @answer c E a hh args e s' w q q' hd op ans =>
    exact shGood_answer (P := P) hg hd op
      (hL q (shOp c.store e) (s', w) q' hg.ext hg.wf (callout_host hd op) ans)
  | silent => exact hg

/-- Product runs preserve the invariant. -/
theorem shGood_shSteps {P : Profile} {s₀ : Store Nat} {L : SEnv I.shE} (hL : I.ShEnvOk s₀ L)
    {ts : List CValType} {x y : Config Nat × L.S} (hg : ShGood I s₀ ts x.1)
    (h : ShSteps P L x y) : ShGood I s₀ ts y.1 := by
  induction h with
  | refl => exact hg
  | tail _ hst ih => exact shGood_shStep hL ih hst

/-- The invariant at an export invocation in a well-formed store, at the declared results. -/
theorem shGood_invoke {f : I.shF.Op} (hw : I.WellFormed f.2.1) :
    ShGood I f.2.1 ((I.exports.get f.1).results.map ScalarType.toC)
      (invoke f.2.1 (I.addr f.1) f.2.2.1) := by
  obtain ⟨fi, hfi, hexp⟩ := hw.export_type f.1
  have hinv : InvokeOk f.2.1 (I.addr f.1) f.2.2.1 :=
    ⟨fi, _, _, hfi, hexp, ScalarInstance.forall₂_valOk_of_hasVal f.2.2.2⟩
  obtain ⟨fi', ps, rs, hfi', hexp', hok⟩ := invoke_ok hw.storeOk hinv
  obtain rfl : fi' = fi := (Option.some.inj (hfi.symm.trans hfi')).symm
  have hboth : ps = Ty.ofList ((I.exports.get f.1).params.map ScalarType.toC) ∧
      rs = Ty.ofList ((I.exports.get f.1).results.map ScalarType.toC) := by
    simpa only [FnType.toComp, Ty.func.injEq] using Expand.func_eq hexp' hexp
  have hrs : rs = Ty.ofList ((I.exports.get f.1).results.map ScalarType.toC) := hboth.2
  have hok' : ConfigOk (invoke f.2.1 (I.addr f.1) f.2.2.1)
      ((I.exports.get f.1).results.map ScalarType.toC) := by
    simpa only [hrs, Ty.toList_ofList] using hok
  exact ⟨hok', hw, Extend.refl hw.storeOk⟩

/-- **Typed results**: a final configuration under the invariant at the declared results is
read as an answer. -/
theorem shGood_result {s₀ : Store Nat} {ft : FnType} {c : Config Nat} {r : Result}
    (hg : ShGood I s₀ (ft.results.map ScalarType.toC) c) (final : c.code = r.toAdmin) :
    ∃ w, Answer.ofResult? ft r = some w := by
  cases r with
  | trap => exact ⟨_, rfl⟩
  | throw a => exact ⟨_, rfl⟩
  | values vs =>
    have htyped : List.Forall₂ ScalarType.HasVal ft.results vs := hasVal_of_configOk hg.ok final
    exact ⟨.values ⟨vs, htyped⟩, by simp only [Answer.ofResult?, htyped, dite_true]⟩

/-! ### Progress -/

/-- The host that diverges on every call and, at stores whose host functions are imports,
has outcomes only for valid import calls. -/
def typedDivHost (I : Silmaril.Wasm.Game.ScalarInstance) : HostSemantics Nat :=
  fun h s args out => out = .diverged ∧ (I.HostsTyped s → ∃ e, ifaceOp? I.imports h args = some e)

/-- `typedDivHost` satisfies the host contract. -/
theorem typedDivHost_ok : HostOk (typedDivHost I) := by
  intro s fi h vs ps rs _ hfi hcode hexp hvs
  refine ⟨⟨.diverged, rfl, fun ht => ?_⟩, fun out hout => ?_⟩
  · obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hfi
    obtain ⟨hlt, hexp'⟩ := ht a fi h ha hcode
    obtain ⟨rfl, -⟩ : ps = Ty.ofList ((I.imports.get ⟨h, hlt⟩).params.map ScalarType.toC) ∧
        rs = Ty.ofList ((I.imports.get ⟨h, hlt⟩).results.map ScalarType.toC) := by
      simpa only [FnType.toComp, Ty.func.injEq] using Expand.func_eq hexp hexp'
    have hty : List.Forall₂ ScalarType.HasVal (I.imports.get ⟨h, hlt⟩).params vs :=
      ScalarInstance.hasVal_of_forall₂_valOk hvs
    exact ⟨⟨⟨h, hlt⟩, ⟨vs, hty⟩⟩, by simp only [ifaceOp?, hlt, hty, ↓reduceDIte]⟩
  · obtain ⟨rfl, -⟩ := hout
    trivial

/-- A Core step at a host-call redex is a host call there. -/
theorem callout_step {P : Profile} {host : HostSemantics Nat} {c c' : Config Nat} {E : Ctx}
    {a hh : Nat} {args : List Val} (hd : decompose? c.store c.code = some (E, a, hh, args))
    (h : Step P host c c') :
    (∃ s' r, host hh c.store args (.returned s' r) ∧ c' = ⟨s', c.frame, E.fill r.toAdmin⟩) ∨
      (host hh c.store args .diverged ∧ c' = c) := by
  rcases Step.split_host h with h₀ | ⟨E', a', hh', args', hd', hcase⟩
  · rw [decompose?_none_of_noRedex (Step.noRedex h₀)] at hd
    cases hd
  · rw [hd] at hd'
    obtain ⟨rfl, -, rfl, rfl⟩ : E = E' ∧ a = a' ∧ hh = hh' ∧ args = args' := by
      simpa only [Option.some.injEq, Prod.mk.injEq] using hd'
    exact hcase

/-- **Typed callouts**: under the invariant every host-call redex is a valid import call. -/
theorem shGood_callout_valid {P : Profile} {s₀ : Store Nat} {ts : List CValType} {c : Config Nat}
    (hg : ShGood I s₀ ts c) {E : Ctx} {a hh : Nat} {args : List Val}
    (hd : decompose? c.store c.code = some (E, a, hh, args)) :
    ∃ e, ifaceOp? I.imports hh args = some e := by
  have ht : I.HostsTyped c.store := hg.wf.host_type
  rcases Config.progress (P := P) (typedDivHost_ok (I := I)) hg.ok with ⟨r, hr⟩ | ⟨c', hc'⟩
  · rw [hr, ScalarInstance.decompose?_toAdmin] at hd
    cases hd
  · rcases callout_step hd hc' with ⟨s', r, ⟨hout, -⟩, -⟩ | ⟨⟨-, hv⟩, -⟩
    · cases hout
    · exact hv ht

/-- **Progress against a store-changing host**: a configuration satisfying the invariant is
final or has a product step, from every host state. -/
theorem shGood_progress {P : Profile} {s₀ : Store Nat} {L : SEnv I.shE} {ts : List CValType}
    {c : Config Nat} (q : L.S) (hg : ShGood I s₀ ts c) :
    (∃ r : Result, c.code = r.toAdmin) ∨ ∃ y, ShStep P L (c, q) y := by
  rcases Config.progress (P := P) (typedDivHost_ok (I := I)) hg.ok with hr | ⟨c', hc'⟩
  · exact Or.inl hr
  · right
    rcases Step.split_host hc' with h0 | ⟨E, a, hh, args, hd, -⟩
    · exact ⟨_, .internal h0⟩
    · obtain ⟨e, op⟩ := shGood_callout_valid (P := P) hg hd
      by_cases hA : ∃ a q', L.Ans q (shOp c.store e) a q'
      · obtain ⟨⟨s', w⟩, q', hans⟩ := hA
        exact ⟨_, .answer hd op hans⟩
      · exact ⟨_, .silent hd op (Or.inr fun a q' h => hA ⟨a, q', h⟩)⟩

end Silmaril.Proofs.Wasm.Game.Shared
