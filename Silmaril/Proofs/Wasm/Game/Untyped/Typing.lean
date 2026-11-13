module

public import Silmaril.Proofs.Wasm.Game.Untyped.Runs
public import Silmaril.Proofs.Wasm.Game.Shared.Typing

/-!
# Store-relative typing in the untyped game

The run invariant `UGood s₀ ts c`: `c` is typed at `ts` and its store extends `s₀`.
No instance-level condition on host functions is needed (unlike `ShGood`, which
asks every host function to be a typed import): any host function, of any type,
added by an answer is called by its host code.

* `uGood_uStep`: product steps preserve it against a well-formed environment
  (`UEnvOk`): an answer step is a Core step against the host replaying exactly that
  answer (`answerHost`), which satisfies `HostOk` by `UEnvOk`, so Core preservation
  applies.
* `callsHost_of_decompose`: at a typed configuration every host-call redex is a
  well-typed host call (`UCall.CallsHost`), read through Core progress against
  `typedDivHost`.
* `uGood_progress`: a typed configuration is final or has a product step.
* `resultTyped_of_final`: a final typed configuration has a typed result, relative to
  its store (values by `ValOk` up to subsumption, exceptions existing).
* `resultTyped_extend`, `uEnvOk_mono`: store growth preserves store-relative typing.

New proofs; preservation and progress follow `Silmaril.Proofs.Wasm.Game.Shared.Typing`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Untyped

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-! ### Store growth -/

/-- **Store growth preserves result typing.** -/
theorem resultTyped_extend {s s' : Store Nat} {r : Result} {ts : List CValType}
    (he : Extend s s') (h : ResultTyped s r ts) : ResultTyped s' r ts := by
  cases r with
  | values vs => exact ValOk.forall₂_extend he h
  | throw a =>
    obtain ⟨x, hx⟩ := h
    obtain ⟨x', hx', -⟩ := he.exns.get hx
    exact ⟨x', hx'⟩
  | trap => trivial

/-- Store growth preserves the host contract of a reply. -/
theorem okFor_extend {s s' : Store Nat} {rs : Ty (.list .val)} {a : UReply}
    (h : a.OkFor s rs) (hs' : StoreOk s') (he : Extend a.store s') :
    (⟨s', a.result⟩ : UReply).OkFor s rs :=
  ⟨hs', h.2.1.trans he, resultTyped_extend he h.2.2⟩

/-- Well-formedness of environments is inherited by later stores. -/
theorem uEnvOk_mono {s₀ s₁ : Store Nat} {L : SEnv UImp} (he : Extend s₀ s₁) (hL : UEnvOk s₀ L) :
    UEnvOk s₁ L :=
  fun q e a q' ps rs hext hc hans => hL q e a q' ps rs (he.trans hext) hc hans

/-! ### The run invariant -/

/-- The run invariant against untyped environments, from the store `s₀`. -/
structure UGood (s₀ : Store Nat) (ts : List CValType) (c : Config Nat) : Prop where
  ok : ConfigOk c ts
  ext : Extend s₀ c.store

/-- The host replaying the reply `a` to the call `h₀ args₀` at store `s₀`, and otherwise
diverging. -/
def answerHost (s₀ : Store Nat) (h₀ : Nat) (args₀ : List Val) (a : UReply) : HostSemantics Nat :=
  fun h s vs out => out = .diverged ∨ (s = s₀ ∧ h = h₀ ∧ vs = args₀ ∧ out = .returned a.store a.result)

/-- The replaying host satisfies the host contract when the reply does for every typing of
the call. -/
theorem answerHost_ok {s₀ : Store Nat} {h₀ : Nat} {args₀ : List Val} {a : UReply}
    (hr : ∀ ps rs, (⟨h₀, s₀, args₀⟩ : UCall Nat).CallsHost ps rs → a.OkFor s₀ rs) :
    HostOk (answerHost s₀ h₀ args₀ a) := by
  intro s fi h vs ps rs hs hfi hcode hexp hvs
  refine ⟨⟨.diverged, Or.inl rfl⟩, fun out hout => ?_⟩
  rcases hout with rfl | ⟨rfl, rfl, rfl, rfl⟩
  · trivial
  · exact hr ps rs ⟨hs, fi, hfi, hcode, hexp, hvs⟩

/-- Host-free steps preserve the invariant. -/
theorem uGood_internal {P : Profile} {s₀ : Store Nat} {ts : List CValType} {c c' : Config Nat}
    (hg : UGood s₀ ts c) (h : Step P (fun _ _ _ _ => False) c c') : UGood s₀ ts c' := by
  obtain ⟨hok', hext'⟩ :=
    Step.preservation (SingleThreaded.divHost_ok (H := Nat)) hg.ok (Step.of_noHost _ h)
  exact ⟨hok', hg.ext.trans hext'⟩

/-- A well-formed answer step preserves the invariant. -/
theorem uGood_answer {P : Profile} {s₀ : Store Nat} {ts : List CValType} {c : Config Nat}
    {E : Ctx} {fa hh : Nat} {args : List Val} {a : UReply} (hg : UGood s₀ ts c)
    (hd : decompose? c.store c.code = some (E, fa, hh, args))
    (hr : ∀ ps rs, (⟨hh, c.store, args⟩ : UCall Nat).CallsHost ps rs → a.OkFor c.store rs) :
    UGood s₀ ts ⟨a.store, c.frame, E.fill a.result.toAdmin⟩ := by
  have hstep : Step P (answerHost c.store hh args a) c ⟨a.store, c.frame, E.fill a.result.toAdmin⟩ :=
    ScalarInstance.step_of_callout_returned hd (Or.inr ⟨rfl, rfl, rfl, rfl⟩)
  obtain ⟨hok', hext'⟩ := Step.preservation (answerHost_ok hr) hg.ok hstep
  exact ⟨hok', hg.ext.trans hext'⟩

/-- **Product steps preserve the invariant**, against a well-formed environment. -/
theorem uGood_uStep {P : Profile} {s₀ : Store Nat} {L : SEnv UImp} (hL : UEnvOk s₀ L)
    {ts : List CValType} {x y : Config Nat × L.S} (hg : UGood s₀ ts x.1) (h : UStep P L x y) :
    UGood s₀ ts y.1 := by
  cases h with
  | internal h0 => exact uGood_internal hg h0
  | @answer c E fa hh args a q q' hd ans =>
    exact uGood_answer (P := P) hg hd fun ps rs hc => hL q _ a q' ps rs hg.ext hc ans
  | silent => exact hg

/-- Product runs preserve the invariant. -/
theorem uGood_uSteps {P : Profile} {s₀ : Store Nat} {L : SEnv UImp} (hL : UEnvOk s₀ L)
    {ts : List CValType} {x y : Config Nat × L.S} (hg : UGood s₀ ts x.1) (h : USteps P L x y) :
    UGood s₀ ts y.1 := by
  induction h with
  | refl => exact hg
  | tail _ hst ih => exact uGood_uStep hL ih hst

/-- The invariant at a well-typed export invocation, at the declared results. -/
theorem uGood_invoke {U : UInstance} {f : U.F.Op} {ps rs : Ty (.list .val)}
    (hq : U.CallOk f ps rs) :
    UGood f.store rs.toList (invoke f.store (U.addr f.target) f.args) := by
  obtain ⟨hs, fi, hfi, hexp, hvs⟩ := hq
  obtain ⟨fi', ps', rs', hfi', hexp', hok⟩ := invoke_ok hs ⟨fi, ps, rs, hfi, hexp, hvs⟩
  have hfi_eq : fi' = fi := (Option.some.inj (hfi.symm.trans hfi')).symm
  have hboth : Ty.func ps' rs' = Ty.func ps rs := Expand.func_eq hexp' (hfi_eq ▸ hexp)
  have hrs : rs' = rs := (Ty.func.inj hboth).2
  exact ⟨hrs ▸ hok, Extend.refl hs⟩

/-! ### Typed results -/

/-- A typed value sequence has values typed at closed result types. -/
theorem forall₂_valOk_of_subEqR {s : Store Nat} {f : Frame} {C : Context} (hst : StateOk s f C)
    {vs : List Val} {ts : List CValType} (hv : List.Forall₂ (ValOk s) vs ts) :
    ∀ {B : List CValType}, List.Forall₂ (SubEqR C.toTypeCtx) ts B → ResultOk {} B →
      List.Forall₂ (ValOk s) vs B := by
  induction hv with
  | nil => intro B hB _; cases hB; exact .nil
  | @cons v t vs ts hvt _ ih =>
    intro B hB hok
    obtain ⟨b, B', hsub, hss, rfl⟩ := List.forall₂_cons_left_iff.mp hB
    have hb : TyOk {} b := hok b (List.mem_cons_self ..)
    have hrest : ResultOk {} B' := fun t ht => hok t (List.mem_cons_of_mem _ ht)
    have hvb : ValOk s v b := by
      rcases hsub with rfl | ⟨hs, -⟩
      · exact hvt
      · exact ValOk.ctxSubAgg hst ⟨hst.1.structsClosed, hst.1.arraysClosed⟩ hvt hs hb
    exact .cons hvb (ih hss hrest)

/-- Final values of a configuration typed at closed results are typed in its store. -/
theorem valOk_of_final {c : Config Nat} {ts : List CValType} {vs : List Val}
    (hc : ConfigOk c ts) (hts : ResultOk {} ts) (hcode : c.code = vals vs) :
    List.Forall₂ (ValOk c.store) vs ts := by
  obtain ⟨C, hst, hadm⟩ := hc
  rw [hcode] at hadm
  obtain ⟨-, -, ts', hv, hsub⟩ := AdminsOk.vals_aux' hadm vs rfl
  have hsub' : List.Forall₂ (SubEqR C.toTypeCtx) ts' ts := by simpa using hsub
  exact forall₂_valOk_of_subEqR hst hv hsub' hts

/-- A typed thrown exception exists in the store. -/
theorem exn_of_final {c : Config Nat} {ts : List CValType} {a : Nat} (hc : ConfigOk c ts)
    (hcode : c.code = [.ref (.exn a), .plain .throwRef]) : ∃ e, c.store.exns[a]? = some e := by
  obtain ⟨C, hst, hadm⟩ := hc
  have hsplit : c.code = vals [.ref (.exn a)] ++ [.plain .throwRef] := hcode
  rw [hsplit] at hadm
  have hwf : C.Wf := FrameOk.ctxWf hst.1 ⟨hst.1.structsClosed, hst.1.arraysClosed⟩ hst.2
  obtain ⟨t₂, xs₁, -, h₁, -, -⟩ := AdminsOk.append_inv hwf (.inl (by simp)) hadm
  obtain ⟨-, -, ts', hv, -⟩ := AdminsOk.vals_aux' h₁ _ rfl
  obtain ⟨t, -, hvt, -⟩ := List.forall₂_cons_left_iff.mp hv
  cases hvt with
  | ref hr => exact RefOk.exn_invExn hr a rfl

/-- **Typed results**: a final configuration typed at closed results has a result typed in
its store. -/
theorem resultTyped_of_final {c : Config Nat} {ts : List CValType} {r : Result}
    (hc : ConfigOk c ts) (hts : ResultOk {} ts) (final : c.code = r.toAdmin) :
    ResultTyped c.store r ts := by
  cases r with
  | values vs => exact valOk_of_final hc hts final
  | throw a => exact exn_of_final hc final
  | trap => trivial

/-! ### Progress -/

/-- The host that diverges on every call and has outcomes only for well-typed host calls. -/
def typedDivHost : HostSemantics Nat :=
  fun h s args out => out = .diverged ∧ ∃ ps rs, (⟨h, s, args⟩ : UCall Nat).CallsHost ps rs

/-- `typedDivHost` satisfies the host contract. -/
theorem typedDivHost_ok : HostOk typedDivHost := by
  intro s fi h vs ps rs hs hfi hcode hexp hvs
  refine ⟨⟨.diverged, rfl, ps, rs, hs, fi, hfi, hcode, hexp, hvs⟩, fun out hout => ?_⟩
  obtain ⟨rfl, -⟩ := hout
  trivial

/-- **Typed callouts**: at a typed configuration every host-call redex is a well-typed host
call, relative to the store. -/
theorem callsHost_of_decompose (P : Profile) {c : Config Nat} {ts : List CValType}
    (hc : ConfigOk c ts) {E : Ctx} {fa hh : Nat} {args : List Val}
    (hd : decompose? c.store c.code = some (E, fa, hh, args)) :
    ∃ ps rs, (⟨hh, c.store, args⟩ : UCall Nat).CallsHost ps rs := by
  rcases Config.progress (P := P) typedDivHost_ok hc with ⟨r, hr⟩ | ⟨c', hc'⟩
  · rw [hr, ScalarInstance.decompose?_toAdmin] at hd
    cases hd
  · rcases Shared.callout_step hd hc' with ⟨s', r, ⟨hout, -⟩, -⟩ | ⟨⟨-, hv⟩, -⟩
    · cases hout
    · exact hv

/-- **Progress against an untyped environment**: a typed configuration is final or has a
product step, from every host state. -/
theorem uGood_progress {P : Profile} {L : SEnv UImp} {ts : List CValType} {c : Config Nat}
    (q : L.S) (hc : ConfigOk c ts) :
    (∃ r : Result, c.code = r.toAdmin) ∨ ∃ y, UStep P L (c, q) y := by
  rcases Config.progress (P := P) (SingleThreaded.divHost_ok (H := Nat)) hc with hr | ⟨c', hc'⟩
  · exact Or.inl hr
  · right
    rcases Step.split_host hc' with h0 | ⟨E, fa, hh, args, hd, -⟩
    · exact ⟨_, .internal h0⟩
    · by_cases hA : ∃ a q', L.Ans q ⟨hh, c.store, args⟩ a q'
      · obtain ⟨a, q', hans⟩ := hA
        exact ⟨_, .answer hd hans⟩
      · exact ⟨_, .silent hd (Or.inr fun a q' h => hA ⟨a, q', h⟩)⟩

end Silmaril.Proofs.Wasm.Game.Untyped
