module

public import Silmaril.Proofs.Wasm.Game.Env.Basic
public import Silmaril.Wasm.SingleThreaded.Soundness
public import Silmaril.Wasm.Execution.Core.Soundness

/-!
# Typing along closed-world runs

Scalar typing versus Core typing, the replay host `replayHost` (which answers
one callout and is `HostOk`), and `result_typed`: a closed-world run of an
export call to a result, from a well-formed store against an environment that
throws only existing exceptions, is read as an answer of the export type.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded

/-- Scalar typing gives Core value typing pointwise. -/
theorem forall₂_valOk_of_hasVal {H : Type} (s : Store H) :
    ∀ {ts : List ScalarType} {vs : List Val}, List.Forall₂ ScalarType.HasVal ts vs →
      List.Forall₂ (ValOk s) vs (ts.map ScalarType.toC)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs =>
    .cons ((ScalarType.hasVal_iff_valOk s _ _).mp h) (forall₂_valOk_of_hasVal s hs)

/-- A value typed at a type equal to, or a subtype of, a scalar type has that scalar type. -/
theorem hasVal_of_subEqR {H : Type} {s : Store H} {Δ : TypeCtx} {v : Val} {t : CValType}
    {st : ScalarType} (hv : ValOk s v t) (hs : SubEqR Δ t st.toC) : st.HasVal v := by
  rcases hs with rfl | ⟨hs, -⟩
  · exact (ScalarType.hasVal_iff_valOk s st v).mpr hv
  · cases st with
    | num n =>
      change Sub Δ t (.num n) at hs
      cases hs
      all_goals first
        | exact (ScalarType.hasVal_iff_valOk s (.num n) v).mpr hv
        | cases hv
    | v128 =>
      change Sub Δ t (.vec .v128) at hs
      cases hs
      all_goals first
        | exact (ScalarType.hasVal_iff_valOk s .v128 v).mpr hv
        | cases hv
    | i31 n =>
      have hs' : Sub Δ t (.refv (.ref n (.abs .i31))) := hs
      obtain ⟨r, rt₀, rfl, hb, hs0⟩ := ValOk.ref_invRT hv hs'
      exact ScalarType.hasVal_i31_of_base hb hs0

theorem forall₂_hasVal_of_subEqR {H : Type} {s : Store H} {Δ : TypeCtx} :
    ∀ {vs : List Val} {ts : List CValType} {sts : List ScalarType},
      List.Forall₂ (ValOk s) vs ts → List.Forall₂ (SubEqR Δ) ts (sts.map ScalarType.toC) →
      List.Forall₂ ScalarType.HasVal sts vs
  | [], [], [], .nil, _ => .nil
  | [], _, _ :: _, .nil, hs => by cases hs
  | _ :: _, _ :: _, _ :: _, .cons hv hvs, hs => by
    cases hs with
    | cons h hss => exact .cons (hasVal_of_subEqR hv h) (forall₂_hasVal_of_subEqR hvs hss)
  | _ :: _, _ :: _, [], .cons _ _, hs => by cases hs

/-- Returned values of a configuration typed at scalar result types are typed. -/
theorem hasVal_of_configOk {H : Type} {c : Config H} {sts : List ScalarType} {vs : List Val}
    (hc : ConfigOk c (sts.map ScalarType.toC)) (hcode : c.code = vals vs) :
    List.Forall₂ ScalarType.HasVal sts vs := by
  obtain ⟨C, -, hadm⟩ := hc
  rw [hcode] at hadm
  obtain ⟨-, -, ts', hv, hsub⟩ := AdminsOk.vals_aux' hadm vs rfl
  exact forall₂_hasVal_of_subEqR hv (by simpa using hsub)

/-- The host that replays the answer `r` to host code `h₀` at store `s₀` (store unchanged)
and otherwise diverges. -/
def replayHost (s₀ : Store Nat) (h₀ : Nat) (r : Result) : HostSemantics Nat :=
  fun h s _ out => out = .diverged ∨ (s = s₀ ∧ h = h₀ ∧ out = .returned s₀ r)

theorem replayHost_ok {s₀ : Store Nat} {h₀ : Nat} {r : Result} (hs : StoreOk s₀)
    (hr : ∀ fi ∈ s₀.funcs, fi.code = .host h₀ → ∀ ps rs, Expand fi.type (.func ps rs) →
      ResultTyped s₀ r rs.toList) : HostOk (replayHost s₀ h₀ r) := by
  intro s fi h vs ps rs _ hfi hcode hexp _
  refine ⟨⟨.diverged, Or.inl rfl⟩, fun out hout => ?_⟩
  rcases hout with rfl | ⟨rfl, rfl, rfl⟩
  · trivial
  · exact ⟨hs, Extend.refl hs, hr fi hfi hcode ps rs hexp⟩

/-- The Core result of an answer that throws below the exception count is typed. -/
theorem resultTyped_toResult {s : Store Nat} {ft : FnType} {w : Answer ft} {n : Nat}
    (hw : Answer.ThrowsBelow n w) (hn : n ≤ s.exns.length) :
    ResultTyped s w.toResult (ft.results.map ScalarType.toC) := by
  cases w with
  | values vs => exact forall₂_valOk_of_hasVal s vs.2
  | trap => trivial
  | throw a =>
    have ha : a < s.exns.length := Nat.lt_of_lt_of_le hw hn
    exact ⟨_, List.getElem?_eq_getElem ha⟩

theorem ifaceOp?_fst {ts : List FnType} {h : Nat} {args : List Val} {e : (ifaceSig ts).Op}
    (he : ifaceOp? ts h args = some e) : e.1.val = h := by
  unfold ifaceOp? at he
  split_ifs at he
  cases he; rfl

namespace ScalarInstance

variable {I : ScalarInstance}

/-- Typing invariant along a closed-world run from store `s`. -/
def RunInv (s : Store Nat) (ts : List CValType) (c : Config Nat) : Prop :=
  ConfigOk c ts ∧ c.store.funcs = s.funcs ∧ Extend s c.store

/-- Both sides of a function type expanded from the same defined type agree. -/
private theorem expand_func_toComp {d : DefType} {ps rs : Ty (.list .val)} {ft : FnType}
    (h₁ : Expand d (.func ps rs)) (h₂ : Expand d ft.toComp) :
    ps = Ty.ofList (ft.params.map ScalarType.toC) ∧
      rs = Ty.ofList (ft.results.map ScalarType.toC) := by
  simpa only [FnType.toComp, Ty.func.injEq] using Expand.func_eq h₁ h₂

/-- Replaying an answer of `K` to an import call is a host satisfying the host contract. -/
private theorem replayHost_answer_ok {s s₀ : Store Nat} (hw : I.WellFormed s)
    {K : Silmaril.Wasm.Game.Env I.E} (hK : ThrowsBelow K s.exns.length) (hS : StoreOk s₀)
    (hfun : s₀.funcs = s.funcs) (hext : Extend s s₀) {hh : Nat} {args : List Val}
    {e : I.E.Op} {w : I.E.Ar e} (he : ifaceOp? I.imports hh args = some e)
    (hans : K.Answers e w) :
    HostOk (replayHost s₀ hh (Answer.toResult (ft := I.imports.get e.1) w)) := by
  refine replayHost_ok hS fun fi hfi hcode ps rs hexp => ?_
  obtain ⟨n, hn⟩ : ∃ n, s.funcs[n]? = some fi := List.mem_iff_getElem?.mp (hfun ▸ hfi)
  obtain ⟨hlt, hexp'⟩ := hw.host_type n fi hh hn hcode
  have hfin : (⟨hh, hlt⟩ : Fin I.imports.length) = e.1 := Fin.ext (ifaceOp?_fst he).symm
  have hrs : rs = Ty.ofList ((I.imports.get e.1).results.map ScalarType.toC) := by
    simpa only [hfin] using (expand_func_toComp hexp hexp').2
  rw [hrs, Ty.toList_ofList]
  exact resultTyped_toResult (hK e w hans) hext.exns.1

theorem RunInv.step {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {K : Silmaril.Wasm.Game.Env I.E} (hK : ThrowsBelow K s.exns.length) {ts : List CValType}
    {c c' : Config Nat} (hc : RunInv s ts c)
    (h : Step P (hostOf I.imports K) c c') : RunInv s ts c' := by
  obtain ⟨hok, hfun, hext⟩ := hc
  rcases Step.split_host h with h0 | ⟨E, a, hh, args, hd, ⟨s', r, hr, rfl⟩ | ⟨-, rfl⟩⟩
  · obtain ⟨hok', hext'⟩ :=
      Step.preservation (SingleThreaded.divHost_ok (H := Nat)) hok (Step.of_noHost _ h0)
    have hi : InternalP P (c.store, .active c.frame c.code) (c'.store, .active c'.frame c'.code) :=
      ⟨c'.frame, c'.code, rfl, h0⟩
    exact ⟨hok', by rw [InternalP.funcs_prefix hi, hfun], hext.trans hext'⟩
  · show RunInv s ts ⟨s', c.frame, E.fill r.toAdmin⟩
    obtain ⟨e, he, ⟨w, hans, hout⟩ | ⟨-, hout⟩⟩ := hr
    · show RunInv s ts ⟨s', c.frame, E.fill r.toAdmin⟩
      obtain ⟨rfl, rfl⟩ : s' = c.store ∧ r = Answer.toResult w := by simpa using hout
      have hres : (resumeResult c.store (.active c.frame c.code) (Answer.toResult w)).config
          c.store = ⟨c.store, c.frame, E.fill (Answer.toResult w).toAdmin⟩ :=
        resumeResult_config hd
      have hstep : Step P (replayHost c.store hh (Answer.toResult w)) c
          ⟨c.store, c.frame, E.fill (Answer.toResult w).toAdmin⟩ :=
        hres ▸ (stepP_iff P (replayHost c.store hh (Answer.toResult w)) c.store
          (.active c.frame c.code) _).mpr
          (Or.inr ⟨E, a, hh, args, hd, Or.inl ⟨c.store, _, Or.inr ⟨rfl, rfl, rfl⟩, rfl⟩⟩)
      have hok' : HostOk (replayHost c.store hh (Answer.toResult w)) :=
        replayHost_answer_ok hw hK (SingleThreaded.ConfigOk.storeOk hok) hfun hext he hans
      exact ⟨(Step.preservation hok' hok hstep).1, hfun, hext⟩
    · cases hout
  · exact ⟨hok, hfun, hext⟩

/-- The typing invariant along a closed-world run. -/
theorem RunInv.steps {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {K : Silmaril.Wasm.Game.Env I.E} (hK : ThrowsBelow K s.exns.length) {ts : List CValType}
    {c c' : Config Nat} (run : Steps P (hostOf I.imports K) c c')
    (hc : RunInv s ts c) : RunInv s ts c' := by
  induction run with
  | refl => exact hc
  | tail _ hst ih => exact RunInv.step hw hK ih hst

/-- **Typed results.** A closed-world run of an export call to a result, from a well-formed
store against an environment throwing only existing exceptions, is read as an answer. -/
theorem result_typed {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {K : Silmaril.Wasm.Game.Env I.E} (hK : ThrowsBelow K s.exns.length) {f : I.F.Op}
    {c' : Config Nat} {r : Result}
    (run : Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c')
    (final : c'.code = r.toAdmin) : ∃ w, Answer.ofResult? (I.exports.get f.1) r = some w := by
  cases r with
  | trap => exact ⟨_, rfl⟩
  | throw a => exact ⟨_, rfl⟩
  | values vs =>
    show ∃ w, Answer.ofResult? (I.exports.get f.1) (.values vs) = some w
    obtain ⟨fi, hfi, hexp⟩ := hw.export_type f.1
    have hinv : InvokeOk s (I.addr f.1) f.2.1 := by
      refine ⟨fi, Ty.ofList ((I.exports.get f.1).params.map ScalarType.toC),
        Ty.ofList ((I.exports.get f.1).results.map ScalarType.toC), hfi, hexp, ?_⟩
      rw [Ty.toList_ofList]
      exact forall₂_valOk_of_hasVal s f.2.2
    obtain ⟨fi', ps, rs, hfi', hexp', hok⟩ := invoke_ok hw.storeOk hinv
    obtain rfl : fi' = fi := (Option.some.inj (hfi.symm.trans hfi')).symm
    have hrs : rs = Ty.ofList ((I.exports.get f.1).results.map ScalarType.toC) :=
      (expand_func_toComp hexp' hexp).2
    have h0 : RunInv s ((I.exports.get f.1).results.map ScalarType.toC)
        (invoke s (I.addr f.1) f.2.1) := by
      refine ⟨?_, rfl, Extend.refl hw.storeOk⟩
      simpa only [hrs, Ty.toList_ofList] using hok
    have hend : RunInv s ((I.exports.get f.1).results.map ScalarType.toC) c' :=
      RunInv.steps hw hK run h0
    have htyped : List.Forall₂ ScalarType.HasVal (I.exports.get f.1).results vs :=
      hasVal_of_configOk hend.1 final
    exact ⟨.values ⟨vs, htyped⟩, by simp only [Answer.ofResult?, htyped, dite_true]⟩

end ScalarInstance

end Silmaril.Proofs.Wasm.Game
