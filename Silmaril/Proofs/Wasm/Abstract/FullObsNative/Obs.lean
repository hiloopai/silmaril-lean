module

public import Silmaril.Wasm.Abstract.FullObsNative.Defs
public import Silmaril.Proofs.Wasm.Abstract.FullObsNative.Local
public import Silmaril.Wasm.Abstract.HostEval.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.FullObsNative.Thms`: the filtered full observation `obsC`
read as paths and infinite runs of the exposed body, its finite part as `EvalO`, its divergence
as `LocalDivO`, and the H2 callee relation `hostCall` on Wasm functions.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FullObsNative

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Wasm.Abstract.FullObsNative Silmaril.Elgot.ITree

variable {H : Type}

theorem ansL_map {C : CallRel H} {cs : List (Call (CallSig H))} :
    AnsL C (cs.map liftCall) ↔ Answered C cs := by
  simp only [AnsL, Answered, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  rfl

theorem mem_obsC_fin {C : CallRel H} {es : List BExpr} {f : Frame} {stk : List Val} {s : Store H}
    {x : CallBeh (liftSig (CallSig H)) (St H) Res} :
    x ∈ (obsC C es f stk).1 ⟨s⟩ ⟨⟩ ↔
      ∃ cs r, Answered C cs ∧ Path (tr (denListE es f stk) ⟨s⟩) cs r ∧ x = (cs.map liftCall, endOf r) := by
  constructor
  · rintro ⟨⟨cs, r, hp, rfl⟩, hA⟩
    exact ⟨cs, r, ansL_map.1 hA, hp, rfl⟩
  · rintro ⟨cs, r, hA, hp, rfl⟩
    exact ⟨⟨cs, r, hp, rfl⟩, ansL_map.2 hA⟩

theorem mem_obsC_inf {C : CallRel H} {es : List BExpr} {f : Frame} {stk : List Val} {s : Store H}
    {ω : Nat → Call (liftSig (CallSig H))} :
    ω ∈ (obsC C es f stk).2 ⟨s⟩ ⟨⟩ ↔
      ∃ ω', AnsweredS C ω' ∧ InfPath (tr (denListE es f stk) ⟨s⟩) ω' ∧ ω = liftCall ∘ ω' := by
  constructor
  · rintro ⟨⟨ω', hp, rfl⟩, hA⟩
    exact ⟨ω', hA, hp, rfl⟩
  · rintro ⟨ω', hA, hp, rfl⟩
    exact ⟨⟨ω', hp, rfl⟩, hA⟩

theorem endOf_ret_inv {r : PathEnd (Ex H Res)} {b : Res} {σ : St H} (h : endOf r = End.ret b σ) :
    r = .val (.ok (b, σ)) := by
  rcases r with (_ | ⟨b', σ'⟩) | _
  · cases h
  · simp only [endOf, End.ret.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · cases h

theorem endOf_trap_inv {r : PathEnd (Ex H Res)} (h : endOf r = End.trap) :
    r = .val (.error ⟨⟩) := by
  rcases r with (e | ⟨b', σ'⟩) | _
  · rfl
  · cases h
  · cases h

theorem endOf_div_inv {r : PathEnd (Ex H Res)} (h : endOf r = End.div) : r = .div := by
  rcases r with (e | ⟨b', σ'⟩) | _
  · cases h
  · cases h
  · rfl

theorem obsC_ret_iff {C : CallRel H} {es : List BExpr} {f : Frame} {stk : List Val} {s s' : Store H}
    {f' : Frame} {fl : Flow} (hfl : fl ≠ .trap) :
    (∃ c, (c, End.ret ⟨(f', fl)⟩ ⟨s'⟩) ∈ (obsC C es f stk).1 ⟨s⟩ ⟨⟩) ↔
      EvalO C s f stk es (s', f', fl) := by
  rw [evalO_iff hfl]
  constructor
  · rintro ⟨c, hx⟩
    obtain ⟨cs, r, hA, hp, hx⟩ := mem_obsC_fin.1 hx
    obtain ⟨-, he⟩ := Prod.mk.inj hx
    rw [endOf_ret_inv he.symm] at hp
    exact ⟨cs, hA, hp⟩
  · rintro ⟨cs, hA, hp⟩
    exact ⟨_, mem_obsC_fin.2 ⟨cs, _, hA, hp, rfl⟩⟩

theorem obsC_trap_iff {C : CallRel H} {es : List BExpr} {f : Frame} {stk : List Val} {s : Store H} :
    (∃ c, (c, End.trap) ∈ (obsC C es f stk).1 ⟨s⟩ ⟨⟩) ↔
      ∃ s' f', EvalO C s f stk es (s', f', .trap) := by
  rw [evalO_trap_iff]
  constructor
  · rintro ⟨c, hx⟩
    obtain ⟨cs, r, hA, hp, hx⟩ := mem_obsC_fin.1 hx
    obtain ⟨-, he⟩ := Prod.mk.inj hx
    rw [endOf_trap_inv he.symm] at hp
    exact ⟨cs, hA, hp⟩
  · rintro ⟨cs, hA, hp⟩
    exact ⟨_, mem_obsC_fin.2 ⟨cs, _, hA, hp, rfl⟩⟩

theorem obsC_div_iff {C : CallRel H} {es : List BExpr} {f : Frame} {stk : List Val} {s : Store H} :
    (∃ c, (c, End.div) ∈ (obsC C es f stk).1 ⟨s⟩ ⟨⟩) ↔
      ∃ cs, Answered C cs ∧ Path (tr (denListE es f stk) ⟨s⟩) cs .div := by
  constructor
  · rintro ⟨c, hx⟩
    obtain ⟨cs, r, hA, hp, hx⟩ := mem_obsC_fin.1 hx
    obtain ⟨-, he⟩ := Prod.mk.inj hx
    rw [endOf_div_inv he.symm] at hp
    exact ⟨cs, hA, hp⟩
  · rintro ⟨cs, hA, hp⟩
    exact ⟨_, mem_obsC_fin.2 ⟨cs, _, hA, hp, rfl⟩⟩

theorem obsC_inf_iff {C : CallRel H} {es : List BExpr} {f : Frame} {stk : List Val} {s : Store H} :
    (∃ ω, ω ∈ (obsC C es f stk).2 ⟨s⟩ ⟨⟩) ↔
      ∃ ω, AnsweredS C ω ∧ InfPath (tr (denListE es f stk) ⟨s⟩) ω := by
  constructor
  · rintro ⟨ω, hω⟩
    obtain ⟨ω', hA, hp, -⟩ := mem_obsC_inf.1 hω
    exact ⟨ω', hA, hp⟩
  · rintro ⟨ω, hA, hp⟩
    exact ⟨_, mem_obsC_inf.2 ⟨ω, hA, hp, rfl⟩⟩

/-- A stuck tree (`try_table`, outside this exposure) has a silent path but does not diverge
locally. -/
theorem tryTable_silent {C : CallRel H} (bt : BlockType) (cs : List Catch) (body : List BExpr)
    (s : Store H) (f : Frame) (stk : List Val) :
    Path (tr (denListE [.tryTable bt cs body] f stk) ⟨s⟩) [] .div ∧
      ¬ LocalDivO C s f stk [.tryTable bt cs body] := by
  refine ⟨?_, fun h => ?_⟩
  · rw [tr_single, denC]
    exact .div rfl
  · have := localDivO_iff_step.1 h
    cases this

/-- The H2 callee relation on a Wasm function: its body, run by `EvalH`. -/
theorem hostCall_wasm_iff {host : HostSemantics H} {s : Store H} {a : Nat} {us : List Val}
    {fi : FuncInst H} {fn : Func} (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    {out : Store H × Flow} :
    hostCall host s a us out ↔
      ∃ ps rs f₂, Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        EvalH host s (Frame.forCall fi.module us fn.locals) [] (liftInstrs fn.body)
          (out.1, f₂, out.2) := by
  rw [hostCall_fixpoint]
  constructor
  · rintro (⟨fi', fn', ps, rs, f₂, hfi', hcode', hty, hev⟩ | ⟨fi', h, r, hfi', hcode', -⟩)
    · rw [hfi] at hfi'
      cases hfi'
      rw [hcode] at hcode'
      cases hcode'
      exact ⟨ps, rs, f₂, hty, hev⟩
    · rw [hfi] at hfi'
      cases hfi'
      rw [hcode] at hcode'
      cases hcode'
  · rintro ⟨ps, rs, f₂, hty, hev⟩
    refine .inl ⟨fi, fn, ps, rs, f₂, hfi, hcode, hty, ?_⟩
    exact hev

/-- Local divergence of a call, on the filtered observation of its body. -/
theorem localCallDivO_obsC {C : CallRel H} {z : (wasmOShape H).self.Op} (h : LocalCallDivO C z) :
    ∃ (fi : FuncInst H) (fn : Func), z.2.2.funcs[z.1]? = some fi ∧ fi.code = .wasm fn ∧
      ((∃ c, (c, End.div) ∈
          (obsC C (liftInstrs fn.body) (Frame.forCall fi.module z.2.1 fn.locals) []).1 ⟨z.2.2⟩ ⟨⟩) ∨
        ∃ ω, ω ∈
          (obsC C (liftInstrs fn.body) (Frame.forCall fi.module z.2.1 fn.locals) []).2 ⟨z.2.2⟩ ⟨⟩) := by
  obtain ⟨fi, fn, hfi, hcode, hL⟩ := h
  refine ⟨fi, fn, hfi, hcode, ?_⟩
  rcases exposed_of_localDivO hL with h | h
  · exact .inl (obsC_div_iff.2 h)
  · exact .inr (obsC_inf_iff.2 h)

/-- A productive filtered run of a call's body is local divergence of the call. -/
theorem localCallDivO_of_obsC {C : CallRel H} {z : (wasmOShape H).self.Op}
    (h : ∃ (fi : FuncInst H) (fn : Func), z.2.2.funcs[z.1]? = some fi ∧ fi.code = .wasm fn ∧
      ∃ ω, ω ∈
        (obsC C (liftInstrs fn.body) (Frame.forCall fi.module z.2.1 fn.locals) []).2 ⟨z.2.2⟩ ⟨⟩) :
    LocalCallDivO C z := by
  obtain ⟨fi, fn, hfi, hcode, hω⟩ := h
  obtain ⟨ω, hA, hp⟩ := obsC_inf_iff.1 hω
  exact ⟨fi, fn, hfi, hcode, localDivO_of_prod ⟨ω, hA, hp⟩⟩

/-- **The H2 callee relation on a Wasm function, on the filtered observation** (non-trap ends). -/
theorem hostCall_iff_obs {host : HostSemantics H} {s : Store H} {a : Nat} {us : List Val}
    {fi : FuncInst H} {fn : Func} (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    {s' : Store H} {fl : Flow} (hfl : fl ≠ .trap) :
    hostCall host s a us (s', fl) ↔
      ∃ ps rs f₂, Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        ∃ c, (c, End.ret ⟨(f₂, fl)⟩ ⟨s'⟩) ∈
          (obsC (hostCall host) (liftInstrs fn.body) (Frame.forCall fi.module us fn.locals) []).1
            ⟨s⟩ ⟨⟩ := by
  rw [hostCall_wasm_iff hfi hcode]
  simp only [obsC_ret_iff hfl]

/-- **The H2 callee relation on a Wasm function, traps.** -/
theorem hostCall_trap_iff_obs {host : HostSemantics H} {s : Store H} {a : Nat} {us : List Val}
    {fi : FuncInst H} {fn : Func} (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn) :
    (∃ s', hostCall host s a us (s', .trap)) ↔
      ∃ ps rs, Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        ∃ c, (c, End.trap) ∈
          (obsC (hostCall host) (liftInstrs fn.body) (Frame.forCall fi.module us fn.locals) []).1
            ⟨s⟩ ⟨⟩ := by
  simp only [hostCall_wasm_iff hfi hcode, obsC_trap_iff]
  constructor
  · rintro ⟨s', ps, rs, f₂, hty, hev⟩
    exact ⟨ps, rs, hty, s', f₂, hev⟩
  · rintro ⟨ps, rs, hty, s', f₂, hev⟩
    exact ⟨s', ps, rs, f₂, hty, hev⟩

end Silmaril.Proofs.Wasm.Abstract.FullObsNative
