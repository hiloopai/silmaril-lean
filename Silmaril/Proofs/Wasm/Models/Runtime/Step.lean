module

public import Silmaril.Proofs.Wasm.Models.Runtime.Family

/-!
# The runtime invariant is preserved by every Core 3.0 step

`step_inFeat`: for every profile and every host that keeps the store in `S` (`HostIn S`), a
Core step keeps `Rt.InFeat S`. The context rules use the induction hypothesis; the call rules
use `StoreIn` (the entered body is of `S`); the delegated families are `Family`; every other
rule rearranges values and instructions of `S` (structured instructions into labels and
handlers, `call_indirect` into its expansion).

New proof.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.Rt

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Models
  Silmaril.Wasm.Models.Rt

variable {S : FeatureSet} {H : Type}

theorem storeIn_of_funcs {s t : Store H} (h : t.funcs = s.funcs) (hs : StoreIn S s) :
    StoreIn S t := fun a fi fn ha => hs a fi fn (h ▸ ha)

/-- A runtime `return_call_ref y` needs typed function references or `call_indirect`. -/
theorem returnCallRef_caps {y : TypeIdx} (h : AdmIn S (.plain (.returnCallRef y))) :
    S.has .typedFuncRef = true ∨ S.has .callIndirect = true := by
  have h' : (S.has .tailCall && S.has .typedFuncRef ||
      S.has .tailCall && S.has .callIndirect) = true := by
    simpa [instrB, Instr.inFeatB, Instr.headB] using h
  have h'' : (S.has .tailCall = true ∧ S.has .typedFuncRef = true) ∨
      (S.has .tailCall = true ∧ S.has .callIndirect = true) := by
    simpa only [Bool.or_eq_true, Bool.and_eq_true] using h'
  exact h''.imp (·.2) (·.2)

theorem admIn_retToCallIn_plain {y : TypeIdx} (m : ModuleInst)
    (h : AdmIn S (.plain (.returnCallRef y))) :
    AdmIn S ((Admin.plain (.returnCallRef y)).retToCallIn m) := by
  have hy := returnCallRef_caps h
  show AdmIn S (match m.types[y.toNat]? with
    | some d => .callRefType d | none => .plain (.callRef y))
  cases m.types[y.toNat]? with
  | some d => trivial
  | none =>
    show instrB S (.callRef y) = true
    rcases hy with h' | h' <;> simp [instrB, Instr.inFeatB, Instr.headB, h']

theorem admIn_retToCallIn {c : Admin} (m : ModuleInst) (hc : c.IsReturnCallRef)
    (h : AdmIn S c) : AdmIn S (c.retToCallIn m) := by
  cases c with
  | plain i =>
    cases i with
    | returnCallRef y => exact admIn_retToCallIn_plain m h
    | _ => exact absurd hc (by simp [Admin.IsReturnCallRef])
  | returnCallRefType d => trivial
  | _ => exact absurd hc (by simp [Admin.IsReturnCallRef])

theorem codeIn_result (r : Result) (hr : ∀ a, r = .throw a → S.has .exn = true) :
    CodeIn S r.toAdmin := by
  cases r with
  | values vs => exact codeIn_vals vs
  | throw a => simp [Result.toAdmin, instrB, Instr.inFeatB, Instr.headB, hr a rfl]
  | trap => simp [Result.toAdmin]

theorem ctxt_instrs {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (ih : InFeat S ⟨s, f, is⟩ → InFeat S ⟨s', f', is'⟩)
    (hc : InFeat S ⟨s, f, vals vs ++ is ++ rest⟩) : InFeat S ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  have hi : CodeIn S is ∧ CodeIn S rest := by simpa using hc.1
  have h' : InFeat S ⟨s', f', is'⟩ := ih ⟨hi.1, hc.2⟩
  exact ⟨by simp [hi.2, h'.1], h'.2⟩

theorem ctxt_label {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {is is' : List Admin} (ih : InFeat S ⟨s, f, is⟩ → InFeat S ⟨s', f', is'⟩)
    (hc : InFeat S ⟨s, f, [.label n cont is]⟩) : InFeat S ⟨s', f', [.label n cont is']⟩ := by
  have hi : Instr.insInFeatB S cont = true ∧ CodeIn S is := by simpa using hc.1
  have h' : InFeat S ⟨s', f', is'⟩ := ih ⟨hi.2, hc.2⟩
  exact ⟨by simp [hi.1, h'.1], h'.2⟩

theorem ctxt_handler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch}
    {is is' : List Admin} (ih : InFeat S ⟨s, f, is⟩ → InFeat S ⟨s', f', is'⟩)
    (hc : InFeat S ⟨s, f, [.handler n cs is]⟩) : InFeat S ⟨s', f', [.handler n cs is']⟩ := by
  have hi : S.has .control = true ∧ CodeIn S is := by simpa using hc.1
  have h' : InFeat S ⟨s', f', is'⟩ := ih ⟨hi.2, hc.2⟩
  exact ⟨by simp [hi.1, h'.1], h'.2⟩

theorem ctxt_frame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (ih : InFeat S ⟨s, fi, is⟩ → InFeat S ⟨s', fi', is'⟩)
    (hc : InFeat S ⟨s, f, [.frame n fi is]⟩) : InFeat S ⟨s', f, [.frame n fi' is']⟩ := by
  have hi : CodeIn S is := by simpa using hc.1
  have h' : InFeat S ⟨s', fi', is'⟩ := ih ⟨hi, hc.2⟩
  exact ⟨by simp [h'.1], h'.2⟩

theorem ret_frame_addr {s : Store H} {f fi : Frame} {k a : Nat} {vs' vs : List Val} {c : Admin}
    {rest : List Admin} (hc' : c.IsReturnCallRef)
    (hc : InFeat S ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩) :
    InFeat S ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩ := by
  have hi : AdmIn S c ∧ CodeIn S rest := by simpa using hc.1
  exact ⟨by simp [admIn_retToCallIn fi.module hc' hi.1], hc.2⟩

theorem throw_inFeat {s : Store H} {f : Frame} {vs : List Val} {x : TagIdx} {e : ExnInst}
    {n : Nat} (hc : InFeat S ⟨s, f, vals vs ++ [.plain (.throw x)]⟩) :
    InFeat S ⟨s.addExn e, f, throwing n⟩ := by
  have hx : S.has .exn = true := by simpa [instrB, Instr.inFeatB, Instr.headB] using hc.1
  exact ⟨by simp [throwing, instrB, Instr.inFeatB, Instr.headB, hx],
    storeIn_of_funcs rfl hc.2⟩

theorem step_inFeat {P : Profile} {host : HostSemantics H} (hh : HostIn S host)
    {c c' : Config H} (h : Step P host c c') (hc : InFeat S c) : InFeat S c' := by
  induction h with
  | parametric h => exact ⟨parametric_codeIn h hc.1, hc.2⟩
  | numeric h => exact ⟨numeric_codeIn h hc.1, hc.2⟩
  | vector h => exact ⟨vector_codeIn h hc.1, hc.2⟩
  | «variable» h =>
    exact ⟨(variable_codeIn h hc.1).1, storeIn_of_funcs (variable_codeIn h hc.1).2 hc.2⟩
  | table h => exact ⟨(table_codeIn h hc.1).1, storeIn_of_funcs (table_codeIn h hc.1).2 hc.2⟩
  | memory h =>
    exact ⟨(memory_codeIn h hc.1).1, storeIn_of_funcs (memory_codeIn h hc.1).2 hc.2⟩
  | reference h =>
    exact ⟨(reference_codeIn h hc.1).1, storeIn_of_funcs (reference_codeIn h hc.1).2 hc.2⟩
  | aggregate h =>
    exact ⟨(aggregate_codeIn h hc.1).1, storeIn_of_funcs (aggregate_codeIn h hc.1).2 hc.2⟩
  | ctxtInstrs _ _ ih => exact ctxt_instrs ih hc
  | ctxtLabel _ ih => exact ctxt_label ih hc
  | ctxtHandler _ ih => exact ctxt_handler ih hc
  | ctxtFrame _ ih => exact ctxt_frame ih hc
  | callRefFunc _ hf _ _ hcode =>
    exact ⟨by simp [Instr.insInFeatB, codeIn_expression (hc.2 _ _ _ hf hcode)], hc.2⟩
  | callRefHost _ _ _ _ _ hhost =>
    exact ⟨codeIn_result _ (hh _ _ _ _ _ hhost hc.2).2, (hh _ _ _ _ _ hhost hc.2).1⟩
  | returnCallRefFrameAddr hc' => exact ret_frame_addr hc' hc
  | throw => exact throw_inFeat hc
  | _ => all_goals simp_all [InFeat, instrB, Instr.inFeatB, Instr.headB, Instr.insInFeatB,
    throwing, codeIn_expression]

end Silmaril.Proofs.Wasm.Models.Rt
