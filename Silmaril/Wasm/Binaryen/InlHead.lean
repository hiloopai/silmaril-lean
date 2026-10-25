module

public import Silmaril.Wasm.Binaryen.InlRel
public import Silmaril.Wasm.SingleThreaded.Exec.Driver

@[expose] public section

/-! # Head steps under a replaced function list and a replaced frame

A head step (`Det.Head`) whose head is a plain instruction other than a local access,
or a call annotation, does not look at function code or at the locals of the frame. It
is therefore also a step in a store with a function list of the same types and in any
frame with the same module (`head_simple`). Calls into a Wasm function
(`Head.callRefFunc`) are the exception: the new frame holds the callee's code; they are
returned separately.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type} {P : Numerics.Profile}

/-- Heads that are neither structured administrative instructions nor local accesses. -/
def SimpleE (e : Admin) : Prop :=
  (∀ n c b, e ≠ .label n c b) ∧ (∀ n cs b, e ≠ .handler n cs b) ∧ (∀ n F b, e ≠ .frame n F b) ∧
    (∀ x, e ≠ .plain (.localGet x)) ∧ (∀ x, e ≠ .plain (.localSet x)) ∧
    (∀ x, e ≠ .plain (.localTee x))

theorem simpleE_plain {i : Instr} (h1 : ∀ x, i ≠ .localGet x) (h2 : ∀ x, i ≠ .localSet x)
    (h3 : ∀ x, i ≠ .localTee x) : SimpleE (.plain i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ h; cases h
  · intro _ _ _ h; cases h
  · intro _ _ _ h; cases h
  · intro x h; cases h; exact h1 x rfl
  · intro x h; cases h; exact h2 x rfl
  · intro x h; cases h; exact h3 x rfl

theorem last_eq_of_append_singleton {α : Type _} {l : List α} {l' : List α} {e a : α}
    (h : l ++ [e] = l' ++ [a]) : e = a :=
  (List.append_inj' h rfl).2 |> fun h => by simpa using h

/-- The data of a call into a Wasm function. -/
def CallData (s : Store H) (f : Frame) (args : List Val) (e : Admin) (c₀ : Config H) : Prop :=
  ∃ (vs : List Val) (a : Nat) (fi : FuncInst H) (ps rs : Ty (.list .val)) (code : Func),
    args = vs ++ [.ref (.func a)] ∧ e.IsCallRef ∧ s.funcs[a]? = some fi ∧
    Expand fi.type (.func ps rs) ∧ vs.length = ps.length ∧ fi.code = .wasm code ∧
    c₀ = ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
      [.label rs.length [] (expression code.body)]]⟩

/-- **Simple head steps transfer.** -/
theorem head_simple {s : Store H} {f : Frame} {args : List Val} {e : Admin} {c₀ : Config H}
    (h : Det.Head P s f args e c₀) (hS : SimpleE e) {X : List (FuncInst H)}
    (hX : SameTypes X s.funcs) (gl : List (Option Val)) :
    CallData s f args e c₀ ∨
    (c₀.frame = f ∧ c₀.store.funcs = s.funcs ∧
      Det.Head P (withFuncs s X) ⟨gl, f.module⟩ args e
        ⟨withFuncs c₀.store X, ⟨gl, f.module⟩, c₀.code⟩) := by
  obtain ⟨hL, hH, hF, hG, hS', hT⟩ := hS
  obtain ⟨s₀, f₀, is₀⟩ := c₀
  cases h with
  | parametric h => exact .inr ⟨rfl, rfl, .parametric h⟩
  | numeric h => exact .inr ⟨rfl, rfl, .numeric h⟩
  | vector h => exact .inr ⟨rfl, rfl, .vector h⟩
  | «variable» h =>
    generalize hc : vals args ++ [e] = code at h
    cases h with
    | localGet _ => exact absurd (last_eq_of_append_singleton (l' := []) hc) (hG _)
    | localSet _ =>
      exact absurd (last_eq_of_append_singleton (l' := [_]) hc) (hS' _)
    | localTee => exact absurd (last_eq_of_append_singleton (l' := [_]) hc) (hT _)
    | globalGet h' => exact .inr ⟨rfl, rfl, .variable (by rw [hc]; exact .globalGet h')⟩
    | globalSet h' => exact .inr ⟨rfl, rfl, .variable (by rw [hc]; exact .globalSet h')⟩
  | table h =>
    obtain ⟨hf, rfl, h'⟩ := tableStep_withFuncs h X
    exact .inr ⟨rfl, hf, .table (h' gl)⟩
  | memory h =>
    obtain ⟨hf, rfl, h'⟩ := memoryStep_withFuncs h X
    exact .inr ⟨rfl, hf, .memory (h' gl)⟩
  | reference h =>
    obtain ⟨hf, rfl, h'⟩ := refStep_withFuncs h hX
    exact .inr ⟨rfl, hf, .reference (h' gl)⟩
  | aggregate h =>
    obtain ⟨hf, rfl, h'⟩ := aggregateStep_withFuncs h X
    exact .inr ⟨rfl, hf, .aggregate (h' gl)⟩
  | ctxtLabel _ => exact absurd rfl (hL _ _ _)
  | ctxtHandler _ => exact absurd rfl (hH _ _ _)
  | ctxtFrame _ => exact absurd rfl (hF _ _ _)
  | block hbt hm => exact .inr ⟨rfl, rfl, .block hbt hm⟩
  | loop hbt hm => exact .inr ⟨rfl, rfl, .loop hbt hm⟩
  | ifTrue hc => exact .inr ⟨rfl, rfl, .ifTrue hc⟩
  | ifFalse hc => exact .inr ⟨rfl, rfl, .ifFalse hc⟩
  | labelVals _ => exact absurd rfl (hL _ _ _)
  | brLabelZero _ _ _ => exact absurd rfl (hL _ _ _)
  | brLabelSucc _ _ => exact absurd rfl (hL _ _ _)
  | brHandler _ => exact absurd rfl (hH _ _ _)
  | brIfTrue hc => exact .inr ⟨rfl, rfl, .brIfTrue hc⟩
  | brIfFalse hc => exact .inr ⟨rfl, rfl, .brIfFalse hc⟩
  | brTableLt hi => exact .inr ⟨rfl, rfl, .brTableLt hi⟩
  | brTableGe hi => exact .inr ⟨rfl, rfl, .brTableGe hi⟩
  | brOnNullNull => exact .inr ⟨rfl, rfl, .brOnNullNull⟩
  | brOnNullAddr hv => exact .inr ⟨rfl, rfl, .brOnNullAddr hv⟩
  | brOnNonNullNull => exact .inr ⟨rfl, rfl, .brOnNonNullNull⟩
  | brOnNonNullAddr hv => exact .inr ⟨rfl, rfl, .brOnNonNullAddr hv⟩
  | brOnCastSucceed h => exact .inr ⟨rfl, rfl, .brOnCastSucceed ((refOk_withFuncs_iff hX).2 h)⟩
  | brOnCastFail h =>
    exact .inr ⟨rfl, rfl, .brOnCastFail fun h' => h ((refOk_withFuncs_iff hX).1 h')⟩
  | brOnCastFailSucceed h =>
    exact .inr ⟨rfl, rfl, .brOnCastFailSucceed ((refOk_withFuncs_iff hX).2 h)⟩
  | brOnCastFailFail h =>
    exact .inr ⟨rfl, rfl, .brOnCastFailFail fun h' => h ((refOk_withFuncs_iff hX).1 h')⟩
  | call hx hf =>
    obtain ⟨fi', hf', ht⟩ := hX.get hf
    have := Det.Head.call (P := P) (s := withFuncs s X) (f := ⟨gl, f.module⟩) hx hf'
    rw [ht] at this
    exact .inr ⟨rfl, rfl, this⟩
  | callRefNull hc => exact .inr ⟨rfl, rfl, .callRefNull hc⟩
  | callRefFunc ha hc hf he hn hcode =>
    exact .inl ⟨_, _, _, _, _, _, ha, hc, hf, he, hn, hcode, rfl⟩
  | returnCall hx hf =>
    obtain ⟨fi', hf', ht⟩ := hX.get hf
    have := Det.Head.returnCall (P := P) (s := withFuncs s X) (f := ⟨gl, f.module⟩) hx hf'
    rw [ht] at this
    exact .inr ⟨rfl, rfl, this⟩
  | returnCallRefLabel _ _ => exact absurd rfl (hL _ _ _)
  | returnCallRefHandler _ _ => exact absurd rfl (hH _ _ _)
  | returnCallRefFrameNull _ _ => exact absurd rfl (hF _ _ _)
  | returnCallRefFrameAddr _ _ _ _ _ => exact absurd rfl (hF _ _ _)
  | callIndirect => exact .inr ⟨rfl, rfl, .callIndirect⟩
  | returnCallIndirect => exact .inr ⟨rfl, rfl, .returnCallIndirect⟩
  | frameVals _ _ => exact absurd rfl (hF _ _ _)
  | returnFrame _ _ => exact absurd rfl (hF _ _ _)
  | returnLabel _ => exact absurd rfl (hL _ _ _)
  | returnHandler _ => exact absurd rfl (hH _ _ _)
  | throw ht he hn => exact .inr ⟨rfl, rfl, .throw ht he hn⟩
  | throwRefNull => exact .inr ⟨rfl, rfl, .throwRefNull⟩
  | throwRefLabel => exact absurd rfl (hL _ _ _)
  | throwRefFrame => exact absurd rfl (hF _ _ _)
  | throwRefHandlerEmpty => exact absurd rfl (hH _ _ _)
  | throwRefHandlerCatch _ _ => exact absurd rfl (hH _ _ _)
  | throwRefHandlerCatchRef _ _ => exact absurd rfl (hH _ _ _)
  | throwRefHandlerCatchAll => exact absurd rfl (hH _ _ _)
  | throwRefHandlerCatchAllRef => exact absurd rfl (hH _ _ _)
  | throwRefHandlerNext _ => exact absurd rfl (hH _ _ _)
  | tryTable hbt hm => exact .inr ⟨rfl, rfl, .tryTable hbt hm⟩
  | handlerVals _ => exact absurd rfl (hH _ _ _)
  | trapLabel => exact absurd rfl (hL _ _ _)
  | trapHandler => exact absurd rfl (hH _ _ _)
  | trapFrame => exact absurd rfl (hF _ _ _)

end Silmaril.Wasm.Binaryen.InlR
