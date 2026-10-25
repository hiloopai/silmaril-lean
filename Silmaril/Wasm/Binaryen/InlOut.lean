module

public import Silmaril.Wasm.Binaryen.InlHead

@[expose] public section

/-! # The reducts of simple head steps

`Out c`: the reduct of a head step whose head is a plain non-structured instruction other
than a local access (or a call annotation) is a trap, a sequence of values and plain
instructions that the callee relocation `InlineTy.xform` leaves alone (`okA`), or one of
the call shapes. `head_out` proves it, family by family.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type} {P : Numerics.Profile}

/-- Local accesses. -/
def IsLocalI : Instr → Bool
  | .localGet _ | .localSet _ | .localTee _ => true
  | _ => false

/-- Tail calls. -/
def IsTailI : Instr → Bool
  | .returnCall _ | .returnCallRef _ | .returnCallIndirect _ _ => true
  | _ => false

/-- Plain instructions unchanged by the relocation and allowed in callee code. -/
def okI (i : Instr) : Bool :=
  !structuredInstr i && !IsLocalI i && !IsTailI i && (match i with | .return_ => false | _ => true)

/-- Values and `okI` instructions. -/
def okA : Admin → Bool
  | .plain i => okI i
  | .ref _ => true
  | _ => false

@[simp] theorem okA_plain (i : Instr) : okA (.plain i) = okI i := rfl

@[simp] theorem okA_ref (r : Ref) : okA (.ref r) = true := rfl

@[simp] theorem okA_val (v : Val) : okA v.toAdmin = true := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

@[simp] theorem okA_constI32 (c : BitVec 32) : okA (constI32 c) = true := okA_val _

@[simp] theorem all_okA_vals (vs : List Val) : (vals vs).all okA = true := by simp [vals]

/-- Reducts of simple head steps other than tail calls. -/
def Out (c : List Admin) : Prop :=
  c = [.trap] ∨ c.all okA = true ∨ (∃ a d, c = [.ref (.func a), .callRefType d])

/-- Reducts of tail calls. -/
def OutT (c : List Admin) : Prop :=
  (∃ a d, c = [.ref (.func a), .returnCallRefType d]) ∨
    (∃ x y, c = [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩),
      .plain (.returnCallRef y)])

/-- Tail-call heads. -/
def TailE (e : Admin) : Prop :=
  (∃ x, e = .plain (.returnCall x)) ∨ (∃ x y, e = .plain (.returnCallIndirect x y))

theorem Out.trap : Out [.trap] := .inl rfl

theorem Out.ok {c : List Admin} (h : c.all okA = true) : Out c := .inr (.inl h)

theorem Out.vals (vs : List Val) : Out (vals vs) := .ok (all_okA_vals vs)

/-- Close `Out` for a literal reduct. -/
macro "out_tac" : tactic => `(tactic| first
  | exact Out.trap
  | exact Out.vals _
  | (apply Out.ok; simp [okI, IsLocalI, IsTailI, structuredInstr, vals, constAddr, aconst, store8,
      load8u, List.all_append, List.all_map]; done)
  | (apply Out.ok; cases ‹AddrType› <;> simp [okI, IsLocalI, IsTailI, structuredInstr, vals,
      constAddr, aconst, store8, load8u, List.all_append, List.all_map]; done))

theorem parametric_out {is is' : List Admin} (h : ParametricStep is is') : Out is' := by
  cases h <;> out_tac

theorem numeric_out {is is' : List Admin} (h : NumericStep P is is') : Out is' := by
  cases h <;> out_tac

theorem vector_out {is is' : List Admin} (h : VectorStep P is is') : Out is' := by
  cases h <;> out_tac

theorem table_out {c c' : Config H} (h : TableStep P c c') : Out c'.code := by
  cases h <;> out_tac

theorem memory_out {c c' : Config H} (h : MemoryStep P c c') : Out c'.code := by
  cases h <;> out_tac

theorem ref_out {c c' : Config H} (h : RefStep c c') : Out c'.code := by
  cases h <;> out_tac

theorem aggregate_out {c c' : Config H} (h : AggregateStep c c') : Out c'.code := by
  cases h
  all_goals first
    | out_tac
    | (apply Out.ok
       simp [okI, structuredInstr, IsLocalI, IsTailI]
       intro x hx
       obtain ⟨r, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop (List.mem_of_mem_take hx))
       rfl)

/-- Structured plain instructions. -/
def StructE (e : Admin) : Prop :=
  (∃ bt b, e = .plain (.block bt b)) ∨ (∃ bt b, e = .plain (.loop bt b)) ∨
    (∃ bt b₁ b₂, e = .plain (.if_ bt b₁ b₂)) ∨ (∃ bt cs b, e = .plain (.tryTable bt cs b))

/-- **The reducts of simple head steps.** -/
theorem head_out {s : Store H} {f : Frame} {args : List Val} {e : Admin} {c₀ : Config H}
    (h : Det.Head P s f args e c₀) (hS : SimpleE e) (hNS : ¬ StructE e) :
    CallData s f args e c₀ ∨ Out c₀.code ∨ (TailE e ∧ OutT c₀.code) := by
  obtain ⟨hL, hH, hF, hG, hS', hT⟩ := hS
  obtain ⟨s₀, f₀, is₀⟩ := c₀
  cases h with
  | parametric h => exact .inr (.inl (parametric_out h))
  | numeric h => exact .inr (.inl (numeric_out h))
  | vector h => exact .inr (.inl (vector_out h))
  | «variable» h =>
    generalize hc : vals args ++ [e] = code at h
    cases h with
    | localGet _ => exact absurd (last_eq_of_append_singleton (l' := []) hc) (hG _)
    | localSet _ =>
      exact absurd (last_eq_of_append_singleton (l' := [_]) hc) (hS' _)
    | localTee => exact absurd (last_eq_of_append_singleton (l' := [_]) hc) (hT _)
    | globalGet _ => exact .inr (.inl (Out.vals [_]))
    | globalSet _ => exact .inr (.inl (Out.vals []))
  | table h => exact .inr (.inl (table_out h))
  | memory h => exact .inr (.inl (memory_out h))
  | reference h => exact .inr (.inl (ref_out h))
  | aggregate h => exact .inr (.inl (aggregate_out h))
  | ctxtLabel _ => exact absurd rfl (hL _ _ _)
  | ctxtHandler _ => exact absurd rfl (hH _ _ _)
  | ctxtFrame _ => exact absurd rfl (hF _ _ _)
  | block _ _ => exact absurd (.inl ⟨_, _, rfl⟩) hNS
  | loop _ _ => exact absurd (.inr (.inl ⟨_, _, rfl⟩)) hNS
  | ifTrue _ => exact absurd (.inr (.inr (.inl ⟨_, _, _, rfl⟩))) hNS
  | ifFalse _ => exact absurd (.inr (.inr (.inl ⟨_, _, _, rfl⟩))) hNS
  | tryTable _ _ => exact absurd (.inr (.inr (.inr ⟨_, _, _, rfl⟩))) hNS
  | labelVals _ => exact absurd rfl (hL _ _ _)
  | brLabelZero _ _ _ => exact absurd rfl (hL _ _ _)
  | brLabelSucc _ _ => exact absurd rfl (hL _ _ _)
  | brHandler _ => exact absurd rfl (hH _ _ _)
  | brIfTrue _ => exact .inr (.inl (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI])))
  | brIfFalse _ => exact .inr (.inl (Out.vals []))
  | brTableLt _ => exact .inr (.inl (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI])))
  | brTableGe _ => exact .inr (.inl (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI])))
  | brOnNullNull => exact .inr (.inl (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI])))
  | brOnNullAddr _ => exact .inr (.inl (Out.vals [_]))
  | brOnNonNullNull => exact .inr (.inl (Out.vals []))
  | brOnNonNullAddr _ => exact .inr (.inl (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI])))
  | brOnCastSucceed _ => exact .inr (.inl (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI])))
  | brOnCastFail _ => exact .inr (.inl (.ok (by simp)))
  | brOnCastFailSucceed _ => exact .inr (.inl (.ok (by simp)))
  | brOnCastFailFail _ => exact .inr (.inl (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI])))
  | call _ _ => exact .inr (.inl (.inr (.inr ⟨_, _, rfl⟩)))
  | callRefNull _ => exact .inr (.inl Out.trap)
  | callRefFunc ha hc hf he hn hcode =>
    exact .inl ⟨_, _, _, _, _, _, ha, hc, hf, he, hn, hcode, rfl⟩
  | returnCall _ _ => exact .inr (.inr ⟨.inl ⟨_, rfl⟩, .inl ⟨_, _, rfl⟩⟩)
  | returnCallRefLabel _ _ => exact absurd rfl (hL _ _ _)
  | returnCallRefHandler _ _ => exact absurd rfl (hH _ _ _)
  | returnCallRefFrameNull _ _ => exact absurd rfl (hF _ _ _)
  | returnCallRefFrameAddr _ _ _ _ _ => exact absurd rfl (hF _ _ _)
  | callIndirect => exact .inr (.inl (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI])))
  | returnCallIndirect => exact .inr (.inr ⟨.inr ⟨_, _, rfl⟩, .inr ⟨_, _, rfl⟩⟩)
  | frameVals _ _ => exact absurd rfl (hF _ _ _)
  | returnFrame _ _ => exact absurd rfl (hF _ _ _)
  | returnLabel _ => exact absurd rfl (hL _ _ _)
  | returnHandler _ => exact absurd rfl (hH _ _ _)
  | throw _ _ _ => exact .inr (.inl (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI])))
  | throwRefNull => exact .inr (.inl Out.trap)
  | throwRefLabel => exact absurd rfl (hL _ _ _)
  | throwRefFrame => exact absurd rfl (hF _ _ _)
  | throwRefHandlerEmpty => exact absurd rfl (hH _ _ _)
  | throwRefHandlerCatch _ _ => exact absurd rfl (hH _ _ _)
  | throwRefHandlerCatchRef _ _ => exact absurd rfl (hH _ _ _)
  | throwRefHandlerCatchAll => exact absurd rfl (hH _ _ _)
  | throwRefHandlerCatchAllRef => exact absurd rfl (hH _ _ _)
  | throwRefHandlerNext _ => exact absurd rfl (hH _ _ _)
  | handlerVals _ => exact absurd rfl (hH _ _ _)
  | trapLabel => exact absurd rfl (hL _ _ _)
  | trapHandler => exact absurd rfl (hH _ _ _)
  | trapFrame => exact absurd rfl (hF _ _ _)

end Silmaril.Wasm.Binaryen.InlR
