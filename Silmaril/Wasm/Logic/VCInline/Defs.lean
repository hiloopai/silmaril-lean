module

public import Silmaril.Wasm.Logic.VCTotal.Defs

/-!
# A verification-condition generator with inlining

`wpi C d inv k is Q s f vs` is `Silmaril.Wasm.Logic.VC.wpc` with two changes that make whole
simulator problems provable without hand-written specifications:

* **inlining**: a `call` of a function whose code is in the table `C` (function instance, body,
  arity) is evaluated by the generator on the callee's body in its initial frame, up to the
  inlining depth `d`; the callee's exits continue the caller (`callK`). Calls outside `C` (or
  at depth `0`) use the specification context `Γ` (`callVC`), as in `wpc`;
* **loops without invariants**: the loop invariants are optional (`IInvs`); a loop with
  `inv k = none` is evaluated once from its entry state and must not branch back (the P-calls
  dispatcher of a straight-line program); with `inv k = some I` it is `wpc`'s rule;
* **branching by `if`**: conditionals, `br_if`, `select` and `br_table` produce `if … then … else`
  (`tableI`), so that `simp` evaluates only the taken branch when the condition is a literal
  (inlined code is mostly called with constant arguments).

Soundness: `Silmaril.Proofs.Wasm.Logic.VCInline.Sound`, under `C.Valid` (each entry's instance
runs its body at the stated arity) and `Γ.Valid`. A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.VC

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post exec1)

variable {H : Type}

/-- The code of a function for inlining. -/
structure ICode (H : Type) where
  /-- The function instance. -/
  fi : FuncInst H
  /-- Its body. -/
  code : Func
  /-- The number of parameters. -/
  np : Nat
  /-- The number of results. -/
  nr : Nat

/-- A code table by function address. -/
abbrev Codes (H : Type) := Nat → Option (ICode H)

/-- Each entry's function instance runs its body with the stated arity. -/
def Codes.Valid (C : Codes H) : Prop :=
  ∀ a c, C a = some c → c.fi.code = .wasm c.code ∧
    ∃ ps rs, Silmaril.Wasm.Validation.Expand c.fi.type (.func ps rs) ∧ ps.length = c.np ∧
      rs.length = c.nr

/-- Optional loop invariants, numbered in pre-order. -/
abbrev IInvs (H : Type) := Nat → Option (Store H → Frame → List Val → Prop)

/-- `br_table` as nested `if`s: `K` of the label the index `c` selects (table from position
`j`). -/
def tableI (K : LabelIdx → Prop) (c : Nat) : Nat → List LabelIdx → LabelIdx → Prop
  | _, [], d => K d
  | j, l :: ls, d => if c = j then K l else tableI K c (j + 1) ls d

/-- **The generator with inlining.** -/
def wpi [Γ : VCSpecs H] (C : Codes H) (d : Nat) (inv : IInvs H) (k : Nat) :
    List Instr → Post H → Store H → Frame → List Val → Prop
  | [], Q, s, f, vs => Q s f (.normal vs)
  | i :: r, Q, s, f, vs =>
    match h : ctl i with
    | .block bt b =>
      have := sizeOf_block h
      enterVC f bt vs fun us args _ n₂ =>
        wpi C d inv k b (labelQ n₂ us (fun s f vs => wpi C d inv (k + loops b) r Q s f vs) Q) s f args
    | .loop bt b =>
      have := sizeOf_loop h
      enterVC f bt vs fun us args n₁ _ =>
        match inv k with
        | none =>
          wpi C d inv (k + 1) b (loopQ n₁ us (fun _ _ _ => False)
            (fun s f vs => wpi C d inv (k + 1 + loops b) r Q s f vs) Q) s f args
        | some I =>
          I s f args ∧
          ∀ s' f' a', I s' f' a' → f'.module = f.module → a'.length = n₁ →
            wpi C d inv (k + 1) b
              (loopQ n₁ us (fun s'' f'' a'' => I s'' f'' a'' ∧ f''.module = f.module)
                (fun s f vs => wpi C d inv (k + 1 + loops b) r Q s f vs) Q) s' f' a'
    | .if_ bt b₁ b₂ =>
      have := sizeOf_if h
      match popI32 vs with
      | some (us, c) =>
        if c = 0 then
          enterVC f bt us fun us' args _ n₂ =>
            wpi C d inv (k + loops b₁) b₂
              (labelQ n₂ us' (fun s f vs => wpi C d inv (k + loops b₁ + loops b₂) r Q s f vs) Q)
              s f args
        else
          enterVC f bt us fun us' args _ n₂ =>
            wpi C d inv k b₁
              (labelQ n₂ us' (fun s f vs => wpi C d inv (k + loops b₁ + loops b₂) r Q s f vs) Q)
              s f args
      | none => False
    | .br l => Q s f (.br l.toNat vs)
    | .brIf l =>
      match popI32 vs with
      | some (us, c) => if c = 0 then wpi C d inv k r Q s f us else Q s f (.br l.toNat us)
      | none => False
    | .brTable ls dl =>
      match popI32 vs with
      | some (us, c) => tableI (fun l => Q s f (.br l.toNat us)) c.toNat 0 ls dl
      | none => False
    | .call x =>
      match f.module.funcs[x.toNat]? with
      | some a =>
        match C a with
        | some c =>
          if _hd : 0 < d then
            c.np ≤ vs.length ∧ s.funcs[a]? = some c.fi ∧
              wpi C (d - 1) (fun _ => none) 0 c.code.body
                (fnPost c.nr fun s' o => callK f (vs.take (vs.length - c.np))
                  (fun s' vs' => wpi C d inv k r Q s' f vs') Q s' o)
                s (Frame.forCall c.fi.module (vs.drop (vs.length - c.np)) c.code.locals) []
          else callVC s f vs x (fun s' vs' => wpi C d inv k r Q s' f vs') Q
        | none => callVC s f vs x (fun s' vs' => wpi C d inv k r Q s' f vs') Q
      | none => False
    | .cvt op =>
      match cvt1 op vs with
      | some vs' => wpi C d inv k r Q s f vs'
      | none => False
    | .select =>
      match popSelect vs with
      | some (us, v₁, v₂, c) =>
        if c = 0 then wpi C d inv k r Q s f (us ++ [v₂]) else wpi C d inv k r Q s f (us ++ [v₁])
      | none => False
    | .ret => Q s f (.ret vs)
    | .trap => Q s f .trap
    | .plain =>
      match exec1 s f vs.reverse i with
      | some (s', f', rs') => wpi C d inv k r Q s' f' rs'.reverse
      | none => False
termination_by is => (d, sizeOf is)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp only [List.cons.sizeOf_spec]; omega)

end Silmaril.Wasm.Logic.VC
