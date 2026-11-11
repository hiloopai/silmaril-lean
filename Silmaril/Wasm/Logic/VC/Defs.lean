module

public import Silmaril.Wasm.Logic.Hoare.Defs

/-!
# A verification-condition generator for structured Wasm code

`wpc inv k is Q s f vs` is a **weakest-precondition calculus computed by recursion on the
instruction list** `is` (Core 3.0, `Silmaril.Wasm.Instr`): a `Prop` that, by
`Silmaril.Wasm.Logic.VC.Thms.wpc_sound`, implies the every-run weakest precondition
`HWP P host s f (vals vs ++ expression is) Q` (partial correctness and safety) at every profile
and for every host relation. `vs` is the operand stack, bottom first.

The fragment:

* straight-line code evaluated by `Silmaril.Wasm.Logic.Core.exec1` (integer constants and
  arithmetic, comparisons and tests, locals, globals, `drop`, `nop`, integer loads and stores);
* `select`, `br`, `br_if`, `br_table`, `return`, `unreachable` (the outcome `trap`);
* the integer conversions `i32.wrap_i64`, `i64.extend_i32_s`, `i64.extend_i32_u` (`cvt1`);
* `call x` of a function with a specification in the **spec context** `VCSpecs.specs`
  (modular: the callee's body is not looked at; the continuation must hold for every outcome
  the specification allows);
* `block`, `if` and `loop`, the loops annotated with invariants `inv k` numbered in pre-order
  (`loops is` counts the loops of `is`; the `k`-th loop of the program gets `inv k`).

The spec context is an instance argument `[VCSpecs H]`: by default (`VCSpecs.empty`, low
priority) it is empty and every `call` gives `False`; a client verifying code with calls
supplies `(Γ := ⟨specs⟩)` and, for soundness, `VCSpecs.Valid` (every listed specification is a
valid `Silmaril.Wasm.Logic.Hoare.FSpecValid`). Code with an empty context and `wpc_sound` are
unchanged.

Anything else gives `False` (the generator is sound, not complete). A loop's invariant is
asked on entry and at every branch back to the loop, for frames of the same module instance.
`ctl` classifies an instruction for the generator; `labelQ`/`loopQ` are the generator's forms of
`Silmaril.Wasm.Logic.Hoare.labelPost`/`loopPost` with the continuation after the construct given
as a predicate `K` on the store, frame and stack (itself a `wpc`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.VC

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post exec1)
open Silmaril.Wasm.Logic.Hoare (FSpec)

variable {H : Type}

/-- **A spec context for calls**: for some function addresses, the number of parameters and a
specification (`Silmaril.Wasm.Logic.Hoare.FSpec`). -/
class VCSpecs (H : Type) where
  /-- The specifications, by function address. -/
  specs : Nat → Option (Nat × FSpec H)

/-- The empty spec context (the default: calls are not supported). -/
instance (priority := low) VCSpecs.empty : VCSpecs H := ⟨fun _ => Option.none⟩

/-- A spec context is **valid** (at a profile and host relation) when each of its
specifications is (`Silmaril.Wasm.Logic.Hoare.FSpecValid`) and its precondition says that the
function exists. The empty context is valid. -/
def VCSpecs.Valid (Γ : VCSpecs H) (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ a n S, Γ.specs a = some (n, S) → Silmaril.Wasm.Logic.Hoare.FSpecValid P host a S ∧
    ∀ s args, S.pre s args → (s.funcs[a]?).isSome

/-- How the generator treats an instruction. -/
inductive Ctl where
  | block (bt : BlockType) (body : List Instr)
  | loop (bt : BlockType) (body : List Instr)
  | if_ (bt : BlockType) (b₁ b₂ : List Instr)
  | br (l : LabelIdx)
  | brIf (l : LabelIdx)
  | brTable (ls : List LabelIdx) (d : LabelIdx)
  | call (x : FuncIdx)
  | cvt (op : ConvertOp)
  | select
  | ret
  | trap
  /-- Evaluated by `exec1` (or unsupported, when `exec1` fails). -/
  | plain

/-! ## Globals by index

`globalVal s m x` is the value of the `x`-th global of the module instance `m` in the store `s`,
`setGlobalIdx s m x v` the store with that global set to `v`. The evaluation lemmas of `wat_vc`
(`Silmaril.Proofs.Wasm.Logic.VC.Exec`) state `global.get`/`global.set` with them, so a store that
is only known through hypotheses `globalVal s m x = some v` (a **symbolic** store) stays
symbolic: setting global `x` leaves global `y ≠ x` unchanged when the instance's global
addresses are distinct (`m.globals.Nodup`, true of every instantiated module). -/

/-- The value of global `x` of the instance `m`. -/
def globalVal {H : Type} (s : Store H) (m : ModuleInst) (x : Nat) : Option Val :=
  (m.globals[x]?).bind fun a => (s.globals[a]?).map (·.value)

/-- Set global `x` of the instance `m` (no change when the instance has no such global). -/
def setGlobalIdx {H : Type} (s : Store H) (m : ModuleInst) (x : Nat) (v : Val) : Store H :=
  match m.globals[x]? with
  | some a => s.setGlobal a v
  | none => s

/-- The classification of an instruction. -/
def ctl : Instr → Ctl
  | .block bt b => .block bt b
  | .loop bt b => .loop bt b
  | .if_ bt b₁ b₂ => .if_ bt b₁ b₂
  | .br l => .br l
  | .brIf l => .brIf l
  | .brTable ls d => .brTable ls d
  | .call x => .call x
  | .convert op => .cvt op
  | .select _ => .select
  | .return_ => .ret
  | .unreachable => .trap
  | _ => .plain

/-- The classes that the reflective generators `Silmaril.Wasm.Auto.VCGen*` evaluate as straight-line
code (by their own `step1`): `plain`, and `br_table`, `call`, conversions and `unreachable`, which
`wpc` handles itself. -/
def PlainCtl (c : Ctl) : Prop :=
  c = .plain ∨ (∃ ls d, c = .brTable ls d) ∨ (∃ x, c = .call x) ∨ (∃ op, c = .cvt op) ∨
    c = .trap

theorem sizeOf_block {i : Instr} {bt : BlockType} {b : List Instr} (h : ctl i = .block bt b) :
    sizeOf b < sizeOf i := by
  cases i <;> simp only [ctl, reduceCtorEq, Ctl.block.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [Instr.block.sizeOf_spec]
  omega

theorem sizeOf_loop {i : Instr} {bt : BlockType} {b : List Instr} (h : ctl i = .loop bt b) :
    sizeOf b < sizeOf i := by
  cases i <;> simp only [ctl, reduceCtorEq, Ctl.loop.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [Instr.loop.sizeOf_spec]
  omega

theorem sizeOf_if {i : Instr} {bt : BlockType} {b₁ b₂ : List Instr} (h : ctl i = .if_ bt b₁ b₂) :
    sizeOf b₁ < sizeOf i ∧ sizeOf b₂ < sizeOf i := by
  cases i <;> simp only [ctl, reduceCtorEq, Ctl.if_.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  simp only [Instr.if_.sizeOf_spec]
  omega

/-- The number of loops of an instruction list (pre-order). -/
def loops : List Instr → Nat
  | [] => 0
  | i :: r =>
    (match h : ctl i with
      | .block _ b => have := sizeOf_block h; loops b
      | .loop _ b => have := sizeOf_loop h; loops b + 1
      | .if_ _ b₁ b₂ => have := sizeOf_if h; loops b₁ + loops b₂
      | _ => 0) + loops r
termination_by is => sizeOf is

/-- Pop an `i32` from a stack (bottom first). -/
def popI32 (vs : List Val) : Option (List Val × BitVec 32) :=
  match vs.reverse with
  | .num ⟨.int .i32, c⟩ :: rus => some (rus.reverse, c)
  | _ => none

/-- Pop the three operands of `select`: two values and an `i32` condition. -/
def popSelect (vs : List Val) : Option (List Val × Val × Val × BitVec 32) :=
  match vs.reverse with
  | .num ⟨.int .i32, c⟩ :: v₂ :: v₁ :: rus => some (rus.reverse, v₁, v₂, c)
  | _ => none

/-- `i32.wrap_i64`. -/
def wrap64 (x : BitVec 64) : BitVec 32 := x.setWidth 32
/-- `i64.extend_i32_u`. -/
def extendU32 (x : BitVec 32) : BitVec 64 := x.setWidth 64
/-- `i64.extend_i32_s`. -/
def extendS32 (x : BitVec 32) : BitVec 64 := x.signExtend 64

/-- The integer conversions: the stack (bottom first) after `i32.wrap_i64`,
`i64.extend_i32_s` or `i64.extend_i32_u`; `none` for other conversions or operands. -/
def cvt1 (op : ConvertOp) (vs : List Val) : Option (List Val) :=
  match op, vs.reverse with
  | .wrap, .num ⟨.int .i64, x⟩ :: rus => some (rus.reverse ++ [.num ⟨.int .i32, wrap64 x⟩])
  | .extend .unsigned, .num ⟨.int .i32, x⟩ :: rus =>
    some (rus.reverse ++ [.num ⟨.int .i64, extendU32 x⟩])
  | .extend .signed, .num ⟨.int .i32, x⟩ :: rus =>
    some (rus.reverse ++ [.num ⟨.int .i64, extendS32 x⟩])
  | _, _ => none

/-- `br_table ls d` on the index `c`: `K l` for the label `l` it branches to, as one conjunct
per entry of the table (`c = j → K l_j`) and one for the default (`j + |ls| ≤ c → K d`), so
that `simp` unfolds it into cases for a concrete table. -/
def tableVC (K : LabelIdx → Prop) (c : Nat) : Nat → List LabelIdx → LabelIdx → Prop
  | j, [], d => j ≤ c → K d
  | j, l :: ls, d => (c = j → K l) ∧ tableVC K c (j + 1) ls d

/-- What a call's outcome `o` (from the callee) asks of the caller, with the values `us` below
the arguments: a return continues with `K` on `us ++ res`; a trap or an exception leaves with
`Q`. (`callPost` admits no other outcome.) -/
def callK (f : Frame) (us : List Val) (K : Store H → List Val → Prop) (Q : Post H)
    (s : Store H) : Outcome → Prop
  | .normal res => K s (us ++ res)
  | .trap => Q s f .trap
  | .throw a => Q s f (.throw a)
  | _ => True

/-- **A call** of `x` from the frame `f` with the stack `vs`: the callee's address `a` has a
specification `(n, S)` in the context, the stack has the `n` arguments, the precondition holds, and every outcome the postcondition allows satisfies `callK`. -/
def callVC [Γ : VCSpecs H] (s : Store H) (f : Frame) (vs : List Val) (x : FuncIdx)
    (K : Store H → List Val → Prop) (Q : Post H) : Prop :=
  match f.module.funcs[x.toNat]? with
  | some a =>
    match Γ.specs a with
    | some (n, S) => n ≤ vs.length ∧
        S.pre s (vs.drop (vs.length - n)) ∧
        ∀ s' o, S.post s (vs.drop (vs.length - n)) s' o →
          callK f (vs.take (vs.length - n)) K Q s' o
    | none => False
  | none => False

/-- A `block` or `loop` of type `bt` entered with the stack `vs`: the block type resolves to
`t₁ → t₂`, the stack has the `t₁` arguments, and `B us args t₁.length t₂.length` holds for
the values `us` below the arguments and the arguments `args`. -/
def enterVC (f : Frame) (bt : BlockType) (vs : List Val) (B : List Val → List Val → Nat → Nat → Prop) :
    Prop :=
  match f.module.blockType? bt with
  | some (t₁, t₂) => t₁.length ≤ vs.length ∧
      B (vs.take (vs.length - t₁.length)) (vs.drop (vs.length - t₁.length)) t₁.length t₂.length
  | none => False

/-- The postcondition of a block body (`labelPost` with the continuation `K`): falling through
or branching to the block (with its `n` results) continues with `K` on the values `us` below the
block; every other outcome leaves the block. -/
def labelQ (n : Nat) (us : List Val) (K : Store H → Frame → List Val → Prop) (Q : Post H) :
    Post H := fun s f o =>
  match o with
  | .normal vs => K s f (us ++ vs)
  | .br 0 vs => n ≤ vs.length ∧ K s f (us ++ vs.drop (vs.length - n))
  | .br (l + 1) vs => Q s f (.br l (us ++ vs))
  | .ret vs => Q s f (.ret (us ++ vs))
  | .trap => Q s f .trap
  | .throw a => Q s f (.throw a)
  | .tail vs a c => Q s f (.tail (us ++ vs) a c)

/-- The postcondition of a loop body (`loopPost`): branching to the loop re-establishes the
invariant `I` on the loop's `n` parameters; falling through continues with `K`. -/
def loopQ (n : Nat) (us : List Val) (I : Store H → Frame → List Val → Prop)
    (K : Store H → Frame → List Val → Prop) (Q : Post H) : Post H := fun s f o =>
  match o with
  | .normal vs => K s f (us ++ vs)
  | .br 0 vs => n ≤ vs.length ∧ I s f (vs.drop (vs.length - n))
  | .br (l + 1) vs => Q s f (.br l (us ++ vs))
  | .ret vs => Q s f (.ret (us ++ vs))
  | .trap => Q s f .trap
  | .throw a => Q s f (.throw a)
  | .tail vs a c => Q s f (.tail (us ++ vs) a c)

/-- Loop invariants, numbered in pre-order, on the store, the frame and the loop parameters. -/
abbrev Invs (H : Type) := Nat → Store H → Frame → List Val → Prop

/-- **The verification-condition generator.** `wpc inv k is Q s f vs`: running `is` from the
store `s`, frame `f` and stack `vs` is safe and every exit satisfies `Q`; the loops of `is` use
the invariants `inv k`, `inv (k + 1)`, … in pre-order. -/
def wpc [Γ : VCSpecs H] (inv : Invs H) (k : Nat) : List Instr → Post H → Store H → Frame → List Val → Prop
  | [], Q, s, f, vs => Q s f (.normal vs)
  | i :: r, Q, s, f, vs =>
    match h : ctl i with
    | .block bt b =>
      have := sizeOf_block h
      enterVC f bt vs fun us args _ n₂ =>
        wpc inv k b (labelQ n₂ us (fun s f vs => wpc inv (k + loops b) r Q s f vs) Q) s f args
    | .loop bt b =>
      have := sizeOf_loop h
      enterVC f bt vs fun us args n₁ _ =>
        inv k s f args ∧
        ∀ s' f' a', inv k s' f' a' → f'.module = f.module → a'.length = n₁ →
          wpc inv (k + 1) b
            (loopQ n₁ us (fun s'' f'' a'' => inv k s'' f'' a'' ∧ f''.module = f.module)
              (fun s f vs => wpc inv (k + 1 + loops b) r Q s f vs) Q) s' f' a'
    | .if_ bt b₁ b₂ =>
      have := sizeOf_if h
      match popI32 vs with
      | some (us, c) =>
        (c ≠ 0 → enterVC f bt us fun us' args _ n₂ =>
          wpc inv k b₁
            (labelQ n₂ us' (fun s f vs => wpc inv (k + loops b₁ + loops b₂) r Q s f vs) Q)
            s f args) ∧
        (c = 0 → enterVC f bt us fun us' args _ n₂ =>
          wpc inv (k + loops b₁) b₂
            (labelQ n₂ us' (fun s f vs => wpc inv (k + loops b₁ + loops b₂) r Q s f vs) Q)
            s f args)
      | none => False
    | .br l => Q s f (.br l.toNat vs)
    | .brIf l =>
      match popI32 vs with
      | some (us, c) => (c ≠ 0 → Q s f (.br l.toNat us)) ∧ (c = 0 → wpc inv k r Q s f us)
      | none => False
    | .brTable ls d =>
      match popI32 vs with
      | some (us, c) => tableVC (fun l => Q s f (.br l.toNat us)) c.toNat 0 ls d
      | none => False
    | .call x => callVC s f vs x (fun s' vs' => wpc inv k r Q s' f vs') Q
    | .cvt op =>
      match cvt1 op vs with
      | some vs' => wpc inv k r Q s f vs'
      | none => False
    | .select =>
      match popSelect vs with
      | some (us, v₁, v₂, c) =>
        (c ≠ 0 → wpc inv k r Q s f (us ++ [v₁])) ∧ (c = 0 → wpc inv k r Q s f (us ++ [v₂]))
      | none => False
    | .ret => Q s f (.ret vs)
    | .trap => Q s f .trap
    | .plain =>
      match exec1 s f vs.reverse i with
      | some (s', f', rs') => wpc inv k r Q s' f' rs'.reverse
      | none => False
termination_by is => sizeOf is

end Silmaril.Wasm.Logic.VC
