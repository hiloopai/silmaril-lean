module

public import Silmaril.Wasm.Logic.Core.Defs

@[expose] public section

/-! # Proof-producing equality saturation for Wasm: terms, rules, certificates

Straight-line integer Wasm code (`i32`/`i64` constants, `local.get`, unary, binary,
test and comparison operators) is a tree once its stack discipline is made explicit.
This module defines

* `Term`: such trees, with `compile` back to Core 3.0 instructions and an evaluator
  `Term.eval` that mirrors `Silmaril.Wasm.Logic.Core.exec` (`none` is a trap or a type
  error, as in `exec`);
* `Pat` and `Rule`: rewrite rules with typed pattern variables, each to be proved once
  over abstract operand values (`Rule.Sound`), at its minimal context;
* `Step` and `Cert`: a certificate is a chain of rule applications at positions, in
  either direction, plus constant-folding steps; `checkEq` and `checkRef` replay a
  certificate. Every function here is structurally recursive, so `decide` evaluates a
  check in the kernel.

The search that produces certificates is untrusted (`tools/wasm-egraph`, an egg-style
e-graph in Rust); the soundness theorems are in `Silmaril.Wasm.Auto.EGraph.Thms`.
-/

namespace Silmaril.Wasm.Auto.EGraph

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core

/-! ## Terms -/

/-- Straight-line integer code as a tree. Constants are stored as natural numbers
(read modulo the width); local indices as natural numbers (read modulo `2 ^ 32`). -/
inductive Term where
  | const (t : IntType) (n : Nat)
  | lget (i : Nat)
  | un (t : IntType) (op : IntUnOp) (a : Term)
  | test (t : IntType) (a : Term)
  | bin (t : IntType) (op : IntBinOp) (a b : Term)
  | rel (t : IntType) (op : IntRelOp) (a b : Term)
  deriving DecidableEq, Repr, Inhabited

/-- The local index of a natural number. -/
def lidx (i : Nat) : LocalIdx := ⟨Fin.ofNat _ i⟩

/-- An integer value of type `t`. -/
def intVal (t : IntType) (x : BitVec t.width) : Val := .num ⟨.int t, x⟩

/-- Read a value as an integer of type `t`. -/
def asInt : (t : IntType) → Val → Option (BitVec t.width)
  | .i32, .num ⟨.int .i32, a⟩ => some a
  | .i64, .num ⟨.int .i64, a⟩ => some a
  | _, _ => none

/-! ### Operations on optional values, shared by terms and patterns -/

/-- A unary operator on an optional operand. -/
def unV (t : IntType) (op : IntUnOp) (a : Option Val) : Option Val :=
  (a.bind (asInt t)).map fun x => intVal t (intUnOp t op x)

/-- `eqz` on an optional operand. -/
def testV (t : IntType) (a : Option Val) : Option Val :=
  (a.bind (asInt t)).map fun x => Val.i32 (intTestOp t .eqz x)

/-- A binary operator on optional operands; a trap is `none`. -/
def binV (t : IntType) (op : IntBinOp) (a b : Option Val) : Option Val :=
  a.bind fun va => b.bind fun vb => (asInt t va).bind fun x => (asInt t vb).bind fun y =>
    match intBinOp t op x y with
    | .ok z => some (intVal t z)
    | .error _ => none

/-- A comparison on optional operands. -/
def relV (t : IntType) (op : IntRelOp) (a b : Option Val) : Option Val :=
  a.bind fun va => b.bind fun vb => (asInt t va).bind fun x => (asInt t vb).map fun y =>
    Val.i32 (intRelOp t op x y)

/-- The value of a term in a frame. -/
def Term.eval (f : Frame) : Term → Option Val
  | .const t n => some (intVal t (BitVec.ofNat _ n))
  | .lget i => localVal? f (lidx i)
  | .un t op a => unV t op (a.eval f)
  | .test t a => testV t (a.eval f)
  | .bin t op a b => binV t op (a.eval f) (b.eval f)
  | .rel t op a b => relV t op (a.eval f) (b.eval f)

/-- The Core 3.0 instructions of a term: operands first, operator last. -/
def Term.compile : Term → List Instr
  | .const t n => [.intConst t (BitVec.ofNat _ n)]
  | .lget i => [.localGet (lidx i)]
  | .un t op a => a.compile ++ [.intUnOp t op]
  | .test t a => a.compile ++ [.intTestOp t .eqz]
  | .bin t op a b => a.compile ++ b.compile ++ [.intBinOp t op]
  | .rel t op a b => a.compile ++ b.compile ++ [.intRelOp t op]

/-- A sequence of terms, pushed left to right. -/
def compileL : List Term → List Instr
  | [] => []
  | e :: es => e.compile ++ compileL es

/-- The values a sequence of terms pushes, first pushed first. -/
def evalL (f : Frame) : List Term → Option (List Val)
  | [] => some []
  | e :: es => (e.eval f).bind fun v => (evalL f es).map (v :: ·)

/-- The type of a term, given the types `Γ` of the locals. -/
def Term.typeOf (Γ : List IntType) : Term → Option IntType
  | .const t _ => some t
  | .lget i => Γ[i]?
  | .un t _ a => if a.typeOf Γ = some t then some t else none
  | .test t a => if a.typeOf Γ = some t then some .i32 else none
  | .bin t _ a b => if a.typeOf Γ = some t ∧ b.typeOf Γ = some t then some t else none
  | .rel t _ a b => if a.typeOf Γ = some t ∧ b.typeOf Γ = some t then some .i32 else none

/-- The term contains no operator that can trap (no division or remainder). -/
def Term.noTrap : Term → Bool
  | .const _ _ | .lget _ => true
  | .un _ _ a | .test _ a => a.noTrap
  | .bin _ op a b =>
    (match op with | .div _ | .rem _ => false | _ => true) && a.noTrap && b.noTrap
  | .rel _ _ a b => a.noTrap && b.noTrap

/-- The frame holds a value of type `Γ[i]` in each local `i < Γ.length` (what validation
gives for a function's parameters and declared locals). -/
def FrameOk (Γ : List IntType) (f : Frame) : Prop :=
  ∀ i t, Γ[i]? = some t → ∃ x, localVal? f (lidx i) = some (intVal t x)

/-- An optional value is a trap or an integer of type `t`. -/
def TypedV (t : IntType) (o : Option Val) : Prop :=
  ∀ v, o = some v → ∃ x, v = intVal t x

/-- An optional value is an integer of type `t` (not a trap). -/
def TotalV (t : IntType) (o : Option Val) : Prop :=
  ∃ x, o = some (intVal t x)

/-! ## Positions -/

/-- The subterm at a path (child indices `0`, `1`). -/
def Term.get? : Term → List Nat → Option Term
  | e, [] => some e
  | .un _ _ a, 0 :: p | .test _ a, 0 :: p => a.get? p
  | .bin _ _ a _, 0 :: p | .rel _ _ a _, 0 :: p => a.get? p
  | .bin _ _ _ b, 1 :: p | .rel _ _ _ b, 1 :: p => b.get? p
  | _, _ => none
termination_by structural e _ => e

/-- Replace the subterm at a path. -/
def Term.set? : Term → List Nat → Term → Option Term
  | _, [], r => some r
  | .un t op a, 0 :: p, r => (a.set? p r).map (.un t op ·)
  | .test t a, 0 :: p, r => (a.set? p r).map (.test t ·)
  | .bin t op a b, 0 :: p, r => (a.set? p r).map (.bin t op · b)
  | .rel t op a b, 0 :: p, r => (a.set? p r).map (.rel t op · b)
  | .bin t op a b, 1 :: p, r => (b.set? p r).map (.bin t op a ·)
  | .rel t op a b, 1 :: p, r => (b.set? p r).map (.rel t op a ·)
  | _, _, _ => none
termination_by structural e _ _ => e

/-! ## Patterns and rules -/

/-- Rule patterns: terms with typed variables and without locals. A total variable
`tvar t n` only matches terms that cannot trap. -/
inductive Pat where
  | var (t : IntType) (n : Nat)
  | tvar (t : IntType) (n : Nat)
  | const (t : IntType) (n : Nat)
  | un (t : IntType) (op : IntUnOp) (a : Pat)
  | test (t : IntType) (a : Pat)
  | bin (t : IntType) (op : IntBinOp) (a b : Pat)
  | rel (t : IntType) (op : IntRelOp) (a b : Pat)
  deriving DecidableEq, Repr

/-- The typed variables of a pattern. -/
def Pat.vars : Pat → List (IntType × Nat)
  | .var t n => [(t, n)]
  | .tvar _ _ | .const _ _ => []
  | .un _ _ a | .test _ a => a.vars
  | .bin _ _ a b | .rel _ _ a b => a.vars ++ b.vars

/-- The total variables of a pattern. -/
def Pat.tvars : Pat → List (IntType × Nat)
  | .tvar t n => [(t, n)]
  | .var _ _ | .const _ _ => []
  | .un _ _ a | .test _ a => a.tvars
  | .bin _ _ a b | .rel _ _ a b => a.tvars ++ b.tvars

/-- The value of a pattern when variable `n` has the value `ρ n`. -/
def Pat.eval (ρ : Nat → Option Val) : Pat → Option Val
  | .var _ n | .tvar _ n => ρ n
  | .const t n => some (intVal t (BitVec.ofNat _ n))
  | .un t op a => unV t op (a.eval ρ)
  | .test t a => testV t (a.eval ρ)
  | .bin t op a b => binV t op (a.eval ρ) (b.eval ρ)
  | .rel t op a b => relV t op (a.eval ρ) (b.eval ρ)

/-- A substitution: pattern variables to terms. -/
abbrev Subst := List (Nat × Term)

/-- Look a variable up. -/
def Subst.find? : Subst → Nat → Option Term
  | [], _ => none
  | (m, e) :: σ, n => if m = n then some e else Subst.find? σ n

/-- Match a pattern against a term, extending `σ`. Each variable occurrence `var t n`
checks that the matched term has type `t`; repeated variables must match equal terms. -/
def Pat.match (Γ : List IntType) : Pat → Term → Subst → Option Subst
  | .var t n, e, σ =>
    if e.typeOf Γ = some t then
      match σ.find? n with
      | some e' => if e' = e then some σ else none
      | none => some ((n, e) :: σ)
    else none
  | .tvar t n, e, σ =>
    if e.typeOf Γ = some t ∧ e.noTrap = true then
      match σ.find? n with
      | some e' => if e' = e then some σ else none
      | none => some ((n, e) :: σ)
    else none
  | .const t n, .const t' n', σ => if t = t' ∧ n = n' then some σ else none
  | .un t op p, .un t' op' a, σ => if t = t' ∧ op = op' then p.match Γ a σ else none
  | .test t p, .test t' a, σ => if t = t' then p.match Γ a σ else none
  | .bin t op p q, .bin t' op' a b, σ =>
    if t = t' ∧ op = op' then (p.match Γ a σ).bind (q.match Γ b) else none
  | .rel t op p q, .rel t' op' a b, σ =>
    if t = t' ∧ op = op' then (p.match Γ a σ).bind (q.match Γ b) else none
  | _, _, _ => none
termination_by structural p _ _ => p

/-- Instantiate a pattern; fails on an unbound variable. -/
def Pat.inst (σ : Subst) : Pat → Option Term
  | .var _ n | .tvar _ n => σ.find? n
  | .const t n => some (.const t n)
  | .un t op a => (a.inst σ).map (.un t op ·)
  | .test t a => (a.inst σ).map (.test t ·)
  | .bin t op a b => (a.inst σ).bind fun a' => (b.inst σ).map (.bin t op a' ·)
  | .rel t op a b => (a.inst σ).bind fun a' => (b.inst σ).map (.rel t op a' ·)

/-- An equation (usable in both directions) or a refinement (`lhs` may trap where `rhs`
does not; usable left to right only). -/
inductive RuleKind where
  | eq | ref
  deriving DecidableEq, Repr

/-- A rewrite rule. -/
structure Rule where
  name : String
  lhs : Pat
  rhs : Pat
  kind : RuleKind := .eq
  deriving Repr

/-- Every variable of `p` is bound in `σ` to a term of its type, every total variable to a
term of its type without division. -/
def bindsOk (Γ : List IntType) (p : Pat) (σ : Subst) : Bool :=
  p.vars.all (fun tn => match σ.find? tn.2 with
    | some e => e.typeOf Γ == some tn.1
    | none => false) &&
  p.tvars.all (fun tn => match σ.find? tn.2 with
    | some e => e.typeOf Γ == some tn.1 && e.noTrap
    | none => false)

/-- **What a rule must satisfy**, over arbitrary operand values: whenever every variable
of either side holds a trap or an integer of its declared type, and every total variable
an integer of its type, the two sides have equal values (`eq`), or the right side has the
left side's value whenever that is not a trap (`ref`). -/
def Rule.Sound (r : Rule) : Prop :=
  ∀ ρ : Nat → Option Val, (∀ tn ∈ r.lhs.vars ++ r.rhs.vars, TypedV tn.1 (ρ tn.2)) →
    (∀ tn ∈ r.lhs.tvars ++ r.rhs.tvars, TotalV tn.1 (ρ tn.2)) →
    match r.kind with
    | .eq => r.lhs.eval ρ = r.rhs.eval ρ
    | .ref => ∀ v, r.lhs.eval ρ = some v → r.rhs.eval ρ = some v

/-! ## Constant folding -/

/-- Fold an operator whose operands are constants (the result of a non-trapping
operator, as a constant). -/
def Term.fold? : Term → Option Term
  | .un t op (.const t' n) =>
    if t = t' then some (.const t (intUnOp t op (BitVec.ofNat _ n)).toNat) else none
  | .test t (.const t' n) =>
    if t = t' then some (.const .i32 (intTestOp t .eqz (BitVec.ofNat _ n)).toNat) else none
  | .bin t op (.const t₁ n₁) (.const t₂ n₂) =>
    if t = t₁ ∧ t = t₂ then
      match intBinOp t op (BitVec.ofNat _ n₁) (BitVec.ofNat _ n₂) with
      | .ok z => some (.const t z.toNat)
      | .error _ => none
    else none
  | .rel t op (.const t₁ n₁) (.const t₂ n₂) =>
    if t = t₁ ∧ t = t₂ then
      some (.const .i32 (intRelOp t op (BitVec.ofNat _ n₁) (BitVec.ofNat _ n₂)).toNat)
    else none
  | _ => none

/-! ## Computed rewrites -/

/-- The exponent `k < w` with `2 ^ k = n`, if any (searched in order, so the kernel can
evaluate it). -/
def pow2Exp? (w n : Nat) : Option Nat := (List.range w).find? fun k => 2 ^ k == n

/-- Rewrites by a computed constant, valid for every operand: multiplication, unsigned
division and unsigned remainder by a power of two as a shift or mask, and shift or rotation
counts reduced modulo the width. -/
def Term.comp? : Term → Option Term
  | .bin t op a (.const t' n) =>
    if t = t' then
      match op with
      | .mul => (pow2Exp? t.width n).map fun k => .bin t .shl a (.const t k)
      | .div .unsigned => (pow2Exp? t.width n).map fun k => .bin t (.shr .unsigned) a (.const t k)
      | .rem .unsigned => (pow2Exp? t.width n).map fun _ => .bin t .and a (.const t (n - 1))
      | .shl | .shr _ | .rotl | .rotr =>
        if t.width ≤ n then some (.bin t op a (.const t (n % t.width))) else none
      | _ => none
    else none
  | _ => none

/-! ## Certificates -/

/-- One step: a library rule at a path, left to right (`fwd`) or right to left, with
bindings `σ₀` for the variables that only the replacing side has; constant folding at a
path, or its converse, replacing a constant by a term `b` that folds to it; a computed
rewrite (`Term.comp?`) at a path, or its converse. -/
inductive Step where
  | rw (rule : Nat) (fwd : Bool) (path : List Nat) (σ₀ : List (Nat × Term))
  | fold (path : List Nat)
  | unfold (path : List Nat) (b : Term)
  | comp (path : List Nat)
  | uncomp (path : List Nat) (b : Term)
  deriving DecidableEq, Repr

/-- Rewrite the subterm at `path` from the matched side `src` to `dst`, matching from the
initial bindings `σ₀`. -/
def rewriteAt (Γ : List IntType) (e : Term) (path : List Nat) (src dst : Pat)
    (σ₀ : Subst) : Option Term :=
  (e.get? path).bind fun a => (src.match Γ a σ₀).bind fun σ =>
    if bindsOk Γ dst σ then (dst.inst σ).bind fun b => e.set? path b else none

/-- Apply a step; the flag says whether the step is an equation (`true`) or only a
refinement (`false`). -/
def applyStep (Γ : List IntType) (rules : List Rule) (e : Term) : Step → Option (Term × Bool)
  | .rw i fwd path σ₀ =>
    match rules[i]? with
    | none => none
    | some r =>
      match r.kind, fwd with
      | .eq, true => (rewriteAt Γ e path r.lhs r.rhs σ₀).map (·, true)
      | .eq, false => (rewriteAt Γ e path r.rhs r.lhs σ₀).map (·, true)
      | .ref, true => (rewriteAt Γ e path r.lhs r.rhs σ₀).map (·, false)
      | .ref, false => none
  | .fold path =>
    (e.get? path).bind fun a => a.fold?.bind fun b => (e.set? path b).map (·, true)
  | .unfold path b =>
    (e.get? path).bind fun a =>
      if b.fold? = some a then (e.set? path b).map (·, true) else none
  | .comp path =>
    (e.get? path).bind fun a => a.comp?.bind fun b => (e.set? path b).map (·, true)
  | .uncomp path b =>
    (e.get? path).bind fun a =>
      if b.comp? = some a then (e.set? path b).map (·, true) else none

/-- Replay a chain of steps; the flag is `true` when every step is an equation. -/
def runSteps (Γ : List IntType) (rules : List Rule) : Term → List Step → Option (Term × Bool)
  | e, [] => some (e, true)
  | e, s :: ss =>
    match applyStep Γ rules e s with
    | none => none
    | some (e', b) =>
      match runSteps Γ rules e' ss with
      | none => none
      | some (e'', b') => some (e'', b && b')

/-- **The equivalence checker**: the steps take `e₁` to `e₂` by equations only. -/
def checkEq (Γ : List IntType) (rules : List Rule) (e₁ e₂ : Term) (steps : List Step) : Bool :=
  match runSteps Γ rules e₁ steps with
  | some (e, true) => e == e₂
  | _ => false

/-- **The refinement checker**: the steps take `e₁` to `e₂` (refinement steps allowed,
left to right only). -/
def checkRef (Γ : List IntType) (rules : List Rule) (e₁ e₂ : Term) (steps : List Step) :
    Bool :=
  match runSteps Γ rules e₁ steps with
  | some (e, _) => e == e₂
  | none => false

/-- A certificate for two sequences of terms: one chain per position. -/
def checkEqL (Γ : List IntType) (rules : List Rule) :
    List Term → List Term → List (List Step) → Bool
  | [], [], [] => true
  | e₁ :: es₁, e₂ :: es₂, c :: cs => checkEq Γ rules e₁ e₂ c && checkEqL Γ rules es₁ es₂ cs
  | _, _, _ => false

/-- `checkEqL` for refinement. -/
def checkRefL (Γ : List IntType) (rules : List Rule) :
    List Term → List Term → List (List Step) → Bool
  | [], [], [] => true
  | e₁ :: es₁, e₂ :: es₂, c :: cs => checkRef Γ rules e₁ e₂ c && checkRefL Γ rules es₁ es₂ cs
  | _, _, _ => false

/-! ## Segment equivalence and refinement -/

/-- Two instruction sequences are **equivalent on frames typed by `Γ`**: from every
store, frame and operand stack, the straight-line interpreter gives the same result. -/
def SegEquiv (Γ : List IntType) (is₁ is₂ : List Instr) : Prop :=
  ∀ {H : Type} (s : Store H) (f : Frame) (rs : List Val), FrameOk Γ f →
    exec s f rs is₁ = exec s f rs is₂

/-- `is₂` **refines** `is₁`: whenever `is₁` runs, `is₂` runs to the same result. -/
def SegRefines (Γ : List IntType) (is₁ is₂ : List Instr) : Prop :=
  ∀ {H : Type} (s : Store H) (f : Frame) (rs : List Val) r, FrameOk Γ f →
    exec s f rs is₁ = some r → exec s f rs is₂ = some r

/-! ## Notions of the soundness statements -/

/-- `o'` has `o`'s value whenever `o` has one. -/
def Ref {α : Type} (o o' : Option α) : Prop := ∀ v, o = some v → o' = some v

/-- The valuation a substitution induces in a frame. -/
def Subst.val (σ : Subst) (f : Frame) (n : Nat) : Option Val := (σ.find? n).bind (·.eval f)

/-- `σ'` extends `σ`. -/
def Subst.Ext (σ σ' : Subst) : Prop := ∀ n e, σ.find? n = some e → σ'.find? n = some e

/-- Every variable of a matched pattern is bound to a term of the variable's type. -/
def Subst.Typed (Γ : List IntType) (σ : Subst) (vs : List (IntType × Nat)) : Prop :=
  ∀ tn ∈ vs, ∃ e, σ.find? tn.2 = some e ∧ e.typeOf Γ = some tn.1

/-- Every total variable of a matched pattern is bound to a term of the variable's type
that cannot trap. -/
def Subst.Total (Γ : List IntType) (σ : Subst) (vs : List (IntType × Nat)) : Prop :=
  ∀ tn ∈ vs, ∃ e, σ.find? tn.2 = some e ∧ e.typeOf Γ = some tn.1 ∧ e.noTrap = true

/-- The hypotheses of a rule at a valuation: typed variables, total total variables. -/
def RuleHyps (src dst : Pat) (ρ : Nat → Option Val) : Prop :=
  (∀ tn ∈ src.vars ++ dst.vars, TypedV tn.1 (ρ tn.2)) ∧
    (∀ tn ∈ src.tvars ++ dst.tvars, TotalV tn.1 (ρ tn.2))

/-- What a step guarantees. -/
def StepOk (f : Frame) (e e' : Term) (b : Bool) : Prop :=
  Ref (e.eval f) (e'.eval f) ∧ (b = true → e.eval f = e'.eval f)

/-- The result of one instruction after pushing values. -/
abbrev pushed {H : Type} (s : Store H) (f : Frame) (rs : List Val) (o : Option Val) :
    Option (Store H × Frame × List Val) :=
  o.map fun v => (s, f, v :: rs)

end Silmaril.Wasm.Auto.EGraph
