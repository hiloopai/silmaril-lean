module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Typing.Expected.Defs

/-! # Schedule the effects in a written request operand -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed

open LambdaSSA (FiniteCFG Flat Region Tm)
open Morphism.CaseSSA (erase)
open NamedFlat (BindingTypes)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
  (PacketType PrimitiveSignature Slot slotAt)

variable {F : Type} {blocks exits captures labels : Nat} {Γ Δ Θ : List PacketType}
  {sig : PrimitiveSignature F} {ty : PacketType}

/-- Silent LambdaSSA values left after scheduling. Injection nodes retain
both summand types even though erasure writes only the selected tag. -/
inductive Residual (Γ : List PacketType) : PacketType → Type
  | var {a : PacketType} : Slot Γ a → Residual Γ a
  | unit : Residual Γ .unit
  | pair {a b : PacketType} : Residual Γ a → Residual Γ b → Residual Γ (.product a b)
  | inl {a b : PacketType} : Residual Γ a → Residual Γ (.coprod a b)
  | inr {a b : PacketType} : Residual Γ b → Residual Γ (.coprod a b)

def Residual.erase (layout : Positions Γ) : {a : PacketType} → Residual Γ a → Tm F
  | _, .var slot => .var (layout slot)
  | _, .unit => .unit
  | _, .pair left right => .pair (left.erase layout) (right.erase layout)
  | _, .inl value => .inl (value.erase layout)
  | _, .inr value => .inr (value.erase layout)

universe u

def Residual.eval {α : Type u} (values : Values Γ α) : {a : PacketType} → Residual Γ a → Value α
  | _, .var slot => values slot
  | _, .unit => .unit
  | _, .pair left right => .pair (left.eval values) (right.eval values)
  | _, .inl value => .inl (value.eval values)
  | _, .inr value => .inr (value.eval values)

/-- The checked operand grammar uses the primitive signature and expected
sum types to type the scheduled payloads. -/
inductive Operand (sig : PrimitiveSignature F) : List PacketType → PacketType → Type
  | pure {Γ : List PacketType} {a : PacketType} (value : Residual Γ a) : Operand sig Γ a
  | pair {Γ : List PacketType} {a b : PacketType} (left : Operand sig Γ a) (right : Operand sig Γ b) :
      Operand sig Γ (.product a b)
  | inl {Γ : List PacketType} {a b : PacketType} (value : Operand sig Γ a) : Operand sig Γ (.coprod a b)
  | inr {Γ : List PacketType} {a b : PacketType} (value : Operand sig Γ b) : Operand sig Γ (.coprod a b)
  | call {Γ : List PacketType} (op : F) (arg : Operand sig Γ (sig.argument op)) : Operand sig Γ (sig.reply op)
  | let₁ {Γ : List PacketType} {a b : PacketType} (value : Operand sig Γ a) (body : Operand sig (a :: Γ) b) :
      Operand sig Γ b
  | let₂ {Γ : List PacketType} {a b c : PacketType} (value : Operand sig Γ (.product a b))
      (body : Operand sig (b :: a :: Γ) c) : Operand sig Γ c
  | case {Γ : List PacketType} {a b c : PacketType} (test : Operand sig Γ (.coprod a b))
      (left : Operand sig (a :: Γ) c) (right : Operand sig (b :: Γ) c) : Operand sig Γ c

def Operand.written : {Γ : List PacketType} → {ty : PacketType} → Operand sig Γ ty → Tm F
  | _, _, .pure value => value.erase position
  | _, _, .pair left right => .pair left.written right.written
  | _, _, .inl value => .inl value.written
  | _, _, .inr value => .inr value.written
  | _, _, .call op arg => .op op arg.written
  | _, _, .let₁ value body => .let₁ value.written body.written
  | _, _, .let₂ value body => .let₂ value.written body.written
  | _, _, .case test left right => .case test.written left.written right.written

abbrev SlotMap (Γ Δ : List PacketType) := ∀ {a}, Slot Γ a → Slot Δ a

abbrev Substitution (Γ Δ : List PacketType) := ∀ {a}, Slot Γ a → Residual Δ a

def substExpr (values : Substitution Γ Δ) : {ty : PacketType} → Residual Γ ty → Residual Δ ty
  | _, .var slot => values slot
  | _, .unit => .unit
  | _, .pair left right => .pair (substExpr values left) (substExpr values right)
  | _, .inl value => .inl (substExpr values value)
  | _, .inr value => .inr (substExpr values value)

def renameExpr (slots : SlotMap Γ Δ) (value : Residual Γ ty) : Residual Δ ty :=
  substExpr (fun slot => .var (slots slot)) value

/-- Only the body gets the initializer's residual value at slot zero. -/
def bindSubstitution (value : Residual Δ ty) (older : Substitution Γ Δ) : Substitution (ty :: Γ) Δ :=
  fun {_} slot => match slot with
  | .here => value
  | .there slot => older slot

/-- A case payload is local to its arm and leaves the older slots in order. -/
def liftSubstitution (values : Substitution Γ Δ) : Substitution (ty :: Γ) (ty :: Δ) :=
  bindSubstitution (.var .here) (fun slot => renameExpr (fun old => .there old) (values slot))

/-- Each application adds its reply to the scope. A silent product
destructuring adds the right field at slot zero and the left at slot one.
A case adds only its result to the shared continuation. -/
inductive Requests (sig : PrimitiveSignature F) : List PacketType → List PacketType → Type
  | done {Γ : List PacketType} : Requests sig Γ Γ
  | request {Γ Δ : List PacketType} (op : F) (arg : Residual Γ (sig.argument op))
      (next : Requests sig (sig.reply op :: Γ) Δ) : Requests sig Γ Δ
  | unpack {Γ Δ : List PacketType} {a b : PacketType} (value : Residual Γ (.product a b))
      (next : Requests sig (b :: a :: Γ) Δ) : Requests sig Γ Δ
  | choose {Γ Δ leftScope rightScope : List PacketType} {a b c : PacketType}
      (test : Residual Γ (.coprod a b))
      (left : Requests sig (a :: Γ) leftScope) (leftValue : Residual leftScope c)
      (right : Requests sig (b :: Γ) rightScope) (rightValue : Residual rightScope c)
      (next : Requests sig (c :: Γ) Δ) : Requests sig Γ Δ

def Requests.append : {Γ Δ : List PacketType} → Requests sig Γ Δ → Requests sig Δ Θ → Requests sig Γ Θ
  | _, _, .done, next => next
  | _, _, .request op arg rest, next => .request op arg (rest.append next)
  | _, _, .unpack value rest, next => .unpack value (rest.append next)
  | _, _, .choose test left l right r rest, next => .choose test left l right r (rest.append next)

/-- Embed an older typed slot through the reply and product binders. -/
def Requests.slots : {Γ Δ : List PacketType} → Requests sig Γ Δ → SlotMap Γ Δ
  | _, _, .done, _, slot => slot
  | _, _, .request _ _ next, _, slot => next.slots (.there slot)
  | _, _, .unpack _ next, _, slot => next.slots (.there (.there slot))
  | _, _, .choose _ _ _ _ _ next, _, slot => next.slots (.there slot)

/-- Carry substituted values through all slots added by a schedule. -/
def Requests.weaken (requests : Requests sig Δ Θ) (values : Substitution Γ Δ) : Substitution Γ Θ :=
  fun {_} slot => renameExpr requests.slots (values slot)

/-- The same embedding for raw lexical indices, including the caller's
ambient environment beyond the checked slots. -/
def Requests.shift : {Γ Δ : List PacketType} → Requests sig Γ Δ → Nat → Nat
  | _, _, .done, i => i
  | _, _, .request _ _ next, i => next.shift (i + 1)
  | _, _, .unpack _ next, i => next.shift (i + 2)
  | _, _, .choose _ _ _ _ _ next, i => next.shift (i + 1)

/-- Insert lets for the schedule. A case joins through one let result instead
of copying the surrounding continuation into both arms. -/
def Requests.wrap : {A : Type} → (bind destruct : Tm F → A → A) →
    {Γ Δ : List PacketType} → Requests sig Γ Δ → A → A
  | _, _, _, _, _, .done, body => body
  | _, bind, destruct, _, _, .request op arg next, body =>
    bind (.op op (arg.erase position)) (next.wrap bind destruct body)
  | _, bind, destruct, _, _, .unpack value next, body =>
    destruct (value.erase position) (next.wrap bind destruct body)
  | _, bind, destruct, _, _, .choose test left l right r next, body =>
    bind (.case (test.erase position) (left.wrap Tm.let₁ Tm.let₂ (l.erase position))
      (right.wrap Tm.let₁ Tm.let₂ (r.erase position))) (next.wrap bind destruct body)

/-- Record only the case-result types. Branch-local binders are addressed
inside the initializer, and the shared continuation is the second child. -/
def Requests.bindings : {Γ Δ : List PacketType} → Requests sig Γ Δ →
    BindingTypes PacketType → BindingTypes PacketType
  | _, _, .done, tail => tail
  | _, _, .request _ _ next, tail | _, _, .unpack _ next, tail =>
    .node none .empty (next.bindings tail) .empty
  | _, _, .choose (c := c) _ left _ right _ next, tail =>
    let arms := BindingTypes.node none .empty (left.bindings .empty) (right.bindings .empty)
    .node (some c) arms (next.bindings tail) .empty

structure Scheduled (sig : PrimitiveSignature F) (Γ : List PacketType) (ty : PacketType) where
  scope : List PacketType
  requests : Requests sig Γ scope
  value : Residual scope ty

/-- Compose effects in written order. Each let schedules its initializer
once, then substitutes the residual value or binds its two fields. -/
def Operand.scheduleWith : {Γ : List PacketType} → {ty : PacketType} → Operand sig Γ ty →
    {Δ : List PacketType} → Substitution Γ Δ → Scheduled sig Δ ty
  | _, _, .pure value, Δ, values => ⟨Δ, .done, substExpr values value⟩
  | _, _, .pair left right, _, values =>
    let l := left.scheduleWith values
    let r := right.scheduleWith (l.requests.weaken values)
    ⟨r.scope, l.requests.append r.requests, .pair (renameExpr r.requests.slots l.value) r.value⟩
  | _, _, .inl value, _, values =>
    let payload := value.scheduleWith values
    ⟨payload.scope, payload.requests, .inl payload.value⟩
  | _, _, .inr value, _, values =>
    let payload := value.scheduleWith values
    ⟨payload.scope, payload.requests, .inr payload.value⟩
  | _, _, .call op arg, _, values =>
    let result := arg.scheduleWith values
    ⟨sig.reply op :: result.scope, result.requests.append (.request op result.value .done), .var .here⟩
  | _, _, .let₁ value body, _, values =>
    let init := value.scheduleWith values
    let body := body.scheduleWith (bindSubstitution init.value (init.requests.weaken values))
    ⟨body.scope, init.requests.append body.requests, body.value⟩
  | _, _, .let₂ (a := a) (b := b) value body, _, values =>
    let init := value.scheduleWith values
    let unpack : Requests sig init.scope (b :: a :: init.scope) := .unpack init.value .done
    let initialized := init.requests.append unpack
    let body := body.scheduleWith
      (bindSubstitution (.var .here) (bindSubstitution (.var (.there .here)) (initialized.weaken values)))
    ⟨body.scope, initialized.append body.requests, body.value⟩
  | Γ, c, .case test left right, _, values =>
    let tested := test.scheduleWith values
    let older : Substitution Γ tested.scope := tested.requests.weaken values
    let l := left.scheduleWith (liftSubstitution older)
    let r := right.scheduleWith (liftSubstitution older)
    ⟨c :: tested.scope, tested.requests.append (.choose tested.value l.requests l.value r.requests r.value .done),
      .var .here⟩

def Operand.scheduleAt (arg : Operand sig Γ ty) (slots : SlotMap Γ Δ) : Scheduled sig Δ ty :=
  arg.scheduleWith (fun slot => .var (slots slot))

def Operand.schedule (arg : Operand sig Γ ty) : Scheduled sig Γ ty :=
  arg.scheduleAt (fun slot => slot)

def Scheduled.term (scheduled : Scheduled sig Γ ty) : Tm F :=
  scheduled.requests.wrap Tm.let₁ Tm.let₂ (scheduled.value.erase position)

def Scheduled.wrapRegion (scheduled : Scheduled sig Γ ty) (body : Region F)
    (bindings : BindingTypes PacketType) : Region F × BindingTypes PacketType :=
  (scheduled.requests.wrap Region.let₁ Region.let₂ body, scheduled.requests.bindings bindings)

/-- Synthesize slots and replies. Propagate a known product or sum type
to its fields and a known result type to a let body. -/
def readOperandAt (sig : PrimitiveSignature F) :
    (Γ : List PacketType) → Option PacketType → Tm F → Option (Σ ty : PacketType, Operand sig Γ ty)
  | Γ, _, .var i => (slotAt Γ i).map fun ⟨ty, slot⟩ => ⟨ty, .pure (.var slot)⟩
  | _, _, .unit => some ⟨.unit, .pure .unit⟩
  | Γ, _, .op op arg => do
    let ⟨ty, arg⟩ ← readOperandAt sig Γ (some (sig.argument op)) arg
    if typed : ty = sig.argument op then
      some ⟨sig.reply op, .call op (typed ▸ arg)⟩
    else none
  | Γ, expected, .pair left right => do
    let (leftType, rightType) := match expected with
      | some (.product a b) => (some a, some b)
      | _ => (none, none)
    let ⟨a, left⟩ ← readOperandAt sig Γ leftType left
    let ⟨b, right⟩ ← readOperandAt sig Γ rightType right
    return ⟨.product a b, .pair left right⟩
  | Γ, expected, .let₁ value body => do
    let ⟨a, value⟩ ← readOperandAt sig Γ none value
    let ⟨b, body⟩ ← readOperandAt sig (a :: Γ) expected body
    return ⟨b, .let₁ value body⟩
  | Γ, expected, .let₂ value body => do
    let ⟨.product a b, value⟩ ← readOperandAt sig Γ none value | none
    let ⟨c, body⟩ ← readOperandAt sig (b :: a :: Γ) expected body
    return ⟨c, .let₂ value body⟩
  | Γ, some (.coprod a b), .inl value => do
    let ⟨ty, value⟩ ← readOperandAt sig Γ (some a) value
    if typed : ty = a then some ⟨.coprod a b, .inl (typed ▸ value)⟩ else none
  | Γ, some (.coprod a b), .inr value => do
    let ⟨ty, value⟩ ← readOperandAt sig Γ (some b) value
    if typed : ty = b then some ⟨.coprod a b, .inr (typed ▸ value)⟩ else none
  | Γ, expected, .case test left right => do
    let ⟨.coprod a b, test⟩ ← readOperandAt sig Γ none test | none
    let ⟨c, left⟩ ← readOperandAt sig (a :: Γ) expected left
    let ⟨d, right⟩ ← readOperandAt sig (b :: Γ) expected right
    if same : d = c ∧ expected.getD c = c then
      some ⟨c, .case test left (same.1 ▸ right)⟩
    else none
  | _, _, _ => none

def readOperand (sig : PrimitiveSignature F) (Γ : List PacketType) (written : Tm F) :
    Option (Σ ty : PacketType, Operand sig Γ ty) :=
  readOperandAt sig Γ none written

/-- Execute the schedule before the outer request. Shift older slots under
its reply, retaining the binder types at their original syntax positions. -/
def hoistWithBindings (outer : F) (arg : Operand sig Γ (sig.argument outer))
    (tail : Region F × BindingTypes PacketType) : Region F × BindingTypes PacketType :=
  let scheduled := arg.schedule
  scheduled.wrapRegion (.let₁ (.op outer (scheduled.value.erase position))
      (tail.1.renameVars (Silmaril.DeBruijn.lift scheduled.requests.shift)))
    (.node none .empty tail.2 .empty)

def hoist (outer : F) (arg : Operand sig Γ (sig.argument outer)) (tail : Region F) : Region F :=
  (hoistWithBindings outer arg (tail, .empty)).1

/-- Execute the operand schedule and send its residual to the same label. -/
def scheduleJumpWithBindings (label : Nat) (arg : Operand sig Γ ty) : Region F × BindingTypes PacketType :=
  let scheduled := arg.schedule
  scheduled.wrapRegion (.br label (scheduled.value.erase position)) .empty

def scheduleJump (label : Nat) (arg : Operand sig Γ ty) : Region F :=
  (scheduleJumpWithBindings label arg).1

/-- An exact written entry boundary and its operand type. Jumps use the
same positional block and exit profile as the shared CFG checker. -/
inductive Boundary (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (types : Fin labels → PacketType)
  | request (outer : F) (arg : Operand sig context.toList (sig.argument outer))
      (tail : Flat F labels (captures + 1))
  | jump (label : Fin labels) (arg : Operand sig context.toList (types label))

def Boundary.written {labels : Nat} {context : BoundCtx PacketType captures}
    {types : Fin labels → PacketType} : Boundary sig context types → Region F
  | .request outer arg tail => .let₁ (.op outer arg.written) tail.erase
  | .jump label arg => .br label.val arg.written

/-- A jump consumes the structural residual directly at its original
target. A request still shifts the older slots beneath its own reply. -/
def Boundary.lower {labels : Nat} {context : BoundCtx PacketType captures}
    {types : Fin labels → PacketType} : Boundary sig context types → Region F
  | .request outer arg tail => hoist outer arg tail.erase
  | .jump label arg => scheduleJump label.val arg

/-- Check both the operand's synthesized type and its exact written syntax. -/
def readArgument [DecidableEq F] (sig : PrimitiveSignature F) (Γ : List PacketType)
    (expected : PacketType) (original : Tm F) :
    Option {arg : Operand sig Γ expected // original = arg.written} := do
  let ⟨ty, arg⟩ ← readOperandAt sig Γ (some expected) original
  if typed : ty = expected then
    let arg := typed ▸ arg
    if exactArg : original = arg.written then some ⟨arg, exactArg⟩ else none
  else none

def Boundary.read [DecidableEq F] (sig : PrimitiveSignature F)
    (context : BoundCtx PacketType captures) (types : Fin labels → PacketType) :
    (original : Flat F labels captures) → Option {b : Boundary sig context types // original.erase = b.written}
  | .let₁ (.op outer original) tail => do
    let ⟨arg, exactArg⟩ ← readArgument sig context.toList (sig.argument outer) (erase original)
    return ⟨.request outer arg tail, by
      change Region.let₁ (.op outer (erase original)) tail.erase = _
      rw [exactArg]
      rfl⟩
  | .br label original => do
    let ⟨arg, exactArg⟩ ← readArgument sig context.toList (types label) (erase original)
    return ⟨.jump label arg, by
      change Region.br label.val (erase original) = _
      rw [exactArg]
      rfl⟩
  | _ => none

structure Lifted (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) where
  boundary : Boundary sig context (SSA.FiniteSum.append packets outputs)
  source_eq : source.entry.erase = boundary.written
  entry : Flat F (blocks + exits) captures
  entry_eq : entry.erase = boundary.lower

def Lifted.code {context : BoundCtx PacketType captures} {packets : Fin blocks → PacketType}
    {outputs : Fin exits → PacketType} {source : FiniteCFG F blocks exits captures}
    (lifted : Lifted sig context packets outputs source) : FiniteCFG F blocks exits captures :=
  ⟨lifted.entry, source.block⟩

/-- Check an operand at a written request or jump, including outward
jumps. Require its exact erased syntax and the boundary's expected type
before reifying the scheduled entry. -/
def lift [DecidableEq F] (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) : Option (Lifted sig context packets outputs source) := do
  let ⟨boundary, sourceEq⟩ ← Boundary.read sig context (SSA.FiniteSum.append packets outputs) source.entry
  let entry ← scopedRow (blocks + exits) captures boundary.lower
  return ⟨boundary, sourceEq, entry.val, entry.property⟩

structure Compiled (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) where
  lifted : Lifted sig context packets outputs source
  sourceTyped : letI := sig.typing; source.HasType context packets outputs
  checked : Multiple.Compiled sig context packets outputs lifted.code

/-- Check the original CFG and lower its operand schedule through the
existing recursive continuation compiler. The old block table is shared.
The continuation compiler requires a nonempty frame at each scheduled
request or unpack. -/
def compile [DecidableEq F] (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) : Option (Compiled sig context packets outputs source) :=
  letI := sig.typing;
  if original : NamedFlat.check source context packets outputs = true then
    match lift sig context packets outputs source with
    | none => none
    | some lifted =>
      (Multiple.compile sig context packets outputs lifted.code).map fun checked =>
        ⟨lifted, NamedFlat.check_sound _ _ _ _ original, checked⟩
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed
