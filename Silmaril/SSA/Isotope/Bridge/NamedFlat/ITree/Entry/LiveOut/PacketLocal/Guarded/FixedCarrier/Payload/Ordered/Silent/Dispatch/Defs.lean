module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Silent.Identity.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Thms

/-! # Exact named Bit dispatch and payload-aware typed normalization -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.PacketDispatch

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree diverge)
open LambdaSSA (Flat FiniteCFG)
open LambdaSSA.Semantics.Interaction (Transfer)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration hiding Row Table
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (Head ConfigurationEnumeration)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent (GuardedTable)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open Recognize (Bit numberedInterface requestTypes)
open Identity (layout Phase)

attribute [local instance] requestTypes

universe v

abbrev NativeTable (Φ : Type) (R : List Syntax.Ty) :=
  LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.Table
    (Recognize.signature Φ) R

abbrev NativeRow (Φ : Type) (R Γ : List Syntax.Ty) :=
  LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.Row
    (Recognize.signature Φ) R Γ

structure Arm (R : List Syntax.Ty) where
  target : Fin R.length
  typed : R.get target = Bit
  useLiteral : Bool

def Arm.code {Φ : Type} {R : List Syntax.Ty} (a : Arm R) : Flat Φ (R.length + 2) 6 :=
  .br (a.target.castAdd 2) (.pair (.bv (if a.useLiteral then 1 else 3)) .unit)

def Arm.operand {R Γ : List Syntax.Ty} (a : Arm R) (literal incoming : Bool) :
    Syntax.Expr Γ (R.get a.target) :=
  cast (congrArg (Syntax.Expr Γ) a.typed.symm) (bitExpr (if a.useLiteral then literal else incoming))

inductive Row (Φ : Type) (R : List Syntax.Ty) (A : Syntax.Ty) where
  | base (row : Identity.Row Φ R A)
  | bitCase (typed : A = Bit) (opcode : Φ) (literal : Bool) (left right : Arm R)

def Row.Agrees {Φ : Type} {R : List Syntax.Ty} {A : Syntax.Ty}
    (lit : Φ → Option Bool) : Row Φ R A → Prop
  | .base row => row.Agrees lit
  | .bitCase _ opcode literal .. => lit opcode = some literal

def Row.code {Φ : Type} {R : List Syntax.Ty} {A : Syntax.Ty} : Row Φ R A → Flat Φ (R.length + 2) 2
  | .base row => row.code
  | .bitCase _ opcode _ l r => .let₂ (.bv 0) (.let₁ (.op opcode .unit) (.case (.bv 2) l.code r.code))

def Row.control {Φ : Type} {R : List Syntax.Ty} {A : Syntax.Ty} : Row Φ R A → NativeRow Φ R [A, Bit]
  | .base (.jump j typed) => .jump j (cast (congrArg (Syntax.Expr [A, Bit]) typed.symm) (.var 0))
  | .base row => .guarded row.guarded
  | .bitCase typed _ literal l r => .dispatch (cast (congrArg (Syntax.Expr [A, Bit]) typed) (.var 0))
      l.target r.target (l.operand literal false) (r.operand literal true)

def readArm {Φ : Type} {R : List Syntax.Ty} (row : Flat Φ (R.length + 2) 6) : Option (Arm R) := do
  let (label, useLiteral) ← match row with
    | .br label (.pair (.bv 1) .unit) => some (label, true)
    | .br label (.pair (.bv 3) .unit) => some (label, false)
    | _ => none
  let target ← Identity.internal? label
  if typed : R.get target = Bit then some ⟨target, typed, useLiteral⟩ else none

def readRow {Φ : Type} {R : List Syntax.Ty} (lit : Φ → Option Bool)
    (i : Fin R.length) (code : Flat Φ (R.length + 2) 2) :
    Option {r : Row Φ R (R.get i) // r.Agrees lit} :=
  match code with
  | .let₂ (.bv _) (.let₁ (.op opcode .unit) (.case (.bv _) left right)) =>
    match agrees : lit opcode with
    | none => none
    | some literal => do
      let l ← readArm left
      let r ← readArm right
      if typed : R.get i = Bit then some ⟨.bitCase typed opcode literal l r, agrees⟩ else none
  | _ => (Identity.readRow lit i code).map fun row => ⟨.base row.val, row.property⟩

abbrev Profile (Φ : Type) (slots : List Bool) :=
  (i : Fin (layout slots).length) → Row Φ (layout slots) ((layout slots).get i)

def Profile.Agrees {Φ : Type} {slots : List Bool} (p : Profile Φ slots) (lit : Φ → Option Bool) : Prop :=
  ∀ i, (p i).Agrees lit

def Profile.expected {Φ : Type} {slots : List Bool} (p : Profile Φ slots) :
    FiniteCFG Φ (layout slots).length 2 1 :=
  ⟨.br 0 (.pair (.bv 0) .unit), fun i => (p i).code⟩

def readProfile {Φ : Type} {slots : List Bool} (lit : Φ → Option Bool)
    (code : FiniteCFG Φ (layout slots).length 2 1) :
    Option {p : Profile Φ slots // p.Agrees lit} :=
  let read i := readRow lit i (code.block i)
  if ok : ∀ i, (read i).isSome = true then
    some ⟨fun i => ((read i).get (ok i)).val, fun i => ((read i).get (ok i)).property⟩
  else none

def Profile.control {Φ : Type} {slots : List Bool} (p : Profile Φ slots) (selected : Tag → Bool) :
    NativeTable Φ (layout slots) :=
  ⟨0, fun i => (p i).control, selected⟩

/-- The exact output is evaluated at the configuration that exposes the
return, including a packet changed by silent dispatch. -/
def Profile.returnPacket {Φ : Type} {slots : List Bool} (p : Profile Φ slots)
    (caller : Syntax.Payload Bit) (q : Packet (layout slots)) (tag : Tag) : Packet Outputs :=
  match p q.1 with
  | .base row => Identity.returnPacket row caller q.2 tag
  | .bitCase .. => outputPacket tag false false

def headBody {Φ : Type} {R : List Syntax.Ty}
    (returns : Tag → Packet Outputs) (head : Head (Recognize.signature Φ) R) :
    Tree (Request Φ) (Transfer Runtime ⊕ Phase R) :=
  match head with
  | .exit tag _ => pure (.inr ⟨.inl (returns tag)⟩)
  | .diverge => diverge
  | .request f arg next => query f arg >>= fun reply =>
      pure (.inr ⟨.inr (next reply.down.1 reply.down.2)⟩)

def Profile.rawStep {Φ : Type} {slots : List Bool} (p : Profile Φ slots) (caller : Syntax.Payload Bit)
    (phase : Phase (layout slots)) : Tree (Request Φ) (Transfer Runtime ⊕ Phase (layout slots)) :=
  match phase.down with
  | .inl result => pure (.inl (packedReturn result))
  | .inr q => match (p.control (fun _ => false)).step caller q with
    | .inl next => pure (.inr ⟨.inr next⟩)
    | .inr exposed => headBody (p.returnPacket caller q) exposed

/-- Retain the productive configuration as well as the head. The next
scan state is exactly #4874's typed packet transition. -/
def Profile.scan {Φ : Type} {slots : List Bool} (p : Profile Φ slots) (caller : Syntax.Payload Bit) :
    Nat → Packet (layout slots) → Option (Packet (layout slots) × Head (Recognize.signature Φ) (layout slots))
  | 0, _ => none
  | fuel + 1, q => match (p.control (fun _ => false)).step caller q with
    | .inl next => p.scan caller fuel next
    | .inr head => some (q, head)

def Profile.normalStep {Φ : Type} {slots : List Bool} (p : Profile Φ slots)
    (configs : ConfigurationEnumeration (layout slots)) (caller : Syntax.Payload Bit)
    (phase : Phase (layout slots)) : Tree (Request Φ) (Transfer Runtime ⊕ Phase (layout slots)) :=
  match phase.down with
  | .inl result => pure (.inl (packedReturn result))
  | .inr q => match p.scan caller configs.configs.length q with
    | none => diverge
    | some (origin, head) => headBody (p.returnPacket caller origin) head

noncomputable def Profile.tree {Φ : Type} {slots : List Bool} (p : Profile Φ slots)
    (configs : ConfigurationEnumeration (layout slots)) (caller : Syntax.Payload Bit)
    (q : Packet (layout slots)) : RunTree Φ :=
  iter (m := Tree (Request Φ)) (p.normalStep configs caller) ⟨.inr q⟩

/-- Observe at a full typed configuration. Selection is applied after
decoding the original ordered result, so a selected exit discards both fields. -/
noncomputable def Profile.observeAt {Φ : Type} {slots : List Bool} {σ : Type v}
    (p : Profile Φ slots) (configs : ConfigurationEnumeration (layout slots))
    (caller : Syntax.Payload Bit) (q : Packet (layout slots)) (prim : Syntax.StatePrimitives Φ σ)
    (s : σ) (selected : Tag → Bool) :=
  decorateOn prim selected (observeOn prim (p.tree configs caller q) s (constructorDecoder PayloadType)) PayloadType

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} {slots : List Bool} {seed first second : V}
  {names : Fin ((layout slots).length + 2) ≃ K}

structure Checked (source : CFG V K P.Instr) (literals : P.Instr → Option Bool) where
  admitted : Admission P (numberedInterface seed names) (fields first second) source
  profile : Profile P.Instr slots
  readback : Recognize.NumberedReadback admitted profile.expected
  literals_agree : profile.Agrees literals

/-- Both the actual packet-local compiler and the exact numbered
reconstruction must accept. -/
def admit? [DecidableEq κ] [DecidableEq P.Instr]
    (source : CFG V K P.Instr) (literals : P.Instr → Option Bool) :
    Option (Checked (P := P) (slots := slots) (seed := seed) (first := first) (second := second)
      (names := names) source literals) :=
  if count : source.blocks.length = (layout slots).length then do
    let a ← PacketLocal.admit (numberedInterface seed names) (fields first second) source
      (fun i => Identity.argumentType (Fin.cast count i))
    (Recognize.checkNumberedReadback a (readProfile literals) (fun p => p.val.expected)).map
      fun ⟨p, readback⟩ => ⟨a, p.val, readback, p.property⟩
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.PacketDispatch
