module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Silent.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Defs

/-! # Packet-local named identity transfers at numbered typed labels -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Identity

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree diverge)
open LambdaSSA.Semantics.Interaction (Transfer)
open LambdaSSA (Flat FiniteCFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration hiding Row Table
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (Typed)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (ConfigurationEnumeration)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint exit_type)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open Recognize (Bit Packets numberedInterface requestTypes requestAt)

attribute [local instance] requestTypes

universe v

def slotType (bit : Bool) : Syntax.Ty := if bit then Bit else .unit

/-- The entry consumes a Bit. Each remaining written slot is Bit or unit. -/
abbrev layout (slots : List Bool) : List Syntax.Ty := Bit :: slots.map slotType

abbrev NativeRow (Φ : Type) (R Γ : List Syntax.Ty) :=
  LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Row (Recognize.signature Φ) R Γ
abbrev SilentTable (Φ : Type) (R : List Syntax.Ty) :=
  LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Table (Recognize.signature Φ) R

structure Routes (R : List Syntax.Ty) where
  dest : Fin 3 → Fin R.length
  typed : ∀ i, R.get (dest i) = Packets.get i
  fallback : Fin R.length
  fallbackType : R.get fallback = .unit

inductive Row (Φ : Type) (R : List Syntax.Ty) (A : Syntax.Ty) where
  | jump (target : Fin R.length) (compatible : R.get target = A)
  | request (opcode : Φ) (typed : A = Bit) (routes : Routes R)
  | ret (tag : Tag) (bit : Bool) (typed : A = slotType bit) (fields : Fields Φ bit)

def Row.Agrees {Φ : Type} {R : List Syntax.Ty} {A : Syntax.Ty}
    (literals : Φ → Option Bool) : Row Φ R A → Prop
  | .jump .. | .request .. => True
  | .ret _ _ _ fields => fields.Agrees literals

def jumpAt {Φ : Type} {d : Nat} (target : Fin d) : Flat Φ (d + 2) 2 :=
  .let₂ (.bv 0) (.br (target.castAdd 2) (.pair (.bv 1) .unit))

def Row.code {Φ : Type} {R : List Syntax.Ty} {A : Syntax.Ty} : Row Φ R A → Flat Φ (R.length + 2) 2
  | .jump j _ => jumpAt j
  | .request op _ routes => requestAt op routes.dest routes.fallback
  | .ret i _ _ fields => fields.rowAt i

def Row.guarded {Φ : Type} {R : List Syntax.Ty} {A : Syntax.Ty} :
    Row Φ R A → NativeRow Φ R [A, Bit]
  | .jump .. => .diverge
  | .request op typed routes => .request op (cast (congrArg (Syntax.Expr [A, Bit]) typed) (.var 0))
      routes.dest routes.typed
  | .ret i .. => .exit i

def Row.output {Φ : Type} {R : List Syntax.Ty} {A : Syntax.Ty} :
    Row Φ R A → Syntax.Expr [A, Bit] PayloadType
  | .ret _ _ typed fields => cast (congrArg (fun t => Syntax.Expr [t, Bit] PayloadType) typed.symm) fields.output
  | _ => recordExpr (bitExpr false) (bitExpr false)

def internal? {d : Nat} (i : Fin (d + 2)) : Option (Fin d) :=
  if h : i.val < d then some ⟨i.val, h⟩ else none

def readRequest {Φ : Type} (R : List Syntax.Ty) (row : Flat Φ (R.length + 2) 2) :
    Option (Φ × Routes R) :=
  match row with
  | .let₂ _ (.case (.op op _) (.br bit _) (.case _ (.br first _)
      (.case _ (.br second _) (.br fallback _)))) => do
    let bit ← internal? bit
    let first ← internal? first
    let second ← internal? second
    let fallback ← internal? fallback
    let route : Fin 3 → Fin R.length := Fin.cases bit (Fin.cases first (fun _ => second))
    if typed : (∀ i, R.get (route i) = Packets.get i) ∧ R.get fallback = .unit then
      some (op, ⟨route, typed.1, fallback, typed.2⟩)
    else none
  | _ => none

def readRow {Φ : Type} {R : List Syntax.Ty} (literals : Φ → Option Bool)
    (i : Fin R.length) (code : Flat Φ (R.length + 2) 2) :
    Option {r : Row Φ R (R.get i) // r.Agrees literals} :=
  match code with
  | .let₂ (.bv _) (.br target (.pair (.bv _) .unit)) => do
    let j ← internal? target
    if eq : R.get j = R.get i then some ⟨.jump j eq, trivial⟩ else none
  | _ =>
    match readRequest R code with
    | some (op, routes) =>
      if eq : R.get i = Bit then some ⟨.request op eq routes, trivial⟩ else none
    | none =>
      let bit := decide (R.get i = Bit)
      if eq : R.get i = slotType bit then
        (readFields literals bit code).map fun (tag, fields) =>
          ⟨.ret tag bit eq fields.val, fields.property⟩
      else none

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

def Profile.silent {Φ : Type} {slots : List Bool} (p : Profile Φ slots) (selected : Tag → Bool) :
    SilentTable Φ (layout slots) where
  entry := 0
  row i :=
    match p i with
    | .jump j compatible => .jump j
        (cast (congrArg (Syntax.Expr [(layout slots).get i, Bit]) compatible.symm) (.var 0))
    | row => .guarded row.guarded
  selected := selected

/-- Use the same finite scan as #4825. A stop retains its label so the
ordered output expression comes from the row that actually returns. -/
def Profile.scan {Φ : Type} {slots : List Bool} (p : Profile Φ slots) (fuel : Nat)
    (i : Fin (layout slots).length) : Option (Result (layout slots).length 1) :=
  search (p.silent (fun _ => false)).labelRows fuel i

def Profile.resolved {Φ : Type} {slots : List Bool} (p : Profile Φ slots) (fuel : Nat)
    (i : Fin (layout slots).length) : Option (Row Φ (layout slots) ((layout slots).get i)) :=
  match p.scan fuel i with
  | some (.ret j _) =>
    if eq : (layout slots).get j = (layout slots).get i then
      some (cast (congrArg (Row Φ (layout slots)) eq) (p j))
    else none
  | _ => none

abbrev Profile.endpoint {Φ : Type} {slots : List Bool} (p : Profile Φ slots) (selected : Tag → Bool) :
    Endpoint (Recognize.signature Φ) (layout slots) PayloadType where
  control := (p.silent selected).normalize
  output i := ((p.resolved (layout slots).length i).map Row.output).getD (recordExpr (bitExpr false) (bitExpr false))

abbrev Phase (R : List Syntax.Ty) := ULift.{1} (Packet Outputs ⊕ Packet R)

def jumpPacket {R : List Syntax.Ty} {i : Fin R.length} (j : Fin R.length)
    (h : R.get j = R.get i) (p : Syntax.Payload (R.get i)) : Packet R :=
  ⟨j, cast (congrArg Syntax.Payload h.symm) p⟩

def returnPacket {Φ : Type} {R : List Syntax.Ty} {A : Syntax.Ty} (row : Row Φ R A)
    (caller : Syntax.Payload Bit) (p : Syntax.Payload A) (i : Tag) : Packet Outputs :=
  ⟨i, cast (congrArg Syntax.Payload (exit_type i).symm)
      (row.output.eval ((Syntax.emptyBindings.push caller).push p))⟩

def activeStep {Φ : Type} {R : List Syntax.Ty} {A : Syntax.Ty} (row : Row Φ R A)
    (caller : Syntax.Payload Bit) (p : Syntax.Payload A) :
    Tree (Request Φ) (Transfer Runtime ⊕ Phase R) :=
  match row with
  | .jump .. => diverge
  | .ret tag .. => pure (.inr ⟨.inl (returnPacket row caller p tag)⟩)
  | .request op typed routes =>
    query op (cast (congrArg Syntax.Payload typed) p) >>= fun r =>
      let q := r.down
      pure (.inr ⟨.inr ⟨routes.dest q.1, cast (congrArg Syntax.Payload (routes.typed q.1).symm) q.2⟩⟩)

def Row.step {Φ : Type} {R : List Syntax.Ty} {i : Fin R.length} (row : Row Φ R (R.get i))
    (caller : Syntax.Payload Bit) (packet : Syntax.Payload (R.get i)) :
    Tree (Request Φ) (Transfer Runtime ⊕ Phase R) :=
  match row with
  | .jump j h => pure (.inr ⟨.inr (jumpPacket j h packet)⟩)
  | row => activeStep row caller packet

def Profile.rawStep {Φ : Type} {slots : List Bool} (p : Profile Φ slots) (caller : Syntax.Payload Bit)
    (phase : Phase (layout slots)) : Tree (Request Φ) (Transfer Runtime ⊕ Phase (layout slots)) :=
  match phase.down with
  | .inl result => pure (.inl (packedReturn result))
  | .inr ⟨i, packet⟩ => (p i).step caller packet

def Profile.isJump {Φ : Type} {slots : List Bool} (p : Profile Φ slots) (phase : Phase (layout slots)) : Bool :=
  match phase.down with
  | .inl _ => false
  | .inr packet => match p packet.1 with
    | .jump .. => true
    | _ => false

def Profile.normalStep {Φ : Type} {slots : List Bool} (p : Profile Φ slots) (caller : Syntax.Payload Bit)
    (phase : Phase (layout slots)) : Tree (Request Φ) (Transfer Runtime ⊕ Phase (layout slots)) :=
  match phase.down with
  | .inl result => pure (.inl (packedReturn result))
  | .inr ⟨i, packet⟩ =>
    match p.resolved (layout slots).length i with
    | some row => activeStep row caller packet
    | none => diverge

noncomputable def Profile.tree {Φ : Type} {slots : List Bool} (p : Profile Φ slots)
    (caller : Syntax.Payload Bit) (config : Packet (layout slots)) : RunTree Φ :=
  iter (m := Tree (Request Φ)) (p.normalStep caller) ⟨.inr config⟩

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} {slots : List Bool} {seed first second : V}
  {names : Fin ((layout slots).length + 2) ≃ K} {source target : CFG V K P.Instr}

structure Checked (source : CFG V K P.Instr) (literals : P.Instr → Option Bool) where
  admitted : Admission P (numberedInterface seed names) (fields first second) source
  profile : Profile P.Instr slots
  readback : Recognize.NumberedReadback admitted profile.expected
  literals_agree : profile.Agrees literals

def argumentType {κ : Type 1} {slots : List Bool} (i : Fin (layout slots).length) : Ty κ :=
  if (layout slots).get i = Bit then .coprod .unit .unit else .unit

/-- Check the source against the supplied typed layout, then infer the
identity targets and reconstruct all original numbered rows. -/
def admit? [DecidableEq κ] [DecidableEq P.Instr]
    (source : CFG V K P.Instr) (literals : P.Instr → Option Bool) :
    Option (Checked (P := P) (slots := slots) (seed := seed) (first := first) (second := second)
      (names := names) source literals) :=
  if count : source.blocks.length = (layout slots).length then do
    let a ← PacketLocal.admit (numberedInterface seed names) (fields first second) source
      (fun i => argumentType (Fin.cast count i))
    (Recognize.checkNumberedReadback a (readProfile literals) (fun p => p.val.expected)).map
      fun ⟨p, readback⟩ => ⟨a, p.val, readback, p.property⟩
  else none

/-- Observe the original mutable runner at the numbered public interface. -/
noncomputable def observeNamedNumbered {Φ : Type} {σ : Type v} {d : Nat}
    (source : CFG V K Φ) (keys : Fin (d + 2) ≃ K) (first second : V) (store : V → Value Runtime)
    (lit : Φ → Option Bool) (prim : Syntax.StatePrimitives Φ σ) (s : σ) (selected : Tag → Bool) :=
  decorateOn prim selected (observeOn prim
    (LiveOut.observeRaw (LiveBit.rawWithLiterals lit)
      [keys ((0 : Tag).natAdd d), keys ((1 : Tag).natAdd d)]
      (fun _ => [first, second]) source store) s (constructorDecoder PayloadType)) PayloadType

/-- Compare through the existing reachable cutoff on the exact normalized
readbacks. The caller must agree with both original mutable seeds. -/
def compare? [DecidableEq P.Instr] {literals : P.Instr → Option Bool}
    (left : Option (Checked (P := P) (slots := slots) (seed := seed) (first := first) (second := second)
      (names := names) source literals))
    (right : Option (Checked (P := P) (slots := slots) (seed := seed) (first := first) (second := second)
      (names := names) target literals))
    (raw raw' : Typed P.Instr [Bit] Outputs) (selected selected' : Tag → Bool)
    (caller : Syntax.Payload Bit) (store store' : V → Value Runtime)
    (configs : ConfigurationEnumeration (layout slots)) : Option Bool :=
  match left, right with
  | some l, some r =>
    if Silent.matchesCaller caller (store seed) && Silent.matchesCaller caller (store' seed) then
      (l.profile.endpoint selected).checkReachable? (r.profile.endpoint selected')
        raw raw' outputCodes caller caller replyPackets configs configs
    else none
  | _, _ => none

def encodePhase {K : Type 1} (keys : Fin ((layout slots).length + 2) ≃ K) (phase : Phase (layout slots)) : K × Value Runtime :=
  match phase.down with
  | .inl packet => (keys (packet.1.natAdd (layout slots).length), PayloadRecognition.packetValue packet)
  | .inr q => (keys (q.1.castAdd 2), .pair (Recognize.encodeValue ULift.up q.2.val) .unit)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Identity
