module

public import Silmaril.Formats.Json.Fast.Elab
public import Silmaril.Prelude.Bytes.Elab.Defs

/-! Benchmark-only certificate for a top-level object followed by LF. No public JSON API depends
on this module; the elaborator proposes data and the kernel checks each fragment proof. -/

@[expose] public section
namespace JsonCertificate

open Silmaril Silmaril.Formats.Json.Fast

abbrev Entry := String × Value

structure Block where
  bytes : KBytes
  count : Nat
  entries : ChunkSeq Entry

def Block.leaf (size packed : Nat) (items : Array Entry) : Block :=
  ⟨.leaf size packed, items.size, .leaf items⟩

def Block.join (left right : Block) : Block :=
  ⟨left.bytes ++ (.leaf 1 0x2c : KBytes) ++ right.bytes, left.count + right.count,
    .branch left.count left.entries right.entries⟩

def Block.render (block : Block) : KBytes :=
  (.leaf 1 0x7b : KBytes) ++ block.bytes ++ (.leaf 2 0x0a7d : KBytes)

def Block.value (block : Block) : Value := .object block.entries none

/-- A nonempty object body, in source order, with literal commas between certified blocks.
The leaves use the existing parser, with normal limits, on an independently bracketed body.
The byte premise retains the exact spelling, not a re-encoding of parsed values. -/
inductive Block.Valid : Block → Prop where
  | leaf (text : String) (size packed : Nat) (items : Array Entry) :
      (KBytes.leaf size packed).toList = text.toUTF8.data.toList →
      items.isEmpty = false →
      parseText ("{" ++ text ++ "}") = .ok (Value.ofObject items) →
      Valid (Block.leaf size packed items)
  | join {left right : Block} : Valid left → Valid right → Valid (left.join right)

theorem Block.Valid.ofPacked (text : String) (size packed : Nat) (items : Array Entry)
    (length : text.toUTF8.data.toList.length = size)
    (encoding : KBytes.leVal text.toUTF8.data.toList = packed)
    (nonempty : items.isEmpty = false)
    (parsed : parseText ("{" ++ text ++ "}") = .ok (Value.ofObject items)) :
    Valid (Block.leaf size packed items) :=
  .leaf text size packed items (length ▸ encoding ▸ KBytes.unpack_leVal _) nonempty parsed

theorem Block.Valid.wf {block : Block} (valid : block.Valid) : block.bytes.wf = true := by
  induction valid with
  | leaf => rfl
  | join _ _ left right => exact KBytes.wf_append (KBytes.wf_append left rfl) right

theorem Block.Valid.sized {block : Block} (valid : block.Valid) :
    block.count = block.entries.toList.length ∧ block.entries.WellSized := by
  induction valid with
  | leaf => simp [Block.leaf, ChunkSeq.toList, ChunkSeq.WellSized]
  | join _ _ left right =>
    exact ⟨by simp [Block.join, ChunkSeq.toList, ← left.1, ← right.1], left.1, left.2, right.2⟩

/-- A byte-exact spelling relation for this object profile (including its final LF).
This is not equality to a run of the monolithic parser or to its particular index layout. -/
def Spells (source : KBytes) (value : Value) : Prop :=
  ∃ block : Block, block.Valid ∧ source.toList = block.render.toList ∧ value = block.value

theorem spells_of_check (source : KBytes) (block : Block) (valid : block.Valid)
    (wf : source.wf = true) (agree : source.sameBytes 4096 block.render = true) :
    Spells source block.value :=
  ⟨block, valid, KBytes.toList_eq_of_sameBytes _ _ _ wf
    (KBytes.wf_append (KBytes.wf_append rfl valid.wf) rfl) agree, rfl⟩

end JsonCertificate

public meta section
namespace JsonCertificate

open Lean Elab Command Silmaril Silmaril.Formats.Json Silmaril.Formats.Json.Fast

elab "certificate_leaf " name:ident " from " path:str : command => do
  let bytes ← liftCoreM <| KBytes.Elab.readRelative path.getString
  let some text := String.fromUTF8? bytes | throwError "invalid UTF-8 in certificate leaf"
  let .ok (.object (.leaf items) _) := parseText ("{" ++ text ++ "}")
    | throwError "expected an object body with at most 32 entries"
  unless !items.isEmpty do throwError "expected a nonempty object body"
  let name := (← getCurrNamespace) ++ name.getId
  let size := mkNatLit bytes.size
  let packed := mkNatLit (KBytes.Elab.encodeRange bytes 0 bytes.size)
  let array := Fast.Elab.arrayExpr Fast.Elab.entryType (items.map fun (key, value) =>
    mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) Fast.Elab.valueType
      (mkStrLit key) (Fast.Elab.valueExpr value))
  liftCoreM do
    Fast.Elab.addDef name (mkConst ``Block) (mkApp3 (mkConst ``Block.leaf) size packed array)
    let rhs := mkApp3 (mkConst ``Except.ok [0, 0]) (mkConst ``Error) (mkConst ``Value)
      (mkApp (mkConst ``Value.ofObject) array)
    let proof := mkAppN (mkConst ``Block.Valid.ofPacked) #[mkStrLit text, size, packed, array,
      mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) size,
      mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) packed,
      mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.false),
      mkApp2 (mkConst ``Eq.refl [1]) Fast.Elab.resultType rhs]
    KBytes.Elab.addThm (name ++ `valid) (mkApp (mkConst ``Block.Valid) (mkConst name)) proof

end JsonCertificate
