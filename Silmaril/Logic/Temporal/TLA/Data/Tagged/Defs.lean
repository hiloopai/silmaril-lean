module

public import Mathlib.SetTheory.ZFC.Basic
public import Silmaril.Logic.Temporal.TLA.Data.Defs

/-! # Tagged mathematical TLA+ values

Set values contain arbitrary values. Only a value with the set tag has
members at the value level. Codes outside the constructors' recognized
images remain opaque values.
-/

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

universe u v

/-- The underlying set codes are an implementation carrier for tagged values. -/
structure Value where
  code : ZFSet.{u}

/-- Payload of a set value. Its members are the codes of its element values. -/
structure SetData where
  codes : ZFSet.{u}

inductive Kind where
  | set | integer | boolean | function | character
  deriving DecidableEq

def Kind.index : Kind → Nat
  | .set => 0
  | .integer => 1
  | .boolean => 2
  | .function => 3
  | .character => 4

/-- Natural-number codes used inside tags and scalar payloads. -/
def natCode : Nat → ZFSet.{u}
  | 0 => ∅
  | n + 1 => {natCode n}

def Value.tagged (kind : Kind) (payload : ZFSet.{u}) : Value.{u} :=
  ⟨ZFSet.pair (natCode kind.index : ZFSet.{u}) payload⟩

/-- A partial inverse to a constructor, on its image. -/
noncomputable def decode {A : Type u} {B : Type v} (encode : A → B) (value : B) : Option A :=
  open Classical in
  if h : ∃ a, encode a = value then some (Classical.choose h) else none

def Value.set (s : SetData.{u}) : Value.{u} :=
  .tagged .set s.codes

noncomputable def Value.asSet : Value.{u} → Option SetData.{u} :=
  decode Value.set

def SetData.mem (x : Value.{u}) (s : SetData.{u}) : Prop :=
  x.code ∈ s.codes

/-- Membership at the value level requires a set on the right. -/
def Value.mem (x s : Value.{u}) : Prop :=
  ∃ t : SetData.{u}, .set t = s ∧ t.mem x

def SetData.empty : SetData.{u} := ⟨∅⟩

def SetData.insert (x : Value.{u}) (s : SetData.{u}) : SetData.{u} :=
  ⟨Insert.insert x.code s.codes⟩

def SetData.enum (xs : List Value.{u}) : SetData.{u} :=
  xs.foldr SetData.insert SetData.empty

def SetData.sep (s : SetData.{u}) (p : Value.{u} → Prop) : SetData.{u} :=
  ⟨s.codes.sep (fun x => p ⟨x⟩)⟩

noncomputable def SetData.image (s : SetData.{u}) (f : Value.{u} → Value.{u}) : SetData.{u} :=
  ⟨ZFSet.range (fun x : s.codes => (f ⟨x.val⟩).code)⟩

def SetData.subset (s t : SetData.{u}) : Prop :=
  ∀ x, s.mem x → t.mem x

/-- Every element of a powerset is itself a tagged set. -/
noncomputable def SetData.powerset (s : SetData.{u}) : SetData.{u} :=
  ⟨ZFSet.range (fun t : s.codes.powerset => (Value.set ⟨t.val⟩).code)⟩

/-- Operations that can use a model-fixed interpretation on unspecified inputs. -/
inductive Operation where
  | add | sub | modulo | le | interval | domain | apply | update
  deriving DecidableEq

/-- Fix one policy across valuations and steps. It receives the operation and its operands. -/
abbrev Unspecified := Operation → List Value.{u} → Value.{u}

end Silmaril.Logic.Temporal.TLA.Data.Tagged
