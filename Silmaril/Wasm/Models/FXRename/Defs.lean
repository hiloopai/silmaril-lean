module

public import Silmaril.Wasm.Models.FXAbort.Defs

/-!
# Renaming exception addresses: definitions

The abortive lowering (`Silmaril.Wasm.Models.FXAbort`) reaches the same code `W; ks` on both sides,
the source at a store `s` and the target at `s.addExn ⟨ta, W⟩`: the target's `throw` has left one
exception instance that nothing refers to. Every later `throw` then allocates its exception one
address higher in the target. The two runs correspond under the renaming

    rnIdx n a = a        (a < n)
    rnIdx n a = a + 1    (n ≤ a)

of exception addresses, with `n = s.exns.length`, applied to every value (in code, locals, and
the store's globals, tables, element segments, structure and array fields and exception
payloads):

* `rnIdx`, `rnRef`, `rnVal`, `rnField`, `rnAdmin`/`rnAdmins`, `rnFrame`, `rnResult`, `rnBeh`:
  the renaming on addresses, references, values, fields, code, frames, results and behaviours;
* `ExnRen n s t`: the store `t` is `s` renamed, with one extra exception instance (`junk`, never
  referred to) at address `n`;
* `RefBelow n`, `ValBelow n`, `AdminsBelow n`, `FrameBelow n`, `StoreBelow n`: every exception
  address is below `n` (the renaming is then the identity).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXRename

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- Rename an exception address: addresses from `n` on move up by one. -/
def rnIdx (n a : Nat) : Nat := if a < n then a else a + 1

/-- Rename the exception addresses of a reference. -/
def rnRef (n : Nat) : Ref → Ref
  | .exn a => .exn (rnIdx n a)
  | .extern r => .extern (rnRef n r)
  | r => r

/-- Rename the exception addresses of a value. -/
def rnVal (n : Nat) : Val → Val
  | .ref r => .ref (rnRef n r)
  | v => v

/-- Rename the exception addresses of a field. -/
def rnField (n : Nat) : FieldVal → FieldVal
  | .val v => .val (rnVal n v)
  | p => p

mutual
/-- Rename the exception addresses of an administrative instruction. -/
def rnAdmin (n : Nat) : Admin → Admin
  | .label k cont body => .label k cont (rnAdmins n body)
  | .handler k cs body => .handler k cs (rnAdmins n body)
  | .frame k f body => .frame k { f with locals := f.locals.map (Option.map (rnVal n)) }
      (rnAdmins n body)
  | .ref r => .ref (rnRef n r)
  | a => a

/-- Rename the exception addresses of a code sequence. -/
def rnAdmins (n : Nat) : List Admin → List Admin
  | [] => []
  | a :: rest => rnAdmin n a :: rnAdmins n rest
end

/-- Rename the exception addresses of a frame's locals. -/
def rnFrame (n : Nat) (f : Frame) : Frame :=
  { f with locals := f.locals.map (Option.map (rnVal n)) }

/-- Rename the exception addresses of a result. -/
def rnResult (n : Nat) : Result → Result
  | .values vs => .values (vs.map (rnVal n))
  | .throw a => .throw (rnIdx n a)
  | .trap => .trap

/-- Rename the exception addresses of a behaviour. -/
def rnBeh (n : Nat) : Behaviour Val → Behaviour Val
  | .returns vs => .returns (vs.map (rnVal n))
  | .throws a => .throws (rnIdx n a)
  | b => b

/-- Rename the payload of an exception instance. -/
def rnExn (n : Nat) (e : ExnInst) : ExnInst := { e with fields := e.fields.map (rnVal n) }

/-- **The renamed store with one unreferenced exception at `n`.** -/
structure ExnRen {H : Type} (n : Nat) (s t : Store H) : Prop where
  le : n ≤ s.exns.length
  exns : ∃ junk, t.exns = (s.exns.take n).map (rnExn n) ++ junk :: (s.exns.drop n).map (rnExn n)
  tags : t.tags = s.tags
  funcs : t.funcs = s.funcs
  mems : t.mems = s.mems
  datas : t.datas = s.datas
  globals : t.globals = s.globals.map fun g => { g with value := rnVal n g.value }
  tables : t.tables = s.tables.map fun ti => { ti with refs := ti.refs.map (rnRef n) }
  elems : t.elems = s.elems.map fun ei => { ei with refs := ei.refs.map (rnRef n) }
  structs : t.structs = s.structs.map fun si => { si with fields := si.fields.map (rnField n) }
  arrays : t.arrays = s.arrays.map fun ai => { ai with fields := ai.fields.map (rnField n) }

/-- Every exception address of a reference is below `n`. -/
def RefBelow (n : Nat) : Ref → Prop
  | .exn a => a < n
  | .extern r => RefBelow n r
  | _ => True

/-- Every exception address of a value is below `n`. -/
def ValBelow (n : Nat) : Val → Prop
  | .ref r => RefBelow n r
  | _ => True

/-- Every exception address of a field is below `n`. -/
def FieldBelow (n : Nat) : FieldVal → Prop
  | .val v => ValBelow n v
  | _ => True

mutual
/-- Every exception address of an administrative instruction is below `n`. -/
def AdminBelow (n : Nat) : Admin → Prop
  | .label _ _ body => AdminsBelow n body
  | .handler _ _ body => AdminsBelow n body
  | .frame _ f body => (∀ o ∈ f.locals, ∀ v ∈ o, ValBelow n v) ∧ AdminsBelow n body
  | .ref r => RefBelow n r
  | _ => True

/-- Every exception address of a code sequence is below `n`. -/
def AdminsBelow (n : Nat) : List Admin → Prop
  | [] => True
  | a :: rest => AdminBelow n a ∧ AdminsBelow n rest
end

/-- Every exception address of a frame's locals is below `n`. -/
def FrameBelow (n : Nat) (f : Frame) : Prop := ∀ o ∈ f.locals, ∀ v ∈ o, ValBelow n v

/-- Every exception address held by the store is below `n`. -/
structure StoreBelow {H : Type} (n : Nat) (s : Store H) : Prop where
  globals : ∀ g ∈ s.globals, ValBelow n g.value
  tables : ∀ ti ∈ s.tables, ∀ r ∈ ti.refs, RefBelow n r
  elems : ∀ ei ∈ s.elems, ∀ r ∈ ei.refs, RefBelow n r
  structs : ∀ si ∈ s.structs, ∀ fv ∈ si.fields, FieldBelow n fv
  arrays : ∀ ai ∈ s.arrays, ∀ fv ∈ ai.fields, FieldBelow n fv
  exns : ∀ e ∈ s.exns, ∀ v ∈ e.fields, ValBelow n v

end Silmaril.Wasm.Models.FXRename
