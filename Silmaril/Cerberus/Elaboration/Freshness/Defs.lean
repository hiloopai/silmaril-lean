module

public import Silmaril.Cerberus.Symbol.Defs

/-! Explicit form of `symbol.lem`'s allocation API and `util/cerb_fresh.ml` at
Cerberus `b3e11ea334e95359907d4abf9194f0e7fedc6c6a`. The caller supplies digest,
host bound and the allocation history's next index. No digest computation or
inference of history from the input AST is claimed.
-/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Freshness
open Silmaril.Cerberus

structure Context where
  digest : Digest
  /-- Next index, corresponding to one plus the upstream mutable counter. -/
  next : Nat
  /-- Largest allocatable index, corresponding to the host's `max_int`. -/
  maximum : Nat
  deriving DecidableEq, Repr

inductive Error where
  | exhausted
  deriving DecidableEq, Repr

/-- The empty digest and first index zero reproduce the initial upstream state;
the host bound remains an explicit parameter. -/
def initial (maximum : Nat) : Context := ⟨⟨[]⟩, 0, maximum⟩

/-- The last allowed index can be returned; the following allocation rejects. -/
def integer (context : Context) : Except Error (Nat × Context) :=
  if context.next ≤ context.maximum then
    .ok (context.next, {context with next := context.next + 1})
  else .error .exhausted

def description (value : SymbolDescription) (context : Context) : Except Error (Sym × Context) := do
  let (index, after) ← integer context
  return (⟨context.digest, index, value⟩, after)

def fresh (context : Context) : Except Error (Sym × Context) := description .none context
def pretty (text : String) (context : Context) : Except Error (Sym × Context) := description (.id text) context
def cn (text : String) (context : Context) : Except Error (Sym × Context) := description (.cnId text) context

/-- Allocate before applying the description function, as in upstream. -/
def prettyWithId (makeText : Nat → String) (context : Context) : Except Error (Sym × Context) := do
  let (index, after) ← integer context
  return (⟨context.digest, index, .id (makeText index)⟩, after)

def fancy (text : Option String) (context : Context) : Except Error (Sym × Context) :=
  match text with
  | none => fresh context
  | some text => pretty text context

def objectAddress (text : String) (context : Context) : Except Error (Sym × Context) :=
  description (.objectAddress text) context
def funarg (location : Loc) (index : Nat) (context : Context) : Except Error (Sym × Context) :=
  description (.funArg location index) context
def setDescription (symbol : Sym) (value : SymbolDescription) : Sym := {symbol with description := value}
def setDigest (context : Context) (digest : Digest) : Context := {context with digest := digest}

end Silmaril.Cerberus.Elaboration.Freshness
