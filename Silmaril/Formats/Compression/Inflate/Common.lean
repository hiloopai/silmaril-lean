module

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate

/-!
# Logical state shared by mathematical inflater-helper translations

A function-by-function mathematical
translation of zlib 1.3.1. These are candidate models and their model-only laws,
not C/Ail execution, frontend correctness, or memory/ABI refinement theorems.

`Option State` abstracts the result of `inflateStateCheck`: `none` means that
the check failed. Establishing the predicate from C pointers, allocator
callbacks, the back-pointer and mode range is a separate obligation. Fields
unused by these helpers are framed away; `State` is not a C struct layout.
-/

/-- The modes declared by zlib 1.3.1's `inflate.h`, without their ABI encoding. -/
inductive Mode where
  | head | flags | time | os | exlen | extra | name | comment | hcrc
  | dictid | dict | type_ | typedo | stored | copyFirst | copy
  | table | lenlens | codelens | lenFirst | len | lenext | dist | distext
  | match_ | lit | check | length | done | bad | mem | sync
deriving Repr, DecidableEq

/-- The fields observed or modified by this small helper pilot. -/
structure State where
  mode : Mode
  hold : Nat
  bits : Nat
  wrap : Nat
deriving Repr, DecidableEq

/-- Canonical bit accumulator and three wrapper/check flag bits. The C
refinement must establish these invariants before using arithmetic laws. -/
def Valid (s : State) : Prop :=
  s.bits ≤ 32 ∧ s.hold < 2 ^ s.bits ∧ s.wrap < 8

inductive Status where
  | ok | streamError
deriving Repr, DecidableEq

end Silmaril.Formats.Compression.Inflate
