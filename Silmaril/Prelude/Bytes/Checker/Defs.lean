module

public import Silmaril.Prelude.Bytes.Defs

/-! # Format checkers over kernel bytes

A **format checker** says that some bytes are the encoding of a value in a data format: an
ELF file of an AST, a JSON or CBOR document of a value, an S-expression or WAT text of a
module. It is format-independent: the format supplies the relation and a `Bool` checker, and
the soundness proof connects them.

```
structure FormatChecker (α : Type) where
  format : String                         -- "elf", "json", "cbor", "sexpr", "wat", …
  Parses : KBytes → α → Prop              -- the specification: `b` encodes `a`
  check  : KBytes → α → Bool              -- a decision procedure for claimed values
  sound  : ∀ b a, check b a = true → Parses b a
```

The checker checks a **claimed** value (emitted by an external or native parser); it never has
to parse. Register its `check` function as a native procedure with its format and soundness
theorem:

```
native_decider json.check := Silmaril.Formats.Json.checkBytes with_kernel_fallback
  format json sound Silmaril.Formats.Json.checkBytes_sound
```

and prove facts with `FormatChecker.parses_of C (by edge_decide)`. `edge_decide` sees through
`C.check` to the registered function. Expensive facts belong in leaf modules that import the
bytes (`kbytes_def`) and the checker.

`cstring` below is the reference instance: NUL-terminated strings, checked with one wide read.
-/

@[expose] public section

namespace Silmaril.KBytes

/-- A data format over kernel bytes, with a sound `Bool` checker for claimed values. -/
structure FormatChecker (α : Type) where
  /-- The format's name, as in the trust registry (`elf`, `json`, `cbor`, `sexpr`, `wat`, …). -/
  format : String
  /-- The specification: the bytes encode the value. -/
  Parses : KBytes → α → Prop
  /-- Decides `Parses` for a claimed value. -/
  check : KBytes → α → Bool
  sound : ∀ b a, check b a = true → Parses b a

/-- A successful check is a parse. -/
theorem FormatChecker.parses_of {α : Type} (C : FormatChecker α) {b : KBytes} {a : α}
    (h : C.check b a = true) : C.Parses b a :=
  C.sound b a h

/-- `b` holds exactly `s` and a terminating NUL, and `s` has no NUL. -/
def CString (b : KBytes) (s : List UInt8) : Prop :=
  b.toList = s ++ [0] ∧ ∀ c ∈ s, c ≠ 0

/-- Checks `CString` with one wide read. -/
def cstringCheck (b : KBytes) (s : List UInt8) : Bool :=
  b.wf && b.len == s.length + 1 && s.all (· != 0) && b.read 0 (s.length + 1) == leVal (s ++ [0])

end Silmaril.KBytes
