module

public import Silmaril.X86.Concurrency.Cir.Csl.Tame.Defs
public import Silmaril.X86.Concurrency.Cir.Robust.Defs

/-!
# Message passing through a release store, with and without a weak data store

The litmus test that shows why the release rule
on XL needs its tameness side condition (`Stmt.wbStores`). Two threads, cells `d` (data) and `f`
(flag), both `0`:

```
thread 0: [d] := 1 (flavour fl); [f] := 1 (release, write-back)
thread 1: rax := [f] (acquire);  rbx := [d]
```

The outcome in question is `rax = 1 ∧ rbx = 0`: the reader sees the flag but not the data.

* `fl = nt` (`mp .nt`): **allowed on XL**, forbidden on TSO. XL lets the write-back flag store
  leave the buffer before the earlier `nt` data store.
* `fl = wb` (`mp .wb`, tame): **forbidden on TSO and on XL** (XL has TSO's runs,
  `Csl.Tame.reach_tso_of_wb`).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Csl.Tame.Litmus

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Robust

/-- The data cell. -/
def d : Nat := 0x100
/-- The flag cell. -/
def f : Nat := 0x200

/-- The writer: data store of flavour `fl`, then the flag store (C11 release, write-back). -/
def writer (fl : Flav) : Stmt :=
  .seq (.store .na 8 fl (.lit d) (.lit 1)) (.store .rel 8 .wb (.lit f) (.lit 1))

/-- The reader: the flag (acquire) into `rax`, then the data into `rbx`. -/
def reader : Stmt := .seq (.load .rax .acq 8 .wb (.lit f)) (.load .rbx .na 8 .wb (.lit d))

/-- **The test**, as a concrete start configuration of the explorer. -/
def mp (fl : Flav) : CSt := start [(writer fl, Regs.zero), (reader, Regs.zero)] [(d, 0), (f, 0)]

/-- The weak outcome: the reader saw the flag but not the data. -/
def weakOut (rs : Regs) : Prop := rs .rax = 1 ∧ rs .rbx = 0

/-- The explorer's form of "not the weak outcome". -/
def notWeakB (c : CSt) : Bool := !((c.th 1).2 .rax == 1 && (c.th 1).2 .rbx == 0)

end Silmaril.X86.Concurrency.Cir.Csl.Tame.Litmus
