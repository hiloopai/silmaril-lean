module

public import Silmaril.Wasm.Examples.LRAT.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Defs

@[expose] public section

/-!
# The LRAT checker as a component

`lratC` wraps the Core 3.0 checker `lratModule` (`Silmaril.Wasm.Examples.LRAT`) as a simple
component of the reference Component Model fragment (`Silmaril.Wasm.Component.Reference.Simple`):
one core instance of the module, and its ten core exports `canon lift`ed at

```wit
add-lit: func(x: s32);
end-clause: func();
step-begin: func(id: u32);
step-lit: func(x: s32);
step-hint: func(h: u32);
step-end: func();
delete: func(id: u32);
is-unsat: func() -> bool;
rat-begin: func(j: u32);
rat-end: func();
```

`is-unsat` returns a `bool`: the flat canonical ABI lifts the core `i32` result of `unsat` to
`true` exactly when it is nonzero (`ValTy.lift .bool`), which is the shape of the Core-level
safety condition `CallOk` ("a nonzero answer is right").

The abstract state at the component level is the DIMACS stream sent so far: `ccontrib` reads it
off a call on its IR values (`add-lit` on `.s32 x` sends `x.toInt`, `end-clause` sends the
terminator `0`, the other exports nothing), and `cstream calls` is the stream of a list of export
calls (by export index, as in `seqBehaviours`).

A list-based interface (`load-cnf: func(list<s32>)`) needs the linear-memory part of the
canonical ABI (`realloc`, pointer/length pairs), which neither the component IR's ABI nor the
reference soundness development covers yet; the interface is therefore scalar, one DIMACS integer
per call. A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference

/-- The checker module with its named numeric exports. -/
def lratNum : NumModule :=
  ⟨lratModule, [("add_lit", ⟨[.int .i32], []⟩), ("end_clause", ⟨[], []⟩),
    ("step_begin", ⟨[.int .i32], []⟩), ("step_lit", ⟨[.int .i32], []⟩),
    ("step_hint", ⟨[.int .i32], []⟩), ("step_end", ⟨[], []⟩), ("delete", ⟨[.int .i32], []⟩),
    ("unsat", ⟨[], [.int .i32]⟩), ("rat_begin", ⟨[.int .i32], []⟩), ("rat_end", ⟨[], []⟩)]⟩

/-- **The checker component**: the scalar LRAT interface, with `is-unsat() -> bool`. -/
def lratC : Simple :=
  ⟨lratNum, [⟨"add-lit", ⟨[.s32], []⟩, 0⟩, ⟨"end-clause", ⟨[], []⟩, 1⟩,
    ⟨"step-begin", ⟨[.u32], []⟩, 2⟩, ⟨"step-lit", ⟨[.s32], []⟩, 3⟩,
    ⟨"step-hint", ⟨[.u32], []⟩, 4⟩, ⟨"step-end", ⟨[], []⟩, 5⟩, ⟨"delete", ⟨[.u32], []⟩, 6⟩,
    ⟨"is-unsat", ⟨[], [.bool]⟩, 7⟩, ⟨"rat-begin", ⟨[.u32], []⟩, 8⟩, ⟨"rat-end", ⟨[], []⟩, 9⟩]⟩

/-- The DIMACS integers a component call sends: the literal of `add-lit`, the terminator of
`end-clause`, nothing otherwise. -/
def ccontrib (q : SimpleExport × List Silmaril.Wasm.Component.Val) : List Int :=
  if q.1.core = 0 then
    match q.2 with
    | [.s32 x] => [x.toInt]
    | _ => []
  else if q.1.core = 1 then [0] else []

/-- **The abstract transition of a component call**: append the integers it sends. -/
def cnext (xs : List Int) (q : SimpleExport × List Silmaril.Wasm.Component.Val) : List Int :=
  xs ++ ccontrib q

/-- The DIMACS stream sent by a list of component calls (export index and IR arguments). -/
def cstream (calls : List (Fin lratC.exports.length × List Silmaril.Wasm.Component.Val)) :
    List Int :=
  (specCalls lratC calls).foldl cnext []

end Silmaril.Wasm.Examples.LRAT
