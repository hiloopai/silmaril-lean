module

public import Silmaril.Wasm.Models.Runtime.Defs

/-!
# Functional Wasm: what a step may do to the store

`AllocOnly s s'`: `s'` differs from `s` only by **allocation**: the functions, globals, memories,
tables, data and element segments and tags are unchanged, and the structs, arrays and
exceptions of `s` are a prefix of those of `s'` (existing aggregates are not written). It is
reflexive and transitive (`Thms`).

`HostAllocOnly host`: host calls only allocate (for instance a host that keeps the store).

The theorem that functional code only allocates is `step_allocOnly` in `Thms`
(`docs/projects/spectec/README.md` §1.2, the `functional` profile).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **`s'` is `s` plus allocations**: no store write other than appending aggregates and
exceptions. -/
structure AllocOnly (s s' : Store H) : Prop where
  funcs : s'.funcs = s.funcs
  globals : s'.globals = s.globals
  mems : s'.mems = s.mems
  tables : s'.tables = s.tables
  datas : s'.datas = s.datas
  elems : s'.elems = s.elems
  tags : s'.tags = s.tags
  structs : s.structs <+: s'.structs
  arrays : s.arrays <+: s'.arrays
  exns : s.exns <+: s'.exns

/-- Host calls only allocate. -/
def HostAllocOnly (host : HostSemantics H) : Prop :=
  ∀ h s vs s' r, host h s vs (.returned s' r) → AllocOnly s s'

end Silmaril.Wasm.Models
