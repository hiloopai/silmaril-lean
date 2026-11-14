module

public import Silmaril.Wasi.Versions.HttpFields.Defs

@[expose] public section

/-!
# HTTP headers across versions: `fields` 0.2 over 0.3 and 0.3 over 0.2

* **`fields2Over3`** imports the 0.3 `fields` functions and exports the 0.2 ones: each call is
  forwarded to the 0.3 function of the same operation (`entries` to `copy-all`), with the same
  arguments, and its answer is returned. No state.
* **`fields3Over2`** imports the 0.2 functions and exports the 0.3 ones: each call is forwarded
  likewise, except `get-and-delete(h, name)`, which has no 0.2 counterpart: it calls
  `get(h, name)`, then `delete(h, name)`, and answers `ok` of the values when `delete`
  succeeds, the `delete` error when it fails, and traps otherwise.

The `header-error` variant has the same three cases in both versions (`invalid-syntax`,
`forbidden`, `immutable`; checked by reading the two `types.wit`), so errors pass unchanged.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)

/-- The 0.3 function of an operation. -/
def fn3 : FOp → FnName
  | .ctor => fieldsFns3.ctor
  | .fromList => fieldsFns3.fromList
  | .get => fieldsFns3.get
  | .has => fieldsFns3.has
  | .set => fieldsFns3.set
  | .delete => fieldsFns3.delete
  | .append => fieldsFns3.append
  | .entries => fieldsFns3.entries
  | .clone => fieldsFns3.clone
  | .getDel => ⟨"wasi:http/types@0.3.2", "[method]fields.get-and-delete"⟩

/-- The 0.2 function of an operation (`get-and-delete` has none; `delete` stands in). -/
def fn2 : FOp → FnName
  | .ctor => fieldsFns2.ctor
  | .fromList => fieldsFns2.fromList
  | .get => fieldsFns2.get
  | .has => fieldsFns2.has
  | .set => fieldsFns2.set
  | .delete => fieldsFns2.delete
  | .append => fieldsFns2.append
  | .entries => fieldsFns2.entries
  | .clone => fieldsFns2.clone
  | .getDel => fieldsFns2.delete

/-- The 0.3 function of an operation has that operation. -/
theorem op3_fn3 (o : FOp) : fieldsFns3.op (fn3 o) = some o := by
  cases o <;> decide

/-- The 0.2 function of an operation other than `get-and-delete` has that operation. -/
theorem op2_fn2 {o : FOp} (h : o ≠ .getDel) : fieldsFns2.op (fn2 o) = some o := by
  cases o <;> first | decide | exact absurd rfl h

/-- The 0.3 function of an operation is a 0.3 `fields` function. -/
theorem fn3_mem (o : FOp) : fn3 o ∈ fieldsFns3.fns := by
  simp [FieldsFns.fns, op3_fn3]

/-- The 0.2 `delete` is a 0.2 `fields` function. -/
theorem fn2_mem (o : FOp) : fn2 o ∈ fieldsFns2.fns := by
  show (fieldsFns2.op (fn2 o)).isSome = true
  cases o <;> decide

/-- The operation of an exported function (`ctor` when it has none, which never happens). -/
def opD (N : FieldsFns) (f : FnName) : FOp := (N.op f).getD .ctor

/-- **`fields` 0.2 over 0.3.** -/
def fields2Over3 : SBody Unit fieldsFns3.fns fieldsFns2.fns := fun _ q =>
  .call (⟨fn3 (opD fieldsFns2 q.1.1), fn3_mem _⟩, q.2) fun r => .pure ((), r)

/-- `get` as a 0.2 import. -/
def iFGet2 : {f // f ∈ fieldsFns2.fns} := ⟨fn2 .get, fn2_mem _⟩
/-- `delete` as a 0.2 import. -/
def iFDel2 : {f // f ∈ fieldsFns2.fns} := ⟨fn2 .delete, fn2_mem _⟩

/-- After `get` answered `x`: the answer for the `delete` answer `r₂`. -/
def delK (x : Val) (r₂ : Option (List Val)) : SProg Unit fieldsFns2.fns :=
  if isOkAns r₂ then .pure ((), some [okV (some x)])
  else
    match r₂ with
    | some [.variant 1 e] => .pure ((), some [.variant 1 e])
    | _ => .pure ((), none)

/-- The program of `get-and-delete(a)` over 0.2. -/
def getDelProg (a : List Val) : SProg Unit fieldsFns2.fns :=
  .call (iFGet2, a) fun r₁ =>
    match r₁ with
    | some [x] => .call (iFDel2, a) (delK x)
    | _ => .pure ((), none)

/-- **`fields` 0.3 over 0.2.** -/
def fields3Over2 : SBody Unit fieldsFns2.fns fieldsFns3.fns := fun _ q =>
  if opD fieldsFns3 q.1.1 = .getDel then getDelProg q.2
  else .call (⟨fn2 (opD fieldsFns3 q.1.1), fn2_mem _⟩, q.2) fun r => .pure ((), r)

end Silmaril.Wasi.Versions.Net
