module

public import Silmaril.Wasi.Versions.HttpAttr.Defs

@[expose] public section

/-!
# HTTP attributes across versions: forwarding adapters

`fwdAttr N N' P e hP` exports the functions of the name table `P` (pairs: exported function,
imported function) and imports the attribute slice `N'`. Each call is forwarded with the same
arguments to the paired function, whose operation in `N'` is the operation of the exported
function in `N` (`hP`, checked by `decide` on the tables). The answer is returned unchanged,
except the errors of a request-options setter (keys 4–6), which become `error(e)`: 0.2
`set-*-timeout` answers `result` (no payload), 0.3 `result<_, request-options-error>`.

* **`attr2Over3`**: exports the 0.2 getters and setters of `outgoing-request`,
  `incoming-request`, `request-options` and `outgoing-response` (and their drops, and the
  `request-options` constructor), imports the 0.3 slice. Both 0.2 request resources go to the
  one 0.3 `request`.
* **`attr3Over2`**: exports the 0.3 getters and setters of `request`, `request-options`,
  `response` (and their drops, and the `request-options` constructor), imports the 0.2 slice.
  A 0.3 `request` goes to the 0.2 `outgoing-request` (an incoming request would trap there:
  traps are allowed by both theories).

Not forwarded: the constructors with headers (0.2 `outgoing-request`, `outgoing-response`;
0.3 `request.new`, `response.new`: the 0.3 ones need a body stream and a trailers future,
which the adapter does not create) and 0.3 `request-options.clone` (no 0.2 counterpart).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)

/-- The paired function of `f` in the table `P` (`f` itself when it has none). -/
def mapF (P : List (FnName × FnName)) (f : FnName) : FnName :=
  ((P.find? (·.1 == f)).map (·.2)).getD f

/-- The exported functions of a table. -/
def domF (P : List (FnName × FnName)) : Set FnName := {f | (P.find? (·.1 == f)).isSome}

/-- A table is **sound** for `N` over `N'`: every exported function has an operation in `N`,
and its pair has the same one in `N'`. -/
def TabOk (N N' : AttrFns) (P : List (FnName × FnName)) : Prop :=
  ∀ p ∈ P, (N.op p.1).isSome = true ∧ N'.op p.2 = N.op p.1

instance (N N' : AttrFns) (P : List (FnName × FnName)) : Decidable (TabOk N N' P) := by
  unfold TabOk; infer_instance

/-- An exported function of a sound table has its operation, and so does its pair. -/
theorem tabOk_find {N N' : AttrFns} {P : List (FnName × FnName)} (hP : TabOk N N' P) {f : FnName}
    (hf : f ∈ domF P) : (N.op f).isSome = true ∧ N'.op (mapF P f) = N.op f := by
  have hs : (P.find? (·.1 == f)).isSome = true := hf
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hs
  have hmem := List.mem_of_find?_eq_some hp
  have heq : p.1 = f := by simpa using List.find?_some hp
  have hm : mapF P f = p.2 := by simp [mapF, hp]
  rw [hm, ← heq]
  exact hP p hmem

/-- The answer of a forwarded call: errors of a request-options setter become `error(e)`. -/
def errTo (e : Option Val) : Option (List Val) → Option (List Val)
  | some [.variant 1 _] => some [.variant 1 e]
  | r => r

/-- The answer translation of an exported operation. -/
def trA (e : Option Val) : Option AOp → Option (List Val) → Option (List Val)
  | some (.set k), r => if k ∈ optKeys then errTo e r else r
  | _, r => r

/-- **The forwarding adapter** of the table `P`. -/
def fwdAttr (N N' : AttrFns) (P : List (FnName × FnName)) (e : Option Val) (hP : TabOk N N' P) :
    SBody Unit N'.fns (domF P) := fun _ q =>
  .call (⟨mapF P q.1.1, by
      have h := tabOk_find hP q.1.2
      show (N'.op (mapF P q.1.1)).isSome = true
      rw [h.2]; exact h.1⟩, q.2) fun r => .pure ((), trA e (N.op q.1.1) r)

/-! ## The tables -/

/-- The 0.2 functions forwarded to 0.3 functions. -/
def tab23 : List (FnName × FnName) := [
  (ht2 "[method]outgoing-request.method", ht3 "[method]request.get-method"),
  (ht2 "[method]outgoing-request.set-method", ht3 "[method]request.set-method"),
  (ht2 "[method]outgoing-request.path-with-query", ht3 "[method]request.get-path-with-query"),
  (ht2 "[method]outgoing-request.set-path-with-query", ht3 "[method]request.set-path-with-query"),
  (ht2 "[method]outgoing-request.scheme", ht3 "[method]request.get-scheme"),
  (ht2 "[method]outgoing-request.set-scheme", ht3 "[method]request.set-scheme"),
  (ht2 "[method]outgoing-request.authority", ht3 "[method]request.get-authority"),
  (ht2 "[method]outgoing-request.set-authority", ht3 "[method]request.set-authority"),
  (ht2 "[resource-drop]outgoing-request", ht3 "[resource-drop]request"),
  (ht2 "[method]incoming-request.method", ht3 "[method]request.get-method"),
  (ht2 "[method]incoming-request.path-with-query", ht3 "[method]request.get-path-with-query"),
  (ht2 "[method]incoming-request.scheme", ht3 "[method]request.get-scheme"),
  (ht2 "[method]incoming-request.authority", ht3 "[method]request.get-authority"),
  (ht2 "[resource-drop]incoming-request", ht3 "[resource-drop]request"),
  (ht2 "[constructor]request-options", ht3 "[constructor]request-options"),
  (ht2 "[method]request-options.connect-timeout", ht3 "[method]request-options.get-connect-timeout"),
  (ht2 "[method]request-options.set-connect-timeout", ht3 "[method]request-options.set-connect-timeout"),
  (ht2 "[method]request-options.first-byte-timeout", ht3 "[method]request-options.get-first-byte-timeout"),
  (ht2 "[method]request-options.set-first-byte-timeout",
    ht3 "[method]request-options.set-first-byte-timeout"),
  (ht2 "[method]request-options.between-bytes-timeout",
    ht3 "[method]request-options.get-between-bytes-timeout"),
  (ht2 "[method]request-options.set-between-bytes-timeout",
    ht3 "[method]request-options.set-between-bytes-timeout"),
  (ht2 "[resource-drop]request-options", ht3 "[resource-drop]request-options"),
  (ht2 "[method]outgoing-response.status-code", ht3 "[method]response.get-status-code"),
  (ht2 "[method]outgoing-response.set-status-code", ht3 "[method]response.set-status-code"),
  (ht2 "[resource-drop]outgoing-response", ht3 "[resource-drop]response")]

/-- The 0.3 functions forwarded to 0.2 functions. -/
def tab32 : List (FnName × FnName) := [
  (ht3 "[method]request.get-method", ht2 "[method]outgoing-request.method"),
  (ht3 "[method]request.set-method", ht2 "[method]outgoing-request.set-method"),
  (ht3 "[method]request.get-path-with-query", ht2 "[method]outgoing-request.path-with-query"),
  (ht3 "[method]request.set-path-with-query", ht2 "[method]outgoing-request.set-path-with-query"),
  (ht3 "[method]request.get-scheme", ht2 "[method]outgoing-request.scheme"),
  (ht3 "[method]request.set-scheme", ht2 "[method]outgoing-request.set-scheme"),
  (ht3 "[method]request.get-authority", ht2 "[method]outgoing-request.authority"),
  (ht3 "[method]request.set-authority", ht2 "[method]outgoing-request.set-authority"),
  (ht3 "[resource-drop]request", ht2 "[resource-drop]outgoing-request"),
  (ht3 "[constructor]request-options", ht2 "[constructor]request-options"),
  (ht3 "[method]request-options.get-connect-timeout", ht2 "[method]request-options.connect-timeout"),
  (ht3 "[method]request-options.set-connect-timeout", ht2 "[method]request-options.set-connect-timeout"),
  (ht3 "[method]request-options.get-first-byte-timeout", ht2 "[method]request-options.first-byte-timeout"),
  (ht3 "[method]request-options.set-first-byte-timeout",
    ht2 "[method]request-options.set-first-byte-timeout"),
  (ht3 "[method]request-options.get-between-bytes-timeout",
    ht2 "[method]request-options.between-bytes-timeout"),
  (ht3 "[method]request-options.set-between-bytes-timeout",
    ht2 "[method]request-options.set-between-bytes-timeout"),
  (ht3 "[resource-drop]request-options", ht2 "[resource-drop]request-options"),
  (ht3 "[method]response.get-status-code", ht2 "[method]outgoing-response.status-code"),
  (ht3 "[method]response.set-status-code", ht2 "[method]outgoing-response.set-status-code"),
  (ht3 "[resource-drop]response", ht2 "[resource-drop]outgoing-response")]

/-- The 0.2-over-0.3 table is sound. -/
theorem tab23_ok : TabOk attrFns2 attrFns3 tab23 := by decide

/-- The 0.3-over-0.2 table is sound. -/
theorem tab32_ok : TabOk attrFns3 attrFns2 tab32 := by decide

/-- **Attributes, 0.2 over 0.3**; a 0.3 options error becomes the 0.2 `error`. -/
def attr2Over3 : SBody Unit attrFns3.fns (domF tab23) := fwdAttr attrFns2 attrFns3 tab23 none tab23_ok

/-- **Attributes, 0.3 over 0.2**; a 0.2 options error becomes `other(none)`. -/
def attr3Over2 : SBody Unit attrFns2.fns (domF tab32) :=
  fwdAttr attrFns3 attrFns2 tab32 (some (.variant 2 (some noneV))) tab32_ok

end Silmaril.Wasi.Versions.Net
