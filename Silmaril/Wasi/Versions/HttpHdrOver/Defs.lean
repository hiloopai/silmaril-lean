module

public import Silmaril.Wasi.Versions.HttpHdr.Defs
public import Silmaril.Wasi.Versions.HttpAttrOver.Defs

@[expose] public section

/-!
# HTTP headers of requests and responses across versions: forwarding adapters

`fwdHdr N N' P hP` exports the functions of the name table `P` and imports the headers slice
`N'`; each call is forwarded with the same arguments to the paired function, whose operation
in `N'` is the operation of the exported one in `N` (`hP`, checked by `decide`), and its answer
is returned unchanged (`header-error` has the same cases in both versions).

* **`hdr2Over3`**: the 0.2 `fields` functions, `[resource-drop]fields`, the four 0.2 headers
  accessors (both request resources to `request.get-headers`, both response resources to
  `response.get-headers`) and the parents' drops, over 0.3.
* **`hdr3Over2`**: the 0.3 `fields` functions except `get-and-delete`, `[resource-drop]fields`,
  `request.get-headers` (to `outgoing-request.headers`), `response.get-headers` (to
  `incoming-response.headers`: the client side) and the parents' drops, over 0.2.

Not forwarded: the constructors with headers (as for the attributes) and, over 0.2,
`get-and-delete` (`fields3Over2` does it as `get` then `delete` for `fieldsTh`; not redone for
this theory).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)

/-- A table is **sound** for the headers slice `N` over `N'`. -/
def HTabOk (N N' : HdrFns) (P : List (FnName × FnName)) : Prop :=
  ∀ p ∈ P, (N.op p.1).isSome = true ∧ N'.op p.2 = N.op p.1

instance (N N' : HdrFns) (P : List (FnName × FnName)) : Decidable (HTabOk N N' P) := by
  unfold HTabOk; infer_instance

/-- An exported function of a sound table has its operation, and so does its pair. -/
theorem hTabOk_find {N N' : HdrFns} {P : List (FnName × FnName)} (hP : HTabOk N N' P)
    {f : FnName} (hf : f ∈ domF P) : (N.op f).isSome = true ∧ N'.op (mapF P f) = N.op f := by
  have hs : (P.find? (·.1 == f)).isSome = true := hf
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hs
  have hmem := List.mem_of_find?_eq_some hp
  have heq : p.1 = f := by simpa using List.find?_some hp
  have hm : mapF P f = p.2 := by simp [mapF, hp]
  rw [hm, ← heq]
  exact hP p hmem

/-- **The forwarding adapter** of the table `P`. -/
def fwdHdr (N N' : HdrFns) (P : List (FnName × FnName)) (hP : HTabOk N N' P) :
    SBody Unit N'.fns (domF P) := fun _ q =>
  .call (⟨mapF P q.1.1, by
      have h := hTabOk_find hP q.1.2
      show (N'.op (mapF P q.1.1)).isSome = true
      rw [h.2]; exact h.1⟩, q.2) fun r => .pure ((), r)

/-- The 0.2 functions forwarded to 0.3 functions. -/
def hTab23 : List (FnName × FnName) := [
  (fieldsFns2.ctor, fieldsFns3.ctor), (fieldsFns2.fromList, fieldsFns3.fromList),
  (fieldsFns2.get, fieldsFns3.get), (fieldsFns2.has, fieldsFns3.has),
  (fieldsFns2.set, fieldsFns3.set), (fieldsFns2.delete, fieldsFns3.delete),
  (fieldsFns2.append, fieldsFns3.append), (fieldsFns2.entries, fieldsFns3.entries),
  (fieldsFns2.clone, fieldsFns3.clone),
  (ht2 "[resource-drop]fields", ht3 "[resource-drop]fields"),
  (ht2 "[method]outgoing-request.headers", ht3 "[method]request.get-headers"),
  (ht2 "[method]incoming-request.headers", ht3 "[method]request.get-headers"),
  (ht2 "[method]outgoing-response.headers", ht3 "[method]response.get-headers"),
  (ht2 "[method]incoming-response.headers", ht3 "[method]response.get-headers"),
  (ht2 "[resource-drop]outgoing-request", ht3 "[resource-drop]request"),
  (ht2 "[resource-drop]incoming-request", ht3 "[resource-drop]request"),
  (ht2 "[resource-drop]outgoing-response", ht3 "[resource-drop]response"),
  (ht2 "[resource-drop]incoming-response", ht3 "[resource-drop]response")]

/-- The 0.3 functions forwarded to 0.2 functions. -/
def hTab32 : List (FnName × FnName) := [
  (fieldsFns3.ctor, fieldsFns2.ctor), (fieldsFns3.fromList, fieldsFns2.fromList),
  (fieldsFns3.get, fieldsFns2.get), (fieldsFns3.has, fieldsFns2.has),
  (fieldsFns3.set, fieldsFns2.set), (fieldsFns3.delete, fieldsFns2.delete),
  (fieldsFns3.append, fieldsFns2.append), (fieldsFns3.entries, fieldsFns2.entries),
  (fieldsFns3.clone, fieldsFns2.clone),
  (ht3 "[resource-drop]fields", ht2 "[resource-drop]fields"),
  (ht3 "[method]request.get-headers", ht2 "[method]outgoing-request.headers"),
  (ht3 "[method]response.get-headers", ht2 "[method]incoming-response.headers"),
  (ht3 "[resource-drop]request", ht2 "[resource-drop]outgoing-request"),
  (ht3 "[resource-drop]response", ht2 "[resource-drop]incoming-response")]

/-- The 0.2-over-0.3 table is sound. -/
theorem hTab23_ok : HTabOk hdrFns2 hdrFns3 hTab23 := by decide

/-- The 0.3-over-0.2 table is sound. -/
theorem hTab32_ok : HTabOk hdrFns3 hdrFns2 hTab32 := by decide

/-- **Headers, 0.2 over 0.3.** -/
def hdr2Over3 : SBody Unit hdrFns3.fns (domF hTab23) := fwdHdr hdrFns2 hdrFns3 hTab23 hTab23_ok

/-- **Headers, 0.3 over 0.2.** -/
def hdr3Over2 : SBody Unit hdrFns2.fns (domF hTab32) := fwdHdr hdrFns3 hdrFns2 hTab32 hTab32_ok

end Silmaril.Wasi.Versions.Net
