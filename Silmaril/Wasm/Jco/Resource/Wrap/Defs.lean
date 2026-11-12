module

public import Silmaril.Wasm.Jco.Resource.Adaptor.Defs
public import Silmaril.Wasm.Jco.Wrap.Defs

/-!
# The monadic construction for worlds with resources (rep-passing modules)

**Metadata** `MetaR`: the world's exported functions, with handle types, and the allocator.

**The rep-passing convention** (FFI style "reps"). The core module `M` does not see handles. It
implements world function `f` as the C convention of `Silmaril.Wasm.Jco.Meta` implements the
**erased** signature `f.erase`, in which every `own<r>` and `borrow<r>` is a `u32`, the
resource's rep:

* an `own<r>` or `borrow<r>` parameter is passed as the rep;
* an `own<r>` result is returned as the rep of the new resource.

`M` owns the resources it is handed: an `own` handle's entry is gone after the call. `MetaR.spec`
is this behaviour, on boundary values: the right-hand side of the behaviour theorem. Values
that do not fit the signature are erased to values that do not fit the erased signature
(`eraseVal`, `poison`), so both sides trap at the same parameter. A `borrow` result is invalid in
the Component Model; both sides trap after the call.

**The construction** `wrapR md` (total in `md`) is the component made of `M`, the handle table of
the component instance, and the adaptor `adaptorR md`:

* function 0, `cabi_realloc`, is `reallocShim` of `Silmaril.Wasm.Jco.Wrap`;
* function `i + 1` is the export shim of world function `i` (`shimR`):
  * prologue: for each `own<r>` parameter at flat position `p`,
    `local.get p; local.get p; resource.rep r; local.set p; resource.drop r`. The handle in
    local `p` is replaced by its rep, and the entry is dropped: ownership passes to `M`;
  * core: the export shim `exportShim` of the erased signature (out-pointer for strings and
    lists);
  * epilogue: for an `own<r>` result, `resource.new r` on the returned rep.
* world function `i` is `canon lift` of adaptor function `i + 1` with `M`'s memory and
  `cabi_realloc`.

`Silmaril.Wasm.Jco.Resource.Wrap.Thms` proves that the component behaves as `md.spec`, up to the
handle table, while the table has room for the call's handles.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Res

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Component (Flat ValTy Val)

/-! ## Erasure: handles as reps -/

/-- Handle types become `u32` reps. -/
def RTy.erase : RTy → PTy
  | .base t => t
  | .own _ | .borrow _ => .val .u32

/-- The erased signature. -/
def RSig.erase (s : RSig) : Sig := ⟨s.name, s.params.map RTy.erase, s.result.map RTy.erase⟩

/-- A value no lowering of `t` accepts. -/
def poison : PTy → PVal
  | .string => .bytes []
  | _ => .string ""

/-- A boundary value at a type, erased. -/
def eraseVal : RTy → RVal → PVal
  | .base _, .base v => v
  | .base t, .res _ => poison t
  | .own _, .res x | .borrow _, .res x => .val (.u32 x)
  | .own _, .base _ | .borrow _, .base _ => .string ""

/-- Boundary values at a parameter list, erased (extra values stay extra). -/
def eraseVals : List RTy → List RVal → List PVal
  | t :: ts, v :: vs => eraseVal t v :: eraseVals ts vs
  | [], vs => vs.map fun _ => .string ""
  | _ :: _, [] => []

/-- A result of the erased signature as a boundary value. -/
def unerase : Option RTy → Option PVal → Option RVal
  | some (.own _), some (.val (.u32 x)) => some (.res x)
  | _, r => r.map .base

/-- Whether a result type is allowed (no `borrow` result). -/
def resultOk : Option RTy → Bool
  | some (.borrow _) => false
  | _ => true

/-! ## Metadata and the convention -/

/-- WIT metadata with handle types. -/
structure MetaR where
  world : List RSig
  alloc : String := "alloc"
  deriving Repr, Inhabited, DecidableEq

/-- The metadata of the erased world. -/
def MetaR.erase (md : MetaR) : Meta := ⟨md.world.map RSig.erase, md.alloc⟩

variable (M : CoreInst) (md : MetaR)

/-- A world function called under the rep-passing convention. -/
def MetaR.specCall (s : RSig) (vs : List RVal) : RM M.St (Option RVal) := do
  let r ← md.erase.specCall M s.erase (eraseVals s.params vs)
  if resultOk s.result then pure (unerase s.result r) else RM.fail

/-- **M's behaviour at the world** under the rep-passing convention. -/
def MetaR.spec (name : String) (vs : List RVal) : RM M.St (Option RVal) :=
  match md.world.find? (·.name == name) with
  | some s => md.specCall M s vs
  | none => RM.fail

/-- The table has room for the handles of world function `name`: one per `own` parameter and one
for an `own` result (sufficient, not necessary). -/
def MetaR.Room (H : HTab) (t : H.T) (name : String) : Prop :=
  ∀ s, md.world.find? (·.name == name) = some s →
    H.Room t (ownCount s.params + ownRes s.result)

/-! ## The construction -/

/-- Replace the handle in local `p` by its rep and drop the handle. -/
def preOwn (r : RtId) (p : Nat) : List RInstr :=
  [.base (.localGet p), .base (.localGet p), .resRep r, .base (.localSet p), .resDrop r]

/-- The prologue for the parameters `ts`, the first at flat position `p`. -/
def prologue : Nat → List RTy → List RInstr
  | _, [] => []
  | p, .own r :: ts => preOwn r p ++ prologue (p + 1) ts
  | p, t :: ts => prologue (p + t.flatLen) ts

/-- The epilogue for a result. -/
def epilogue : Option RTy → List RInstr
  | some (.own r) => [.resNew r]
  | _ => []

/-- The export shim of a world function with handle types. -/
def shimR (s : RSig) : RFn :=
  { pre := prologue 0 s.params, core := exportShim md.erase s.erase, post := epilogue s.result }

/-- The generated adaptor module. -/
def adaptorR : List (String × RFn) :=
  ("cabi_realloc", { core := reallocShim md.alloc }) :: md.world.map fun s => (s.name, shimR md s)

/-- The lifts of world functions `k, k + 1, …`. -/
def liftsFromR : Nat → List RSig → List RLift
  | _, [] => []
  | k, s :: ss => ⟨s, .adapt (k + 1), .adapt 0⟩ :: liftsFromR (k + 1) ss

/-- **The monadic construction with resources.** -/
def wrapR : RComp := { adaptor := adaptorR md, lifts := liftsFromR 0 md.world }

end Silmaril.Wasm.Jco.Res
