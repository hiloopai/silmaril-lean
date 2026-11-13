module

public import Silmaril.Wasm.Jco.Resource.Wrap.Defs

/-!
# Merging a resource manager into the module (jco-style handle tables)

A jco-style toolchain need not use the Component Model's handle tables: the handle tables can be
owned by an added **resource-manager module**, merged with `M`. The output is then a core module
(or a component without resource types) whose world functions take and return **handles of the
manager's table** as `u32`s; the caller holds those handles.

* `mgr H`: the resource manager, a core instance whose state is a handle table of `H` and whose
  exports mirror the caller-side canonical operations: `rm.new(rep, rt) -> handle` (`lower_own`),
  `rm.take(handle, rt) -> rep` (`lift_own`: remove, check the type) and `rm.rep(handle, rt) -> rep`
  (`lift_borrow`: read, check the type). The resource type is passed as an `i32`.
* `link M R`: `M` and `R` merged into one instance: calls of the manager's names go to `R`,
  all others to `M`; the memory is `M`'s. Whether `link` is two instances (adaptor style) or one
  fused module, its behaviour is this product; that is the definition here, as `fuseSem` is in
  `Silmaril.Wasm.Jco.Fuse`.
* The glue `shimM md s`: one adaptor function per world function. It turns each `own`/`borrow`
  handle parameter into its rep through the manager (`preM`), runs part (a)'s export shim of the
  erased signature, and turns an `own` result rep into a new handle (`postM`).
* `merged md`: the component of part (a) (`Comp`, no resource types) with this glue, over
  `link M (mgr H)`, exporting the erased world (`MetaR.erase`): handles are `u32`s.
* `MetaR.hostView`: a function of the erased world read at the world's types, a handle being
  `RVal.res h`.

**The canonical counterpart** (`canonHost`): a caller with its own canonical handle table `Th`
calls `wrapR md`, whose instance has the table `Tc`. The caller lifts its arguments
(`hostLift`: `lift_own` removes the caller's handle, `lift_borrow` reads it, both check the
resource type), the component runs, and the caller lowers an `own` result (`hostLower`:
`lower_own` adds an entry to the caller's table). `specHost` is the same with `md.spec` in place
of the component.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.RM

variable {σ τ α : Type}

/-- A computation on the second component of the state. -/
def onSnd (m : RM τ α) : RM (σ × τ) α := fun st o =>
  match o with
  | .ok a st' => m st.2 (.ok a st'.2) ∧ st'.1 = st.1
  | .trap => m st.2 .trap

/-- A deterministic computation (`none` traps). -/
def ofFn (f : σ → Option (α × σ)) : RM σ α := fun s o =>
  o = match f s with
    | some (a, s') => .ok a s'
    | none => .trap

/-- A computation of the state's first component inside a state with a middle component. -/
def liftMid {ρ : Type} (m : RM (σ × τ) α) : RM ((σ × ρ) × τ) α := fun st o =>
  match o with
  | .ok a st' => m (st.1.1, st.2) (.ok a (st'.1.1, st'.2)) ∧ st'.1.2 = st.1.2
  | .trap => m (st.1.1, st.2) .trap

end Silmaril.Wasm.Jco.RM

namespace Silmaril.Wasm.Jco.Res

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Component (Flat)

variable (H : HTab)

/-! ## Table operations of a caller -/

/-- `lower_own` into a table: add an entry, return the handle. -/
def newF (r : RtId) (rep : BitVec 32) (t : H.T) : Option (BitVec 32 × H.T) :=
  (H.add? t ⟨r, rep⟩).map fun p => (BitVec.ofNat 32 p.1, p.2)

/-- `lift_own` from a table: remove the entry, check its type, return the rep. -/
def takeF (r : RtId) (h : BitVec 32) (t : H.T) : Option (BitVec 32 × H.T) :=
  (H.remove? t h.toNat).bind fun p => if p.1.rt == r then some (p.1.rep, p.2) else none

/-- `lift_borrow` from a table: read the entry, check its type, return the rep. -/
def repF (r : RtId) (h : BitVec 32) (t : H.T) : Option (BitVec 32 × H.T) :=
  (H.get? t h.toNat).bind fun e => if e.rt == r then some (e.rep, H.touch t h.toNat) else none

/-! ## The resource manager and the merge -/

/-- The names of the manager's exports. -/
def mgrName (n : String) : Bool := n == "rm.new" || n == "rm.take" || n == "rm.rep"

/-- The manager's exports. -/
def mgrCall (n : String) : List Flat → RM H.T (List Flat)
  | [⟨.int .i32, x⟩, ⟨.int .i32, rt⟩] =>
    if n = "rm.new" then RM.ofFn fun t => (newF H rt.toNat x t).map fun p => ([Flat.i32 p.1], p.2)
    else if n = "rm.take" then
      RM.ofFn fun t => (takeF H rt.toNat x t).map fun p => ([Flat.i32 p.1], p.2)
    else if n = "rm.rep" then
      RM.ofFn fun t => (repF H rt.toNat x t).map fun p => ([Flat.i32 p.1], p.2)
    else RM.fail
  | _ => RM.fail

/-- **The resource manager**: a core instance owning a handle table, without memory. -/
abbrev mgr : CoreInst where
  St := H.T
  mem _ := []
  setMem t _ := t
  call := mgrCall H

/-- **The merge** of a core instance and the manager. -/
abbrev link (M R : CoreInst) : CoreInst where
  St := M.St × R.St
  mem s := M.mem s.1
  setMem s m := (M.setMem s.1 m, s.2)
  call n xs := if mgrName n then (R.call n xs).onSnd else (M.call n xs).onFst

/-! ## The glue -/

/-- Replace the handle of resource type `r` in local `p` by its rep, with the manager's `op`. -/
def preHandle (op : String) (r : RtId) (p : Nat) : List AInstr :=
  [.localGet p, .i32Const (BitVec.ofNat 32 r), .call op 2, .localSet p]

/-- The handle conversions of the parameters `ts`, the first at flat position `p`. -/
def preM : Nat → List RTy → List AInstr
  | _, [] => []
  | p, .own r :: ts => preHandle "rm.take" r p ++ preM (p + 1) ts
  | p, .borrow r :: ts => preHandle "rm.rep" r p ++ preM (p + 1) ts
  | p, .base t :: ts => preM (p + t.flat.length) ts

/-- The handle conversion of the result. -/
def postM : Option RTy → List AInstr
  | some (.own r) => [.i32Const (BitVec.ofNat 32 r), .call "rm.new" 2]
  | _ => []

/-- The glue function of a world function: conversions, part (a)'s export shim, conversion. -/
def shimM (md : MetaR) (s : RSig) : AFn :=
  let c := exportShim md.erase s.erase
  { params := c.params, locals := c.locals, body := preM 0 s.params ++ c.body ++ postM s.result }

/-- **The merged output**: a component without resource types over `link M (mgr H)`. -/
def merged (md : MetaR) : Comp where
  adaptor := ⟨("cabi_realloc", reallocShim md.alloc) :: md.world.map fun s => (s.name, shimM md s)⟩
  lifts := liftsFrom 0 md.erase.world

/-! ## Reading the erased world at the world's types -/

/-- A function of the erased world, at the world's types (handles as `res`). -/
def MetaR.hostView {σ : Type} (md : MetaR) (f : String → List PVal → RM σ (Option PVal))
    (name : String) (vs : List RVal) : RM σ (Option RVal) :=
  match md.world.find? (·.name == name) with
  | some s => do
    let r ← f name (eraseVals s.params vs)
    if resultOk s.result then pure (unerase s.result r) else RM.fail
  | none => RM.fail

/-! ## The canonical counterpart -/

variable (M : CoreInst)

/-- The caller lifts one argument. -/
def hostLiftP : RTy → RVal → RM (M.St × H.T) RVal
  | .own r, .res h => do
    let rep ← RM.ofTab (takeF H r h)
    pure (.res rep)
  | .borrow r, .res h => do
    let rep ← RM.ofTab (repF H r h)
    pure (.res rep)
  | .own _, .base _ | .borrow _, .base _ => RM.fail
  | .base _, v => pure v

/-- The caller lifts its arguments (arity mismatches are left to the callee, which traps). -/
def hostLift : List RTy → List RVal → RM (M.St × H.T) (List RVal)
  | t :: ts, v :: vs => do
    let a ← hostLiftP H M t v
    let b ← hostLift ts vs
    pure (a :: b)
  | [], vs => pure vs
  | _ :: _, [] => pure []

/-- The caller lowers the result. -/
def hostLower : Option RTy → Option RVal → RM (M.St × H.T) (Option RVal)
  | some (.own r), some (.res rep) => do
    let h ← RM.ofTab (newF H r rep)
    pure (some (.res h))
  | _, v => pure v

/-- **The canonical counterpart**: a caller with table `Th` calls `wrapR md`, whose instance has
the table `Tc`; states `(M.St × Th) × Tc`. -/
def canonHost (md : MetaR) (name : String) (vs : List RVal) :
    RM ((M.St × H.T) × H.T) (Option RVal) :=
  match md.world.find? (·.name == name) with
  | some s => do
    let reps ← (hostLift H M s.params vs).onFst
    let r ← ((wrapR md).callExport M H name reps).liftMid
    (hostLower H M s.result r).onFst
  | none => RM.fail

/-- The same with `M`'s behaviour under the rep-passing convention in place of the component. -/
def specHost (md : MetaR) (name : String) (vs : List RVal) : RM (M.St × H.T) (Option RVal) :=
  match md.world.find? (·.name == name) with
  | some s => do
    let reps ← hostLift H M s.params vs
    let r ← (md.specCall M s reps).onFst
    hostLower H M s.result r
  | none => RM.fail

/-! ## Hypotheses -/

/-- `M`'s allocator never diverges. -/
def MetaR.AllocTotal (md : MetaR) : Prop := ∀ xs s, ∃ o, M.call md.alloc xs s o

/-- No export of `M` the glue calls has a manager name, and resource types fit in an `i32`. -/
structure MetaR.MergeOk (md : MetaR) : Prop where
  alloc : mgrName md.alloc = false
  names : ∀ s ∈ md.world, mgrName s.name = false
  rts : ∀ s ∈ md.world, ∀ t ∈ s.result.toList ++ s.params, ∀ r,
    (t = .own r ∨ t = .borrow r) → r < 2 ^ 32

end Silmaril.Wasm.Jco.Res
