module

public import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun

@[expose] public section

/-!
# Kernel-reducible runs of the verified interpreter

silmaril-lean's verified interpreter `runI` (and `runInvoke?`) reduces in Lean's kernel, but its
`i32.load`/`i32.store` go through `ByteArray.extract`/`copySlice`, whose logical definitions
(`Array.extract.loop`, `Array.push` as `List.concat`) are quadratic in the size of the memory: a
single store into a one-page memory costs billions of kernel steps. This topic gives

* `kernel_rfl`: closes an equation `lhs = rhs` by the kernel's definitional check alone, after
  reverting the local context (as `decide +kernel` does for decidable propositions). Moved here
  from the toy resource component (`Silmaril.Proofs.Wasm.Resource.CompToy.Init`) to be shared;
* `fload`, `fstore`: the memory accesses `Memory.load`, `Memory.store` on the list of bytes, by
  linear structural recursion (`dropX`, `takeX`, `lenGe`, `writeL`);
* `headF o`: the interpreter's head step `interpHead o` with the memory family's plain integer
  loads and stores (`intLoad t none`, `intStore t none`) computed by `fload`/`fstore`;
* `runIF o := run? (headF o)` and `runInvokeF`, mirroring `runI` and `runInvoke?`;
* `splitK`, `stepK`, `runK`, `runIK`, `runInvokeK`: the same run with the driver `step?` (defined
  by well-founded recursion on the size of the code, which the kernel reduces through `Acc.rec`
  and `sizeOf` proofs) replaced by `stepK`, structural recursion on a nesting-depth fuel
  (`kDepth = 64` layers of labels, handlers and frames; deeper code falls back to `step?`), and
  `splitVals` (which evaluates its recursive call twice) by `splitK` (`List.rec`, once). About
  2× faster on a 100-iteration loop (`benchmarks/wasm-tactics`).

`runIF_eq : runIF = runI`, `runInvokeF_eq : runInvokeF = runInvoke?`, `runIK_eq : runIK = runI`
and `runInvokeK_eq : runInvokeK = runInvoke?` (`Silmaril.Wasm.Verify.Kernel.Thms`) let a kernel
evaluation of `runInvokeK` (or `runInvokeF`) prove a statement about the verified interpreter,
hence (by `runInvoke?_sound`) about Core runs.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Verify.Kernel

open Lean Elab Tactic Meta in
/-- Close `lhs = rhs` by the kernel's definitional check only: revert the local context and
add `fun xs => Eq.refl lhs` as an auxiliary lemma (checked by the kernel, as `decide +kernel`
checks its auxiliary lemma). -/
elab "kernel_rfl" : tactic => do
  liftMetaTactic1 fun g => do
    let g ← g.cleanup
    let (_, g) ← g.revert (clearAuxDeclsInsteadOfRevert := true) (← g.getDecl).lctx.getFVarIds
    return g
  closeMainGoalUsing `kernel_rfl fun ty _ => do
    let ty ← instantiateMVars ty
    let pf ← forallTelescope ty fun xs body => do
      let some (_, l, _) := body.eq? | throwError "kernel_rfl: the goal is not an equation"
      mkLambdaFVars xs (← mkEqRefl l)
    let lvls := (collectLevelParams {} ty).params
    let lemmaLevels := (← Term.getLevelNames).reverse.filter lvls.contains
    let n ← withOptions (Elab.async.set · false) do mkAuxLemma lemmaLevels ty pf
    return mkConst n (lemmaLevels.map .param)

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec

variable {α : Type} {H : Type}

/-! ## Lists of bytes -/

/-! The list functions are written with `List.rec` (so `noncomputable`: they are meant for the
kernel only): the kernel reduces a recursor application directly, while the structural recursion
of an equation compiler definition goes through `brecOn` and costs much more time and memory. -/

/-- `l` without its first `n` elements, if it has `n`. -/
noncomputable def dropX (l : List α) : Nat → Option (List α) :=
  List.rec (motive := fun _ => Nat → Option (List α))
    (fun n => match n with | 0 => some [] | _ + 1 => none)
    (fun a l ih n => match n with | 0 => some (a :: l) | n + 1 => ih n) l

/-- The first `n` elements of `l`, if it has `n`. -/
noncomputable def takeX (l : List α) : Nat → Option (List α) :=
  List.rec (motive := fun _ => Nat → Option (List α))
    (fun n => match n with | 0 => some [] | _ + 1 => none)
    (fun a _ ih n => match n with | 0 => some [] | n + 1 => (ih n).map (a :: ·)) l

/-- `l` has at least `n` elements. -/
noncomputable def lenGe (l : List α) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun n => match n with | 0 => true | _ + 1 => false)
    (fun _ _ ih n => match n with | 0 => true | n + 1 => ih n) l

/-- `l` with its first elements replaced by `bs` (cut to the length of `l`). -/
noncomputable def overL (l : List α) : List α → List α :=
  List.rec (motive := fun _ => List α → List α)
    (fun _ => [])
    (fun a l ih bs => match bs with | [] => a :: l | b :: bs => b :: ih bs) l

/-- `l` with the elements from position `n` on replaced by `bs` (cut to the length of `l`). -/
noncomputable def writeL (l : List α) : Nat → List α → List α :=
  List.rec (motive := fun _ => Nat → List α → List α)
    (fun _ _ => [])
    (fun a l ih n bs => match n with | 0 => overL (a :: l) bs | n + 1 => a :: ih n bs) l

/-- `Memory.load`, by list recursion. -/
noncomputable def fload (m : Memory.Bytes) (st count : Nat) : Option (BitVec (8 * count)) :=
  ((dropX m.data.toList st).bind (takeX · count)).map fun bs =>
    BitVec.ofNat (8 * count) (Memory.decodeLE ⟨⟨bs⟩⟩)

/-- `Memory.store`, by list recursion. -/
noncomputable def fstore (m : Memory.Bytes) (st : Nat) {count : Nat} (w : BitVec (8 * count)) :
    Option Memory.Bytes :=
  if lenGe m.data.toList (st + count) then
    some ⟨⟨writeL m.data.toList st (Memory.encodeLE count w.toNat).data.toList⟩⟩
  else none

/-! ## The head step and the run -/

section Instrs

variable (s : Store H) (f : Frame)

/-- `Mem.loadInt` with `fload`. -/
noncomputable def loadIntF (t : IntType) (x : MemIdx) (arg : MemArg) :
    List Val → Option (Config H)
  | [v] =>
    match Mem.addrOf? v, s.mem? f x with
    | some ⟨_, i⟩, some (_, mi) =>
      match fload mi.bytes (effAddr i.toNat arg) (t.width / 8) with
      | some c => some ⟨s, f, [.plain (.intConst t (c.setWidth t.width))]⟩
      | none => some ⟨s, f, [.trap]⟩
    | _, _ => none
  | _ => none

/-- `Mem.storeInt` with `fstore`. -/
noncomputable def storeIntF (t : IntType) (x : MemIdx) (arg : MemArg) :
    List Val → Option (Config H)
  | [v, w] =>
    match Mem.addrOf? v, Mem.intOf? t w, s.mem? f x with
    | some ⟨_, i⟩, some c, some (ma, mi) =>
      match fstore mi.bytes (effAddr i.toNat arg) (count := t.width / 8) (c.setWidth _) with
      | some b => some ⟨s.setMem ma { mi with bytes := b }, f, []⟩
      | none => some ⟨s, f, [.trap]⟩
    | _, _, _ => none
  | _ => none

end Instrs

/-- `Mem.stepArgs` with `loadIntF`, `storeIntF`. -/
noncomputable def stepArgsF (o : GrowOracle) (s : Store H) (f : Frame) (args : List Val)
    (e : Admin) :
    Option (Config H) :=
  match e with
  | .plain (.intLoad t none x arg) => loadIntF s f t x arg args
  | .plain (.intStore t none x arg) => storeIntF s f t x arg args
  | _ => Mem.stepArgs o s f args e

/-- `memoryStep?` with `stepArgsF`. -/
noncomputable def memoryStepF (o : GrowOracle) (s : Store H) (f : Frame) (vs : List Val)
    (e : Admin) :
    Option (Nat × Config H) :=
  match Mem.arity e with
  | some k =>
    if k ≤ vs.length then (stepArgsF o s f (vs.drop (vs.length - k)) e).map (k, ·) else none
  | none => none

/-- `interpHead o` with `memoryStepF`. -/
noncomputable def headF (o : GrowOracle) : HeadFn H := fun s f vs e =>
  match famOf e with
  | .memory => memoryStepF o s f vs e
  | _ => interpHead o s f vs e

/-- The interpreter run with `headF`. -/
noncomputable def runIF (o : GrowOracle) : Nat → Config H → Config H × Bool := run? (headF o)

/-- `runInvoke?` with `runIF`. -/
noncomputable def runInvokeF (o : GrowOracle) (n : Nat) (s : Store H) (a : Nat)
    (vs : List Val) :
    Option (Config H × Bool × Option Result) :=
  let r := runIF o n (invoke s a vs)
  some (r.1, r.2, r.1.outcome?)

/-! ## A kernel-friendly driver -/

/-- `splitVals` by `List.rec`, with the recursive result used once. -/
noncomputable def splitK (l : List Admin) : List Val × List Admin :=
  List.rec (motive := fun _ => List Val × List Admin) ([], [])
    (fun a as ih => match a.val? with
      | some v => (v :: ih.1, ih.2)
      | none => ([], a :: as)) l

/-- The nesting depth up to which `stepK` uses its own recursion. -/
def kDepth : Nat := 64

/-- The driver `step? head` by recursion on a depth fuel `d`; out of fuel, `step? head`. -/
noncomputable def stepK (head : HeadFn H) : Nat → Config H → Option (Config H)
  | 0, c => step? head c
  | d + 1, c =>
    match splitK c.code with
    | (_, []) => none
    | (vs, e :: rest) => Drv.layer head c.store c.frame vs e rest fun c' _ => stepK head d c'

/-- `run? head` with `stepK head kDepth`. -/
noncomputable def runK (head : HeadFn H) : Nat → Config H → Config H × Bool
  | 0, c => (c, false)
  | n + 1, c =>
    match stepK head kDepth c with
    | none => (c, true)
    | some c' => runK head n c'

/-- The interpreter run with `headF` and `stepK`. -/
noncomputable def runIK (o : GrowOracle) : Nat → Config H → Config H × Bool := runK (headF o)

/-- `runInvoke?` with `runIK`. -/
noncomputable def runInvokeK (o : GrowOracle) (n : Nat) (s : Store H) (a : Nat)
    (vs : List Val) :
    Option (Config H × Bool × Option Result) :=
  let r := runIK o n (invoke s a vs)
  some (r.1, r.2, r.1.outcome?)

end Silmaril.Wasm.Verify.Kernel
