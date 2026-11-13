module

public import Silmaril.Wasm.Det.Core.Defs
public import Silmaril.Wasm.Det.Core.Component.Defs
public import Silmaril.Wasm.Det.Core.Litmus.Defs
public import Silmaril.Wasm.Logic.Hoare.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Defs

/-!
# Components: determinism and statelessness modulo traps and imports across calls

Component-level notions on top of the shared definitions of `Silmaril.Wasm.Det.Core`
(`DetCall`, `ObsAgree`, `Runs`, `Call`), at an **arbitrary** silmaril-lean `Profile` `P`.

## 1. One export call on the reference machine

* `ExportDet prof h σ0 comp args name vals`: the `returns` behaviours of an export call
  (`Silmaril.Wasm.Component.Reference.exportBehaviours`: instantiation from the empty store, then
  the call) coincide. Traps, deadlock and divergence are exempt. The shared `CompDet` implies it
  (`Silmaril.Wasm.Det.Core.Component.exportBehaviours_returns_eq`).
* `CoreDet P c x`: the core function that export `x` of the simple component `c` lifts is
  deterministic modulo traps and imports (`DetCall`) on every list of flat arguments, in the
  instance of the core module.

The lifting theorem (`Silmaril.Wasm.Det.Component.Thms`) goes through the proved
reference-to-specification half of IR soundness (`refToSpec_of_arity`).

## 2. Sessions: one core instance, many export calls

The reference machine keeps the core store across top-level calls. The multi-call bridge between
the machine and the canonical-ABI specification (`seq_refToSpec`) is only in a proof module and
not exported from a header, so the sessions below are an explicit **canonical-ABI model over Core
3.0 runs**. Each export call runs on the persistent core store of one instance.

* `CallSem α β`: an export call as a relation `s v tr s' o`. It runs from core store `s` on
  argument `v`, makes the import calls `tr` (the shared-oracle reading of `Silmaril.Wasm.Det.Core`),
  and ends in core store `s'`, with non-trapping output `some w` or a trap `none`.
* `SReach C s₀`: the call states, meaning the stores reached from `s₀` by any finished calls of
  any exports, with any arguments, any answers and any outcome. Traps are included because the
  store persists.
* `SDetAt C s₀ i`: two calls of export `i` from one call state, with the same argument and
  answers, that both return have equal outputs and equal final stores.
* `SStatelessAt C s₀ i`: two calls of export `i` from **any two** call states, with the same
  argument and answers, that both return have equal outputs. `SDet` and `SStateless` hold for
  every export.

**The canonical-ABI model** (`AbiFn`, `AbiCall`) covers `canon lift` of one core function at four
shapes: `func(u32*) -> u32*` (flat, `MAX_FLAT_PARAMS`/`MAX_FLAT_RESULTS` direct) and
`func(list<u8>) -> …` / `func(…) -> list<u8>`.

* **Lowering** a `list<u8>` argument (`Lower.buf`) calls the instance's `realloc(0, 0, 1, n)`. It
  writes the bytes at the returned pointer into linear memory `m` (`memWrite`) and passes
  `(ptr, n)`.
* **Lifting** a `list<u8>` result (`liftRes`) reads the `(ptr, len)` pair at the returned pointer
  and then the bytes (`memRead`). A result type with two flat values goes through a return
  pointer.
* **Post-return** runs after lifting (`PostRet`); if it fails, the call traps.

`realloc` and `post-return` runs are host-free.

## 3. Observable state and the scratch discipline

* `Obs`: a partial equivalence relation on core stores that says when two call states agree on
  their **observable state**. One instance is `ScratchEq m lo hi`: equal except on the bytes
  `[lo, hi)` of memory `m`, the scratch region. Another is "the same function instances".
* `Confined C s₀ Obs`: every call from a call state, finished with any outcome, ends in a store
  `Obs`-related to its start. The call's effects are confined to what `Obs` ignores.
* `ObsDetermines C Obs i`: calls of `i` from `Obs`-related stores have equal non-trapping
  outputs. The output reads only observable state, plus what the call itself wrote.

The unwinding theorem (`sStatelessAt_of_obs`) says that confinement and observation give
statelessness. For `AbiCall`, both conditions split into per-phase verification conditions:
`ReallocVC`, `WriteVC`, `CoreVC`, `ConfVC`. Each is either a Core-level property of one function
or a fact about `memWrite`. `StepConfined` is the per-step form of confinement (an invariant
closed under every Core step).

New definitions (no source file).
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Component

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Det.Core

/-! ## 1. One export call on the reference machine -/

section Ref

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Reference (Host Engine Outcome exportBehaviours)

variable {E : Engine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)]

/-- **One export call, deterministic modulo traps**: the `returns` behaviours of calling export
`name` on `vals` after instantiating `comp` from the empty store are equal. -/
def ExportDet (prof : ProfileKind) (h : Host E σ) (σ0 : σ) (comp : Syntax.Component E.Module)
    (args : Instantiate.Exports E) (name : String) (vals : List Value.Val) : Prop :=
  ∀ r₁ r₂, Outcome.returns r₁ ∈ exportBehaviours prof h σ0 comp args name vals →
    Outcome.returns r₂ ∈ exportBehaviours prof h σ0 comp args name vals → r₁ = r₂

end Ref

open Silmaril.Wasm.Component.Reference (Simple SimpleExport NumModule) in
/-- The core function lifted by export `x` of the simple component `c` is deterministic modulo
traps and imports on every list of flat arguments, in the instance of `c`'s core module. -/
def CoreDet (P : Profile) (c : Simple) (x : SimpleExport) : Prop :=
  ∀ I, c.mod.IsInst I → ∀ xs : List Silmaril.Wasm.Component.Flat,
    DetCall P I.store (I.addrs.getD x.core 0) (xs.map ofFlat)

/-! ## 2. Sessions -/

/-- An export call: from core store `s` on argument `v`, with import calls `tr`, to core store
`s'` with non-trapping output `some w` or a trap `none`. -/
abbrev CallSem (α β : Type) : Type := Store Nat → α → List Call → Store Nat → Option β → Prop

/-- The call states of a session from `s₀`: any finished calls of any exports, any outcome. -/
inductive SReach {ι α β : Type} (C : ι → CallSem α β) (s₀ : Store Nat) : Store Nat → Prop where
  | init : SReach C s₀ s₀
  | call {s s' : Store Nat} {i : ι} {v : α} {tr : List Call} {o : Option β}
      (hs : SReach C s₀ s) (hc : C i s v tr s' o) : SReach C s₀ s'

/-- **Per export, determinism modulo traps and imports**: from every call state, two calls of
`i` with the same argument and answers that both return have the same output and store. -/
def SDetAt {ι α β : Type} (C : ι → CallSem α β) (s₀ : Store Nat) (i : ι) : Prop :=
  ∀ s, SReach C s₀ s → ∀ v tr s₁ s₂ w₁ w₂, C i s v tr s₁ (some w₁) → C i s v tr s₂ (some w₂) →
    w₁ = w₂ ∧ s₁ = s₂

/-- **Per export, statelessness modulo traps and imports**: calls of `i` from any two call
states with the same argument and answers that both return have the same output. -/
def SStatelessAt {ι α β : Type} (C : ι → CallSem α β) (s₀ : Store Nat) (i : ι) : Prop :=
  ∀ s₁ s₂, SReach C s₀ s₁ → SReach C s₀ s₂ → ∀ v tr t₁ t₂ w₁ w₂,
    C i s₁ v tr t₁ (some w₁) → C i s₂ v tr t₂ (some w₂) → w₁ = w₂

/-- Every export is deterministic. -/
def SDet {ι α β : Type} (C : ι → CallSem α β) (s₀ : Store Nat) : Prop := ∀ i, SDetAt C s₀ i

/-- Every export is stateless. -/
def SStateless {ι α β : Type} (C : ι → CallSem α β) (s₀ : Store Nat) : Prop :=
  ∀ i, SStatelessAt C s₀ i

/-! ## The canonical-ABI model -/

/-- Write `bs` into `b` from offset `p` on. -/
def writeBytes (b : ByteArray) (p : Nat) : List UInt8 → ByteArray
  | [] => b
  | x :: xs => writeBytes (b.set! p x) (p + 1) xs

/-- Write `bs` at address `p` of memory `m` (`none`: out of bounds, a trap). -/
def memWrite (s : Store Nat) (m p : Nat) (bs : List UInt8) : Option (Store Nat) :=
  match s.mems[m]? with
  | some mi =>
    if p + bs.length ≤ mi.bytes.size then
      some { s with mems := s.mems.set m { mi with bytes := writeBytes mi.bytes p bs } }
    else none
  | none => none

/-- Read `n` bytes at address `p` of memory `m` (`none`: out of bounds, a trap). -/
def memRead (s : Store Nat) (m p n : Nat) : Option (List UInt8) :=
  match s.mems[m]? with
  | some mi =>
    if p + n ≤ mi.bytes.size then some ((List.range n).map fun i => mi.bytes.get! (p + i))
    else none
  | none => none

/-- The little-endian number of a byte list. -/
def le32 (bs : List UInt8) : Nat := bs.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- All values are `i32`s. -/
def i32s? : List Silmaril.Wasm.Execution.Core.Val → Option (List (BitVec 32))
  | [] => some []
  | .num ⟨.int .i32, b⟩ :: vs => (i32s? vs).map (b :: ·)
  | _ => none

/-- The arguments of `realloc(0, 0, 1, n)` (fresh allocation of `n` bytes, alignment `1`). -/
def reallocArgs (n : Nat) : List Silmaril.Wasm.Execution.Core.Val :=
  [Silmaril.Wasm.Execution.Core.Val.i32 0, Silmaril.Wasm.Execution.Core.Val.i32 0, Silmaril.Wasm.Execution.Core.Val.i32 1, Silmaril.Wasm.Execution.Core.Val.i32 (BitVec.ofNat 32 n)]

/-- The canonical-ABI shape of a lifted export over one core instance: the core function
address, `some (realloc, m)` for a `list<u8>` parameter lowered into memory `m`, `some m` for a
`list<u8>` result returned through a return pointer into memory `m`, and an optional
`post-return` function. -/
structure AbiFn where
  fn : Nat
  argBuf : Option (Nat × Nat) := none
  resBuf : Option Nat := none
  post : Option Nat := none

/-- Component values of the model: `u32`s (flat) or one `list<u8>`. -/
inductive AVal where
  | flat (xs : List (BitVec 32))
  | bytes (bs : List UInt8)
  deriving DecidableEq

/-- **Lowering**: the flat arguments and the store after lowering. -/
inductive Lower (P : Profile) (x : AbiFn) : Store Nat → AVal → Store Nat → List Silmaril.Wasm.Execution.Core.Val → Prop where
  | flat {s : Store Nat} {xs : List (BitVec 32)} (hx : x.argBuf = none) :
      Lower P x s (.flat xs) s (xs.map Silmaril.Wasm.Execution.Core.Val.i32)
  | buf {s s' : Store Nat} {d : Config Nat} {ra m : Nat} {bs : List UInt8} {p : BitVec 32}
      (hx : x.argBuf = some (ra, m))
      (hs : Steps P (Det.noHost (H := Nat)) (invoke s ra (reallocArgs bs.length)) d)
      (hd : d.code = vals [Silmaril.Wasm.Execution.Core.Val.i32 p]) (hw : memWrite d.store m p.toNat bs = some s') :
      Lower P x s (.bytes bs) s' [Silmaril.Wasm.Execution.Core.Val.i32 p, Silmaril.Wasm.Execution.Core.Val.i32 (BitVec.ofNat 32 bs.length)]

/-- **Lowering traps**, leaving the store `s'`: `realloc` ends without a single `i32`, or the
write is out of bounds. -/
inductive LowerFails (P : Profile) (x : AbiFn) : Store Nat → AVal → Store Nat → Prop where
  | realloc {s : Store Nat} {d : Config Nat} {ra m : Nat} {bs : List UInt8} {r : Result}
      (hx : x.argBuf = some (ra, m))
      (hs : Steps P (Det.noHost (H := Nat)) (invoke s ra (reallocArgs bs.length)) d)
      (hd : d.code = r.toAdmin) (hr : ∀ p, r ≠ .values [Silmaril.Wasm.Execution.Core.Val.i32 p]) :
      LowerFails P x s (.bytes bs) d.store
  | write {s : Store Nat} {d : Config Nat} {ra m : Nat} {bs : List UInt8} {p : BitVec 32}
      (hx : x.argBuf = some (ra, m))
      (hs : Steps P (Det.noHost (H := Nat)) (invoke s ra (reallocArgs bs.length)) d)
      (hd : d.code = vals [Silmaril.Wasm.Execution.Core.Val.i32 p]) (hw : memWrite d.store m p.toNat bs = none) :
      LowerFails P x s (.bytes bs) d.store

/-- **Lifting** the core results `ws` in store `s`. -/
def liftRes (x : AbiFn) (s : Store Nat) (ws : List Silmaril.Wasm.Execution.Core.Val) : Option AVal :=
  match x.resBuf with
  | none => (i32s? ws).map .flat
  | some m =>
    match i32s? ws with
    | some [rp] =>
      (memRead s m rp.toNat 8).bind fun b8 =>
        (memRead s m (le32 (b8.take 4)) (le32 (b8.drop 4))).map .bytes
    | _ => none

/-- **Post-return** on the core results: the store after it and whether it returned. -/
inductive PostRet (P : Profile) (x : AbiFn) : Store Nat → List Silmaril.Wasm.Execution.Core.Val → Store Nat → Bool → Prop where
  | none {s : Store Nat} {ws : List Silmaril.Wasm.Execution.Core.Val} (hx : x.post = none) : PostRet P x s ws s true
  | run {s : Store Nat} {ws : List Silmaril.Wasm.Execution.Core.Val} {pr : Nat} {e : Config Nat} {r : Result}
      (hx : x.post = some pr) (hs : Steps P (Det.noHost (H := Nat)) (invoke s pr ws) e)
      (he : e.code = r.toAdmin) : PostRet P x s ws e.store (decide (r = .values []))

/-- **One canonical-ABI export call** over the core store: lowering, the core call (with import
calls `tr`), lifting, post-return. A failure anywhere is a trap (`none`), with the store where
it happened. -/
inductive AbiCall (P : Profile) (x : AbiFn) : CallSem AVal AVal where
  | lowerFails {s s' : Store Nat} {v : AVal} (h : LowerFails P x s v s') : AbiCall P x s v [] s' none
  | coreFails {s s₁ : Store Nat} {v : AVal} {args : List Silmaril.Wasm.Execution.Core.Val} {tr : List Call} {d : Config Nat}
      {r : Result} (hl : Lower P x s v s₁ args) (hr : Runs P (invoke s₁ x.fn args) tr d)
      (hd : d.code = r.toAdmin) (hv : ∀ ws, r ≠ .values ws) : AbiCall P x s v tr d.store none
  | ret {s s₁ s' : Store Nat} {v : AVal} {args : List Silmaril.Wasm.Execution.Core.Val} {tr : List Call} {d : Config Nat}
      {ws : List Silmaril.Wasm.Execution.Core.Val} {ok : Bool} (hl : Lower P x s v s₁ args)
      (hr : Runs P (invoke s₁ x.fn args) tr d) (hd : d.code = vals ws)
      (hp : PostRet P x d.store ws s' ok) :
      AbiCall P x s v tr s' (if ok then liftRes x d.store ws else none)

/-- The session of a component whose exports `X i` are canonical-ABI lifts over one core
instance. -/
def abiSem {ι : Type} (P : Profile) (X : ι → AbiFn) : ι → CallSem AVal AVal :=
  fun i => AbiCall P (X i)

/-! ## 3. Observable state, confinement and the verification conditions -/

/-- `Obs` is a partial equivalence relation. -/
structure IsPER (Obs : Store Nat → Store Nat → Prop) : Prop where
  symm : ∀ {a b}, Obs a b → Obs b a
  trans : ∀ {a b c}, Obs a b → Obs b c → Obs a c

/-- **Confinement**: every call from a call state ends (any outcome) in an `Obs`-related store. -/
def Confined {ι α β : Type} (C : ι → CallSem α β) (s₀ : Store Nat)
    (Obs : Store Nat → Store Nat → Prop) : Prop :=
  ∀ s i v tr s' o, SReach C s₀ s → C i s v tr s' o → Obs s s'

/-- **Observation**: calls of `i` from `Obs`-related stores have equal non-trapping outputs. -/
def ObsDetermines {ι α β : Type} (C : ι → CallSem α β) (Obs : Store Nat → Store Nat → Prop)
    (i : ι) : Prop :=
  ∀ s₁ s₂, Obs s₁ s₂ → ∀ v tr t₁ t₂ w₁ w₂, C i s₁ v tr t₁ (some w₁) → C i s₂ v tr t₂ (some w₂) →
    w₁ = w₂

/-- **The scratch region**: two stores are equal except on the bytes `[lo, hi)` of memory `m`
(same memories otherwise, same type and size of memory `m`). This is "the observable state"
of the scratch discipline: everything but the scratch bytes. -/
def ScratchEq (m lo hi : Nat) (s₁ s₂ : Store Nat) : Prop :=
  { s₁ with mems := [] } = { s₂ with mems := [] } ∧ s₁.mems.length = s₂.mems.length ∧
    (∀ j, j ≠ m → s₁.mems[j]? = s₂.mems[j]?) ∧
    ∀ mi₁ mi₂, s₁.mems[m]? = some mi₁ → s₂.mems[m]? = some mi₂ →
      mi₁.type = mi₂.type ∧ mi₁.bytes.size = mi₂.bytes.size ∧
        ∀ k, (k < lo ∨ hi ≤ k) → mi₁.bytes.data[k]? = mi₂.bytes.data[k]?

/-- The same function instances (the observable state of code without memory, globals or
tables effects that matter). -/
def FuncsEq (s₁ s₂ : Store Nat) : Prop := s₁.funcs = s₂.funcs

/-- Both stores hold the function instances `F`. -/
def FuncsAt (F : List (FuncInst Nat)) (s₁ s₂ : Store Nat) : Prop := s₁.funcs = F ∧ s₂.funcs = F

/-- **Per-step confinement**: on configurations satisfying `J` (closed under steps and import
resumptions), every host-free step keeps the store `Obs`-related. -/
structure StepConfined (P : Profile) (Obs : Store Nat → Store Nat → Prop)
    (J : Config Nat → Prop) : Prop where
  closed : Closed P J
  step : ∀ c d, J c → Step P (Det.noHost (H := Nat)) c d → Obs c.store d.store

/-- **The `realloc` VC** (scratch pointer): from `Obs`-related stores, two `realloc` runs that
return one `i32` return the same pointer, and the stores are `Mid`-related. -/
def ReallocVC (P : Profile) (Obs Mid : Store Nat → Store Nat → Prop) (ra : Nat) : Prop :=
  ∀ s₁ s₂ n d₁ d₂ p₁ p₂, Obs s₁ s₂ →
    Steps P (Det.noHost (H := Nat)) (invoke s₁ ra (reallocArgs n)) d₁ →
    Steps P (Det.noHost (H := Nat)) (invoke s₂ ra (reallocArgs n)) d₂ →
    d₁.code = vals [Silmaril.Wasm.Execution.Core.Val.i32 p₁] → d₂.code = vals [Silmaril.Wasm.Execution.Core.Val.i32 p₂] → p₁ = p₂ ∧ Mid d₁.store d₂.store

/-- **The write VC**: writing the same bytes at the same address of memory `m` in `Mid`-related
stores gives `Arg`-related stores. -/
def WriteVC (Mid Arg : Store Nat → Store Nat → Prop) (m : Nat) : Prop :=
  ∀ s₁ s₂ p bs t₁ t₂, Mid s₁ s₂ → memWrite s₁ m p bs = some t₁ → memWrite s₂ m p bs = some t₂ →
    Arg t₁ t₂

/-- Numeric values (the flat arguments the canonical ABI passes). -/
def Nums (vs : List Silmaril.Wasm.Execution.Core.Val) : Prop := ∀ v ∈ vs, ∃ n, v = .num n

/-- **The core VC** of export `x`: from `Arg`-related stores, two runs of the core function on
the same numeric arguments with the same answers that both return values return the same
values, and lift to the same output (the result region read out was written by the call). -/
def CoreVC (P : Profile) (Arg : Store Nat → Store Nat → Prop) (x : AbiFn) : Prop :=
  ∀ t₁ t₂ args tr d₁ d₂ ws₁ ws₂, Arg t₁ t₂ → Nums args →
    Runs P (invoke t₁ x.fn args) tr d₁ → Runs P (invoke t₂ x.fn args) tr d₂ →
    d₁.code = vals ws₁ → d₂.code = vals ws₂ → ws₁ = ws₂ ∧ liftRes x d₁.store ws₁ = liftRes x d₂.store ws₂

/-- **The confinement VC** of export `x`: `realloc`, the write, the core call and `post-return`
each end (any outcome) in an `Obs`-related store. -/
structure ConfVC (P : Profile) (Obs : Store Nat → Store Nat → Prop) (x : AbiFn) : Prop where
  realloc : ∀ ra m, x.argBuf = some (ra, m) → ∀ s n d,
    Steps P (Det.noHost (H := Nat)) (invoke s ra (reallocArgs n)) d → Obs s d.store
  write : ∀ ra m, x.argBuf = some (ra, m) → ∀ s n d p bs t,
    Steps P (Det.noHost (H := Nat)) (invoke s ra (reallocArgs n)) d → d.code = vals [Silmaril.Wasm.Execution.Core.Val.i32 p] →
    memWrite d.store m p.toNat bs = some t → Obs d.store t
  core : ∀ s args tr d, Runs P (invoke s x.fn args) tr d → Obs s d.store
  post : ∀ pr, x.post = some pr → ∀ s ws e,
    Steps P (Det.noHost (H := Nat)) (invoke s pr ws) e → Obs s e.store

/-! ## Verification conditions over the Hoare logic -/

/-- No host-free run from `c` reaches an import call. -/
def NoCalls (P : Profile) (c : Config Nat) : Prop :=
  ∀ d, Steps P (Det.noHost (H := Nat)) c d → decompose? d.store d.code = none

/-- The every-run postcondition "returns exactly `F`, or traps" of the Hoare logic
(`Silmaril.Wasm.Logic.Hoare.HWP`). With `F` a function of the observable state of the start store,
`HWP … (RetOrTrap F)` is a functional specification; it gives output agreement of two
invocations whose specifications agree (`obsAgree_of_hwp`). -/
def RetOrTrap (F : List Silmaril.Wasm.Execution.Core.Val) : Silmaril.Wasm.Logic.Core.Post Nat :=
  fun _ _ o => o = .normal F ∨ o = .trap

/-! ## Executable checks (for the tactics) -/

/-- **The leaf check of an ABI export** in store `s₀`: the result is flat, and the core function
and `realloc` (if any) pass `Silmaril.Wasm.Det.Core.Litmus.leafCheck` (store-free native leaf
functions on numbers). `post-return` is not checked (it does not affect outputs). -/
def abiLeafCheck (s₀ : Store Nat) (x : AbiFn) : Bool :=
  x.resBuf.isNone && Silmaril.Wasm.Det.Core.Litmus.leafCheck s₀ x.fn &&
    match x.argBuf with
    | none => true
    | some (ra, _) => Silmaril.Wasm.Det.Core.Litmus.leafCheck s₀ ra

open Silmaril.Wasm.Validation in
/-- **The leaf check of core export `k` of the instance of module `m`**: `m` validates, is
instantiated by `instantiateOnce?` against fresh host functions without a start function (as in
`Silmaril.Wasm.Game.IsInstance`), and its `k`-th function export passes `leafCheck`. -/
def instLeafCheck (m : Module) (k : Nat) : Bool :=
  match validate? m with
  | some mt =>
    match instantiateOnce? (Silmaril.Wasm.Game.importStore (CExternType.funcs mt.imports)) m
        ((List.range mt.imports.length).map ExternAddr.func) with
    | some (s, f, none) =>
      Silmaril.Wasm.Det.Core.Litmus.leafCheck s ((Silmaril.Wasm.Game.exportFuncAddrs f.module).getD k 0)
    | _ => false
  | none => false

end Silmaril.Wasm.Det.Component
