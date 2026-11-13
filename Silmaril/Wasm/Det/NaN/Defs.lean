module

public import Silmaril.Wasm.Det.Core.Defs

/-!
# Determinism up to NaN payloads: floats whose NaN bits are never observed (definitions)

The third subset of `docs/projects/wasm-wasi.md`: Core 3.0 code with **non-relaxed scalar
floating point**, whose only nondeterminism at an arbitrary profile `P` is the choice of NaN
payloads (and signs) made by the float operators (`floatUnOpP`, `floatBinOpP`, `convertP`).
Everything is stated against silmaril-lean's `Step P host` at an **arbitrary** profile.

## The abstraction: canonicalising NaNs

`canonVal` maps every `f32`/`f64` NaN to the positive canonical NaN of silmaril-lean's float
model (`F32.canonicalNaN`, `F64.canonicalNaN`) and leaves every other value alone; `canonCfg`
applies it to every value in a configuration: the code (value instructions, including
`f32.const`/`f64.const` in function bodies once they are administrative code, through labels and
frames), the locals of every frame and the values of the store's globals. Memory bytes, tables,
GC objects and exceptions are not touched.

Two values with the same image are equal or are both NaNs: `canonVal` is the coarsest
**taint**: every float value is treated as possibly carrying nondeterministic payload bits, and
the analysis makes sure no instruction can observe those bits.

## The fragment (a syntactic predicate on Wasm 3.0 code)

`nanInstr set i` accepts: `nop`, `unreachable`, `drop`, `select`, `block`, `loop`, `if` (with
accepted bodies), `br`, `br_if`, `br_table`, `return`, `call`, `throw_ref`, `local.get/set/tee`,
`global.get`, `global.set` (only when `set = true`), integer constants and operators, `v128`
constants (values), float constants, **every scalar float unary operator, every float binary
operator except `copysign`, every float comparison, and every conversion except
`i32/i64.reinterpret_f32/f64`** (`ConvertOp.reinterpretInt`, float bits to an integer).

It rejects the **bit sinks** of a float: `copysign` (its sign operand exposes the sign of a
NaN), reinterpretation of a float as an integer, float stores to memory (all memory
instructions are excluded), vector instructions (relaxed SIMD in particular), `memory.grow` and
`table.grow` (their failure is a profile choice), tables, references, GC aggregates, `throw`,
`try_table`, `call_ref`, `call_indirect` and tail calls.

Every accepted float operator depends on its NaN operands only through silmaril-lean's float
model, which canonicalises NaN payloads (`F32.model`), or through an `isNaN` test: comparisons,
`trunc`/`trunc_sat`, `min`/`max` and arithmetic agree on two inputs that are equal or both NaN.
`neg`/`abs` flip or clear the sign bit, so they map NaNs to NaNs. This is what makes the
abstraction a simulation (`Silmaril.Proofs.Wasm.Det.NaN.Step`).

* `NAdms set code`: administrative code whose source instructions are accepted, through labels
  (and their continuations) and frames, with no `handler` and no `return_call_ref`;
* `NFuncs set F`: every Wasm function of `F` has an accepted body (host functions are imports:
  calling them stops the run at an import call);
* `NCfg set c`: both, for a configuration and its store;
* `nanCheck set s`: an executable `NFuncs set s.funcs`.

The check is store-wide (every function a call may reach is accepted); it is not a per-function
call-graph analysis.

## Notions

* `NaNDetCfg P c`: **determinism modulo traps, imports and NaN payloads**: two runs from `c`
  with the same import calls and answers that both reach a non-trapping stop have outputs equal
  up to NaN payloads (`canonOut`) and stores equal up to the NaN payloads of their globals;
* `NaNDetFn`, `NaNDetModule`: per function and per module, as in `Silmaril.Wasm.Det.Core`;
* `OutNaNFree o`: no value of the output is a float NaN; `NaNFreeOut P c`: every non-trapping
  output of every run from `c` is NaN-free. This is the **output sink** condition: outputs that
  are NaN-free and equal up to NaN payloads are equal.

Theorems in `Silmaril.Wasm.Det.NaN.Thms`. New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.NaN

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Numeric.Ieee754
open Silmaril.Wasm.Numerics (Profile asF32 asF64)
open Silmaril.Wasm.Det.Core

/-! ## Canonical NaNs -/

/-- The bits of the canonical `f32` NaN of silmaril-lean's float model. -/
def nan32 : BitVec 32 := F32.canonicalNaN.bits.toBitVec

/-- The bits of the canonical `f64` NaN of silmaril-lean's float model. -/
def nan64 : BitVec 64 := F64.canonicalNaN.bits.toBitVec

/-- Replace an `f32` NaN by the canonical NaN. -/
def canon32 (b : BitVec 32) : BitVec 32 := if (asF32 b).isNaN then nan32 else b

/-- Replace an `f64` NaN by the canonical NaN. -/
def canon64 (b : BitVec 64) : BitVec 64 := if (asF64 b).isNaN then nan64 else b

/-- Canonicalise the bits of a number of type `t` (integers are unchanged). -/
def canonBits : (t : NumType) → BitVec t.width → BitVec t.width
  | .int _, b => b
  | .float .f32, b => canon32 b
  | .float .f64, b => canon64 b

/-- Is the number of type `t` a float NaN? -/
def nanBits : (t : NumType) → BitVec t.width → Bool
  | .int _, _ => false
  | .float .f32, b => (asF32 b).isNaN
  | .float .f64, b => (asF64 b).isNaN

/-- Canonicalise a value: float NaNs become the canonical NaN. -/
def canonVal : Val → Val
  | .num ⟨t, b⟩ => .num ⟨t, canonBits t b⟩
  | v => v

/-- Is the value a float NaN? -/
def nanVal : Val → Bool
  | .num ⟨t, b⟩ => nanBits t b
  | _ => false

/-- Canonicalise a source instruction: only float constants change. -/
def canonInstr : Instr → Instr
  | .floatConst t b => .floatConst t (canonBits (.float t) b)
  | i => i

/-- Canonicalise the locals of a frame. -/
def canonFrame (f : Frame) : Frame :=
  { f with locals := f.locals.map (Option.map canonVal) }

mutual
/-- Canonicalise administrative code (through labels, handlers and frames). -/
def canonAdmin : Admin → Admin
  | .plain i => .plain (canonInstr i)
  | .label n cont body => .label n cont (canonAdmins body)
  | .handler n cs body => .handler n cs (canonAdmins body)
  | .frame n f body => .frame n (canonFrame f) (canonAdmins body)
  | a => a

/-- `canonAdmin` on a sequence. -/
def canonAdmins : List Admin → List Admin
  | [] => []
  | a :: as => canonAdmin a :: canonAdmins as
end

/-- Canonicalise the values of the globals of a store. -/
def canonStore (s : Store Nat) : Store Nat :=
  { s with globals := s.globals.map fun g => { g with value := canonVal g.value } }

/-- Canonicalise a configuration. -/
def canonCfg (c : Config Nat) : Config Nat :=
  ⟨canonStore c.store, canonFrame c.frame, canonAdmins c.code⟩

/-- Canonicalise a result. -/
def canonResult : Result → Result
  | .values vs => .values (vs.map canonVal)
  | r => r

/-- Canonicalise an output. -/
def canonOut : Out → Out
  | .ret r => .ret (canonResult r)
  | .call h args => .call h (args.map canonVal)

/-- Canonicalise an evaluation context. -/
def canonCtx : Ctx → Ctx
  | .top pre rest => .top (pre.map canonVal) (canonAdmins rest)
  | .label pre n cont E rest => .label (pre.map canonVal) n cont (canonCtx E) (canonAdmins rest)
  | .handler pre n cs E rest => .handler (pre.map canonVal) n cs (canonCtx E) (canonAdmins rest)
  | .frame pre n f E rest =>
    .frame (pre.map canonVal) n (canonFrame f) (canonCtx E) (canonAdmins rest)

/-! ## The fragment -/

/-- Flat instructions of the fragment (`global.set` and structured instructions are handled by
`nanInstr`). -/
def floatOk : Instr → Bool
  | .nop | .unreachable | .drop | .select _ | .br _ | .brIf _ | .brTable _ _ | .return_
  | .call _ | .throwRef | .localGet _ | .localSet _ | .localTee _ | .globalGet _
  | .intConst _ _ | .intUnOp _ _ | .intBinOp _ _ | .intTestOp _ _ | .intRelOp _ _
  | .floatConst _ _ | .vecConst _ | .floatUnOp _ _ | .floatRelOp _ _ => true
  | .floatBinOp _ op => op != .copysign
  | .convert (.reinterpretInt _) => false
  | .convert _ => true
  | _ => false

mutual
/-- **Instructions of the fragment** (recursively through `block`, `loop` and `if`); `set`
says whether `global.set` is allowed. -/
def nanInstr (set : Bool) : Instr → Bool
  | .block _ b => nanInstrs set b
  | .loop _ b => nanInstrs set b
  | .if_ _ b₁ b₂ => nanInstrs set b₁ && nanInstrs set b₂
  | .globalSet _ => set
  | i => floatOk i

/-- `nanInstr` on a sequence. -/
def nanInstrs (set : Bool) : List Instr → Bool
  | [] => true
  | i :: is => nanInstr set i && nanInstrs set is
end

mutual
/-- Administrative instructions of the fragment. -/
def NAdm (set : Bool) : Admin → Prop
  | .plain i => nanInstr set i = true
  | .ref _ | .callRefType _ | .trap => True
  | .returnCallRefType _ => False
  | .label _ cont body => nanInstrs set cont = true ∧ NAdms set body
  | .handler _ _ _ => False
  | .frame _ _ body => NAdms set body

/-- Administrative code of the fragment. -/
def NAdms (set : Bool) : List Admin → Prop
  | [] => True
  | a :: as => NAdm set a ∧ NAdms set as
end

/-- Every Wasm function has a body in the fragment. -/
def NFuncs (set : Bool) (F : List (FuncInst Nat)) : Prop :=
  ∀ fi ∈ F, ∀ fn, fi.code = .wasm fn → nanInstrs set fn.body = true

/-- **The invariant**: code and every Wasm function of the store are in the fragment. -/
def NCfg (set : Bool) (c : Config Nat) : Prop :=
  NAdms set c.code ∧ NFuncs set c.store.funcs

/-- **The executable check**: every Wasm function of the store is in the fragment. -/
def nanCheck (set : Bool) (s : Store Nat) : Bool :=
  s.funcs.all fun fi => match fi.code with
    | .wasm fn => nanInstrs set fn.body
    | .host _ => true

/-! ## Determinism up to NaN payloads -/

/-- **Determinism modulo traps, imports and NaN payloads**: two runs from `c` with the same
import calls and answers that both reach a non-trapping stop have outputs equal up to NaN
payloads and stores equal up to the NaN payloads of their globals. -/
def NaNDetCfg (P : Profile) (c : Config Nat) : Prop :=
  ∀ tr d₁ d₂ o₁ o₂, Runs P c tr d₁ → Runs P c tr d₂ → OutAt d₁ o₁ → OutAt d₂ o₂ →
    canonOut o₁ = canonOut o₂ ∧ canonStore d₁.store = canonStore d₂.store

/-- Per function: every typed invocation is deterministic up to NaN payloads. -/
def NaNDetFn (P : Profile) (s : Store Nat) (a : Nat) : Prop :=
  ∀ vs, InvokeOk s a vs → NaNDetCfg P (invoke s a vs)

/-- Per module: every entry is deterministic up to NaN payloads at every reachable call
state. -/
def NaNDetModule (P : Profile) (Entry : Nat → Prop) (s₀ : Store Nat) : Prop :=
  ∀ s, CallReach P Entry s₀ s → ∀ a, Entry a → NaNDetFn P s a

/-- No value of the output is a float NaN. -/
def OutNaNFree : Out → Prop
  | .ret (.values vs) => ∀ v ∈ vs, nanVal v = false
  | .ret _ => True
  | .call _ args => ∀ v ∈ args, nanVal v = false

/-- **The output sink**: every non-trapping output of every run from `c` is NaN-free. -/
def NaNFreeOut (P : Profile) (c : Config Nat) : Prop :=
  ∀ tr d o, Runs P c tr d → OutAt d o → OutNaNFree o

end Silmaril.Wasm.Det.NaN
