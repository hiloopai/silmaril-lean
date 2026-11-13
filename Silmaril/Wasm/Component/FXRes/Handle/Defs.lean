module

public import Silmaril.Wasm.Component.FXRes.Defs
public import Silmaril.Wasm.Resource.Table.Defs

/-!
# Continuations as Component Model resources: `own<cont>` and `borrow<cont>` handles

A component exposes a continuation through the Component Model as a **resource handle** of a
resource type `cont`: an `i32` index into a Canonical ABI handle table
(`Silmaril.Wasm.Component.Runtime.Table`) whose entries are continuations. This module gives the
canonical built-ins of that resource type over the WasmFX semantics with continuation values
(`StepFX'`), and the joint system of FX steps and built-ins.

* `JState H`: the handle table of the `cont` resource and an FX configuration.
* `handleVal h`: a handle as an `i32` constant of FX code.
* `RStep st o ev sevs st'`: the canonical built-in `o` (`ROp`), acting on the head of the code:
  * `new` (`resource.new`, lowering an `own<cont>`): the live continuation `k` named by the
    `contRef k` at the head **moves** from the continuation store into the table (the store
    entry is consumed, so a stale `contRef k` traps), and the code gets its handle;
  * `take` (lifting an `own<cont>` back into a continuation): the handle at the head is removed
    from the table and its continuation gets a fresh store index, which replaces the handle;
  * `drop` (`resource.drop` of an `own<cont>`): the handle is removed and popped; the
    continuation is discarded without being resumed;
  * `borrow` (reading a `borrow<cont>`): a table lookup only; nothing changes.
  `ev` is the table event (`Table.Event`), `sevs` the continuation-store events (`HEv ℕ`, as in
  `KStep`).
* `JStep`, `JSteps`: the joint system, FX steps (the table unchanged, store events from `KStep`)
  interleaved with built-ins, with the table history and the store history.
* `ownEv`: the table events as ownership events (`OEv ℕ`, `Silmaril.Wasm.Resource.Handle`): `new`
  hands the program an owned handle (`alloc`), `take` and `drop` end its ownership (`free`),
  `borrow` uses it.

Theorems (`Silmaril.Wasm.Component.FXRes.Handle.Thms`): the table history of every joint run is
accepted by the handle protocol in both roles and its ownership history by `obProto`; the store
history stays one-shot; a handle is dead after `take` or `drop`; a borrow consumes nothing.

Modelling choice: the built-ins are rules of a joint relation over one FX configuration, not yet
host calls of the threads of the WasmFX component engine `fxEV` (whose host calls pass flat Core
values, so a `contRef` cannot reach the host there).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Resource
open Silmaril.Wasm.Component.Runtime (Table)
open Silmaril.Wasm.Numerics (Profile)

/-- The handle table of the `cont` resource and an FX configuration. -/
structure JState (H : Type) where
  tab : Silmaril.Wasm.Component.Runtime.Table ContFX
  cfg : ConfigFX H

/-- A handle as an `i32` constant of FX code. -/
def handleVal (h : ℕ) : AdminFX := .core (constI32 (BitVec.ofNat 32 h))

/-- The canonical built-ins of the `cont` resource type. -/
inductive ROp where
  | new
  | take
  | drop
  | borrow
  deriving DecidableEq, Repr

variable {H : Type}

/-- **The canonical built-ins of the `cont` resource**, on the head of the code. -/
inductive RStep : JState H → ROp → Table.Event ContFX → List (HEv ℕ) → JState H → Prop where
  | new {t t' : Silmaril.Wasm.Component.Runtime.Table ContFX} {s : Store H} {K : KStore} {f : Frame} {k h : ℕ} {C : ContFX}
      {rest : List AdminFX} (hk : K[k]? = some (some C)) (ht : t.add? C = some (h, t')) :
      RStep ⟨t, ⟨s, K, f, .contRef k :: rest⟩⟩ .new (.added h C) [.free k]
        ⟨t', ⟨s, K.set k none, f, handleVal h :: rest⟩⟩
  | take {t t' : Silmaril.Wasm.Component.Runtime.Table ContFX} {s : Store H} {K : KStore} {f : Frame} {b : BitVec 32}
      {C : ContFX} {rest : List AdminFX} (ht : t.remove? b.toNat = some (C, t')) :
      RStep ⟨t, ⟨s, K, f, .core (constI32 b) :: rest⟩⟩ .take (.removed b.toNat C) [.alloc K.length]
        ⟨t', ⟨s, K ++ [some C], f, .contRef K.length :: rest⟩⟩
  | drop {t t' : Silmaril.Wasm.Component.Runtime.Table ContFX} {s : Store H} {K : KStore} {f : Frame} {b : BitVec 32}
      {C : ContFX} {rest : List AdminFX} (ht : t.remove? b.toNat = some (C, t')) :
      RStep ⟨t, ⟨s, K, f, .core (constI32 b) :: rest⟩⟩ .drop (.removed b.toNat C) []
        ⟨t', ⟨s, K, f, rest⟩⟩
  | borrow {t : Silmaril.Wasm.Component.Runtime.Table ContFX} {s : Store H} {K : KStore} {f : Frame} {b : BitVec 32}
      {C : ContFX} {rest : List AdminFX} (ht : t.get? b.toNat = some C) :
      RStep ⟨t, ⟨s, K, f, .core (constI32 b) :: rest⟩⟩ .borrow (.got b.toNat C) []
        ⟨t, ⟨s, K, f, .core (constI32 b) :: rest⟩⟩

/-- **The joint system**: FX steps and canonical built-ins. -/
inductive JStep (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) :
    JState H → List (Table.Event ContFX) → List (HEv ℕ) → JState H → Prop where
  | fx {t : Silmaril.Wasm.Component.Runtime.Table ContFX} {c c' : ConfigFX H} {sevs : List (HEv ℕ)}
      (h : StepFX' P host fx c c') (hk : KStep c.conts c'.conts sevs) :
      JStep P host fx ⟨t, c⟩ [] sevs ⟨t, c'⟩
  | op {st st' : JState H} {o : ROp} {ev : Table.Event ContFX} {sevs : List (HEv ℕ)}
      (h : RStep st o ev sevs st') : JStep P host fx st [ev] sevs st'

/-- Runs of the joint system, with their table and store histories. -/
inductive JSteps (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) :
    JState H → List (Table.Event ContFX) → List (HEv ℕ) → JState H → Prop where
  | refl (st : JState H) : JSteps P host fx st [] [] st
  | cons {st₁ st₂ st₃ : JState H} {t₁ t₂ : List (Table.Event ContFX)} {e₁ e₂ : List (HEv ℕ)}
      (h : JStep P host fx st₁ t₁ e₁ st₂) (r : JSteps P host fx st₂ t₂ e₂ st₃) :
      JSteps P host fx st₁ (t₁ ++ t₂) (e₁ ++ e₂) st₃

/-- A handle event as an ownership event of the program holding the handles: allocation hands it
an owned handle, use needs a held handle, and freeing (`take` or `drop`) needs an owned one. -/
def hevOwn : HEv ℕ → OEv ℕ
  | .alloc h => .alloc h
  | .use h => .use h
  | .free h => .free h
  | .skip => .skip

/-- The table events of the `cont` resource as ownership events. -/
def ownEv (ev : Table.Event ContFX) : OEv ℕ := hevOwn (tableEv ev)

end Silmaril.Wasm.Component.FXRes
