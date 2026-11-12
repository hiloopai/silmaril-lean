module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int3.Defs

/-!
# SpecTec ↔ Core 3.0, round 5, track refok: definitions

Track fwd's leaf `Round5.Fwd.RefOkB` asks SpecTec's `Ref_ok`, read declaratively (`DDerives`),
to agree with Core's `RefOk` on typed stores and bounded reference types. This track refutes
it, and finds that the refutation does not need the nested `REC 1` type that pass 2 argued
from.

* **Why `RefOkB` fails.** `DDerives` evaluates a rule's conclusion (`EvalExp`). `Reftype_ok`'s
  only rule concludes `C ⊢ REF NULL? heaptype : OK`. The IL writes `NULL?` as an option
  iteration with no domain variables, `iterE (NULL) (opt [])`, and the evaluator rejects an
  iteration with an empty domain (`Res.assert (ds.isEmpty = false)`). So `Reftype_ok` is never
  derivable, and `Ref_ok/sub` never fires: the only `Ref_ok` type of `REF.NULL_ADDR` is
  `REF NULL BOT`. Core's `RefOk s .null (REF NULL ANY)` holds by `RefOk.sub`.
* **The restriction fails too.** The type `REF NULL ANY` is Core-valid and closed, and the empty
  store is Core-valid and has a typed image. So `RefOkBV`, the restriction of `RefOkB` to
  Core-valid stores and Core-valid closed types, is false as well.
* **The nested `REC 1` type is not a counterexample.** On the nested type (`nestedRT`) both sides
  fail at `null`: SpecTec's because `Ref_ok/sub` never fires, Core's because
  `TyOk {} nestedRT` fails.
* **The `Open` variant without `refOk`.** `Open5` is `Round5.Int3.Open4` with `refOk` replaced by
  the cast-rule obligations it was used for: forward (`CastsFwd`, the four cast fields of
  `Round5.Fwd.Rest`) and backward (`CastsBwd`, `Step_read` 2–5 and 65–68). It is no stronger
  than `Open4`. The forward obligation is argued false at
  `ref.null; ref.test (ref null any)`, and `Open5` is unsatisfiable through `simd` anyway.

See `docs/projects/spectec/README.md`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.RefOk

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4Int (BI)
open Round4 (Bounded)

variable {H : Type}

/-! ## The reference types of the counterexamples -/

/-- `REF NULL ANY`: Core-valid, closed and bounded, and Core types `null` at it through
`RefOk.sub`. -/
def nullAny : CRefType := .ref true (.abs .any)

/-- The inner group's subtype, `SUB FINAL (STRUCT (CONST (REF NULL (REC 1))))`. Its `REC 1`
points past its own one-element group. -/
def stIn : CSubType :=
  .sub true .nil (.struct (.cons (.field .const (.val (.refv (.ref true (.use (.recv 1)))))) .nil))

/-- `D_in := _DEF (REC stIn) 0`. -/
def dIn : DefType := .defn (.group (.cons stIn .nil)) 0

/-- The outer group's subtype, `SUB FINAL (STRUCT (CONST (REF NULL D_in)))`. -/
def stOut : CSubType :=
  .sub true .nil (.struct (.cons (.field .const (.val (.refv (.ref true (.use (.dt dIn)))))) .nil))

/-- `D_out := _DEF (REC stOut) 0`. -/
def dOut : DefType := .defn (.group (.cons stOut .nil)) 0

/-- `REF NULL D_out`, the nested type that pass 2 argued `RefOkB` false at. -/
def nestedRT : CRefType := .ref true (.use (.dt dOut))

/-! ## The restriction to Core-valid stores and closed types -/

/-- **`Fwd.RefOkB` restricted to Core-valid stores and Core-valid closed types**: `Ref_ok` is
`RefOk` at one store and reference type, when the store is valid in Core (`StoreOk`), its image
is typed, and the type is bounded and valid in the empty context (`TyOk {}`). False
(`not_refOkBV`). -/
structure RefOkBV (env : Env) : Prop where
  /-- On a Core-valid, typed store and a Core-valid, closed, bounded reference type. -/
  refOk : ∀ {H : Type} (hn : H → String) (s : Store H) (rt : CRefType),
    TypedV env storeT (storeV hn s) → StoreOk s → Round4.tyBnd rt = true → TyOk {} rt →
      Fwd.RefOkAt env hn s rt

/-! ## The cast-rule obligations `RefOkB` was used for -/

/-- **The cast rules, forward**: the four cast fields of `Round5.Fwd.Rest` (`ref.test`,
`ref.cast`, `br_on_cast`, `br_on_cast_fail`), which `Round5.Fwd.rest_of` proves from
`Fwd.RefOkB`. -/
structure CastsFwd (B : Builtins) (hn : H → String) : Prop where
  /-- `ref.test`. -/
  refTest : ∀ (s : Store H) (f : Frame) (r : Ref) (rt : RefType),
    Bounded ⟨s, f, [.ref r, .plain (.refTest rt)]⟩ →
    (RefOk s r (f.module.instRef rt) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩ ⟨s, f, [constI32 1]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩ ⟨s, f, [constI32 0]⟩)
  /-- `ref.cast`. -/
  refCast : ∀ (s : Store H) (f : Frame) (r : Ref) (rt : RefType),
    Bounded ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ →
    (RefOk s r (f.module.instRef rt) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ ⟨s, f, [.ref r]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ ⟨s, f, [.trap]⟩)
  /-- `br_on_cast`. -/
  brOnCast : ∀ (s : Store H) (f : Frame) (r : Ref) (l : LabelIdx) (rt₁ rt₂ : RefType),
    Bounded ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩ →
    (RefOk s r (f.module.instRef rt₂) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r, .plain (.br l)]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt₂) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩ ⟨s, f, [.ref r]⟩)
  /-- `br_on_cast_fail`. -/
  brOnCastFail : ∀ (s : Store H) (f : Frame) (r : Ref) (l : LabelIdx) (rt₁ rt₂ : RefType),
    Bounded ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩ →
    (RefOk s r (f.module.instRef rt₂) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩ ⟨s, f, [.ref r]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt₂) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r, .plain (.br l)]⟩)

/-- **The cast rules, backward**: `Step_read` 2–5 and 65–68 (`Round5.Read.readDoneK`), under
`ReadValidS`, which `Round5.Read.read_doneK` proves from `Fwd.RefOkB`. -/
def CastsBwd (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ i ∈ Round5.Read.readDoneK, ∀ (c : Config H) (w : Value), Round5.Read.ReadValidS c →
    Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩

/-- **`Round5.Int3.Open4` without `refOk`**: the cast-rule obligations take its place. -/
structure Open5 (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- Typing of the SIMD instructions other than `v128.const`. False for every
  builtins: `Round5.SimdTy.not_simdTyping`. -/
  simd : Pos.SimdTyping (BI P hn host)
  /-- The lane-wise vector operators agree with Core. False under the spec NaN
  profile: `Round5.Simd.not_vecAgreeOps_spec`. -/
  vecOps : Simd.VecAgreeOps (simEnv (BI P hn host)) P
  /-- The cast rules, forward. Argued false at `ref.null; ref.test (ref null any)`: Core tests
  true, and SpecTec's `ref.test-true` cannot fire. -/
  castsFwd : CastsFwd (BI P hn host) hn
  /-- The cast rules, backward. -/
  castsBwd : CastsBwd hn P host

end Silmaril.Wasm.SpecTec.Sim.Round5.RefOk
