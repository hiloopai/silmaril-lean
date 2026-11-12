module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Defs

/-!
# SpecTec ↔ Core 3.0, round 6, track memsimd: definitions

Two leftovers of round 5 (`docs/projects/spectec/README.md`, items 3 and 4).

**Memory SIMD (`Step` 22–25, `Step_read` 42–51).** `Sim.instrToV` still sends `vecLoad`,
`vecLoadLane`, `vecStore` and `vecStoreLane` through the provisional `schemaInstrV`, whose memory
argument is a `$record` *case*, not the IL record `memarg`. This header adds, without changing
`instrToV`:

* `memSimd i`: `i` is one of the four memory SIMD instructions; `instrMS`/`instrsMS`: none occurs
  in `i`, at any depth of block bodies; `AdminMS`, `StoreMS`, `NoMemSimd c`: none occurs in the
  code of `c` (at every depth) or in a Wasm function body of its store. This is **the explicit
  exclusion** of memory SIMD from the domain of the round-6 target: `Round4.Bounded` already
  implies it (`Round6.MemSimd.noMemSimd_of_bounded`), because `Round4.instrBnd` rejects the four
  constructors.
* `vecLoadOpV`, `vecMemV`, `instrToVM`: **an IL encoding of the four instructions written against
  the IL type `instr`** (`VLOAD vectype vloadop_(vectype)? memidx memarg`, `VLOAD_LANE vectype sz
  memidx memarg laneidx`, `VSTORE vectype memidx memarg`, `VSTORE_LANE vectype sz memidx memarg
  laneidx`, definition 271 of the fixed script), as an additive layer: `instrToVM` is `instrToV`
  except at the four constructors.

**U7 (`$utf8`).** `withUtf8 B` answers `$utf8` with the UTF-8 encoding of a list of characters
and is `B` elsewhere. Round 5 proved that no builtin can give `$utf8` a value in `simEnv B`
(`callDef` consults `B` only on `undef`, and the first clause of `$utf8` loops to `outOfFuel`);
round 6 restates that for `withUtf8` (`Round6.MemSimd.not_typedV_moduleinst_withUtf8`) and lifts
it to the forward conjunct (`Round6.MemSimd.not_forwardSelE`), so the `NoExports` restriction
cannot be dropped from a target read in `simEnv`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.Execution (pctV)

variable {H : Type}

/-! ## The exclusion -/

/-- **One of the four memory SIMD instructions.** -/
def memSimd : Instr → Bool
  | .vecLoad .. | .vecLoadLane .. | .vecStore .. | .vecStoreLane .. => true
  | _ => false

mutual
/-- **No memory SIMD instruction in `i`**, block bodies included. -/
def instrMS : Instr → Bool
  | .block _ body => instrsMS body
  | .loop _ body => instrsMS body
  | .if_ _ b₁ b₂ => instrsMS b₁ && instrsMS b₂
  | .tryTable _ _ body => instrsMS body
  | i => !memSimd i

/-- `instrMS` on a sequence. -/
def instrsMS : List Instr → Bool
  | [] => true
  | i :: is => instrMS i && instrsMS is
end

mutual
/-- No memory SIMD instruction inside an administrative instruction, at any depth. -/
def AdminMS : Admin → Prop
  | .plain i => instrMS i = true
  | .label _ cont body => instrsMS cont = true ∧ AdminsMS body
  | .handler _ _ body => AdminsMS body
  | .frame _ _ body => AdminsMS body
  | _ => True

/-- `AdminMS` on a sequence. -/
def AdminsMS : List Admin → Prop
  | [] => True
  | a :: l => AdminMS a ∧ AdminsMS l
end

/-- No Wasm function body of the store has a memory SIMD instruction. -/
def StoreMS (s : Store H) : Prop :=
  ∀ fi ∈ s.funcs, ∀ fn, fi.code = .wasm fn → instrsMS fn.body = true

/-- **No memory SIMD instruction occurs in the configuration**: the explicit exclusion of
`Step` 22–25 and `Step_read` 42–51 from the round-6 domain. -/
structure NoMemSimd (c : Config H) : Prop where
  /-- The function bodies of the store. -/
  store : StoreMS c.store
  /-- The code, at every depth. -/
  code : AdminsMS c.code

/-! ## An IL encoding of the memory SIMD instructions (additive) -/

/-- `vloadop_(V128)?`: `none` for `v128.load`, otherwise `SHAPE sz X M _ sx`, `SPLAT sz` (a bare
`sz` payload, the case type being `varT "sz"`) or `ZERO sz`. -/
def vecLoadOpV : VecLoadOp → Option Value
  | .full => none
  | .extend8x8 s => some (.case "SHAPE%X%_%" (.tuple [pctV 8, pctV 8, Vec.sxV s]))
  | .extend16x4 s => some (.case "SHAPE%X%_%" (.tuple [pctV 16, pctV 4, Vec.sxV s]))
  | .extend32x2 s => some (.case "SHAPE%X%_%" (.tuple [pctV 32, pctV 2, Vec.sxV s]))
  | .splat p => some (.case "SPLAT" (szV p))
  | .zero32 => some (.case "ZERO" (.tuple [pctV 32]))
  | .zero64 => some (.case "ZERO" (.tuple [pctV 64]))

/-- **The IL image of a memory SIMD instruction**, against the IL type `instr`; `none` on every
other instruction. The memory argument is the IL record `memargV`, as for `LOAD`/`STORE`. -/
def vecMemV : Instr → Option Value
  | .vecLoad op m a => some (.case "VLOAD"
      (.tuple [Vec.vecTypeV, .opt (vecLoadOpV op), Encode.toValue m, memargV a]))
  | .vecLoadLane p m a l => some (.case "VLOAD_LANE"
      (.tuple [Vec.vecTypeV, szV p, Encode.toValue m, memargV a, Vec.laneIdxV l]))
  | .vecStore m a => some (.case "VSTORE" (.tuple [Vec.vecTypeV, Encode.toValue m, memargV a]))
  | .vecStoreLane p m a l => some (.case "VSTORE_LANE"
      (.tuple [Vec.vecTypeV, szV p, Encode.toValue m, memargV a, Vec.laneIdxV l]))
  | _ => none

/-- **`instrToV` with the memory SIMD instructions encoded against `instr`** (additive; the
simulation proper still uses `instrToV`). -/
def instrToVM (i : Instr) : Value := (vecMemV i).getD (instrToV i)

/-! ## U7: a `$utf8` builtin -/

/-- The bytes of a character given by its code point, as `byte` values. -/
def utf8CharV (n : Nat) : List Value :=
  (String.utf8EncodeChar (Char.ofNat n)).map fun b => pctV b.toNat

/-- The code point of a `char` value. -/
def charCode? : Value → Option Nat
  | .case "%" (.tuple [.num (.natN n)]) => some n
  | _ => none

/-- `$utf8(char*)`, read functionally: the concatenated UTF-8 bytes of the characters. -/
def utf8Call : List ArgV → Option Value
  | [.val (.list cs)] =>
      (cs.mapM charCode?).map fun ns => .list (ns.flatMap utf8CharV)
  | _ => none

/-- **`B` with `$utf8` answered by `utf8Call`** (upstream item U7, as round 4 planned it). -/
def withUtf8 (B : Builtins) : Builtins :=
  ⟨fun x ws => if x = "utf8" then utf8Call ws else B.call x ws⟩

/-- **`Target.BoundedSel` without `NoExports`**: bounded and free of `FloatMissel` code. The
domain a target would have if U7 allowed dropping the export-free restriction. -/
def BoundedSelE (c : Config H) : Prop := Round4.Bounded c ∧ Round5.Target.NoMissel c

/-- **`Round5.Task.wholeStepValidSel` with `NoExports` dropped** (`BoundedSelE` for
`Target.BoundedSel`), at a given `B` per host and profile. Refuted for every choice of `B`
(`Round6.MemSimd.not_wholeStepValidSelE`), so in particular for `withUtf8`. -/
def WholeStepValidSelE : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host →
      ∀ (nd : Bool) (r : Numerics.RelaxedChoice), ∃ B : Builtins,
        (∀ (c c' : Config H) (ts : List Validation.CValType), ConfigOk c ts → BoundedSelE c →
          BoundedSelE c' → Step (Numerics.Profile.spec nd r) host c c' →
          ∃ d', Bwd.ConfigEq c' d' ∧ SStep (simEnv B) (configV hn c) (configV hn d')) ∧
        (∀ (c : Config H) (ts : List Validation.CValType) (w : Value), ConfigOk c ts →
          BoundedSelE c → SStep (simEnv B) (configV hn c) w →
          ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧
            Step (Numerics.Profile.spec nd r) host c c')

end Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd
