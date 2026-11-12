module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.R4Fwd.NewElem
public import Silmaril.Proofs.Wasm.SpecTec.Sim.R4Fwd.PackedArms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.R4Fwd.PackedAlloc
public import Silmaril.Proofs.Wasm.SpecTec.Sim.R4Fwd.PackedCopy
public import Silmaril.Proofs.Wasm.SpecTec.Sim.R4Fwd.PackedDefault
public import Silmaril.Proofs.Wasm.SpecTec.Sim.R4Fwd.NewData
public import Silmaril.Proofs.Wasm.SpecTec.Sim.R4Fwd.LitTyping

/-!
# The aggregate steps at every frame

`fwd_aggregate_any` is `Forward.aggregate` at `simEnv B` with **no** `Aggregates.Unpacked`
restriction: every `AggregateStep` constructor except `array.new_data-num` and `array.init_data-zero` (taken as
hypotheses) is a SpecTec step of the images, for fields of every storage type.
Compared with `FwdSimdAgg.fwd_aggregate_wide'`:

* the field reads, writes and allocations go through the `*_any`/`*Any` lemmas of this track
  (packed fields by the second clauses of `$packfield_`, `$unpackfield_`, `$unpack`, `$sx`);
* `array.new_elem-alloc` is `fwd_arrayNewElemAlloc` (`NewElem.lean`);
* `array.new_data-oob`, `array.init_data-oob2`, `array.init_data-num` are this track's
  (`NewData.lean`, `InitData.lean`), the last under `ZBytes.ZB B` and `ExpandInv`.

It needs `Floats.FloatB P B` (for `$wrap__`/`$extend__` at packed widths) besides the hypotheses of
round 2/3.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.R4Fwd

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Aggregates
open RefsGC (RTyping RStoreFuns)

variable {H : Type} {hn : H → String} {B : Builtins} {P : Numerics.Profile}

/-- `array.copy-le`, as a forward obligation, at every element storage type. -/
theorem fwd_arrayCopyLeAny (hV : FwdSimdAgg.VVB B) (T : TypingFacts (simEnv B) hn)
    (R : RTyping (simEnv B)) (G : RStoreFuns (simEnv B)) (A : AggTypes (simEnv B)) {s : Store H}
    {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32} {a₁ a₂ : Nat} {ai₁ ai₂ : ArrayInst}
    {d₂ : DefType} {ft₂ : CFieldType} (hbd : Bounded s)
    (ha₁ : s.arrays[a₁]? = some ai₁) (ha₂ : s.arrays[a₂]? = some ai₂)
    (h : i₁.toNat + n.toNat ≤ ai₁.fields.length ∧ i₂.toNat + n.toNat ≤ ai₂.fields.length)
    (hn0 : n ≠ 0) (hd : f.type? x₂ = some d₂) (he : Expand d₂ (.array ft₂))
    (hle : i₁.toNat ≤ i₂.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n,
      .plain (.arrayCopy x₁ x₂)]⟩
      ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂,
        .plain (.arrayGet (storageSx (fieldStorage ft₂)) x₂), .plain (.arraySet x₁),
        arrRef a₁, constI32 (i₁ + 1), arrRef a₂, constI32 (i₂ + 1), constI32 (n - 1),
        .plain (.arrayCopy x₁ x₂)]⟩ := by
  obtain ⟨m, zt⟩ := ft₂
  refine RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz _ => ?_
  exact sread_arrayCopyLeAny (x₁ := x₁) (hn := hn) hV R G A ha₁ ha₂ h hn0 hd he hle
    (hbd.array ha₁) (hbd.array ha₂) hz

/-- `array.copy-gt`, as a forward obligation, at every element storage type. -/
theorem fwd_arrayCopyGtAny (hV : FwdSimdAgg.VVB B) (T : TypingFacts (simEnv B) hn)
    (R : RTyping (simEnv B)) (G : RStoreFuns (simEnv B)) (A : AggTypes (simEnv B)) {s : Store H}
    {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32} {a₁ a₂ : Nat} {ai₁ ai₂ : ArrayInst}
    {d₂ : DefType} {ft₂ : CFieldType} (hbd : Bounded s)
    (ha₁ : s.arrays[a₁]? = some ai₁) (ha₂ : s.arrays[a₂]? = some ai₂)
    (h : i₁.toNat + n.toNat ≤ ai₁.fields.length ∧ i₂.toNat + n.toNat ≤ ai₂.fields.length)
    (hn0 : n ≠ 0) (hd : f.type? x₂ = some d₂) (he : Expand d₂ (.array ft₂))
    (hgt : i₂.toNat < i₁.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n,
      .plain (.arrayCopy x₁ x₂)]⟩
      ⟨s, f, [arrRef a₁, constI32 (i₁ + n - 1), arrRef a₂, constI32 (i₂ + n - 1),
        .plain (.arrayGet (storageSx (fieldStorage ft₂)) x₂), .plain (.arraySet x₁),
        arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 (n - 1),
        .plain (.arrayCopy x₁ x₂)]⟩ := by
  obtain ⟨m, zt⟩ := ft₂
  refine RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz _ => ?_
  exact sread_arrayCopyGtAny (x₁ := x₁) (hn := hn) hV R G A ha₁ ha₂ h hn0 hd he hgt
    (hbd.array ha₁) (hbd.array ha₂) hz

/-- **The aggregate case at every frame**: every constructor, with `array.new_data-num` and
`array.init_data-zero` taken from the hypotheses `hND`, `hIZ`. -/
theorem fwd_aggregate_any (hF : Floats.FloatB P B) (hV : FwdSimdAgg.VVB B) (Z : ZBytes.ZB B)
    (XI : ExpandInv (simEnv B)) (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B))
    (G : RStoreFuns (simEnv B)) (A : AggTypes (simEnv B)) (hND : NewDataNumObl B hn)
    (hIZ : InitDataZeroObl B hn) {c c' : Config H} (h : AggregateStep c c')
    (hb : Bounded c.store) : FwdP (simEnv B) hn c c' := by
  cases h with
  | structNew hd he hn hp => exact fwd_structNewAny hF T R A hd he hn hp
  | structNewDefault hd he hdef =>
    exact RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz _ =>
      sread_structNewDefaultAny R A hd he hdef hz
  | structGetNull => exact fwd_structGetNull T R G
  | structGetStruct hs hf hd he hi hu' => exact fwd_structGetStruct_any hF T R A hs hf hd he hi hu'
  | structSetNull => exact fwd_structSetNull T R G
  | structSetStruct hd he hi hs hf hp => exact fwd_structSetStruct_any hF T R A hd he hi hs hf hp
  | arrayNew v n => exact fwd_arrayNew T R v n
  | @arrayNewDefault s f x n d ft v hd he hv =>
    obtain ⟨m, zt⟩ := ft
    exact RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz _ =>
      sread_arrayNewDefaultAny R A hd he hv hz
  | @arrayNewFixed s f x n d ft vs hd he hn hp =>
    obtain ⟨m, zt⟩ := ft
    exact fwd_arrayNewFixedAny hF T R A hd he hn hp
  | arrayNewElemOob he hl => exact fwd_arrayNewElemOob T R G he hl
  | arrayNewElemAlloc he hl => exact fwd_arrayNewElemAlloc T R G he hl
  | arrayGetNull => exact fwd_arrayGetNull T R G
  | arrayGetOob ha hl => exact fwd_arrayGetOob T R G ha hl
  | arrayGetArray ha hf hd he hu' => exact fwd_arrayGetArray_any hF T R A ha hf hd he hu'
  | arraySetNull => exact fwd_arraySetNull T R G
  | arraySetOob ha hl => exact fwd_arraySetOob T R G ha hl
  | arraySetArray ha hl hd he hp => exact fwd_arraySetArray_any hF T R A ha hl hd he hp
  | arrayLenNull => exact fwd_arrayLenNull T R G
  | arrayLenArray ha => exact fwd_arrayLenArray T R G ha hb
  | arrayFillNull => exact fwd_arrayFillNull T R G
  | arrayFillOob ha hl => exact fwd_arrayFillOob T R G ha hl
  | arrayFillZero ha hl => exact fwd_arrayFillZero T R G ha hl
  | arrayFillSucc ha hl hn0 => exact fwd_arrayFillSucc T R G ha hl hn0 hb
  | arrayCopyNull₁ => exact fwd_arrayCopyNull₁ T R G
  | arrayCopyNull₂ => exact fwd_arrayCopyNull₂ T R G
  | arrayCopyOob₁ ha hl => exact fwd_arrayCopyOob₁ T R G ha hl
  | arrayCopyOob₂ ha hl => exact fwd_arrayCopyOob₂ T R G ha hl
  | arrayCopyZero ha₁ ha₂ hl => exact fwd_arrayCopyZero T R G ha₁ ha₂ hl
  | arrayCopyLe ha₁ ha₂ hl hn0 hd he hle =>
    exact fwd_arrayCopyLeAny hV T R G A hb ha₁ ha₂ hl hn0 hd he hle
  | arrayCopyGt ha₁ ha₂ hl hn0 hd he hgt =>
    exact fwd_arrayCopyGtAny hV T R G A hb ha₁ ha₂ hl hn0 hd he hgt
  | arrayInitElemNull => exact fwd_arrayInitElemNull T R G
  | arrayInitElemOob₁ ha hl => exact fwd_arrayInitElemOob₁ T R G ha hl
  | arrayInitElemOob₂ he hl => exact fwd_arrayInitElemOob₂ T R G he hl
  | arrayInitElemZero ha he hl => exact fwd_arrayInitElemZero T R G ha he hl
  | arrayInitElemSucc ha he hl hn0 hr =>
    exact FwdSimdAgg.fwd_arrayInitElemSucc T R G hb ha he hl hn0 hr
  | arrayNewDataOob hd he hdat hz hl => exact fwd_arrayNewDataOob T R A hd he hdat hz hl
  | arrayNewDataNum hd he hdat hz hl hvs => exact hND _ _ _ _ _ _ _ _ _ _ _ hd he hdat hz hl hvs
  | arrayInitDataNull => exact fwd_arrayInitDataNull T R G
  | arrayInitDataOob₁ ha hl => exact fwd_arrayInitDataOob₁ T R G ha hl
  | arrayInitDataOob₂ hd he hdat hz hl => exact fwd_arrayInitDataOob₂ T R A hd he hdat hz hl
  | arrayInitDataZero ha hdat hl => exact hIZ _ _ _ _ _ _ _ _ _ _ ha hdat hl
  | arrayInitDataNum ha hd he hdat hl hn0 hv =>
    exact fwd_arrayInitDataNum hF Z XI (litTyping_simEnv B) T R G A hb ha hd he hdat hl hn0 hv

end Silmaril.Wasm.SpecTec.Sim.R4Fwd
