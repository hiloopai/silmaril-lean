module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdSimdAgg.Bitwise
public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdSimdAgg.InitElem

/-!
# Track `fwd-simd-agg`: the vector and aggregate cases of the widened fragment

`fwd_vector_wide` and `fwd_aggregate_wide` are the `VectorStep` and `AggregateStep` cases of
`Integrate.forward_wide` on `Integrate.CodeOk` code, after this track's additions:

* vectors: the four bitwise constructors (`Bitwise.lean`); every other `VectorStep` constructor
  starts at an instruction `Integrate.Instr.Open` still lists;
* aggregates: family R's and the aggregates track's constructors (`Aggregates.fwd_aggregate`'s
  arms), plus `struct.new_default`, `array.new_default` (`NewDefault.lean`) and `array.copy-le`,
  `array.copy-gt`, `array.init_elem-succ` (`Copy.lean`). Still open: `array.new_elem`,
  `array.new_data`, `array.init_data` (slices; obstruction 2) and packed fields (`Unpacked`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Aggregates
open RefsGC (RTyping RStoreFuns)

variable {H : Type} {hn : H → String} {B : Builtins} {P : Numerics.Profile}

/-- Every instruction of `CodeOk` code is closed. -/
theorem codeOk_mem {l : List Admin} (h : Integrate.CodeOk l) {a : Admin} (ha : a ∈ l) :
    Integrate.Admin.Open a = false :=
  match l, h, ha with
  | _ :: _, .cons hb _ _ _, .head _ => hb
  | _ :: _, .cons _ _ _ hl, .tail _ hm => codeOk_mem hl hm

/-- Code holding an open instruction is not `CodeOk`. -/
theorem not_codeOk {l : List Admin} (he : ∃ a ∈ l, Integrate.Admin.Open a = true) :
    ¬ Integrate.CodeOk l := fun h => by
  obtain ⟨a, hm, ho⟩ := he
  have := codeOk_mem h hm
  rw [ho] at this
  exact Bool.noConfusion this

/-- **The vector case of the widened fragment**: the bitwise operators, through their rules; every
other `VectorStep` constructor starts at an open instruction. -/
theorem fwd_vector_wide (hI : IntNumeric.IntB B) (hV : VVB B) {s : Store H} {f : Frame}
    {is is' : List Admin} (h : VectorStep P is is') (hc : Integrate.CodeOk is) :
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  cases h with
  | vecUnOp op a => exact fwd_vecUnOp hV op a
  | vecBinOp op a b => exact fwd_vecBinOp hI hV op a b
  | vecTernOp op a b c => exact fwd_vecTernOp hV op a b c
  | vecTestOp op a => exact fwd_vecTestOp op a
  | _ => exact absurd hc (not_codeOk (by simp [Integrate.Admin.Open, Integrate.Instr.Open]))

/-- The aggregate instructions still outside the fragment: `array.new_elem`, `array.new_data`,
`array.init_data` (they read a slice or need the `$zbytes_` family). -/
def AggOpenW : Admin → Bool
  | .plain (.arrayNewElem ..) | .plain (.arrayNewData ..) | .plain (.arrayInitData ..) => true
  | _ => false

theorem aggOpenW_of_open {a : Admin} (h : Integrate.Admin.Open a = false) : AggOpenW a = false := by
  cases a with
  | plain i => cases i <;> simp_all [Integrate.Admin.Open, Integrate.Instr.Open, AggOpenW]
  | _ => rfl

/-- **The aggregate case of the widened fragment**, for any code whose instructions are not
`AggOpenW` (used by `Integrate.forward_wide` and by `forward_upTo`). -/
theorem fwd_aggregate_wide' (hV : VVB B) (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B))
    (G : RStoreFuns (simEnv B)) (A : AggTypes (simEnv B)) {c c' : Config H}
    (h : AggregateStep c c') (hb : Bounded c.store) (hu : Unpacked c.frame)
    (hc : ∀ a ∈ c.code, AggOpenW a = false) : FwdP (simEnv B) hn c c' := by
  cases h with
  | structNew hd he hn _ => exact fwd_structNew_u T R A hu hd he hn
  | structNewDefault hd he hdef => exact fwd_structNewDefault T R A hu hd he hdef
  | structGetNull => exact fwd_structGetNull T R G
  | structGetStruct hs hf hd he hi hu' => exact fwd_structGetStruct_u T R A hu hs hf hd he hi hu'
  | structSetNull => exact fwd_structSetNull T R G
  | structSetStruct hd he hi hs hf _ => exact fwd_structSetStruct_u T R A hu hd he hi hs hf
  | arrayNew v n => exact fwd_arrayNew T R v n
  | arrayNewDefault hd he hv => exact fwd_arrayNewDefault T R A hu hd he hv
  | arrayNewFixed hd he hn _ => exact fwd_arrayNewFixed_u T R A hu hd he hn
  | arrayGetNull => exact fwd_arrayGetNull T R G
  | arrayGetOob ha hl => exact fwd_arrayGetOob T R G ha hl
  | arrayGetArray ha hf hd he hu' => exact fwd_arrayGetArray_u T R A hu ha hf hd he hu'
  | arraySetNull => exact fwd_arraySetNull T R G
  | arraySetOob ha hl => exact fwd_arraySetOob T R G ha hl
  | arraySetArray ha hl hd he _ => exact fwd_arraySetArray_u T R A hu ha hl hd he
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
    exact FwdSimdAgg.fwd_arrayCopyLe hV T R G A hu hb ha₁ ha₂ hl hn0 hd he hle
  | arrayCopyGt ha₁ ha₂ hl hn0 hd he hgt =>
    exact FwdSimdAgg.fwd_arrayCopyGt hV T R G A hu hb ha₁ ha₂ hl hn0 hd he hgt
  | arrayInitElemNull => exact fwd_arrayInitElemNull T R G
  | arrayInitElemOob₁ ha hl => exact fwd_arrayInitElemOob₁ T R G ha hl
  | arrayInitElemOob₂ he hl => exact fwd_arrayInitElemOob₂ T R G he hl
  | arrayInitElemZero ha he hl => exact fwd_arrayInitElemZero T R G ha he hl
  | arrayInitElemSucc ha he hl hn0 hr =>
    exact FwdSimdAgg.fwd_arrayInitElemSucc T R G hb ha he hl hn0 hr
  | arrayNewElemOob | arrayNewElemAlloc | arrayNewDataOob | arrayNewDataNum
  | arrayInitDataNull | arrayInitDataOob₁ | arrayInitDataOob₂ | arrayInitDataZero
  | arrayInitDataNum =>
    exact absurd hc (by simp [AggOpenW])

/-- **The aggregate case of the widened fragment.** -/
theorem fwd_aggregate_wide (hV : VVB B) (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B))
    (G : RStoreFuns (simEnv B)) (A : AggTypes (simEnv B)) {c c' : Config H}
    (h : AggregateStep c c') (hb : Bounded c.store) (hu : Unpacked c.frame)
    (hc : Integrate.CodeOk c.code) : FwdP (simEnv B) hn c c' :=
  fwd_aggregate_wide' hV T R G A h hb hu fun _ ha => aggOpenW_of_open (codeOk_mem hc ha)

/-- **The concrete `B` answers `vvCall`**: `$inot_`, `$iandnot_`, `$ibitselect_` and `$sx` are
neither float nor integer primitives, so `Prims.call` reaches its `vvCall` arms. -/
theorem vvB_builtins {prof : Numerics.Profile} (hn : H → String) (host : HostSemantics H) :
    VVB (Prims.builtins prof hn host) := by
  intro x ws v h
  show Prims.call prof hn host x ws = some v
  unfold vvCall at h
  split at h <;> first
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | simp [Prims.call, Floats.floatCall, Floats.floatNames, IntNumeric.intCall, vvCall, h]

end Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg
