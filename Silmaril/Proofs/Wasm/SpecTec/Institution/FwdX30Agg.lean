module

public import Silmaril.Wasm.SpecTec.Institution.FwdX30.Defs
public import Silmaril.Wasm.SpecTec.Sim.Aggregates.Thms
public import Silmaril.Wasm.SpecTec.Sim.R4Fwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5Fwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms
public import Silmaril.Wasm.SpecTec.Sim.Prims.Thms

/-!
# The forward direction at wasm-3.0, extended: the aggregate rules of `Step_read`

At the concrete primitives `Round4Int.BI`, every `AggregateStep` whose instruction is a
`Step_read` instruction (`aggReadInstr`: `struct.new_default`, `struct.get`,
`array.new_default`, `array.new_elem`, `array.new_data`, `array.get`, `array.len`, `array.fill`,
`array.copy`, `array.init_elem`, `array.init_data`) is a `Step_read` fact of the declarative
reading, from a typed configuration that is bounded 's sense.

The arms are the bodies of `Round5.Fwd.fwd_aggregate5`'s leaves (`Aggregates.fwd_*`,
`Round5.Fwd.fwd_*B`, `R4Fwd.fwd_arrayNewElemAlloc`, `FwdSimdAgg.fwd_arrayInitElemSucc`,
`Round5.FwdRef.fwd_arrayNewDataNumB`, `Round5.Fwd.fwd_arrayInitDataZero5`), stopped before the
leaf lifts the fact with `Step/read`: each is `RefsGC.fwd_of_sread T _ fun hz hc => t` and the
arm here is `t`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdX30

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim
open RefsGC (RTyping RStoreFuns)
open Round4Int (BI)

variable {H : Type} {P : Profile} (hn : H → String) (host : HostSemantics H)

/-- `array.get` at an array, at every storage type (`Round5.Fwd.fwd_arrayGetArray_anyB`). -/
theorem sreadL_arrayGetArray {s : Store H} {f : Frame} [Fact (Round4.ModuleBnd f.module)]
    {sx : Option Signedness} {x : TypeIdx} {i : BitVec 32} {a : Nat} {ai : ArrayInst}
    {fv : FieldVal} {d : DefType} {ft : CFieldType}
    (ha : s.arrays[a]? = some ai) (hf : ai.fields[i.toNat]? = some fv)
    (hd : f.type? x = some d) (he : Expand d (.array ft))
    (hu' : unpackable (fieldStorage ft) sx fv = true)
    (hz : TypedV (simEnv (BI P hn host)) stateT (stateV hn s f)) :
    SRead (simEnv (BI P hn host)) (configV hn ⟨s, f, [arrRef a, constI32 i, .plain (.arrayGet sx x)]⟩)
      (adminsToV [(unpackField sx fv).toAdmin]) := by
  have hF : Floats.FloatB P (BI P hn host) := Prims.floatB_builtins hn host
  have R : RTyping (simEnv (BI P hn host)) := Typing.rTyping_simEnv _
  have A : Round5.Fwd.AggTypesB (simEnv (BI P hn host)) :=
    Round5.Fwd.aggTypesB_of (Round5.Int.typesB _)
  cases ft with | field m zt => ?_
  cases zt with
  | val t =>
    obtain ⟨rfl, v, rfl⟩ := Aggregates.unpackable_val hu'
    simpa only [unpackField] using Round5.Fwd.sread_arrayGetArrayValB (hn := hn)
      (Aggregates.rd _).arrayGetArray R (Aggregates.aggDefs_simEnv _)
      (State.stateDefs_simEnv _) A (Aggregates.unpackDef_simEnv _) ha hf hd he hz
  | pack p =>
    show SRead (simEnv (BI P hn host)) (configV hn _) (adminsToV [(unpackField sx fv).toAdmin])
    cases sx with
    | none => cases fv <;> simp [unpackable, fieldStorage] at hu'
    | some sx =>
      cases fv with
      | val _ => simp [unpackable, fieldStorage] at hu'
      | pack p' c =>
        obtain rfl : p = p' := by simpa [unpackable, fieldStorage] using hu'
        exact Round5.Fwd.sread_arrayGetArrayPackB hF R A ha hf hd he hz

/-- `struct.get` at a struct, at every storage type (`Round5.Fwd.fwd_structGetStruct_anyB`). -/
theorem sreadL_structGetStruct {s : Store H} {f : Frame} [Fact (Round4.ModuleBnd f.module)]
    {sx : Option Signedness} {x : TypeIdx} {i : FieldIdx} {a : Nat} {si : StructInst}
    {fv : FieldVal} {d : DefType} {fs : Silmaril.Wasm.Validation.Ty (.list .field)} {ft : CFieldType}
    (hs : s.structs[a]? = some si) (hf : si.fields[i.toNat]? = some fv)
    (hd : f.type? x = some d) (he : Expand d (.struct fs)) (hi : fs.toList[i.toNat]? = some ft)
    (hu' : unpackable (fieldStorage ft) sx fv = true)
    (hz : TypedV (simEnv (BI P hn host)) stateT (stateV hn s f)) :
    SRead (simEnv (BI P hn host))
      (configV hn ⟨s, f, [.ref (.struct a), .plain (.structGet sx x i)]⟩)
      (adminsToV [(unpackField sx fv).toAdmin]) := by
  have hF : Floats.FloatB P (BI P hn host) := Prims.floatB_builtins hn host
  have R : RTyping (simEnv (BI P hn host)) := Typing.rTyping_simEnv _
  have A : Round5.Fwd.AggTypesB (simEnv (BI P hn host)) :=
    Round5.Fwd.aggTypesB_of (Round5.Int.typesB _)
  cases ft with | field m zt => ?_
  cases zt with
  | val t =>
    obtain ⟨rfl, v, rfl⟩ := Aggregates.unpackable_val hu'
    simpa only [unpackField] using Round5.Fwd.sread_structGetStructValB (hn := hn)
      (Aggregates.rd _).structGetStruct R (Aggregates.aggDefs_simEnv _)
      (State.stateDefs_simEnv _) A (Aggregates.unpackDef_simEnv _) hs hf hd he hi hz
  | pack p =>
    show SRead (simEnv (BI P hn host)) (configV hn _) (adminsToV [(unpackField sx fv).toAdmin])
    cases sx with
    | none => cases fv <;> simp [unpackable, fieldStorage] at hu'
    | some sx =>
      cases fv with
      | val _ => simp [unpackable, fieldStorage] at hu'
      | pack p' c =>
        obtain rfl : p = p' := by simpa [unpackable, fieldStorage] using hu'
        exact Round5.Fwd.sread_structGetStructPackB hF R A hs hf hd he hi hz

/-- A code whose last instruction fails `p` is not `LastIs p`. -/
theorem not_lastIs' {p : Instr → Bool} {is : List Admin} {j : Instr}
    (h : is.getLast? = some (.plain j)) (hj : p j = false) : ¬ LastIs p is := by
  rintro ⟨i, hi, hp⟩
  have hij : Admin.plain i = Admin.plain j := Option.some.inj (hi.symm.trans h)
  have hij' : i = j := Admin.plain.inj hij
  rw [hij', hj] at hp
  exact Bool.false_ne_true hp

/-- **The aggregate rules of `Step_read`** at `BI`: every `AggregateStep` whose instruction is a
`Step_read` instruction, from a typed configuration bounded 's sense, is a `Step_read`
fact (`Round5.Fwd.fwd_aggregate5` before the lift). -/
theorem sread_of_aggStep {c c' : Config H} (h : AggregateStep c c')
    (hl : LastIs aggReadInstr c.code) (hb : Round4.Bounded c)
    (hc : Typed (simEnv (BI P hn host)) hn c) :
    SRead (simEnv (BI P hn host)) (configV hn c) (adminsToV c'.code) := by
  have hF : Floats.FloatB P (BI P hn host) := Prims.floatB_builtins hn host
  have hV : FwdSimdAgg.VVB (BI P hn host) := FwdSimdAgg.vvB_builtins hn host
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have R : RTyping (simEnv (BI P hn host)) := Typing.rTyping_simEnv _
  have G : RStoreFuns (simEnv (BI P hn host)) := Round5.Fwd.rStore_builtins hn host
  have A : Round5.Fwd.AggTypesB (simEnv (BI P hn host)) :=
    Round5.Fwd.aggTypesB_of (Round5.Int.typesB _)
  have rd : Equiv.ExecRead.HasReadRules (simEnv (BI P hn host)) := Aggregates.rd _
  have hsb : Aggregates.Bounded c.store := hb.store.aggs
  have : Fact (Round4.ModuleBnd c.frame.module) := ⟨hb.frame⟩
  have hz : TypedV (simEnv (BI P hn host)) stateT (stateV hn c.store c.frame) :=
    ((T.config c).1 hc).1
  have hcode : TypedV (simEnv (BI P hn host)) instrsT (.list (adminsToV c.code)) :=
    ((T.config c).1 hc).2
  cases h with
  | @structNew s f x d fs vs _ _ _ _ =>
    exact absurd hl (not_lastIs' (j := .structNew x) (by simp) rfl)
  | structNewDefault hd he hdef => exact Round5.Fwd.sread_structNewDefaultAnyB R A hd he hdef hz
  | structGetNull => exact RefsGC.sread_structGetNull rd.structGetNull R hz hcode
  | structGetStruct hs hf hd he hi hu' => exact sreadL_structGetStruct hn host hs hf hd he hi hu' hz
  | structSetNull => exact absurd hl (not_lastIs' rfl rfl)
  | structSetStruct _ _ _ _ _ _ => exact absurd hl (not_lastIs' rfl rfl)
  | arrayNew _ _ => exact absurd hl (not_lastIs' rfl rfl)
  | @arrayNewDefault s f x n d ft v hd he hv =>
    obtain ⟨m, zt⟩ := ft
    exact Round5.Fwd.sread_arrayNewDefaultAnyB R A hd he hv hz
  | @arrayNewFixed s f x n d ft vs _ _ _ _ =>
    exact absurd hl (not_lastIs' (j := .arrayNewFixed x n) (by simp) rfl)
  | arrayNewElemOob he hl' => exact RefsGC.sread_arrayNewElemOob rd.arrayNewElemOob R G he hl' hz
  | @arrayNewElemAlloc s f x y i n ea ei he hl' =>
    exact R4Fwd.sread_arrayNewElemAlloc (x := x) (hn := hn) R G he hl' hz
  | @arrayNewDataOob s f x y i n d ft da di hd he hdat h0 hl' =>
    obtain ⟨m, zt⟩ := ft
    exact Round5.Fwd.sread_arrayNewDataOobB R A hd he hdat h0 hl' hz
  | @arrayNewDataNum s f x y i n d ft da di vs hd he hdat h0 hl' hvs =>
    obtain ⟨m, zt⟩ := ft
    exact Round5.FwdRef.sread_arrayNewDataNumB hF (R4Fwd.zB_builtins hn host) R A hd he hdat h0
      hl' hvs hz
  | arrayGetNull => exact RefsGC.sread_arrayGetNull rd.arrayGetNull R hz hcode
  | arrayGetOob ha hl' => exact RefsGC.sread_arrayGetOob rd.arrayGetOob R G ha hl' hz hcode
  | arrayGetArray ha hf hd he hu' => exact sreadL_arrayGetArray hn host ha hf hd he hu' hz
  | arraySetNull => exact absurd hl (not_lastIs' rfl rfl)
  | arraySetOob _ _ => exact absurd hl (not_lastIs' rfl rfl)
  | arraySetArray _ _ _ _ _ => exact absurd hl (not_lastIs' rfl rfl)
  | arrayLenNull => exact RefsGC.sread_arrayLenNull rd.arrayLenNull hz hcode
  | arrayLenArray ha =>
    exact RefsGC.sread_arrayLenArray rd.arrayLenArray R G ha (hsb.array ha) hz hcode
  | arrayFillNull => exact RefsGC.sread_arrayFillNull rd.arrayFillNull T R hz hcode
  | arrayFillOob ha hl' => exact RefsGC.sread_arrayFillOob rd.arrayFillOob T R G ha hl' hz hcode
  | arrayFillZero ha hl' =>
    exact RefsGC.sread_arrayFillZero rd.arrayFillZero rd.arrayFillNull rd.arrayFillOob
      (RefsGC.readTable_simEnv _) T R G ha hl' hz hcode
  | arrayFillSucc ha hl' hn0 =>
    exact RefsGC.sread_arrayFillSucc rd.arrayFillSucc rd.arrayFillNull rd.arrayFillOob
      rd.arrayFillZero (RefsGC.readTable_simEnv _) T R G ha hl' hn0 (hsb.array ha) hz hcode
  | arrayCopyNull₁ => exact RefsGC.sread_arrayCopyNull₁ rd.arrayCopyNull1 T R hz hcode
  | arrayCopyNull₂ => exact RefsGC.sread_arrayCopyNull₂ rd.arrayCopyNull2 T R hz hcode
  | arrayCopyOob₁ ha hl' => exact RefsGC.sread_arrayCopyOob₁ rd.arrayCopyOob1 R G ha hl' hz hcode
  | arrayCopyOob₂ ha hl' => exact RefsGC.sread_arrayCopyOob₂ rd.arrayCopyOob2 R G ha hl' hz hcode
  | arrayCopyZero ha₁ ha₂ hl' =>
    exact RefsGC.sread_arrayCopyZero rd.arrayCopyZero rd.arrayCopyOob1 rd.arrayCopyOob2
      (RefsGC.readTable_simEnv _) R G ha₁ ha₂ hl' hz
  | @arrayCopyLe s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₁ ai₂ d₂ ft₂ ha₁ ha₂ hl' hn0 hd he hle =>
    obtain ⟨m, zt⟩ := ft₂
    exact Round5.Fwd.sread_arrayCopyLeAnyB (x₁ := x₁) (hn := hn) hV R G A ha₁ ha₂ hl' hn0 hd he
      hle (hsb.array ha₁) (hsb.array ha₂) hz
  | @arrayCopyGt s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₁ ai₂ d₂ ft₂ ha₁ ha₂ hl' hn0 hd he hgt =>
    obtain ⟨m, zt⟩ := ft₂
    exact Round5.Fwd.sread_arrayCopyGtAnyB (x₁ := x₁) (hn := hn) hV R G A ha₁ ha₂ hl' hn0 hd he
      hgt (hsb.array ha₁) (hsb.array ha₂) hz
  | arrayInitElemNull => exact RefsGC.sread_arrayInitElemNull rd.arrayInitElemNull R hz hcode
  | arrayInitElemOob₁ ha hl' =>
    exact RefsGC.sread_arrayInitElemOob₁ rd.arrayInitElemOob1 R G ha hl' hz hcode
  | arrayInitElemOob₂ he hl' =>
    exact RefsGC.sread_arrayInitElemOob₂ rd.arrayInitElemOob2 R G he hl' hz
  | arrayInitElemZero ha he hl' =>
    exact RefsGC.sread_arrayInitElemZero rd.arrayInitElemZero rd.arrayInitElemOob1
      rd.arrayInitElemOob2 (RefsGC.readTable_simEnv _) R G ha he hl' hz
  | @arrayInitElemSucc s f x y i j n a ea ai ei r ha he hl' hn0 hr =>
    exact FwdSimdAgg.sread_arrayInitElemSucc (x := x) (hn := hn) R G ha he hl' hn0 hr
      (hsb.array ha) (hsb.elems ei (List.mem_of_getElem? (State.Store.elem?_eq_some he).2)) hz
  | arrayInitDataNull => exact RefsGC.sread_arrayInitDataNull rd.arrayInitDataNull R hz hcode
  | arrayInitDataOob₁ ha hl' =>
    exact RefsGC.sread_arrayInitDataOob₁ rd.arrayInitDataOob1 R G ha hl' hz hcode
  | @arrayInitDataOob₂ s f x y i j n a da d ft di hd he hdat h0 hl' =>
    obtain ⟨m, zt⟩ := ft
    exact Round5.Fwd.sread_arrayInitDataOob₂B R A hd he hdat h0 hl' hz
  | arrayInitDataZero ha hdat hl' => exact Round5.Fwd.sread_arrayInitDataZero5 R G ha hdat hl' hz
  | @arrayInitDataNum s f x y i j n a da ai d ft di v ha hd he hdat hl' hn0 hv =>
    obtain ⟨m, zt⟩ := ft
    exact Round5.Fwd.sread_arrayInitDataNumB hF (R4Fwd.zB_builtins hn host)
      (R4Fwd.expandInv_builtins hn host) (R4Fwd.litTyping_simEnv _) R G A ha hd he hdat hl' hn0 hv
      (hsb.array ha) (hsb.datas di (List.mem_of_getElem? (State.Store.data?_eq_some hdat).2)) hz

end Silmaril.Wasm.SpecTec.Institution.FwdX30
