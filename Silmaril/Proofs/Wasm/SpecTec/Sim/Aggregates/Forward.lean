module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Aggregates.Alloc

/-!
# Aggregates: the forward obligation on the covered aggregate fragment

`fwd_aggregate` is `Forward.aggregate` at `simEnv B`, restricted to

* configurations whose code holds no instruction of `AggOpen` (the instructions with an
  `AggregateStep` constructor still open: `struct.new_default`,
  `array.new_default`, `array.new_elem`, `array.new_data`, `array.copy`, `array.init_elem`,
  `array.init_data`);
* frames whose module's composite types have no packed field (`Unpacked`; see the
  `$packfield_` finding in `Store.lean`);
* bounded stores (`Bounded`: `array.len` and `array.fill` disagree beyond `2 ^ 32` entries).

Under these, every one of the remaining 22 `AggregateStep` constructors (struct.new, struct.get ×2,
struct.set ×2, array.new, array.new_fixed, array.get ×3, array.set ×3, array.len ×2,
array.fill ×4; the null/oob traps of the open instructions are excluded with them) is a
SpecTec step of the images. Hypotheses: `TypingFacts`, `RTyping` and `RStoreFuns` (family R) and
`AggTypes`; the state functions are evaluated, not assumed (`aggDefs_simEnv`,
`State.stateDefs_simEnv`, `unpackDef_simEnv`, `packDef_simEnv`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Aggregates

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open RefsGC

/-- A composite type without packed fields. -/
def NoPacked : CCompType → Prop
  | .array ft => ∃ m t, ft = .field m (.val t)
  | .struct fs => ∀ ft ∈ fs.toList, ∃ m t, ft = .field m (.val t)
  | _ => True

/-- Every aggregate type the frame's module names has unpacked fields. -/
def Unpacked (f : Frame) : Prop :=
  ∀ (x : TypeIdx) (d : DefType) (ct : CCompType), f.type? x = some d → Expand d ct → NoPacked ct

/-- The aggregate instructions with an open `AggregateStep` constructor. -/
def AggOpen : Admin → Bool
  | .plain (.structNewDefault _) | .plain (.arrayNewDefault _)
  | .plain (.arrayNewElem ..) | .plain (.arrayNewData ..) | .plain (.arrayCopy ..)
  | .plain (.arrayInitElem ..) | .plain (.arrayInitData ..) => true
  | _ => false

/-- The configuration's code holds no `AggOpen` instruction. -/
def AggCovered {H : Type} (c : Config H) : Prop := ∀ a ∈ c.code, AggOpen a = false

variable {H : Type} {hn : H → String} {B : Builtins}

theorem not_aggCovered {c : Config H} {a : Admin} (hm : a ∈ c.code) (ho : AggOpen a = true) :
    ¬ AggCovered c := fun h => by
  have := h a hm
  rw [ho] at this
  exact Bool.noConfusion this

/-- An unpacked array type. -/
theorem Unpacked.array {f : Frame} (hu : Unpacked f) {x : TypeIdx} {d : DefType} {ft : CFieldType}
    (hd : f.type? x = some d) (he : Expand d (.array ft)) : ∃ m t, ft = .field m (.val t) :=
  hu x d _ hd he

/-- An unpacked struct field. -/
theorem Unpacked.struct {f : Frame} (hu : Unpacked f) {x : TypeIdx} {d : DefType}
    {fs : Ty (.list .field)} {ft : CFieldType} {i : Nat} (hd : f.type? x = some d)
    (he : Expand d (.struct fs)) (hi : fs.toList[i]? = some ft) : ∃ m t, ft = .field m (.val t) :=
  hu x d _ hd he ft (List.mem_of_getElem? hi)

/-- On an unpacked storage type, `unpackable` forces no signedness and an unpacked field. -/
theorem unpackable_val {t : CValType} {sx : Option Signedness} {fv : FieldVal}
    (h : unpackable (.val t) sx fv) : sx = none ∧ ∃ v, fv = .val v := by
  cases sx <;> cases fv <;> simp_all [unpackable]

section Arms
variable (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B)) (A : AggTypes (simEnv B))
include T R A

/-- The `struct.get-struct` arm. -/
theorem fwd_structGetStruct_u {s : Store H} {f : Frame} {sx : Option Signedness} {x : TypeIdx}
    {i : FieldIdx} {a : Nat} {si : StructInst} {fv : FieldVal} {d : DefType}
    {fs : Ty (.list .field)} {ft : CFieldType} (hu : Unpacked f)
    (hs : s.structs[a]? = some si) (hf : si.fields[i.toNat]? = some fv)
    (hd : f.type? x = some d) (he : Expand d (.struct fs)) (hi : fs.toList[i.toNat]? = some ft)
    (hu' : unpackable (fieldStorage ft) sx fv) :
    FwdP (simEnv B) hn ⟨s, f, [.ref (.struct a), .plain (.structGet sx x i)]⟩
      ⟨s, f, [(unpackField sx fv).toAdmin]⟩ := by
  obtain ⟨m, t, rfl⟩ := hu.struct hd he hi
  obtain ⟨rfl, v, rfl⟩ := unpackable_val hu'
  exact RefsGC.fwd_of_sread T (st B).read fun hz _ => by
    simpa only [unpackField] using sread_structGetStructVal (hn := hn) (rd B).structGetStruct R
      (aggDefs_simEnv B) (State.stateDefs_simEnv B) A (unpackDef_simEnv B) hs hf hd he hi hz

/-- The `struct.set-struct` arm. -/
theorem fwd_structSetStruct_u {s : Store H} {f : Frame} {x : TypeIdx} {i : FieldIdx} {v : Val}
    {a : Nat} {d : DefType} {fs : Ty (.list .field)} {ft : CFieldType} {si : StructInst}
    (hu : Unpacked f) (hd : f.type? x = some d) (he : Expand d (.struct fs))
    (hi : fs.toList[i.toNat]? = some ft) (hs : s.structs[a]? = some si)
    (hf : i.toNat < si.fields.length) :
    FwdP (simEnv B) hn ⟨s, f, [.ref (.struct a), v.toAdmin, .plain (.structSet x i)]⟩
      ⟨s.setStructField a i.toNat (packField (fieldStorage ft) v), f, []⟩ := by
  obtain ⟨m, t, rfl⟩ := hu.struct hd he hi
  exact fwd_structSetStructVal (st B).structSetStruct T R (aggDefs_simEnv B)
    (State.stateDefs_simEnv B) A (packDef_simEnv B) hd he hi hs hf

/-- The `array.new_fixed` arm. -/
theorem fwd_arrayNewFixed_u {s : Store H} {f : Frame} {x : TypeIdx} {n : Fin (2 ^ 32)}
    {d : DefType} {ft : CFieldType} {vs : List Val} (hu : Unpacked f)
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (hvn : vs.length = n.val) :
    FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.plain (.arrayNewFixed x n)]⟩
      ⟨s.addArray ⟨d, vs.map (packField (fieldStorage ft))⟩, f, [arrRef s.arrays.length]⟩ := by
  obtain ⟨m, t, rfl⟩ := hu.array hd he
  exact fwd_arrayNewFixedVal (st B).arrayNewFixed T R (aggDefs_simEnv B)
    (State.stateDefs_simEnv B) A (packDef_simEnv B) hd he hvn

/-- The `array.get-array` arm. -/
theorem fwd_arrayGetArray_u {s : Store H} {f : Frame} {sx : Option Signedness} {x : TypeIdx}
    {i : BitVec 32} {a : Nat} {ai : ArrayInst} {fv : FieldVal} {d : DefType} {ft : CFieldType}
    (hu : Unpacked f) (ha : s.arrays[a]? = some ai) (hf : ai.fields[i.toNat]? = some fv)
    (hd : f.type? x = some d) (he : Expand d (.array ft))
    (hu' : unpackable (fieldStorage ft) sx fv) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, .plain (.arrayGet sx x)]⟩
      ⟨s, f, [(unpackField sx fv).toAdmin]⟩ := by
  obtain ⟨m, t, rfl⟩ := hu.array hd he
  obtain ⟨rfl, v, rfl⟩ := unpackable_val hu'
  exact RefsGC.fwd_of_sread T (st B).read fun hz _ => by
    simpa only [unpackField] using sread_arrayGetArrayVal (hn := hn) (rd B).arrayGetArray R
      (aggDefs_simEnv B) (State.stateDefs_simEnv B) A (unpackDef_simEnv B) ha hf hd he hz

/-- The `array.set-array` arm. -/
theorem fwd_arraySetArray_u {s : Store H} {f : Frame} {x : TypeIdx} {i : BitVec 32} {v : Val}
    {a : Nat} {ai : ArrayInst} {d : DefType} {ft : CFieldType} (hu : Unpacked f)
    (ha : s.arrays[a]? = some ai) (h : i.toNat < ai.fields.length) (hd : f.type? x = some d)
    (he : Expand d (.array ft)) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x)]⟩
      ⟨s.setArrayField a i.toNat (packField (fieldStorage ft) v), f, []⟩ := by
  obtain ⟨m, t, rfl⟩ := hu.array hd he
  exact fwd_arraySetArrayVal (st B).arraySetArray T R (aggDefs_simEnv B)
    (State.stateDefs_simEnv B) A (packDef_simEnv B) ha h hd he

/-- The `struct.new` arm. -/
theorem fwd_structNew_u {s : Store H} {f : Frame} {x : TypeIdx} {d : DefType}
    {fs : Ty (.list .field)} {vs : List Val} (hu : Unpacked f) (hd : f.type? x = some d)
    (he : Expand d (.struct fs)) (hvn : vs.length = fs.length) :
    FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.plain (.structNew x)]⟩
      ⟨s.addStruct ⟨d, (fs.toList.zip vs).map fun (ft, v) => packField (fieldStorage ft) v⟩, f,
        [.ref (.struct s.structs.length)]⟩ :=
  fwd_structNewVal (st B).structNew T R (aggDefs_simEnv B) (State.stateDefs_simEnv B) A
    (packDef_simEnv B) hd he hvn (hu x d _ hd he)

end Arms

/-- **`Forward.aggregate` at `simEnv B`, on the covered aggregate fragment.** -/
theorem fwd_aggregate (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B))
    (G : RStoreFuns (simEnv B)) (A : AggTypes (simEnv B)) {c c' : Config H}
    (h : AggregateStep c c') (hb : Bounded c.store) (hu : Unpacked c.frame)
    (hcov : AggCovered c) : FwdP (simEnv B) hn c c' := by
  cases h with
  | structNew hd he hn _ => exact fwd_structNew_u T R A hu hd he hn
  | structNewDefault => exact absurd hcov (by simp [AggCovered, AggOpen])
  | structGetNull => exact fwd_structGetNull T R G
  | structGetStruct hs hf hd he hi hu' => exact fwd_structGetStruct_u T R A hu hs hf hd he hi hu'
  | structSetNull => exact fwd_structSetNull T R G
  | structSetStruct hd he hi hs hf _ => exact fwd_structSetStruct_u T R A hu hd he hi hs hf
  | arrayNew v n => exact fwd_arrayNew T R v n
  | arrayNewDefault => exact absurd hcov (by simp [AggCovered, AggOpen])
  | arrayNewFixed hd he hn _ => exact fwd_arrayNewFixed_u T R A hu hd he hn
  | arrayNewElemOob | arrayNewElemAlloc | arrayNewDataOob | arrayNewDataNum =>
      exact absurd hcov (by simp [AggCovered, AggOpen])
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
  | arrayCopyNull₁ | arrayCopyNull₂ | arrayCopyOob₁ | arrayCopyOob₂ | arrayCopyZero
  | arrayCopyLe | arrayCopyGt => exact absurd hcov (by simp [AggCovered, AggOpen])
  | arrayInitElemNull | arrayInitElemOob₁ | arrayInitElemOob₂ | arrayInitElemZero
  | arrayInitElemSucc => exact absurd hcov (by simp [AggCovered, AggOpen])
  | arrayInitDataNull | arrayInitDataOob₁ | arrayInitDataOob₂ | arrayInitDataZero
  | arrayInitDataNum => exact absurd hcov (by simp [AggCovered, AggOpen])

end Silmaril.Wasm.SpecTec.Sim.Aggregates
