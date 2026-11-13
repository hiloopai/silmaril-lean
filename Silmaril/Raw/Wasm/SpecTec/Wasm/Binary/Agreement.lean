module

public import Silmaril.Wasm.Binary.Core.Modules
public import Silmaril.Raw.Wasm.SpecTec.Wasm.V1.Binary
public import Silmaril.Raw.Wasm.SpecTec.Wasm.Lime1.Binary
public import Silmaril.Wasm.Lime1.FromV1
public import Silmaril.Wasm.Component.Reference.Defs
public import Silmaril.Raw.Wasm.SpecTec.Wasm.Lime1.Validation.Aligns
public import Silmaril.Raw.Wasm.SpecTec.Wasm.Binary.Agreement.Sections
public import Silmaril.Raw.Wasm.SpecTec.Wasm.Binary.V1Lime1
public import Silmaril.Raw.Wasm.SpecTec.Wasm.Binary.Lime1Core
public import Silmaril.Wasm.Component.Reference.Wasm.Lime1.Validation.FromV1.Thms
-- Hand copy (track ws4-p1-lime-wasmi): source namespaces kept, only import lines rewritten
-- (imports of other topics' Raw modules go through their public headers).

/-! # Agreement of the Wasm 1.0, Lime1 and Core 3.0 binary encodings

The source embeddings `V1.Module.toLime` and `Lime1.Module.toCore` are compared
with the three `Encoding`s.

## Status

Everything here is proved, with no `sorry` in the dependency closure (only `propext`,
`Classical.choice` and `Quot.sound`). The Wasm 1.0/Lime1 theorems (`v1_instr_lime1`,
`lime1_instr_v1`, `v1_expr_iff_lime1`, `v1_iff_lime1`) are those of
`Binary/V1Lime1.lean`; the instruction-level Lime1/Core theorems (`lime1_instr_core`,
`core_instr_lime1`) are those of `Binary/Lime1Core.lean`, whose alignment premise
`Lime1Core.instrAligns` agrees with `Lime1.Instr.alignsBelow64`
(`Lime1Core.instrAligns_eq`). The module-level Lime1/Core theorems (`lime1_core_forms`,
`core_forms_lime1`) are proved section by section (`Binary/Agreement/Sections.lean`)
from the instruction-level ones, and `ModuleValid.binaryCompat` outright. The
functionality and monotonicity lemmas of the three grammars come from
`Binary/Core/Instructions.lean` and the V1/Lime1 grammars. The docstrings name, for
each derived result, the results it follows from.

## What is claimed

1. **Wasm 1.0 ⊆ Lime1, exactly.** `V1.Encodes b m ↔ Lime1.EncodesWith false b m.toLime`,
   so `V1.Encodes b m → Lime1.Encodes b m.toLime`. A Lime1 encoding of a 1.0 image
   that is not a 1.0 encoding uses call-indirect-overlong (`lime1_v1_or_overlong`):
   the only extra rule reaching the image is `TableIdxZero.padded`, since
   `BlockType.idx` yields `.typeIdx`, outside the image.
2. **Lime1 ⊆ Core 3.0, on compatible modules, up to element-segment types.** Two
   corrections are needed, and both are forced:
   * *Element types.* Core 3.0 decodes the legacy segment form `0:u32 e y*` to element
     type `(ref func)` (non-null; 5.4:101–102), whereas `toCore` assigns `funcref`
     (`(ref null func)`), the type of segment kind `4`. The embedding that agrees
     with the binary format is therefore `toCoreBinary`, which differs from
     `toCore` only in those element types (`toCore_eq_retype`); see
     `lime1_core_toCore_counterexample` for the failure of the naive statement.
     `Binary/Bridge.lean` states that validity and instantiation carry over from
     `toCore` to `toCoreBinary`, so the semantic results apply to what Core decodes.
   * *Binary compatibility* (`BinaryCompat`). The 1.0 grammar admits syntax that the
     Core grammar reads differently: alignment exponents `≥ 2^6` (bit 6 is Core's
     memory-index flag), and element/data segments with a nonzero table/memory
     index (their leading `u32` is Core's segment kind). Every *valid* module is
     compatible (`Lime1.Validation.ModuleValid.binaryCompat`).
   Under compatibility the agreement is again exact, against the Core grammar with
   the gated forms restricted (`Core.Forms.ofOverlong`) *and numeric locals*
   (`Core.NumLocalsModule`), and the converse needs no premise:
   `Lime1.EncodesWith ov b m ↔ Core.NumLocalsModule (Forms.ofOverlong ov) b m.toCoreBinary`,
   in particular `Lime1.Encodes b m ↔ Core.NumLocalsModule Forms.lime1 b m.toCoreBinary`
   and `V1.Encodes b m ↔ Core.NumLocalsModule Forms.v1 b m.toCoreBinary`. The forward
   direction also holds into `Core.Module` (`lime1_core_forms`). The locals restriction
   is forced: Core's `Blocals` admits a zero-count entry of a non-number type (e.g.
   `00 7B`), invisible in the abstract syntax and ungated by `Forms`, so
   `Core.Module (Forms.ofOverlong ov) b m.toCoreBinary` does not imply a Lime1
   encoding.
3. **Reflection.** Hence a Core 3.0 encoding of an *image* module is a Lime1 (resp.
   1.0) encoding unless it uses a gated form or a non-numeric locals entry
   (`UsesGatedForm`). This is meaningful
   only for image modules: the gates do not cover Core-only syntax outside the
   image (see `Core/Types.lean`). `Examples.lean` exhibits, at the instruction
   level, `memargMemIdx`, `tableIdxImm` and `memIdxImm`; `Examples/Gated.lean`
   exhibits the other gated forms (`memargOffset64`, `limits64`, `dataCount`,
   `elemKinds`, `dataKinds`).
4. **Functionality** of all three encodings, and, from it, transport
   of lifted relations along the embeddings.
-/

@[expose] public section

open Silmaril.Wasm.Binary

namespace Silmaril.Wasm.Lime1

/-! ## Binary compatibility and the binary-faithful Core embedding -/

mutual
/-- All alignment exponents in an instruction are below `2^6`. -/
def Instr.alignsBelow64 : Instr → Bool
  | .block _ body | .loop _ body => Expr.alignsBelow64 body
  | .if_ _ left right => Expr.alignsBelow64 left && Expr.alignsBelow64 right
  | .intLoad _ _ a | .floatLoad _ a | .intStore _ _ a | .floatStore _ a => decide
      (a.align.val < 2 ^ 6)
  | _ => true

/-- All alignment exponents in an expression are below `2^6`. -/
def Expr.alignsBelow64 : Expr → Bool
  | [] => true
  | i :: is => Instr.alignsBelow64 i && Expr.alignsBelow64 is
end

/-- Syntax on which the 1.0/Lime1 and Core 3.0 grammars read the same bytes alike. -/
structure Module.BinaryCompat (m : Module) : Prop where
  elemTables : ∀ e ∈ m.elems, e.table = ⟨0⟩
  dataMemories : ∀ d ∈ m.data, d.memory = ⟨0⟩
  funcAligns : ∀ f ∈ m.funcs, Expr.alignsBelow64 f.body = true
  globalAligns : ∀ g ∈ m.globals, Expr.alignsBelow64 g.init = true
  elemAligns : ∀ e ∈ m.elems, Expr.alignsBelow64 e.offset = true
  dataAligns : ∀ d ∈ m.data, Expr.alignsBelow64 d.offset = true

/-- The element segment as the Core 3.0 binary format decodes it: `(ref func)`. -/
def Elem.toCoreBinary (e : Elem) : Wasm.Elem := { e.toCore with type := ⟨false, .abstract .func⟩ }

/-- `toCore`, with element types as decoded from the legacy segment form. -/
def Module.toCoreBinary (m : Module) : Wasm.Module :=
  { m.toCore with elems := m.elems.map Elem.toCoreBinary }

theorem Module.toCoreBinary_eq_toCore {m : Module} (h : m.elems = []) :
    m.toCoreBinary = m.toCore := by
  cases m
  simp_all [toCoreBinary, toCore]

/-- `toCore` is `toCoreBinary` with every element type widened to `funcref`
(`(ref func)` matches `funcref`). -/
theorem Module.toCore_eq_retype (m : Module) :
    m.toCore = { m.toCoreBinary with
      elems := m.toCoreBinary.elems.map fun e => { e with type := V1.funcref } } := by
  cases m
  simp [toCoreBinary, toCore, Elem.toCoreBinary, Elem.toCore, Function.comp_def]

theorem Module.toCoreBinary_injective : Function.Injective toCoreBinary := by
  intro a b h
  apply Module.toCore_injective
  rw [toCore_eq_retype, toCore_eq_retype, h]

/-- `ofCore?` also retracts the binary-faithful embedding. -/
@[simp] theorem Elem.ofCore?_toCoreBinary (e : Elem) : Elem.ofCore? e.toCoreBinary = some e := by
  cases e
  simp [toCoreBinary, Elem.toCore, Elem.ofCore?, List.mapM_map, Function.comp_def, V1.funcref]

@[simp] theorem Module.ofCore?_toCoreBinary (m : Module) :
    Module.ofCore? m.toCoreBinary = some m := by
  cases m
  simp [toCoreBinary, toCore, ofCore?, List.mapM_map, Function.comp_def]

namespace Validation

/-- Well-typed instructions have alignment exponents below `2^6`. -/
theorem InstrType.alignsBelow64 {C : Context} {i : Instr} {a b : ResultType}
    (h : InstrType C i a b) : i.alignsBelow64 = true := by
  refine InstrType.rec (motive_1 := fun _ i _ _ _ => i.alignsBelow64 = true)
    (motive_2 := fun _ e _ _ _ => Expr.alignsBelow64 e = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals intros
  all_goals simp_all [Instr.alignsBelow64, Expr.alignsBelow64]
  all_goals first
    | exact IntAccess.align_lt ‹_›
    | exact Aligned.align_lt ‹_› (FloatType.width_le _)

/-- Well-typed expressions have alignment exponents below `2^6`. -/
theorem ExprType.alignsBelow64 {C : Context} {e : Expr} {a b : ResultType}
    (h : ExprType C e a b) : Expr.alignsBelow64 e = true := by
  induction e generalizing a with
  | nil => simp [Expr.alignsBelow64]
  | cons i is ih =>
    cases h with
    | cons hi his => simp [Expr.alignsBelow64, InstrType.alignsBelow64 hi, ih his]

/-- An index into a list of length at most one is `0`. -/
theorem idx_eq_zero {α : Type} {k : IndexKind} {l : List α} (hl : l.length ≤ 1) {x : Idx k}
    (hx : ∃ y, l[x.toNat]? = some y) : x = ⟨0⟩ := by
  obtain ⟨y, hy⟩ := hx
  have := (List.getElem?_eq_some_iff.mp hy).1
  obtain ⟨⟨v, hv⟩⟩ := x
  simp only [Idx.toNat] at this
  have hv0 : v = 0 := by omega
  subst hv0
  rfl

/-- Valid Lime1 modules are binary compatible. -/
theorem ModuleValid.binaryCompat {m : Module} (h : ModuleValid m) : m.BinaryCompat where
  elemTables e he := idx_eq_zero h.singleTable (h.elements e he).table
  dataMemories d hd := idx_eq_zero h.singleMemory (h.data d hd).memory
  funcAligns f hf := by
    obtain ⟨_, _, _, ht⟩ := h.functions f hf
    exact ht.alignsBelow64
  globalAligns g hg := (ConstExprType.typed (h.globals g hg)).alignsBelow64
  elemAligns e he := (h.elements e he).offset.typed.alignsBelow64
  dataAligns d hd := (h.data d hd).offset.typed.alignsBelow64

end Validation

end Silmaril.Wasm.Lime1

namespace Silmaril.Wasm.V1

/-- Wasm 1.0 binary compatibility is that of the Lime1 image. -/
abbrev Module.BinaryCompat (m : Module) : Prop := m.toLime.BinaryCompat

/-- The element segment as the Core 3.0 binary format decodes it: `(ref func)`. -/
def Elem.toCoreBinary (e : Elem) : Wasm.Elem := { e.toCore with type := ⟨false, .abstract .func⟩ }

/-- `toCore`, with element types as decoded from the legacy segment form. -/
def Module.toCoreBinary (m : Module) : Wasm.Module :=
  { m.toCore with elems := m.elems.map Elem.toCoreBinary }

/-- `ofCore?` also retracts the binary-faithful embedding. -/
@[simp] theorem Elem.ofCore?_toCoreBinary (e : Elem) : Elem.ofCore? e.toCoreBinary = some e := by
  cases e
  simp [toCoreBinary, Elem.toCore, Elem.ofCore?, List.mapM_map, Function.comp_def, funcref]

@[simp] theorem Module.ofCore?_toCoreBinary (m : Module) :
    Module.ofCore? m.toCoreBinary = some m := by
  cases m
  simp [toCoreBinary, toCore, ofCore?, List.mapM_map, Function.comp_def]

/-- The binary-faithful embeddings commute: Wasm 1.0 → Lime1 → Core 3.0 is the direct one. -/
@[simp] theorem Module.toLime_toCoreBinary (m : Module) :
    m.toLime.toCoreBinary = m.toCoreBinary := by
  simp only [Lime1.Module.toCoreBinary, toCoreBinary, toLime_toCore]
  congr 1
  simp [toLime, Function.comp_def, Lime1.Elem.toCoreBinary, Elem.toCoreBinary]

theorem Validation.ModuleValid.binaryCompat {m : Module} (h : Validation.ModuleValid m) :
    m.BinaryCompat :=
  Lime1.Validation.ModuleValid.binaryCompat h.toLime

end Silmaril.Wasm.V1

namespace Silmaril.Wasm.Binary.Lime1Core

mutual
/-- `instrAligns` (the premise of `Lime1Core.instr_core`) is `Lime1.Instr.alignsBelow64`. -/
theorem instrAligns_eq (i : Lime1.Instr) : instrAligns i = i.alignsBelow64 := by
  cases i
  case block _ body | loop _ body =>
    simp only [instrAligns, Lime1.Instr.alignsBelow64, exprAligns_eq body]
  case if_ _ left right =>
    simp only [instrAligns, Lime1.Instr.alignsBelow64, exprAligns_eq left, exprAligns_eq right]
  all_goals rfl

/-- `exprAligns` is `Lime1.Expr.alignsBelow64`. -/
theorem exprAligns_eq : (e : Lime1.Expr) → exprAligns e = Lime1.Expr.alignsBelow64 e
  | [] => rfl
  | i :: is => by
    simp only [exprAligns, Lime1.Expr.alignsBelow64, instrAligns_eq i, exprAligns_eq is]
end

end Silmaril.Wasm.Binary.Lime1Core

namespace Silmaril.Wasm.Binary

/-! ## Wasm 1.0 and Lime1 -/

theorem v1_instr_lime1 {b : Bytes} {i : V1.Instr} (h : V1.Binary.Instr b i) :
    Lime1.Binary.Instr false b i.toLime :=
  V1Lime1.instr_forward h

/-- On the 1.0 image, Lime1 without call-indirect-overlong is exactly Wasm 1.0. -/
theorem lime1_instr_v1 {b : Bytes} {i : V1.Instr} (h : Lime1.Binary.Instr false b i.toLime) :
    V1.Binary.Instr b i :=
  V1Lime1.instr_backward h

theorem v1_expr_iff_lime1 {b : Bytes} {e : V1.Expr} :
    V1.Binary.Expr b e ↔ Lime1.Binary.Expr false b (V1.Expr.toLime e) :=
  V1Lime1.expr_iff

/-- Wasm 1.0 is the Lime1 grammar without call-indirect-overlong, on the 1.0 image. -/
theorem v1_iff_lime1 {b : Bytes} {m : V1.Module} :
    V1.Binary.Encodes b m ↔ Lime1.Binary.EncodesWith false b m.toLime :=
  V1Lime1.encodes_iff

/-- Every Wasm 1.0 encoding is a Lime1 encoding of the image.
Follows from `v1_iff_lime1` and `EncodesWith.mono`. -/
theorem v1_lime1 {b : Bytes} {m : V1.Module} (h : V1.Binary.Encodes b m) :
    Lime1.Binary.Encodes b m.toLime :=
  Lime1.Binary.EncodesWith.mono (v1_iff_lime1.mp h)

/-- A Lime1 encoding of a 1.0 image is a 1.0 encoding, or needs call-indirect-overlong.
Follows from `v1_iff_lime1`. (`Examples.overlong_lime1`/`overlong_not_lime1_strict`
show the instruction-level witness `11 00 80 00`.) -/
theorem lime1_v1_or_overlong {b : Bytes} {m : V1.Module}
    (_h : Lime1.Binary.Encodes b m.toLime) :
    V1.Binary.Encodes b m ∨ ¬ Lime1.Binary.EncodesWith false b m.toLime := by
  by_cases hf : Lime1.Binary.EncodesWith false b m.toLime
  · exact .inl (v1_iff_lime1.mpr hf)
  · exact .inr hf

/-- The Lime1 decoding of Wasm 1.0 bytes is the image of their 1.0 decoding.
Follows from `v1_lime1` and `Lime1.Binary.functional`. -/
theorem lime1_decode_of_v1 {b : Bytes} {m : V1.Module} {m' : Lime1.Module}
    (h : V1.Binary.Encodes b m) (h' : Lime1.Binary.Encodes b m') : m' = m.toLime :=
  Lime1.Binary.functional h' (v1_lime1 h)

/-! ## Lime1 and Core 3.0

All statements are parameterized by Lime1's `overlong` flag, against
`Core.Forms.ofOverlong ov` (`lime1` or `v1`), so that the Wasm 1.0 case follows from
`v1_iff_lime1` without a second instruction-level proof. -/

theorem lime1_instr_core {ov : Bool} {b : Bytes} {i : Lime1.Instr}
    (h : Lime1.Binary.Instr ov b i) (ha : i.alignsBelow64 = true) :
    Core.Instr (Core.Forms.ofOverlong ov) b i.toCore :=
  Lime1Core.instr_core h (by rw [Lime1Core.instrAligns_eq]; exact ha)

/-- No compatibility premise: the restricted Core grammar rejects alignments `≥ 2^6`. -/
theorem core_instr_lime1 {ov : Bool} {b : Bytes} {i : Lime1.Instr}
    (h : Core.Instr (Core.Forms.ofOverlong ov) b i.toCore) : Lime1.Binary.Instr ov b i :=
  Lime1Core.core_instr h

theorem lime1_instrs_core {ov : Bool} {b : Bytes} {is : Lime1.Expr}
    (h : Lime1.Binary.Instrs ov b is) (ha : Lime1.Expr.alignsBelow64 is = true) :
    Core.Instrs (Core.Forms.ofOverlong ov) b (Lime1.Expr.toCore is) := by
  induction is generalizing b with
  | nil => cases h; exact .nil
  | cons i is ih =>
    cases h with
    | cons hi hs =>
      simp only [Lime1.Expr.alignsBelow64, Bool.and_eq_true] at ha
      exact .cons (lime1_instr_core hi ha.1) (ih hs ha.2)

theorem core_instrs_lime1 {ov : Bool} {b : Bytes} {is : Lime1.Expr}
    (h : Core.Instrs (Core.Forms.ofOverlong ov) b (Lime1.Expr.toCore is)) :
    Lime1.Binary.Instrs ov b is := by
  induction is generalizing b with
  | nil =>
    change Core.Instrs _ b [] at h
    cases h
    exact .nil
  | cons i is ih =>
    change Core.Instrs _ b (Lime1.Instr.toCore i :: Lime1.Expr.toCore is) at h
    cases h with
    | cons hi hs => exact .cons (core_instr_lime1 hi) (ih hs)

/-- Follows from `lime1_instr_core`. -/
theorem lime1_expr_core {ov : Bool} {b : Bytes} {e : Lime1.Expr}
    (h : Lime1.Binary.Expr ov b e) (ha : Lime1.Expr.alignsBelow64 e = true) :
    Core.Expr (Core.Forms.ofOverlong ov) b (Lime1.Expr.toCore e) := by
  cases h with
  | mk hi => exact .mk (lime1_instrs_core hi ha)

/-- Follows from `core_instr_lime1`. -/
theorem core_expr_lime1 {ov : Bool} {b : Bytes} {e : Lime1.Expr}
    (h : Core.Expr (Core.Forms.ofOverlong ov) b (Lime1.Expr.toCore e)) :
    Lime1.Binary.Expr ov b e := by
  cases h with
  | mk hi => exact .mk (core_instrs_lime1 hi)

/-! ### Declarations with expressions -/

section Declarations

variable {ov : Bool} {b : Bytes}

theorem lime1_global_core {g : Lime1.Global}
    (h : Scalar.Binary.Global (Lime1.Binary.Expr ov) b g)
    (ha : Lime1.Expr.alignsBelow64 g.init = true) :
    Core.Global (Core.Forms.ofOverlong ov) b g.toCore := by
  cases h with
  | mk ht he => exact .mk (Core.GlobalType.of_v1 ht) (lime1_expr_core he ha)

theorem core_global_lime1 {g : Lime1.Global}
    (h : Core.Global (Core.Forms.ofOverlong ov) b g.toCore) :
    Scalar.Binary.Global (Lime1.Binary.Expr ov) b g := by
  obtain ⟨gt, e⟩ := g
  change Core.Global _ b ⟨gt.toCore, Lime1.Expr.toCore e⟩ at h
  generalize hE : Lime1.Expr.toCore e = E at h
  cases h with
  | mk ht he =>
    subst hE
    exact .mk (Core.GlobalType.to_v1 ht) (core_expr_lime1 he)

theorem lime1_elem_core {e : Lime1.Elem} (h : Scalar.Binary.Elem (Lime1.Binary.Expr ov) b e)
    (ht : e.table = ⟨0⟩) (ha : Lime1.Expr.alignsBelow64 e.offset = true) :
    Core.Elem (Core.Forms.ofOverlong ov) b e.toCoreBinary := by
  cases h with
  | mk hx he hy =>
    subst ht
    exact .k0 hx (lime1_expr_core he ha) hy

theorem funcRef_injective : Function.Injective Lime1.funcRef := fun _ _ h => by
  simpa [Lime1.funcRef] using h

/-- No compatibility premise: only the legacy kind `0` is open, and it has table `0`. -/
theorem core_elem_lime1 {e : Lime1.Elem}
    (h : Core.Elem (Core.Forms.ofOverlong ov) b e.toCoreBinary) :
    Scalar.Binary.Elem (Lime1.Binary.Expr ov) b e := by
  have hF := Core.Forms.ofOverlong_le_lime1 ov
  obtain ⟨x, off, ys⟩ := e
  change Core.Elem _ b ⟨⟨false, .abstract .func⟩, ys.map Lime1.funcRef,
    .active x (Lime1.Expr.toCore off)⟩ at h
  generalize hI : ys.map Lime1.funcRef = I at h
  generalize hE : Lime1.Expr.toCore off = E at h
  cases h
  case k0 =>
    subst hE
    obtain rfl := List.map_injective_iff.mpr funcRef_injective hI
    exact .mk ‹_› (core_expr_lime1 ‹_›) ‹_›
  all_goals exact (Core.Forms.not_gate hF ‹_› (by decide)).elim

theorem lime1_data_core {d : Lime1.Data} (h : Scalar.Binary.Data (Lime1.Binary.Expr ov) b d)
    (hm : d.memory = ⟨0⟩) (ha : Lime1.Expr.alignsBelow64 d.offset = true) :
    Core.Data (Core.Forms.ofOverlong ov) b d.toCore := by
  cases h with
  | mk hx he hb =>
    subst hm
    exact .k0 hx (lime1_expr_core he ha) hb

set_option linter.unusedTactic false in
/-- No compatibility premise: only the legacy kind `0` is open, and it has memory `0`. -/
theorem core_data_lime1 {d : Lime1.Data}
    (h : Core.Data (Core.Forms.ofOverlong ov) b d.toCore) :
    Scalar.Binary.Data (Lime1.Binary.Expr ov) b d := by
  have hF := Core.Forms.ofOverlong_le_lime1 ov
  obtain ⟨x, off, ⟨arr⟩⟩ := d
  change Core.Data _ b ⟨⟨arr⟩, .active x (Lime1.Expr.toCore off)⟩ at h
  generalize hE : Lime1.Expr.toCore off = E at h
  cases h
  case k0 =>
    subst hE
    exact .mk ‹_› (core_expr_lime1 ‹_›) ‹_›
  all_goals exact (Core.Forms.not_gate hF ‹_› (by decide)).elim

/-- The Lime1 code entry `(locals, body)` as Core decodes it. -/
abbrev codeToCore (c : List V1.ValType × Lime1.Expr) : List Wasm.ValType × Wasm.Expr :=
  (c.1.map V1.ValType.toCore, Lime1.Expr.toCore c.2)

theorem lime1_code_core {c : List V1.ValType × Lime1.Expr}
    (h : Scalar.Binary.Code (Lime1.Binary.Expr ov) b c)
    (ha : Lime1.Expr.alignsBelow64 c.2 = true) :
    Core.NumCode (Core.Forms.ofOverlong ov) b (codeToCore c) := by
  obtain ⟨hl, hlen, ⟨hv, he, hlen'⟩⟩ := h
  refine .mk hl hlen ?_
  rw [codeToCore, List.map_flatten]
  exact .mk (Vec.map (fun _ _ h => Core.NumLocals.of_v1 h) hv) (lime1_expr_core he ha)
    (by simpa [← List.map_flatten] using hlen')

theorem core_code_lime1 {c : List V1.ValType × Lime1.Expr}
    (h : Core.NumCode (Core.Forms.ofOverlong ov) b (codeToCore c)) :
    Scalar.Binary.Code (Lime1.Binary.Expr ov) b c := by
  obtain ⟨ls, e⟩ := c
  generalize hc : codeToCore (ls, e) = c' at h
  obtain ⟨hl, hlen, ⟨hv, he, hlen'⟩⟩ := h
  obtain ⟨lss₀, rfl, hv₀⟩ := Core.Vec.numLocals_to_v1 hv
  simp only [codeToCore, Prod.mk.injEq] at hc
  obtain ⟨h₁, rfl⟩ := hc
  rw [← List.map_flatten] at h₁
  obtain rfl := Core.ValType.toCore_map_injective h₁
  exact .mk hl hlen (.mk hv₀ (core_expr_lime1 he) (by simpa [← List.map_flatten] using hlen'))

end Declarations

/-! ### Modules -/

/-- Lime1 encodings of compatible modules are Core 3.0 encodings, with no gated form
other than those matching `ov` and with numeric locals only. Follows from
`lime1_instr_core`. -/
theorem lime1_coreNum_forms {ov : Bool} {b : Bytes} {m : Lime1.Module}
    (h : Lime1.Binary.EncodesWith ov b m) (hc : m.BinaryCompat) :
    Core.NumLocalsModule (Core.Forms.ofOverlong ov) b m.toCoreBinary := by
  cases h with
  | @mk c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ bty bim bfn btb bme bgl bex bst bel bco bda
      types imports typeidxs tables mems globals exports start elems codes data
      h₀ hty h₁ him h₂ hfn h₃ htb h₄ hme h₅ hgl h₆ hex h₇ hst h₈ hel h₉ hco h₁₀ hda h₁₁
      hfuncs =>
  obtain ⟨hcE, hcD, hcF, hcG, hcEA, hcDA⟩ := hc
  have hcodes : ∀ c ∈ codes, Lime1.Expr.alignsBelow64 c.2 = true := fun c hc' => by
    obtain ⟨x, hx⟩ := Core.mem_zipFuncs hfuncs hc'
    exact hcF _ hx
  have hty' : Core.TypeSec (Core.Forms.ofOverlong ov) bty (types.map V1.FuncType.toCoreRec) :=
    Section.map (fun _ h => Vec.map (fun _ _ h => Core.RecType.of_v1 h) h) hty
  have him' : Core.ImportSec (Core.Forms.ofOverlong ov) bim (imports.map V1.Import.toCore) :=
    Section.map (fun _ h => Vec.map (fun _ _ h => Core.Import.of_v1 h) h) him
  have htb' : Core.TableSec (Core.Forms.ofOverlong ov) btb (tables.map Lime1.tableToCore) :=
    Section.map (fun _ h => Vec.map (fun _ _ h => Core.Table.of_v1 h) h) htb
  have hme' : Core.MemSec (Core.Forms.ofOverlong ov) bme (mems.map V1.MemoryType.toCore) :=
    Section.map (fun _ h => Vec.map (fun _ _ h => Core.MemType.of_v1 h) h) hme
  have hgl' : Core.GlobalSec (Core.Forms.ofOverlong ov) bgl (globals.map Lime1.Global.toCore) :=
    Section.map (fun _ h => Vec.map_of (P := fun g => Lime1.Expr.alignsBelow64 g.init = true)
      (fun _ _ hp h => lime1_global_core h hp) hcG h) hgl
  have hex' : Core.ExportSec bex (exports.map V1.Export.toCore) :=
    Section.map (fun _ h => Vec.map (fun _ _ h => Core.Export.of_v1 h) h) hex
  have hel' : Core.ElemSec (Core.Forms.ofOverlong ov) bel (elems.map Lime1.Elem.toCoreBinary) :=
    Section.map (fun _ h => Vec.map_of
      (P := fun e => e.table = ⟨0⟩ ∧ Lime1.Expr.alignsBelow64 e.offset = true)
      (fun _ _ hp h => lime1_elem_core h hp.1 hp.2) (fun e he => ⟨hcE e he, hcEA e he⟩) h) hel
  have hco' : Section 10 (Vec (Core.NumCode (Core.Forms.ofOverlong ov))) bco
      (codes.map codeToCore) :=
    Section.map (fun _ h => Vec.map_of (P := fun c => Lime1.Expr.alignsBelow64 c.2 = true)
      (fun _ _ hp h => lime1_code_core h hp) hcodes h) hco
  have hda' : Core.DataSec (Core.Forms.ofOverlong ov) bda (data.map Lime1.Data.toCore) :=
    Section.map (fun _ h => Vec.map_of
      (P := fun d => d.memory = ⟨0⟩ ∧ Lime1.Expr.alignsBelow64 d.offset = true)
      (fun _ _ hp h => lime1_data_core h hp.1 hp.2) (fun d hd => ⟨hcD d hd, hcDA d hd⟩) h) hda
  have hM := Core.NumLocalsModule.mk (c₆ := []) (btg := []) (bdc := []) (c₁₁ := [])
    h₀ hty' h₁ him' h₂ hfn h₃ htb' h₄ hme' h₅ .absent .nil hgl' h₆ hex' h₇ hst h₈ hel' h₉
    .absent .nil hco' h₁₀ hda' h₁₁ (by simp) (.inr (Core.codesDataIdxs_toCore codes))
    (by simpa using hfuncs)
  convert hM using 1
  · simp
  · simp [Lime1.Module.toCoreBinary, Lime1.Module.toCore, Core.zipFuncs_map]

/-- Lime1 encodings of compatible modules are Core 3.0 encodings without gated forms
other than those matching `ov`. Follows from `lime1_instr_core`. -/
theorem lime1_core_forms {ov : Bool} {b : Bytes} {m : Lime1.Module}
    (h : Lime1.Binary.EncodesWith ov b m) (hc : m.BinaryCompat) :
    Core.Module (Core.Forms.ofOverlong ov) b m.toCoreBinary :=
  (lime1_coreNum_forms h hc).toModule

/-- Reflection: a Core 3.0 encoding of an image module that uses no gated form outside
`ofOverlong ov`, and only numeric locals, is a Lime1 encoding. No compatibility premise
is needed: only kind `0` segments yield table/memory `0` here, and alignments `≥ 2^6`
are rejected.

The restriction to `Core.NumLocalsModule` is necessary: Core's `Blocals` admits a
zero-count entry of any value type (e.g. `00 7B`), which leaves the decoded module
unchanged but is not 1.0/Lime1 syntax (see `Core.NumLocals`). Follows from
`core_instr_lime1`. -/
theorem core_forms_lime1 {ov : Bool} {b : Bytes} {m : Lime1.Module}
    (h : Core.NumLocalsModule (Core.Forms.ofOverlong ov) b m.toCoreBinary) :
    Lime1.Binary.EncodesWith ov b m := by
  have hF := Core.Forms.ofOverlong_le_lime1 ov
  generalize hM : m.toCoreBinary = M at h
  cases h with
  | mk h₀ hty h₁ him h₂ hfn h₃ htb h₄ hme h₅ htg h₆ hgl h₇ hex h₈ hst h₉ hel h₁₀ hdc h₁₁ hco
      h₁₂ hda h₁₃ _ _ hfuncs =>
  cases htg with
  | present g _ => exact (Core.Forms.not_gate hF g (by decide)).elim
  | absent =>
  cases hdc with
  | present g _ => exact (Core.Forms.not_gate hF g (by decide)).elim
  | absent =>
  obtain ⟨mty, mim, mfn, mgl, mtb, mme, mel, mda, mst, mex⟩ := m
  simp only [Lime1.Module.toCoreBinary, Lime1.Module.toCore, Wasm.Module.mk.injEq] at hM
  obtain ⟨rfl, rfl, -, rfl, rfl, rfl, hfn', rfl, rfl, rfl, rfl⟩ := hM
  obtain ⟨rfl, rfl⟩ := Core.zipFuncs_eq_map hfuncs hfn'
  have e : (mfn.map fun f => (f.locals.map V1.ValType.toCore, Lime1.Expr.toCore f.body)) =
      (mfn.map fun f => (f.locals, f.body)).map codeToCore := by
    simp [Function.comp_def]
  rw [e] at hco
  have hM := Scalar.Binary.Module.mk (G := Lime1.Binary.Expr ov)
    (codes := mfn.map fun f => (f.locals, f.body)) (data := mda)
    h₀ (Section.of_map (fun _ h => Vec.of_map (G := V1.Binary.FuncType)
      (fun _ _ h => Core.RecType.to_v1 hF h) h) hty)
    h₁ (Section.of_map (fun _ h => Vec.of_map (G := Scalar.Binary.Import)
      (fun _ _ h => Core.Import.to_v1 hF h) h) him)
    h₂ hfn
    h₃ (Section.of_map (fun _ h => Vec.of_map (G := V1.Binary.TableType)
      (fun _ _ h => Core.Table.to_v1 hF h) h) htb)
    h₄ (Section.of_map (fun _ h => Vec.of_map (G := V1.Binary.MemType)
      (fun _ _ h => Core.MemType.to_v1 hF h) h) hme)
    (Customs.append h₅ h₆)
    (Section.of_map (fun _ h => Vec.of_map
      (G := Scalar.Binary.Global (Lime1.Binary.Expr ov)) (fun _ _ h => core_global_lime1 h) h) hgl)
    h₇ (Section.of_map (fun _ h => Vec.of_map (G := Scalar.Binary.Export)
      (fun _ _ h => Core.Export.to_v1 h) h) hex)
    h₈ hst
    h₉ (Section.of_map (fun _ h => Vec.of_map
      (G := Scalar.Binary.Elem (Lime1.Binary.Expr ov)) (fun _ _ h => core_elem_lime1 h) h) hel)
    (Customs.append h₁₀ h₁₁)
    (Section.of_map (fun _ h => Vec.of_map
      (G := Scalar.Binary.Code (Lime1.Binary.Expr ov)) (fun _ _ h => core_code_lime1 h) h) hco)
    h₁₂ (Section.of_map (fun _ h => Vec.of_map
      (G := Scalar.Binary.Data (Lime1.Binary.Expr ov)) (fun _ _ h => core_data_lime1 h) h) hda)
    h₁₃ (by simp)
  rw [Core.zipFuncs_self] at hM
  convert hM using 1
  simp

/-- Exact agreement with the restricted Core grammar (gates of `lime1` closed, numeric
locals). Follows from `lime1_instr_core` and `core_instr_lime1`. -/
theorem lime1_iff_core_forms {b : Bytes} {m : Lime1.Module} (hc : m.BinaryCompat) :
    Lime1.Binary.Encodes b m ↔ Core.NumLocalsModule Core.Forms.lime1 b m.toCoreBinary :=
  ⟨fun h => lime1_coreNum_forms (ov := true) h hc, core_forms_lime1 (ov := true)⟩

/-- Every Lime1 encoding of a compatible module is a Core 3.0 encoding of its image.
Follows from `lime1_core_forms` and `Core.Module.mono`. -/
theorem lime1_core {b : Bytes} {m : Lime1.Module} (h : Lime1.Binary.Encodes b m)
    (hc : m.BinaryCompat) : Core.Encodes b m.toCoreBinary :=
  Core.Module.mono (Core.Forms.le_all _) (lime1_core_forms (ov := true) h hc)

/-- The Core 3.0 decoding of Lime1 bytes (of a compatible module) is the image.
Follows from `lime1_core` and `Core.functional`. -/
theorem core_decode_of_lime1 {b : Bytes} {m : Lime1.Module} {m' : Wasm.Module}
    (h : Lime1.Binary.Encodes b m) (hc : m.BinaryCompat) (h' : Core.Encodes b m') :
    m' = m.toCoreBinary :=
  Core.functional h' (lime1_core h hc)

/-! ## Wasm 1.0 and Core 3.0

Derived from the Lime1 statements at `ov = false`, through `v1_iff_lime1` and the
commuting triangle `V1.Module.toLime_toCoreBinary`. -/

/-- Follows from `v1_iff_lime1` and `lime1_core_forms`. -/
theorem v1_core_forms {b : Bytes} {m : V1.Module} (h : V1.Binary.Encodes b m)
    (hc : m.BinaryCompat) : Core.Module Core.Forms.v1 b m.toCoreBinary := by
  have := lime1_core_forms (ov := false) (v1_iff_lime1.mp h) hc
  rwa [V1.Module.toLime_toCoreBinary] at this

/-- Follows from `v1_iff_lime1` and `lime1_coreNum_forms`. -/
theorem v1_coreNum_forms {b : Bytes} {m : V1.Module} (h : V1.Binary.Encodes b m)
    (hc : m.BinaryCompat) : Core.NumLocalsModule Core.Forms.v1 b m.toCoreBinary := by
  have := lime1_coreNum_forms (ov := false) (v1_iff_lime1.mp h) hc
  rwa [V1.Module.toLime_toCoreBinary] at this

/-- No compatibility premise. Follows from `v1_iff_lime1` and `core_forms_lime1`. -/
theorem core_forms_v1 {b : Bytes} {m : V1.Module}
    (h : Core.NumLocalsModule Core.Forms.v1 b m.toCoreBinary) : V1.Binary.Encodes b m := by
  rw [← V1.Module.toLime_toCoreBinary] at h
  exact v1_iff_lime1.mpr (core_forms_lime1 (ov := false) h)

/-- Exact agreement with the restricted Core grammar. Follows from the above. -/
theorem v1_iff_core_forms {b : Bytes} {m : V1.Module} (hc : m.BinaryCompat) :
    V1.Binary.Encodes b m ↔ Core.NumLocalsModule Core.Forms.v1 b m.toCoreBinary :=
  ⟨fun h => v1_coreNum_forms h hc, core_forms_v1⟩

/-- Follows from `v1_core_forms` and `Core.Module.mono`. -/
theorem v1_core {b : Bytes} {m : V1.Module} (h : V1.Binary.Encodes b m) (hc : m.BinaryCompat) :
    Core.Encodes b m.toCoreBinary :=
  Core.Module.mono (Core.Forms.le_all _) (v1_core_forms h hc)

/-- Follows from `v1_core` and `Core.functional`. -/
theorem core_decode_of_v1 {b : Bytes} {m : V1.Module} {m' : Wasm.Module}
    (h : V1.Binary.Encodes b m) (hc : m.BinaryCompat) (h' : Core.Encodes b m') :
    m' = m.toCoreBinary :=
  Core.functional h' (v1_core h hc)

/-! ## Gated forms -/

/-- `b` encodes `m` in Core 3.0 only by using a gated form outside `F`, or a
non-numeric `Blocals` entry: the Core grammar accepts it, but the grammar with those
gates closed and numeric locals (`Core.NumLocalsModule F`) does not.

This is meaningful when `m` is in the image of `V1.Module.toCoreBinary` or
`Lime1.Module.toCoreBinary`. For other modules it is not "uses Core-only syntax":
ungated Core-only productions (`v128`, GC, …) are accepted for every `F`. -/
def UsesGatedForm (F : Core.Forms) (b : Bytes) (m : Wasm.Module) : Prop :=
  Core.Encodes b m ∧ ¬ Core.NumLocalsModule F b m

/-- The strongest converse: a Core 3.0 encoding of a Lime1 module's image is either a
Lime1 encoding or uses a gated form. Follows from `core_forms_lime1`. -/
theorem core_lime1_or_gated {b : Bytes} {m : Lime1.Module}
    (h : Core.Encodes b m.toCoreBinary) :
    Lime1.Binary.Encodes b m ∨ UsesGatedForm Core.Forms.lime1 b m.toCoreBinary := by
  by_cases hf : Core.NumLocalsModule Core.Forms.lime1 b m.toCoreBinary
  · exact .inl (core_forms_lime1 (ov := true) hf)
  · exact .inr ⟨h, hf⟩

/-- No compatibility premise. Follows from `core_forms_v1`. -/
theorem core_v1_or_gated {b : Bytes} {m : V1.Module}
    (h : Core.Encodes b m.toCoreBinary) :
    V1.Binary.Encodes b m ∨ UsesGatedForm Core.Forms.v1 b m.toCoreBinary := by
  by_cases hf : Core.NumLocalsModule Core.Forms.v1 b m.toCoreBinary
  · exact .inl (core_forms_v1 hf)
  · exact .inr ⟨h, hf⟩

/-! ## The naive statements -/

/-- `toCore` itself does not agree with the binary formats: any compatible Lime1
module with an element segment has Lime1 encodings that are not Core 3.0 encodings of
its `toCore` image. Follows from `core_decode_of_lime1` (hence `lime1_core_forms`,
`Core.Module.mono` and `Core.Module.functional`). -/
theorem lime1_core_toCore_counterexample {b : Bytes} {m : Lime1.Module}
    (h : Lime1.Binary.Encodes b m) (hc : m.BinaryCompat) (he : m.elems ≠ []) :
    ¬ Core.Encodes b m.toCore := by
  intro h'
  have := core_decode_of_lime1 h hc h'
  obtain ⟨e, es, hes⟩ := List.exists_cons_of_ne_nil he
  have ht := congrArg (fun m : Wasm.Module => m.elems.head?.map Wasm.Elem.type) this
  simp [Lime1.Module.toCore, Lime1.Module.toCoreBinary, hes, Lime1.Elem.toCore,
    Lime1.Elem.toCoreBinary, V1.funcref] at ht

/-! ## Lifting relations along the embeddings -/

/-- The Lime1 → Core 3.0 embedding agrees with the encodings on compatible modules.
Follows from `lime1_core`. -/
theorem lime1_agrees :
    Encoding.Agrees (α := Lime1.Module) (β := Wasm.Module) Lime1.Module.BinaryCompat
      Lime1.Module.toCoreBinary :=
  fun _ _ h hc => lime1_core h hc

/-- Follows from `v1_core`. -/
theorem v1_agrees :
    Encoding.Agrees (α := V1.Module) (β := Wasm.Module) V1.Module.BinaryCompat
      V1.Module.toCoreBinary :=
  fun _ _ h hc => v1_core h hc

/-- Follows from `v1_lime1`. -/
theorem v1_agrees_lime1 :
    Encoding.Agrees (α := V1.Module) (β := Lime1.Module) (fun _ => True) V1.Module.toLime :=
  fun _ _ h _ => v1_lime1 h

/-- A PER on Core 3.0 modules lifts to a PER on bytes. Follows from `Core.functional`. -/
theorem core_lift_isPER {R : Wasm.Module → Wasm.Module → Prop} (hR : Encoding.IsPER R) :
    Encoding.IsPER (Encoding.Lift R) :=
  Encoding.Lift.isPER Core.functional hR

/-- A refinement preorder on Core 3.0 modules lifts to a preorder on encodable bytes.
Follows from `Core.functional`. -/
theorem core_lift_isPreorderOn {R : Wasm.Module → Wasm.Module → Prop}
    (hR : Encoding.IsPreorder R) :
    Encoding.IsPreorderOn (Encoding.Encodable Wasm.Module) (Encoding.Lift R) :=
  Encoding.Lift.isPreorderOn Core.functional hR

/-- Relating Wasm 1.0 bytes by the Core 3.0 relation `R` is the same as relating their
1.0 decodings' images: the 1.0 → Core embedding commutes with `Lift`. Follows from
`v1_agrees` and the functionality lemmas. -/
theorem v1_lift_core_iff {R : Wasm.Module → Wasm.Module → Prop} {b b' : Bytes}
    {m m' : V1.Module} (h : V1.Binary.Encodes b m) (h' : V1.Binary.Encodes b' m')
    (hc : m.BinaryCompat) (hc' : m'.BinaryCompat) :
    Encoding.Lift (α := Wasm.Module) R b b' ↔
      Encoding.Lift (α := V1.Module) (fun x y => R x.toCoreBinary y.toCoreBinary) b b' :=
  Encoding.Lift.agrees_iff V1.Binary.functional Core.functional v1_agrees h h' hc hc'

/-- Follows from `lime1_agrees` and the functionality lemmas. -/
theorem lime1_lift_core_iff {R : Wasm.Module → Wasm.Module → Prop} {b b' : Bytes}
    {m m' : Lime1.Module} (h : Lime1.Binary.Encodes b m) (h' : Lime1.Binary.Encodes b' m')
    (hc : m.BinaryCompat) (hc' : m'.BinaryCompat) :
    Encoding.Lift (α := Wasm.Module) R b b' ↔
      Encoding.Lift (α := Lime1.Module) (fun x y => R x.toCoreBinary y.toCoreBinary) b b' :=
  Encoding.Lift.agrees_iff Lime1.Binary.functional Core.functional lime1_agrees h h' hc hc'

/-- The 1.0 → Lime1 embedding commutes with `Lift` unconditionally. Follows from
`v1_agrees_lime1` and the functionality lemmas. -/
theorem v1_lift_lime1_iff {R : Lime1.Module → Lime1.Module → Prop} {b b' : Bytes}
    {m m' : V1.Module} (h : V1.Binary.Encodes b m) (h' : V1.Binary.Encodes b' m') :
    Encoding.Lift (α := Lime1.Module) R b b' ↔
      Encoding.Lift (α := V1.Module) (fun x y => R x.toLime y.toLime) b b' :=
  Encoding.Lift.agrees_iff V1.Binary.functional Lime1.Binary.functional v1_agrees_lime1 h h'
    trivial trivial

end Silmaril.Wasm.Binary
