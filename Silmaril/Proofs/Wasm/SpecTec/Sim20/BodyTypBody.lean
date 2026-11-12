module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.BodyTypOps

/-!
# IL typing of erased function bodies, and `InvokeOk` without the typing assumption

* `typedV_blockType`: every block type is a `blocktype`.
* **`typedA_eD`**: every instruction the forward invariant covers (`StoreBulk.ctrlOkB`), erased
  by `StoreDeep.eD`, is an `admininstr` of `simEnv20 B`, when its packed loads are below their
  type's width (`packOkI`). The proof is a strong induction on the instruction's size; blocks,
  loops and conditionals recurse into their bodies, scalar stores become `nop`.
* **`typedV_body_eD`**: such a body, erased, is a typed `instr*`, the last component of
  `StoreBulk.InvokeOk`.
* `InvokeOkS`: `StoreBulk.InvokeOk` with the body typing replaced by `packOkI` on the bodies.
  **`invokeOk_of_S`**: under `StoreOkB`, `InvokeOkS` gives `InvokeOk`, and
  **`good20B_invoke_okS`** gives `Good20B` at `val* (CALL_ADDR a)`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.BodyTyp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (ctrlOkB bulkOkI StoreOkB StoreSmall InvokeOk Good20B
  FuncTypeSmall TypesSmall NamesTyped)
open Silmaril.Wasm.SpecTec.Sim20.StoreDeep (eD ctrlOkD)

set_option maxRecDepth 100000

variable {B : Builtins}

/-! ## Block types -/

theorem findTyp_blocktype20 : (simEnv20 B).findTyp? "blocktype" = some ([], [.instD [] []
    (.variantT [.mk "_RESULT" (.iterT (.varT "valtype" []) .opt) [] [],
      .mk "_IDX" (.varT "typeidx" []) [] []])]) := rfl

/-- **Every block type is a `blocktype`.** -/
theorem typedV_blockType (bt : V2.BlockType) : TypedV (simEnv20 B) Pure.blocktypeT (blockTypeV bt) := by
  rcases bt with t | x
  · refine Pure.typedV_closedCase20 findTyp_blocktype20 rfl (hasTyp_iterT_opt_iff.2 ?_)
    rcases t with _ | t
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl, Whole.typedV_valType20 t _ valsOnly_empty⟩
  · exact Pure.typedV_closedCase20 findTyp_blocktype20 rfl (typedV_idxA (by decide) x _ valsOnly_empty)

/-- A triple of payloads, each typed in every term-only scope. -/
theorem hasTyp_tup3 {a b c : IL.Id} {τ₁ τ₂ τ₃ : Typ} {u v w : Value} (h₁ : TypedV (simEnv20 B) τ₁ u)
    (h₂ : TypedV (simEnv20 B) τ₂ v) (h₃ : TypedV (simEnv20 B) τ₃ w) :
    HasTyp (simEnv20 B) VarEnv.empty (.tupT [.mk a τ₁, .mk b τ₂, .mk c τ₃]) (.tuple [u, v, w]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, h₁ _ valsOnly_empty,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_bind h₂ _ valsOnly_empty _ _,
      hasTypTup_cons_iff.2 ⟨_, _, rfl,
        hasTyp_bind h₃ _ (Sim.ConfigOk.valsOnly_bindVal valsOnly_empty _ _) _ _,
        hasTypTup_nil_iff.2 rfl⟩⟩⟩⟩

theorem typedA_loop {bt : V2.BlockType} {b : List V2.Instr}
    (h : TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV b))) : TypedA B (.loop bt b) :=
  typedA_case rfl (Whole.hasTyp_tup2G (typedV_blockType bt) h)

theorem typedA_if {bt : V2.BlockType} {b₁ b₂ : List V2.Instr}
    (h₁ : TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV b₁)))
    (h₂ : TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV b₂))) : TypedA B (.if_ bt b₁ b₂) :=
  typedA_case rfl (hasTyp_tup3 (typedV_blockType bt) h₁ h₂)

/-! ## Packed loads -/

mutual
/-- **Every packed load is below its type's width**, at every depth. -/
def packOkI : V2.Instr → Bool
  | .intLoad t (some (sz, _)) _ => decide (sz.width < t.width)
  | .block _ b | .loop _ b => packOkIL b
  | .if_ _ l r => packOkIL l && packOkIL r
  | _ => true

/-- `packOkI` on a sequence. -/
def packOkIL : List V2.Instr → Bool
  | [] => true
  | i :: is => packOkI i && packOkIL is
end

@[simp] theorem packOkIL_eq (l : List V2.Instr) : packOkIL l = l.all packOkI := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [packOkIL, ih]

theorem packOk_of {t : IntType} {p : Option (PackSize × Signedness)} {a : V2.MemArg}
    (h : packOkI (.intLoad t p a) = true) : PackOk t p := by
  rcases p with _ | ⟨sz, sx⟩
  · trivial
  · simpa [packOkI, PackOk] using h

/-! ## Erased instructions -/

/-- A list of instructions each typed as an `admininstr` is a typed `instr*`. -/
theorem typedV_instrs_of {l : List V2.Instr} (h : ∀ i ∈ l, TypedA B i) :
    TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV l)) := by
  rw [Whole.instrsToV_map20]
  exact Sim.typedV_list_iff.2 fun u hu => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hu
    exact (Whole.typedV_plain20_iff i).1 (h i hi)

/-- The non-block covered instructions, erased, are typed. -/
theorem typedA_eD_flat (m : ModuleInst) (i : V2.Instr) (hok : ctrlOkB m i = true)
    (hp : packOkI i = true) (hb : ∀ bt b, i ≠ .block bt b) (hl : ∀ bt b, i ≠ .loop bt b)
    (hi : ∀ bt b₁ b₂, i ≠ .if_ bt b₁ b₂) : TypedA B (eD i) := by
  cases i with
  | block bt b => exact absurd rfl (hb bt b)
  | loop bt b => exact absurd rfl (hl bt b)
  | if_ bt b₁ b₂ => exact absurd rfl (hi bt b₁ b₂)
  | intStore t p a => exact typedA_nop
  | floatStore t a => exact typedA_nop
  | intLoad t p a => exact typedA_intLoad t p a (packOk_of hp)
  | intUnOp t op =>
    have hv : op.valid t = true := by
      simpa [ctrlOkB, ctrlOkD, GoodMerge.ctrlOkM, CallIndGood.ctrlOkI, Whole.ctrlOk, bulkOkI,
        StoreGood.storeOkI] using hok
    exact typedA_intUnOp t op hv
  | cvtOp t₁ t₂ op =>
    have hv : (op.toShared t₁ t₂).isSome = true := by
      simpa [ctrlOkB, ctrlOkD, GoodMerge.ctrlOkM, CallIndGood.ctrlOkI, Whole.ctrlOk, bulkOkI,
        StoreGood.storeOkI] using hok
    exact typedA_cvtOp t₁ t₂ op hv
  | nop => exact typedA_nop
  | unreachable => exact typedA_unreachable
  | drop => exact typedA_drop
  | return_ => exact typedA_return
  | refIsNull => exact typedA_refIsNull
  | memorySize => exact typedA_memorySize
  | memoryFill => exact typedA_memoryFill
  | memoryCopy => exact typedA_memoryCopy
  | br l => exact typedA_br l
  | brIf l => exact typedA_brIf l
  | call x => exact typedA_call x
  | refFunc x => exact typedA_refFunc x
  | localGet x => exact typedA_localGet x
  | localSet x => exact typedA_localSet x
  | localTee x => exact typedA_localTee x
  | globalGet x => exact typedA_globalGet x
  | globalSet x => exact typedA_globalSet x
  | tableGet x => exact typedA_tableGet x
  | tableSet x => exact typedA_tableSet x
  | tableSize x => exact typedA_tableSize x
  | tableFill x => exact typedA_tableFill x
  | memoryInit x => exact typedA_memoryInit x
  | dataDrop x => exact typedA_dataDrop x
  | elemDrop x => exact typedA_elemDrop x
  | callIndirect x y => exact typedA_callIndirect x y
  | tableCopy x y => exact typedA_tableCopy x y
  | tableInit x y => exact typedA_tableInit x y
  | brTable ls l => exact typedA_brTable ls l
  | select ts => exact typedA_select ts
  | refNull t => exact typedA_refNull t
  | intConst t b => exact typedA_intConst t b
  | floatConst t b => exact typedA_floatConst t b
  | vecConst b => exact typedA_vecConst b
  | floatUnOp t op => exact typedA_floatUnOp t op
  | intBinOp t op => exact typedA_intBinOp t op
  | floatBinOp t op => exact typedA_floatBinOp t op
  | intTestOp t op => exact typedA_intTestOp t op
  | intRelOp t op => exact typedA_intRelOp t op
  | floatRelOp t op => exact typedA_floatRelOp t op
  | floatLoad t a => exact typedA_floatLoad t a
  | _ =>
    simp [ctrlOkB, ctrlOkD, GoodMerge.ctrlOkM, CallIndGood.ctrlOkI, Whole.ctrlOk, bulkOkI,
      StoreGood.storeOkI] at hok

/-- The members of a body are smaller than the block holding it. -/
theorem sizeOf_mem_lt {l : List V2.Instr} {j : V2.Instr} (hj : j ∈ l) : sizeOf j < sizeOf l :=
  List.sizeOf_lt_of_mem hj

/-- A body typing, for the bodies of one block. -/
abbrev BodyT (B : Builtins) (m : ModuleInst) (b : List V2.Instr) : Prop :=
  b.all (ctrlOkB m) = true → b.all packOkI = true →
    TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV (b.map eD)))

theorem typedA_eD_block {m : ModuleInst} {bt : V2.BlockType} {b : List V2.Instr}
    (hT : BodyT B m b) (hok : ctrlOkB m (.block bt b) = true)
    (hp : packOkI (.block bt b) = true) : TypedA B (eD (.block bt b)) := by
  have hok' : b.all (ctrlOkB m) = true := by simpa using hok
  have hp' : b.all packOkI = true := by simpa [packOkI] using hp
  have he : eD (.block bt b) = .block bt (b.map eD) := StoreDeep.eD_block bt b
  rw [he]
  exact Whole.typed_block20 (typedV_blockType bt) (hT hok' hp')

theorem typedA_eD_loop {m : ModuleInst} {bt : V2.BlockType} {b : List V2.Instr}
    (hT : BodyT B m b) (hok : ctrlOkB m (.loop bt b) = true)
    (hp : packOkI (.loop bt b) = true) : TypedA B (eD (.loop bt b)) := by
  have hok' : b.all (ctrlOkB m) = true := by simpa using hok
  have hp' : b.all packOkI = true := by simpa [packOkI] using hp
  have he : eD (.loop bt b) = .loop bt (b.map eD) := StoreDeep.eD_loop bt b
  rw [he]
  exact typedA_loop (hT hok' hp')

theorem typedA_eD_if {m : ModuleInst} {bt : V2.BlockType} {b₁ b₂ : List V2.Instr}
    (hT₁ : BodyT B m b₁) (hT₂ : BodyT B m b₂) (hok : ctrlOkB m (.if_ bt b₁ b₂) = true)
    (hp : packOkI (.if_ bt b₁ b₂) = true) : TypedA B (eD (.if_ bt b₁ b₂)) := by
  have hok' : b₁.all (ctrlOkB m) = true ∧ b₂.all (ctrlOkB m) = true := by simpa using hok
  have hp' : b₁.all packOkI = true ∧ b₂.all packOkI = true := by simpa [packOkI] using hp
  have he : eD (.if_ bt b₁ b₂) = .if_ bt (b₁.map eD) (b₂.map eD) := StoreDeep.eD_if bt b₁ b₂
  rw [he]
  exact typedA_if (hT₁ hok'.1 hp'.1) (hT₂ hok'.2 hp'.2)

/-- **Every covered instruction, erased, is typed**, below a size bound. -/
theorem typedA_eD_lt (m : ModuleInst) (n : Nat) :
    ∀ i : V2.Instr, sizeOf i < n → ctrlOkB m i = true → packOkI i = true → TypedA B (eD i) := by
  induction n with
  | zero => intro i hs; omega
  | succ n ih =>
    show ∀ i : V2.Instr, sizeOf i < n + 1 → ctrlOkB m i = true → packOkI i = true →
      TypedA B (eD i)
    intro i hs hok hp
    have hbody : ∀ b : List V2.Instr, sizeOf b < n → BodyT B m b :=
      fun b hb hok' hp' => typedV_instrs_of fun j hj => by
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hj
        have hk' : sizeOf k < n := Nat.lt_trans (sizeOf_mem_lt hk) hb
        exact ih k hk' (List.all_eq_true.1 hok' k hk) (List.all_eq_true.1 hp' k hk)
    cases i with
    | block bt b =>
      have hb : sizeOf b < n := by simp only [V2.Instr.block.sizeOf_spec] at hs; omega
      exact typedA_eD_block (hbody b hb) hok hp
    | loop bt b =>
      have hb : sizeOf b < n := by simp only [V2.Instr.loop.sizeOf_spec] at hs; omega
      exact typedA_eD_loop (hbody b hb) hok hp
    | if_ bt b₁ b₂ =>
      have hb : sizeOf b₁ < n ∧ sizeOf b₂ < n := by
        simp only [V2.Instr.if_.sizeOf_spec] at hs; omega
      exact typedA_eD_if (hbody b₁ hb.1) (hbody b₂ hb.2) hok hp
    | _ => exact typedA_eD_flat m _ hok hp (by simp) (by simp) (by simp)

/-- **Every covered instruction, erased, is an `admininstr` of `simEnv20 B`.** -/
theorem typedA_eD (m : ModuleInst) (i : V2.Instr) (hok : ctrlOkB m i = true)
    (hp : packOkI i = true) : TypedA B (eD i) :=
  typedA_eD_lt m _ i (Nat.lt_succ_self _) hok hp

/-- **A covered body, erased, is a typed `instr*` of `simEnv20 B`.** -/
theorem typedV_body_eD (m : ModuleInst) (l : List V2.Instr) (hok : l.all (ctrlOkB m) = true)
    (hp : l.all packOkI = true) :
    TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV (l.map eD))) :=
  typedV_instrs_of fun j hj => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hj
    exact typedA_eD m k (List.all_eq_true.1 hok k hk) (List.all_eq_true.1 hp k hk)

/-! ## `InvokeOk` without the typing assumption -/

variable {H : Type}

/-- **`StoreBulk.InvokeOk` with the body typing replaced by `packOkI`.** -/
structure InvokeOkS (B : Builtins) (s : Store H) (f : Frame) : Prop where
  frameTypes : TypesSmall f.module
  frameNames : NamesTyped B f.module
  funcs : ∀ fi ∈ s.funcs, FuncTypeSmall fi.type ∧ TypesSmall fi.module ∧ NamesTyped B fi.module
  packs : ∀ fi ∈ s.funcs, ∀ fn, fi.code = .wasm fn → fn.body.all packOkI = true

/-- **`InvokeOkS` and `StoreOkB` give `InvokeOk`.** -/
theorem invokeOk_of_S {s : Store H} {f : Frame} (h : InvokeOkS B s f) (hs : StoreOkB s) :
    Silmaril.Wasm.SpecTec.Sim20.StoreBulk.InvokeOk B s f where
  frameTypes := h.frameTypes
  frameNames := h.frameNames
  funcs fi hfi := by
    obtain ⟨a, ha⟩ := List.mem_iff_getElem?.1 hfi
    obtain ⟨fn, hc, hok⟩ := hs a fi ha
    obtain ⟨h₁, h₂, h₃⟩ := h.funcs fi hfi
    exact ⟨fn, hc, h₁, h₂, h₃, typedV_body_eD fi.module fn.body hok (h.packs fi hfi fn hc)⟩

/-- **`Good20B` at an invocation, with no typing assumption on the bodies.** -/
theorem good20B_invoke_okS {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile} {s : Store H}
    {f : Frame} {args : List Val} {a : FuncAddr} (h : InvokeOkS (Whole.storeB P) s f)
    (hs : StoreOkB s) (hm : StoreSmall s) : Good20B hn P ⟨s, f, vals args ++ [.callAddr a]⟩ :=
  StoreBulk.good20B_invoke_ok (invokeOk_of_S h hs) hs hm

end Silmaril.Wasm.SpecTec.Sim20.BodyTyp
