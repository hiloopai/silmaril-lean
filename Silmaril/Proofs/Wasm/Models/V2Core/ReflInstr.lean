module

public import Silmaril.Proofs.Wasm.Models.V2Core.ReflSeq

/-!
# Every Core typing of the image of 2.0 code reads back

* `goodI`: every Wasm 2.0 instruction reflects (`GoodI`), by well-founded recursion on the
  instruction: the bodies of `block`, `loop` and `if` are smaller, and the sequence lemma
  `good_of` lifts their instructions to the body;
* **`instrs_refl`**: a Core typing of the image of a 2.0 instruction sequence, in a Core context
  that is the image of a 2.0 context, reads back (through `erT`) as a 2.0 typing.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core.Reflect

/-- An instruction whose image is a fixed Core instruction reflects when every Core typing of
that instruction reads back. -/
theorem atom {i : Silmaril.Wasm.V2.Instr} {c' : Silmaril.Wasm.Instr}
    (hc₀ : Silmaril.Wasm.V2.Instr.toCore i = some c')
    (f : ∀ {C : VCtx} {D : KCtx} {it : Silmaril.Wasm.Validation.InstrType}, Rel C D →
      KOk D c' it → VSeq C [i] (erT D.toTypeCtx it)) : GoodI i :=
  fun hR hc h => f hR (by rw [hc₀] at hc; cases hc; exact h)

/-- **Every 2.0 instruction reflects.** -/
theorem goodI : (i : Silmaril.Wasm.V2.Instr) → GoodI i
  | .select none => atom rfl fun hR h => r_selectImpl hR h
  | .select (some ts) => atom rfl fun _ h => r_selectExpl ts h
  | .cvtOp _ _ _ => fun _ hc h => by
    obtain ⟨c, hc', rfl⟩ := Option.map_eq_some_iff.mp hc
    exact r_cvtOp hc' h
  | .block _ body => fun hR hc h => by
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact r_block hR (good_of fun j (_ : j ∈ body) => goodI j) hl h
  | .loop _ body => fun hR hc h => by
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact r_loop hR (good_of fun j (_ : j ∈ body) => goodI j) hl h
  | .if_ _ b₁ b₂ => fun hR hc h => by
    obtain ⟨l₁, hl₁, hc'⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨l₂, hl₂, rfl⟩ := Option.map_eq_some_iff.mp hc'
    exact r_if hR (good_of fun j (_ : j ∈ b₁) => goodI j) (good_of fun j (_ : j ∈ b₂) => goodI j)
      hl₁ hl₂ h
  | .nop => atom rfl fun _ h => r_nop h
  | .unreachable => atom rfl fun _ h => r_unreachable h
  | .drop => atom rfl fun _ h => r_drop h
  | .br _ => atom rfl fun hR h => r_br hR h
  | .brIf _ => atom rfl fun hR h => r_brIf hR h
  | .brTable _ _ => atom rfl fun hR h => r_brTable hR h
  | .call _ => atom rfl fun hR h => r_call hR h
  | .callIndirect _ _ => atom rfl fun hR h => r_callIndirect hR h
  | .return_ => atom rfl fun hR h => r_return hR h
  | .intConst _ _ => atom rfl fun _ h => r_intConst h
  | .floatConst _ _ => atom rfl fun _ h => r_floatConst h
  | .intUnOp _ _ => atom rfl fun _ h => r_intUnOp h
  | .floatUnOp _ _ => atom rfl fun _ h => r_floatUnOp h
  | .intBinOp _ _ => atom rfl fun _ h => r_intBinOp h
  | .floatBinOp _ _ => atom rfl fun _ h => r_floatBinOp h
  | .intTestOp _ _ => atom rfl fun _ h => r_intTestOp h
  | .intRelOp _ _ => atom rfl fun _ h => r_intRelOp h
  | .floatRelOp _ _ => atom rfl fun _ h => r_floatRelOp h
  | .vecConst _ => atom rfl fun _ h => r_vecConst h
  | .vvUnOp _ => atom rfl fun _ h => r_vvUnOp h
  | .vvBinOp _ => atom rfl fun _ h => r_vvBinOp h
  | .vvTernOp _ => atom rfl fun _ h => r_vvTernOp h
  | .vvTestOp _ => atom rfl fun _ h => r_vvTestOp h
  | .vecIntUnOp _ _ => atom rfl fun _ h => r_vecIntUnOp h
  | .vecFloatUnOp _ _ => atom rfl fun _ h => r_vecFloatUnOp h
  | .vecIntBinOp _ _ => atom rfl fun _ h => r_vecIntBinOp h
  | .vecFloatBinOp _ _ => atom rfl fun _ h => r_vecFloatBinOp h
  | .vecAllTrue _ => atom rfl fun _ h => r_vecAllTrue h
  | .vecIntRelOp _ _ => atom rfl fun _ h => r_vecIntRelOp h
  | .vecFloatRelOp _ _ => atom rfl fun _ h => r_vecFloatRelOp h
  | .vecShiftOp _ _ => atom rfl fun _ h => r_vecShiftOp h
  | .vecBitmask _ => atom rfl fun _ h => r_vecBitmask h
  | .vecSwizzle => atom rfl fun _ h => r_vecSwizzle h
  | .vecShuffle _ => atom rfl fun _ h => r_vecShuffle h
  | .vecSplat _ => atom rfl fun _ h => r_vecSplat h
  | .vecExtractLane _ _ _ => atom rfl fun _ h => r_vecExtractLane h
  | .vecReplaceLane _ _ => atom rfl fun _ h => r_vecReplaceLane h
  | .vecExtUnOp _ _ _ => atom rfl fun _ h => r_vecExtUnOp h
  | .vecExtBinOp _ _ _ => atom rfl fun _ h => r_vecExtBinOp h
  | .vecNarrow _ _ _ => atom rfl fun _ h => r_vecNarrow h
  | .vecCvtOp _ _ _ => atom rfl fun _ h => r_vecCvtOp h
  | .refNull _ => atom rfl fun _ h => r_refNull h
  | .refFunc _ => atom rfl fun hR h => r_refFunc hR h
  | .refIsNull => atom rfl fun _ h => r_refIsNull h
  | .localGet _ => atom rfl fun hR h => r_localGet hR h
  | .localSet _ => atom rfl fun hR h => r_localSet hR h
  | .localTee _ => atom rfl fun hR h => r_localTee hR h
  | .globalGet _ => atom rfl fun hR h => r_globalGet hR h
  | .globalSet _ => atom rfl fun hR h => r_globalSet hR h
  | .tableGet _ => atom rfl fun hR h => r_tableGet hR h
  | .tableSet _ => atom rfl fun hR h => r_tableSet hR h
  | .tableSize _ => atom rfl fun hR h => r_tableSize hR h
  | .tableGrow _ => atom rfl fun hR h => r_tableGrow hR h
  | .tableFill _ => atom rfl fun hR h => r_tableFill hR h
  | .tableCopy _ _ => atom rfl fun hR h => r_tableCopy hR h
  | .tableInit _ _ => atom rfl fun hR h => r_tableInit hR h
  | .elemDrop _ => atom rfl fun hR h => r_elemDrop hR h
  | .intLoad _ _ _ => atom rfl fun hR h => r_intLoad hR h
  | .floatLoad _ _ => atom rfl fun hR h => r_floatLoad hR h
  | .intStore _ _ _ => atom rfl fun hR h => r_intStore hR h
  | .floatStore _ _ => atom rfl fun hR h => r_floatStore hR h
  | .vecLoad _ _ => atom rfl fun hR h => r_vecLoad hR h
  | .vecLoadLane _ _ _ => atom rfl fun hR h => r_vecLoadLane hR h
  | .vecStore _ => atom rfl fun hR h => r_vecStore hR h
  | .vecStoreLane _ _ _ => atom rfl fun hR h => r_vecStoreLane hR h
  | .memorySize => atom rfl fun hR h => r_memorySize hR h
  | .memoryGrow => atom rfl fun hR h => r_memoryGrow hR h
  | .memoryFill => atom rfl fun hR h => r_memoryFill hR h
  | .memoryCopy => atom rfl fun hR h => r_memoryCopy hR h
  | .memoryInit _ => atom rfl fun hR h => r_memoryInit hR h
  | .dataDrop _ => atom rfl fun hR h => r_dataDrop hR h
termination_by i => sizeOf i
decreasing_by
  all_goals
    have := List.sizeOf_lt_of_mem ‹_›
    simp_wf
    omega

/-- **Core typings of the image of 2.0 code read back.** -/
theorem instrs_refl {C : VCtx} {D : KCtx} {is : List Silmaril.Wasm.V2.Instr}
    {l : List Silmaril.Wasm.Instr} {it : Silmaril.Wasm.Validation.InstrType} (hR : Rel C D)
    (hc : Silmaril.Wasm.V2.Expr.toCore is = some l) (h : Silmaril.Wasm.Validation.InstrsOk D l it) :
    VSeq C is (erT D.toTypeCtx it) :=
  good_of (fun i _ => goodI i) hR hc h

end Silmaril.Proofs.Wasm.Models.V2Core.Reflect
