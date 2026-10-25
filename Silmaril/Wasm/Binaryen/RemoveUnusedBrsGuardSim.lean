module

public import Silmaril.Wasm.Binaryen.CodeSimModule
public import Silmaril.Wasm.SingleThreaded.Determinism.Stuck
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet
public import Silmaril.Wasm.SingleThreaded.HeadInversion

@[expose] public section

/-! # Guard inversion as a code simulation (one direction)

RemoveUnusedBrs turns `block [] (local.get x; br_if 0; R)` (the **original** `O`) into
`local.get x; i32.eqz; if [] R' end` (the **result** `T`, with `R'` the rewritten
`R`). The two sides run as follows, `v` the value of local `x`:

* `O`: enter the block, read `x`, `br_if` (to `label{R}` when `v = 0`, to
  `label{br 0; R}` and then `[]` otherwise);
* `T`: read `x`, `eqz`, `if` (to `block R'` or `block []`), enter the block.

`guardBaseSim` is the `BaseSim` (`Sim/Closure/Basic.lean`) with `T` on the left: the
read of `T` is matched by the block entry and the read of `O` (two steps, in the same
frame), `eqz` and `if` of `T` stutter (the code shrinks), and the block entry of `T`
is matched by the `br_if` of `O`. Every intermediate pair holds the value `v` on both
sides, so the pairs do not depend on the frame.

The converse is proved in `RemoveUnusedBrsGuardAny.lean`: a body-aware rank pays
for the first block-entry stutter, and an entered phase leaves both local reads
pending until they can be matched in the same frame. That yields a frame-free
`BaseSim` in each direction at the same arbitrary numerical profile.

Steps are inverted with `Det.Step.decomp` (closed host).
-/

namespace Silmaril.Wasm.Binaryen.GuardSim

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded

variable {H : Type} {P : Profile}

/-! ## Inverting the head steps of the result side -/

/-- A closed-host step of `val* e rest`, for a head `e` that is neither a trap nor
`throw_ref`, is a head step at `e`. -/
theorem head_inv {s : Store H} {f : Frame} {W : List Val} {e : Admin} {rest : List Admin}
    {c' : Config H} (he : e.val? = none) (htrap : e ≠ .trap) (hthrow : e ≠ .plain .throwRef)
    (h : Step P closedHost ⟨s, f, vals W ++ e :: rest⟩ c') :
    ∃ vs args c₀, W = vs ++ args ∧ Det.Head P s f args e c₀ ∧
      c' = ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩ :=
  SingleThreaded.hostFree_head_inv he htrap hthrow h

theorem vals_eq_nil {vs : List Val} (h : vals vs = []) : vs = [] := by
  cases vs <;> simp_all [vals]

/-- `local.get x` reads the local. -/
theorem head_localGet {s : Store H} {f : Frame} {args : List Val} {x : LocalIdx} {c₀ : Config H}
    (h : Det.Head P s f args (.plain (.localGet x)) c₀) :
    args = [] ∧ ∃ v, f.local? x = some (some v) ∧ c₀ = ⟨s, f, [v.toAdmin]⟩ := by
  have hv := h.fam_inv (by simp [Det.famOf])
  simp only [Det.famOf, Det.FamRel] at hv
  generalize hc : (⟨s, f, vals args ++ [.plain (.localGet x)]⟩ : Config H) = c at hv
  cases hv with
  | @localGet s' f' x' v hl =>
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, rfl, hc⟩ := hc
    have := (Det.append_singleton_inj (l₂ := [])).mp hc
    obtain ⟨h1, h2⟩ := this
    simp only [Admin.plain.injEq, Instr.localGet.injEq] at h2
    subst h2
    exact ⟨vals_eq_nil h1, v, hl, rfl⟩
  | _ =>
    simp only [Config.mk.injEq] at hc
    have := congrArg List.getLast? hc.2.2
    simp at this

/-- `i32.eqz` tests its operand. -/
theorem head_eqz {s : Store H} {f : Frame} {args : List Val} {c₀ : Config H}
    (h : Det.Head P s f args (.plain (.intTestOp .i32 .eqz)) c₀) :
    ∃ c : BitVec 32, args = [.num ⟨.int .i32, c⟩] ∧
      c₀ = ⟨s, f, [constI32 (intTestOp .i32 .eqz c)]⟩ := by
  have hv := h.fam_inv (by simp [Det.famOf])
  simp only [Det.famOf, Det.FamRel] at hv
  obtain ⟨is', hv, rfl⟩ := hv
  generalize hc : vals args ++ [Admin.plain (.intTestOp .i32 .eqz)] = l at hv
  cases hv with
  | @intTestOp t op x =>
    obtain ⟨h1, h2⟩ := (Det.append_singleton_inj (l₂ := [Admin.plain (.intConst t x)])).mp hc
    simp only [Admin.plain.injEq, Instr.intTestOp.injEq] at h2
    obtain ⟨rfl, -⟩ := h2
    cases op
    obtain ⟨w, rfl⟩ : ∃ w, args = [w] := by
      have hl := congrArg List.length h1
      simp only [vals, List.length_map, List.length_singleton] at hl
      match args, hl with
      | [w], _ => exact ⟨w, rfl⟩
    simp only [vals, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1
    have hw := Det.toAdmin_eq_iff.mp h1
    simp only [Admin.val?, Option.some.injEq] at hw
    subst hw
    exact ⟨x, rfl, rfl⟩
  | _ =>
    have := congrArg List.getLast? hc
    simp at this

set_option hygiene false in
/-- A family rule at a control instruction is impossible. -/
local macro "fam_no" : tactic => `(tactic| first
  | exact absurd (Det.famOf_of_shape (Det.ParametricStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.NumericStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.VectorStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.VariableStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.TableStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.MemoryStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.RefStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.AggregateStep.shape ‹_›)).2 (by simp [Det.famOf])
  | (exfalso; simp_all [Admin.IsCallRef, Admin.IsReturnCallRef]))

/-- `if` selects a branch. -/
theorem head_if {s : Store H} {f : Frame} {args : List Val} {bt : BlockType} {b₁ b₂ : List Instr}
    {c₀ : Config H} (h : Det.Head P s f args (.plain (.if_ bt b₁ b₂)) c₀) :
    ∃ c : BitVec 32, args = [.num ⟨.int .i32, c⟩] ∧
      c₀ = ⟨s, f, [.plain (.block bt (if c = 0 then b₂ else b₁))]⟩ := by
  cases h with
  | ifTrue hc => exact ⟨_, rfl, by simp only [hc, ↓reduceIte]⟩
  | ifFalse hc => exact ⟨_, rfl, by simp only [hc, ↓reduceIte]⟩
  | _ => fam_no

/-- An empty-typed `block` enters its label. -/
theorem head_block {s : Store H} {f : Frame} {args : List Val} {body : List Instr}
    {c₀ : Config H} (h : Det.Head P s f args (.plain (.block .empty body)) c₀) :
    args = [] ∧ c₀ = ⟨s, f, [.label 0 [] (expression body)]⟩ := by
  cases h with
  | block hbt hm =>
    simp only [ModuleInst.blockType?, Option.some.injEq, Prod.mk.injEq] at hbt
    obtain ⟨rfl, rfl⟩ := hbt
    simp only [List.length_nil, List.length_eq_zero_iff] at hm
    subst hm
    exact ⟨rfl, by simp [vals]⟩
  | _ => fam_no

/-- An empty label exits. -/
theorem head_label_nil {s : Store H} {f : Frame} {args : List Val} {c₀ : Config H}
    (h : Det.Head P s f args (.label 0 [] []) c₀) : args = [] ∧ c₀ = ⟨s, f, []⟩ := by
  cases h with
  | ctxtLabel h => exact (Det.not_step_vals (W := []) (by simpa [vals] using h)).elim
  | labelVals hb =>
    obtain rfl := vals_eq_nil hb.symm
    exact ⟨rfl, rfl⟩
  | brLabelZero hb => simp at hb
  | brLabelSucc hb => simp at hb
  | returnCallRefLabel hb => simp at hb
  | returnLabel hb => simp at hb
  | _ => fam_no

/-! ## Base relations -/

/-- Source base pairs, stratified so that the tails may themselves hold base pairs. -/
def GBI : Nat → List Instr → List Instr → Prop
  | 0, _, _ => False
  | n + 1, x, y => ∃ (i : LocalIdx) (l : LabelIdx) (R R' : List Instr), l.toNat = 0 ∧
      InstrsRel (GBI n) R R' ∧ x = [.block .empty (.localGet i :: .brIf l :: R)] ∧
      y = [.localGet i, .intTestOp .i32 .eqz, .if_ .empty R' []]

/-- Source base pairs: the original guard on the left, the inverted one on the right. -/
def guardBI (x y : List Instr) : Prop := ∃ n, GBI n x y

mutual
theorem InstrRel.mono {BI BI' : List Instr → List Instr → Prop} (hB : ∀ x y, BI x y → BI' x y) :
    ∀ {i i' : Instr}, InstrRel BI i i' → InstrRel BI' i i'
  | _, _, .refl i => .refl i
  | _, _, .block bt h => .block bt (InstrsRel.mono hB h)
  | _, _, .loop bt h => .loop bt (InstrsRel.mono hB h)
  | _, _, .if_ bt h₁ h₂ => .if_ bt (InstrsRel.mono hB h₁) (InstrsRel.mono hB h₂)
  | _, _, .tryTable bt cs h => .tryTable bt cs (InstrsRel.mono hB h)
theorem InstrsRel.mono {BI BI' : List Instr → List Instr → Prop} (hB : ∀ x y, BI x y → BI' x y) :
    ∀ {x y : List Instr}, InstrsRel BI x y → InstrsRel BI' x y
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (InstrRel.mono hB h) (InstrsRel.mono hB t)
  | _, _, .base h => .base (hB _ _ h)
  | _, _, .append h t => .append (InstrsRel.mono hB h) (InstrsRel.mono hB t)
end

theorem instrsRel_guard {n : Nat} {R R' : List Instr} (h : InstrsRel (GBI n) R R') :
    InstrsRel guardBI R R' :=
  InstrsRel.mono (fun _ _ h => ⟨n, h⟩) h

/-- Runtime states of a guard pair (original, result), `l` the label `0`. -/
inductive GS (l : LabelIdx) (R R' : List Instr) : List Admin → List Admin → Prop where
  | start (i : LocalIdx) : GS l R R' [.plain (.block .empty (.localGet i :: .brIf l :: R))]
      [.plain (.localGet i), .plain (.intTestOp .i32 .eqz), .plain (.if_ .empty R' [])]
  | read (v : Val) : GS l R R' [.label 0 [] (v.toAdmin :: .plain (.brIf l) :: expression R)]
      [v.toAdmin, .plain (.intTestOp .i32 .eqz), .plain (.if_ .empty R' [])]
  | test (c : BitVec 32) : GS l R R'
      [.label 0 [] (constI32 c :: .plain (.brIf l) :: expression R)]
      [constI32 (intTestOp .i32 .eqz c), .plain (.if_ .empty R' [])]
  | pick (c : BitVec 32) : GS l R R'
      [.label 0 [] (constI32 c :: .plain (.brIf l) :: expression R)]
      [.plain (.block .empty (if c = 0 then R' else []))]
  | exit : GS l R R' [.label 0 [] (.plain (.br l) :: expression R)] [.label 0 [] []]

/-- Runtime base pairs. -/
def guardB (x y : List Admin) : Prop :=
  ∃ (l : LabelIdx) (R R' : List Instr), l.toNat = 0 ∧ InstrsRel guardBI R R' ∧ GS l R R' x y

/-! ## Sizes -/

theorem codeSize_replace_lt (p q m : List Admin) (a : Admin) (h : codeSize [a] < codeSize m) :
    codeSize (p ++ [a] ++ q) < codeSize (p ++ m ++ q) := by
  have h1 := codeSize_append (p ++ [a]) q
  have h2 := codeSize_append p [a]
  have h3 := codeSize_append (p ++ m) q
  have h4 := codeSize_append p m
  omega

theorem eqz_eq_zero (c : BitVec 32) : intTestOp .i32 .eqz c = 0 ↔ c ≠ 0 := by
  show (if (c == (0 : BitVec 32)) = true then (1 : BitVec 32) else 0) = 0 ↔ c ≠ 0
  by_cases hc : c = 0 <;> simp [hc]

theorem bv_sizeOf {n : Nat} (b : BitVec n) : sizeOf b = b.toNat + 2 := by
  cases b with
  | ofFin f => cases f; simp

theorem sizeOf_intConst32 (c : BitVec 32) :
    sizeOf (Instr.intConst .i32 c) = 1 + sizeOf IntType.i32 + sizeOf c := rfl

theorem codeSize_eqz (c : BitVec 32) :
    codeSize [constI32 (intTestOp .i32 .eqz c)] <
      codeSize [constI32 c, .plain (.intTestOp .i32 .eqz)] := by
  simp only [codeSize, List.cons.sizeOf_spec, List.nil.sizeOf_spec, constI32, Val.i32,
    Val.toAdmin, Admin.plain.sizeOf_spec, sizeOf_intConst32, bv_sizeOf]
  have : (intTestOp .i32 .eqz c).toNat ≤ 1 := by
    unfold intTestOp bool32; split <;> simp
  omega

theorem codeSize_if (b : BitVec 32) {B R' : List Instr} (hB : B = R' ∨ B = []) :
    codeSize [.plain (.block .empty B)] < codeSize [constI32 b, .plain (.if_ .empty R' [])] := by
  have hle : sizeOf B ≤ sizeOf R' := by
    rcases hB with rfl | rfl
    · exact le_refl _
    · cases R' <;> simp
      omega
  simp only [codeSize, List.cons.sizeOf_spec, List.nil.sizeOf_spec, Admin.plain.sizeOf_spec,
    Instr.block.sizeOf_spec, Instr.if_.sizeOf_spec]
  omega

/-! ## The simulation -/

/-- No exit kernel starts at a head that is neither a branch, `return`, a tail call,
`trap` nor `throw_ref`. -/
theorem not_exit {W us : List Val} {e₀ : Admin} {x' k j : List Admin} (he₀ : e₀.val? = none)
    (hbr : ∀ l, e₀ ≠ .plain (.br l)) (hret : e₀ ≠ .plain .return_) (hrc : ¬ e₀.IsReturnCallRef)
    (htr : e₀ ≠ .trap) (hth : e₀ ≠ .plain .throwRef) (hk : Exit k)
    (h : vals W ++ e₀ :: x' = vals us ++ k ++ j) : False := by
  have key : ∀ (pre : List Val) (e : Admin), e.val? = none → k = vals pre ++ [e] → e₀ = e := by
    intro pre e hen hke
    have h' : vals W ++ e₀ :: x' = vals (us ++ pre) ++ e :: j := by rw [h, hke]; simp
    exact (vals_append_cons_inj he₀ hen h').2.1
  cases hk with
  | br l => exact hbr l (key [] _ rfl rfl)
  | return_ => exact hret (key [] _ rfl rfl)
  | returnCallRef hc => exact hrc (by rw [key [] _ (Det.IsReturnCallRef.val_none hc) rfl]; exact hc)
  | trap => exact htr (key [] _ rfl rfl)
  | throw a => exact hth (key [.ref (.exn a)] _ rfl rfl)

/-- **The result side simulates the original**: `BaseSim` with `T` on the left. -/
theorem guardBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P closedHost F (fun a b => guardBI b a) (fun a b => guardB b a) where
  src := by
    rintro x y ⟨n, h⟩
    cases n with
    | zero => exact h.elim
    | succ n =>
      obtain ⟨i, l, R, R', hl, hR, rfl, rfl⟩ := h
      exact ⟨l, R, R', hl, instrsRel_guard hR, by simpa [expression] using GS.start i⟩
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    obtain ⟨l, R, R', hl, hR, hg⟩ := hxy
    cases hg with
    | start i =>
      have e : vals vs ++ [Admin.plain (.localGet i), .plain (.intTestOp .i32 .eqz),
          .plain (.if_ .empty R' [])] ++ rest = vals vs ++ .plain (.localGet i) ::
          (.plain (.intTestOp .i32 .eqz) :: .plain (.if_ .empty R' []) :: rest) := by simp
      rw [e] at hstep
      obtain ⟨vs, args, c₀, hW, hh, hc'⟩ := head_inv rfl (by simp) (by simp) hstep
      obtain ⟨rfl, v, hv, rfl⟩ := head_localGet hh
      simp only [List.append_nil] at hW
      subst hW
      simp only [Config.mk.injEq] at hc'
      obtain ⟨h1, h2, h3⟩ := hc'
      subst h3
      have h1 := h1.symm
      have h2 := h2.symm
      subst h1 h2
      refine ⟨t, vals vs ++ [.label 0 [] (v.toAdmin :: .plain (.brIf l) :: expression R)] ++ rest',
        Or.inl ?_, hst, ?_⟩
      · have h1 : Step P closedHost
            ⟨t, f, vals vs ++ [.plain (.block .empty (.localGet i :: .brIf l :: R))] ++ rest'⟩
            ⟨t, f, vals vs ++ [.label 0 [] (expression (.localGet i :: .brIf l :: R))] ++ rest'⟩ := by
          have := Step.append_right (Step.vals_left (Step.block (P := P) (host := closedHost)
            (s := t) (f := f) (bt := .empty) (body := .localGet i :: .brIf l :: R) (vs := [])
            (t₁ := []) (t₂ := []) rfl rfl) vs) rest'
          simpa [vals] using this
        have h2 : Step P closedHost
            ⟨t, f, vals vs ++ [.label 0 [] (expression (.localGet i :: .brIf l :: R))] ++ rest'⟩
            ⟨t, f, vals vs ++ [.label 0 [] (v.toAdmin :: .plain (.brIf l) :: expression R)] ++
              rest'⟩ := by
          have hin : Step P closedHost ⟨t, f, [.plain (.localGet i)]⟩ ⟨t, f, [v.toAdmin]⟩ :=
            Step.variable (VariableStep.localGet hv)
          have := Step.append_right (Step.vals_left (Step.ctxtLabel (n := 0) (cont := [])
            (Step.append_right hin (.plain (.brIf l) :: expression R))) vs) rest'
          simpa [expression] using this
        exact .tail (.single h1) h2
      · have e : vals vs ++ [v.toAdmin] ++ (.plain (.intTestOp .i32 .eqz) ::
            .plain (.if_ .empty R' []) :: rest) = vals vs ++ [v.toAdmin,
            .plain (.intTestOp .i32 .eqz), .plain (.if_ .empty R' [])] ++ rest := by simp
        rw [e]
        exact ((AdminsRel.refl _).append (AdminsRel.base ⟨l, R, R', hl, hR, GS.read v⟩)).append
          hrest
    | read v =>
      have e : vals vs ++ [v.toAdmin, .plain (.intTestOp .i32 .eqz), .plain (.if_ .empty R' [])] ++
          rest = vals (vs ++ [v]) ++ .plain (.intTestOp .i32 .eqz) ::
          (.plain (.if_ .empty R' []) :: rest) := by simp
      rw [e] at hstep
      obtain ⟨vs₀, args, c₀, hW, hh, hc'⟩ := head_inv rfl (by simp) (by simp) hstep
      obtain ⟨c, rfl, rfl⟩ := head_eqz hh
      obtain ⟨rfl, rfl⟩ := Det.append_singleton_inj.mp hW
      simp only [Config.mk.injEq] at hc'
      obtain ⟨h1, h2, h3⟩ := hc'
      subst h3
      have h1 := h1.symm
      have h2 := h2.symm
      subst h1 h2
      refine ⟨t, vals vs ++ [.label 0 [] (constI32 c :: .plain (.brIf l) :: expression R)] ++ rest',
        Or.inr ⟨rfl, rfl, rfl, ?_⟩, hst, ?_⟩
      · have := codeSize_replace_lt (vals vs) (.plain (.if_ .empty R' []) :: rest)
          [constI32 c, .plain (.intTestOp .i32 .eqz)] _ (codeSize_eqz c)
        simpa [constI32, Val.i32] using this
      · have e : vals vs ++ [constI32 (intTestOp .i32 .eqz c)] ++ (.plain (.if_ .empty R' []) :: rest) =
            vals vs ++ [constI32 (intTestOp .i32 .eqz c), .plain (.if_ .empty R' [])] ++ rest := by
          simp
        rw [e]
        exact ((AdminsRel.refl _).append (AdminsRel.base ⟨l, R, R', hl, hR, GS.test c⟩)).append
          hrest
    | test c =>
      have e : vals vs ++ [constI32 (intTestOp .i32 .eqz c), .plain (.if_ .empty R' [])] ++ rest =
          vals (vs ++ [.i32 (intTestOp .i32 .eqz c)]) ++ .plain (.if_ .empty R' []) :: rest := by
        simp [constI32]
      rw [e] at hstep
      obtain ⟨vs₀, args, c₀, hW, hh, hc'⟩ := head_inv rfl (by simp) (by simp) hstep
      obtain ⟨b, rfl, rfl⟩ := head_if hh
      obtain ⟨rfl, hb⟩ := Det.append_singleton_inj.mp hW
      have hb' : b = intTestOp .i32 .eqz c := by
        simp only [Val.i32, Val.num.injEq] at hb
        cases hb
        rfl
      subst hb'
      simp only [Config.mk.injEq] at hc'
      obtain ⟨h1, h2, h3⟩ := hc'
      subst h3
      have h1 := h1.symm
      have h2 := h2.symm
      subst h1 h2
      have hsel : (if intTestOp .i32 .eqz c = 0 then [] else R') = (if c = 0 then R' else []) := by
        by_cases hc : c = 0
        · have : intTestOp .i32 .eqz c ≠ 0 := fun h => (eqz_eq_zero c).mp h hc
          simp only [this, ↓reduceIte]
          simp only [hc, ↓reduceIte]
        · have : intTestOp .i32 .eqz c = 0 := (eqz_eq_zero c).mpr hc
          simp only [this, hc, ↓reduceIte]
      rw [hsel]
      refine ⟨t, vals vs ++ [.label 0 [] (constI32 c :: .plain (.brIf l) :: expression R)] ++ rest',
        Or.inr ⟨rfl, rfl, rfl, ?_⟩, hst, ?_⟩
      · have hB : (if c = 0 then R' else []) = R' ∨ (if c = 0 then R' else []) = [] := by
          split <;> simp
        have := codeSize_replace_lt (vals vs) rest
          [constI32 (intTestOp .i32 .eqz c), .plain (.if_ .empty R' [])] _
          (codeSize_if (intTestOp .i32 .eqz c) hB)
        simpa using this
      · exact ((AdminsRel.refl _).append (AdminsRel.base ⟨l, R, R', hl, hR, GS.pick c⟩)).append
          hrest
    | pick c =>
      have e : vals vs ++ [Admin.plain (.block .empty (if c = 0 then R' else []))] ++ rest =
          vals vs ++ .plain (.block .empty (if c = 0 then R' else [])) :: rest := by simp
      rw [e] at hstep
      obtain ⟨vs₀, args, c₀, hW, hh, hc'⟩ := head_inv rfl (by simp) (by simp) hstep
      obtain ⟨rfl, rfl⟩ := head_block hh
      simp only [List.append_nil] at hW
      subst hW
      simp only [Config.mk.injEq] at hc'
      obtain ⟨h1, h2, h3⟩ := hc'
      subst h3
      have h1 := h1.symm
      have h2 := h2.symm
      subst h1 h2
      by_cases hc : c = 0
      · subst hc
        simp only [↓reduceIte]
        refine ⟨t, vals vs ++ [.label 0 [] (expression R)] ++ rest', Or.inl (.single ?_), hst, ?_⟩
        · have hin : Step P closedHost ⟨t, f, [constI32 0, .plain (.brIf l)]⟩ ⟨t, f, []⟩ :=
            Step.brIfFalse
          have := Step.append_right (Step.vals_left (Step.ctxtLabel (n := 0) (cont := [])
            (Step.append_right hin (expression R))) vs) rest'
          simpa using this
        · exact ((AdminsRel.refl _).append
            (AdminsRel.cons (AdminRel.label 0 .nil (AdminsRel.src hR.flip)) .nil)).append hrest
      · simp only [hc, ↓reduceIte]
        refine ⟨t, vals vs ++ [.label 0 [] (.plain (.br l) :: expression R)] ++ rest',
          Or.inl (.single ?_), hst, ?_⟩
        · have hin : Step P closedHost ⟨t, f, [constI32 c, .plain (.brIf l)]⟩
              ⟨t, f, [.plain (.br l)]⟩ := Step.brIfTrue hc
          have := Step.append_right (Step.vals_left (Step.ctxtLabel (n := 0) (cont := [])
            (Step.append_right hin (expression R))) vs) rest'
          simpa using this
        · exact ((AdminsRel.refl _).append (AdminsRel.base ⟨l, R, R', hl, hR, GS.exit⟩)).append
            hrest
    | exit =>
      have e : vals vs ++ [Admin.label 0 [] []] ++ rest = vals vs ++ .label 0 [] [] :: rest := by
        simp
      rw [e] at hstep
      obtain ⟨vs₀, args, c₀, hW, hh, hc'⟩ := head_inv rfl (by simp) (by simp) hstep
      obtain ⟨rfl, rfl⟩ := head_label_nil hh
      simp only [List.append_nil] at hW
      subst hW
      simp only [Config.mk.injEq] at hc'
      obtain ⟨h1, h2, h3⟩ := hc'
      subst h3
      have h1 := h1.symm
      have h2 := h2.symm
      subst h1 h2
      refine ⟨t, vals vs ++ rest', Or.inl (.single ?_), hst, ?_⟩
      · have hin : Step P closedHost ⟨t, f, [.label 0 [] (.plain (.br l) :: expression R)]⟩
            ⟨t, f, []⟩ := by
          have := Step.brLabelZero (P := P) (host := closedHost) (s := t) (f := f) (n := 0)
            (cont := []) (vs' := []) (vs := []) (l := l) (rest := expression R) hl rfl
          simpa [vals, expression] using this
        have := Step.append_right (Step.vals_left hin vs) rest'
        simpa using this
      · simpa using (AdminsRel.refl (vals vs)).append hrest
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    exfalso
    obtain ⟨l, R, R', hl, hR, hg⟩ := hxy
    cases hg with
    | start i =>
      refine not_exit (us := us) (j := j) (W := vs) (e₀ := .plain (.localGet i))
        (x' := [.plain (.intTestOp .i32 .eqz), .plain (.if_ .empty R' [])]) rfl ?_ ?_ ?_ ?_ ?_ hk ?_
      all_goals first | (simp [Admin.IsReturnCallRef]; done) | simpa using he
    | read v =>
      refine not_exit (us := us) (j := j) (W := vs ++ [v]) (e₀ := .plain (.intTestOp .i32 .eqz))
        (x' := [.plain (.if_ .empty R' [])]) rfl ?_ ?_ ?_ ?_ ?_ hk ?_
      all_goals first | (simp [Admin.IsReturnCallRef]; done) | simpa using he
    | test c =>
      refine not_exit (us := us) (j := j) (W := vs ++ [.i32 (intTestOp .i32 .eqz c)])
        (e₀ := .plain (.if_ .empty R' [])) (x' := []) rfl ?_ ?_ ?_ ?_ ?_ hk ?_
      all_goals first | (simp [Admin.IsReturnCallRef]; done) | simpa [constI32] using he
    | pick c =>
      refine not_exit (us := us) (j := j) (W := vs) (e₀ := .plain (.block .empty (if c = 0 then R' else [])))
        (x' := []) rfl ?_ ?_ ?_ ?_ ?_ hk ?_
      all_goals first | (simp [Admin.IsReturnCallRef]; done) | simpa using he
    | exit =>
      refine not_exit (us := us) (j := j) (W := vs) (e₀ := .label 0 [] []) (x' := []) rfl ?_ ?_ ?_ ?_ ?_ hk ?_
      all_goals first | (simp [Admin.IsReturnCallRef]; done) | simpa using he
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    obtain ⟨l, R, R', hl, hR, hg⟩ := hxy
    have hall : ∀ a ∈ x, a.val? ≠ none := by
      rw [hx]; intro a ha; exact Det.mem_vals ha
    cases hg with
    | start i => exact hall (.plain (.localGet i)) (by simp) rfl
    | read v => exact hall (.plain (.intTestOp .i32 .eqz)) (by simp) rfl
    | test c => exact hall (.plain (.if_ .empty R' [])) (by simp) rfl
    | pick c => exact hall (.plain (.block .empty (if c = 0 then R' else []))) (by simp) rfl
    | exit => exact hall (.label 0 [] []) (by simp) rfl

end Silmaril.Wasm.Binaryen.GuardSim
