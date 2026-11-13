module

public import Silmaril.Raw.Wasm.Versions.V2.ToCore.Sim.Common

@[expose] public section

/-! # Step simulation: the `Step_pure` rules (`8-reduction:6`)

One lemma per constructor of `Silmaril.Wasm.V2.Execution.PureStep`, named after
it. **Every rule in this file is lock-step**: one 2.0 `Step_pure` rule is
exactly one Core 3.0 step, modulo the zero or more `Step_read/ref.null` steps
that `catchUp` (`Sim/Common.lean`) runs first to bring the Core configuration up
to the 2.0 one. The Core counterparts are

| 2.0 | Core 3.0 |
| --- | --- |
| `unreachable`, `nop`, `drop`, `select-*` | `Step.parametric` |
| `if-*`, `label-vals`, `br*`, `frame-vals`, `return-*`, `trap-*` | `Step.*` directly |
| `unop`/`binop`/`testop`/`relop`/`cvtop` | `Step.numeric` |
| `ref.is_null-*` | `Step.reference` |
| `vvunop` … `vcvtop` | `Step.vector` |
| `local.tee` | `Step.variable` |

**Where the profile goes.** Both machines are indexed by the same
`Numerics.Profile`, and 2.0's `FloatUnOpResult P`, `FloatBinOpResult P`,
`VecFloatUnOpResult P`, `VecFloatBinOpResult P` and `VecCvtOpResult P` are
*definitionally* Core's `floatUnOpP P`, `floatBinOpP P`, `VecFloatUnOpRel P`,
`VecFloatBinOpRel P` and `VecConvertRel P` (`V2/Execution/Numerics.lean`), so the
float rules transfer with no profile shift. This is why the simulation is stated
for a common `P` rather than for the fixed `Profile.spec` of
`Lime1/ToCore/Execution.lean`; see the docstring of `V2/ToCore/Execution.lean`.

**Two rules of 2.0 have no Core counterpart and are vacuous**:
`Step_pure/unop-trap` for integers (`intUnOpTrap`) and for floats
(`floatUnOpTrap`); likewise `binop-trap` for floats. Core 3.0 omits them for
exactly the reason 2.0's are unreachable — the result set is never empty — so the
lemmas are proved by exhibiting a result.
-/

namespace Silmaril.Wasm.V2.Execution.ToCoreSim

open Silmaril.Wasm.Numerics (Profile V128)
open Silmaril.Wasm.V2.Execution.ToCore

variable {H : Type} {P : Profile} {tgt : CHostSemantics H} {s : Store H} {f : Frame}

/-! ## Helpers for the structural rules

`Step_pure/br-zero`, `br-succ`, `return-frame`, `return-label` and `trap-vals`
all have a redex of the shape "values, one rigid instruction, an arbitrary
tail", possibly under a `LABEL` or a `FRAME`. Splitting the Core image along
that shape and running `catchUpSplit` (`Sim/Common.lean`) on it is the whole
content of those five lemmas, so the splitting is factored out here. The `pv_`
prefix matches the `pb_` convention of `Lime1/ToCore/Sim/PBCommon.lean`. -/

/-- The Core image of a concatenation splits, and both halves are defined. -/
theorem pv_split {xs ys : List Admin} {L : List CAdmin}
    (h : Admin.listToCore s (xs ++ ys) = some L) :
    ∃ x y, Admin.listToCore s xs = some x ∧ Admin.listToCore s ys = some y ∧ L = x ++ y := by
  induction xs generalizing L with
  | nil => exact ⟨[], L, rfl, by simpa using h, rfl⟩
  | cons a as ih =>
    simp only [List.cons_append, Admin.listToCore_cons, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨u, hu, v, hv, rfl⟩ := h
    obtain ⟨x, y, hx, hy, rfl⟩ := ih hv
    exact ⟨u ++ x, y, by simp [hu, hx], hy, by simp⟩

/-- No `admininstr` has an empty Core image. -/
theorem pv_toCore_ne_nil {a : Admin} {x : List CAdmin} (h : Admin.toCore s a = some x) :
    x ≠ [] := by
  rintro rfl
  cases a <;> simp_all [Admin.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff]

/-- Hence only the empty code sequence has an empty Core image. -/
theorem pv_eq_nil {l : List Admin} (h : Admin.listToCore s l = some []) : l = [] := by
  cases l with
  | nil => rfl
  | cons a as =>
    exfalso
    simp only [Admin.listToCore_cons, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨u, hu, v, -, huv⟩ := h
    exact pv_toCore_ne_nil hu (List.append_eq_nil_iff.mp huv).1

/-- A rigid code sequence is its own normal form. -/
theorem pv_map_norm_rigid {m : CModuleInst} {R : List CAdmin} (hR : ∀ y ∈ R, Rigid y) :
    R.map (ToCore.Admin.norm m) = R := by
  induction R with
  | nil => rfl
  | cons y R ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hR
    simp only [List.map_cons, hR.1.norm, ih hR.2]

/-- … and so is a value prefix followed by one. -/
theorem pv_map_norm_valsRigid (m : CModuleInst) (vs : List CVal) {R : List CAdmin}
    (hR : ∀ y ∈ R, Rigid y) : (cvals vs ++ R).map (ToCore.Admin.norm m) = cvals vs ++ R := by
  rw [List.map_append, map_norm_cvals, pv_map_norm_rigid hR]

/-- The Core image of a value sequence is pinned down by `values_toCore`. -/
theorem pv_vals_eq {vs : List Val} {A : List CAdmin} (h : Admin.listToCore s (vals vs) = some A) :
    A = cvals (vs.map Val.toCore) :=
  Option.some.inj (h.symm.trans (values_toCore s vs))

/-- The Core image of one plain, non-`REF.NULL` instruction. -/
theorem pv_plain_eq {i : Instr} {ci : Wasm.Instr} {A : List CAdmin}
    (hi : Instr.toCore i = some ci) (hn : ∀ ht, ci ≠ .refNull ht)
    (h : Admin.listToCore s [.plain i] = some A) : A = [(.plain ci : CAdmin)] :=
  Option.some.inj (h.symm.trans (by simp [hi, ToCore.plainOrNull_eq_plain hn]))

/-- `cvals` distributes over concatenation. -/
theorem pv_cvals_append (a b : List CVal) : cvals (a ++ b) = cvals a ++ cvals b :=
  Silmaril.Wasm.Execution.Core.vals_append a b

/-- Under `Sim`, both arms of an `IF` have a Core image: `Instr.toCore` is
partial only through the `CVTOP` immediates, and the `Sim` hypothesis says the
whole redex is in the image. -/
theorem pv_if {bt : BlockType} {b₁ b₂ : List Instr} {cc : BitVec 32} {cs : CStore H}
    {cf : CFrame} {cl : List CAdmin}
    (hs : Sim ⟨s, f, [constI32 cc, .plain (.if_ bt b₁ b₂)]⟩ ⟨cs, cf, cl⟩) :
    ∃ l r, Expr.toCore b₁ = some l ∧ Expr.toCore b₂ = some r := by
  have hcode := sim_code hs
  cases hl : Expr.toCore b₁ with
  | none => simp [Instr.toCore, hl] at hcode
  | some l =>
    cases hr : Expr.toCore b₂ with
    | none => simp [Instr.toCore, hl, hr] at hcode
    | some r => exact ⟨l, r, rfl, rfl⟩

/-- 2.0's `labelPred` (`8-reduction:95`) is Core 3.0's. -/
theorem pv_labelPred (l : LabelIdx) :
    labelPred l = Silmaril.Wasm.Execution.Core.labelPred l := rfl

/-! ## Polymorphic instructions (`8-reduction:40-58`) -/

theorem pure_unreachable {c : CConfig H} (hs : Sim ⟨s, f, [.plain .unreachable]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := []) (R := [.plain .unreachable]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.parametric .unreachable)

theorem pure_nop {c : CConfig H} (hs : Sim ⟨s, f, [.plain .nop]⟩ c) :
    Target P tgt ⟨s, f, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := []) (R := [.plain .nop]) (L' := [])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.parametric .nop)

theorem pure_drop {v : Val} {c : CConfig H} (hs : Sim ⟨s, f, [v.toAdmin, .plain .drop]⟩ c) :
    Target P tgt ⟨s, f, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [v.toCore]) (R := [.plain .drop]) (L' := [])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.parametric (.drop _))

theorem pure_selectTrue {v₁ v₂ : Val} {cc : BitVec 32} {ts : Option (List ValType)}
    (hc : cc ≠ 0) {c : CConfig H}
    (hs : Sim ⟨s, f, [v₁.toAdmin, v₂.toAdmin, constI32 cc, .plain (.select ts)]⟩ c) :
    Target P tgt ⟨s, f, [v₁.toAdmin]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [v₁.toCore, v₂.toCore, .num ⟨.int .i32, cc⟩])
    (R := [.plain (.select (ts.map ResultType.toCore))]) (L' := [(Val.toCore v₁).toAdmin])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.parametric (.selectTrue hc))

theorem pure_selectFalse {v₁ v₂ : Val} {ts : Option (List ValType)} {c : CConfig H}
    (hs : Sim ⟨s, f, [v₁.toAdmin, v₂.toAdmin, constI32 0, .plain (.select ts)]⟩ c) :
    Target P tgt ⟨s, f, [v₂.toAdmin]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [v₁.toCore, v₂.toCore, .num ⟨.int .i32, 0⟩])
    (R := [.plain (.select (ts.map ResultType.toCore))]) (L' := [(Val.toCore v₂).toAdmin])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.parametric (.selectFalse _ _ _))

/-! ## Block and branch instructions (`8-reduction:61-114`) -/

theorem pure_ifTrue {cc : BitVec 32} {bt : BlockType} {b₁ b₂ : List Instr} (hc : cc ≠ 0)
    {c : CConfig H} (hs : Sim ⟨s, f, [constI32 cc, .plain (.if_ bt b₁ b₂)]⟩ c) :
    Target P tgt ⟨s, f, [.plain (.block bt b₁)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨l, r, hl, hr⟩ := pv_if hs
  exact finishSame hs (vs := [.num ⟨.int .i32, cc⟩])
    (R := [.plain (.if_ bt.toCore l r)]) (L' := [.plain (.block bt.toCore l)])
    (by simp [cvals, Silmaril.Wasm.Execution.Core.vals, Instr.toCore, ToCore.plainOrNull,
      Silmaril.Wasm.Execution.Core.Val.toAdmin, hl, hr])
    (by v2rigid)
    (by simp [Instr.toCore, ToCore.plainOrNull, hl])
    (by simp) (.ifTrue hc)

theorem pure_ifFalse {bt : BlockType} {b₁ b₂ : List Instr} {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 0, .plain (.if_ bt b₁ b₂)]⟩ c) :
    Target P tgt ⟨s, f, [.plain (.block bt b₂)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨l, r, hl, hr⟩ := pv_if hs
  exact finishSame hs (vs := [.num ⟨.int .i32, 0⟩])
    (R := [.plain (.if_ bt.toCore l r)]) (L' := [.plain (.block bt.toCore r)])
    (by simp [cvals, Silmaril.Wasm.Execution.Core.vals, Instr.toCore, ToCore.plainOrNull,
      Silmaril.Wasm.Execution.Core.Val.toAdmin, hl, hr]; rfl)
    (by v2rigid)
    (by simp [Instr.toCore, ToCore.plainOrNull, hr])
    (by simp) .ifFalse

theorem pure_labelVals {n : Nat} {cont : List Instr} {vs : List Val} {c : CConfig H}
    (hs : Sim ⟨s, f, [.label n cont (vals vs)]⟩ c) : Target P tgt ⟨s, f, vals vs⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨k, b, B, rfl, hk, hB, hb⟩ := sim_label hs
  have hBv : B = cvals (vs.map Val.toCore) := by
    simpa [cvals] using (Option.some.inj ((values_toCore s vs).symm.trans hB)).symm
  subst hBv
  have hinner : Silmaril.Wasm.Execution.Core.Steps P tgt ⟨cs, cf, b⟩
      ⟨cs, cf, cvals (vs.map Val.toCore)⟩ := by
    simpa using catchUp (P := P) (tgt := tgt) (R := []) (by simp) (by simpa using hb)
  refine finishFrom (P := P) (tgt := tgt) (s' := s) (f' := f)
    (Relation.TransGen.trans_right (Silmaril.Wasm.Execution.Core.Steps.label hinner)
      (Relation.TransGen.single (Silmaril.Wasm.Execution.Core.Step.labelVals
        (P := P) (host := tgt) (s := cs) (f := cf) (n := n) (cont := k)
        (vs := vs.map Val.toCore)))) ?_ (sim_store hs) (sim_frame hs)
    ⟨(sim_wf hs).1, (sim_wf hs).2.1, by simp⟩
  rw [values_toCore]
  exact congrArg some (map_norm_cvals _ _).symm

theorem pure_brZero {n : Nat} {cont : List Instr} {vs' vs : List Val} {l : LabelIdx}
    {rest : List Admin} (hl : l.toNat = 0) (hn : vs.length = n) {c : CConfig H}
    (hs : Sim ⟨s, f, [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)]⟩ c) :
    Target P tgt ⟨s, f, vals vs ++ expression cont⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨k, b, B, rfl, hk, hB, hb⟩ := sim_label hs
  obtain ⟨A₁, T, hA₁, hT, rfl⟩ := pv_split hB
  obtain ⟨A₂, A₃, hA₂, hA₃, rfl⟩ := pv_split hA₁
  obtain ⟨A₄, A₅, hA₄, hA₅, rfl⟩ := pv_split hA₂
  obtain rfl := pv_vals_eq hA₄
  obtain rfl := pv_vals_eq hA₅
  obtain rfl := pv_plain_eq (i := Instr.br l) rfl (by simp) hA₃
  rw [← pv_cvals_append] at hb
  obtain ⟨t, -, hsteps⟩ := catchUpSplit (P := P) (tgt := tgt) (cs := cs)
    (rigid_singleton (by v2rigid)) hb
  rw [pv_cvals_append] at hsteps
  refine finishFrom (P := P) (tgt := tgt) (s' := s) (f' := f)
    (Relation.TransGen.trans_right (Silmaril.Wasm.Execution.Core.Steps.label hsteps)
      (Relation.TransGen.single (Silmaril.Wasm.Execution.Core.Step.brLabelZero
        (P := P) (host := tgt) (s := cs) (f := cf) (n := n) (cont := k)
        (vs' := vs'.map Val.toCore) (vs := vs.map Val.toCore) (l := l) (rest := t)
        hl (by simpa using hn)))) ?_ (sim_store hs) (sim_frame hs)
    ⟨(sim_wf hs).1, (sim_wf hs).2.1, by simp⟩
  rw [Admin.listToCore_append s (values_toCore s vs)
      (show Admin.listToCore s (expression cont) = some (k.map ToCore.plainOrNull) by
        simp [hk]),
    List.map_append, map_norm_cvals, map_norm_expression hk]

theorem pure_brSucc {n : Nat} {cont : List Instr} {vs : List Val} {l : LabelIdx}
    {rest : List Admin} (hl : 0 < l.toNat) {c : CConfig H}
    (hs : Sim ⟨s, f, [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)]⟩ c) :
    Target P tgt ⟨s, f, vals vs ++ [.plain (.br (labelPred l))]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨k, b, B, rfl, hk, hB, hb⟩ := sim_label hs
  obtain ⟨A₁, T, hA₁, hT, rfl⟩ := pv_split hB
  obtain ⟨A₂, A₃, hA₂, hA₃, rfl⟩ := pv_split hA₁
  obtain rfl := pv_vals_eq hA₂
  obtain rfl := pv_plain_eq (i := Instr.br l) rfl (by simp) hA₃
  obtain ⟨t, -, hsteps⟩ := catchUpSplit (P := P) (tgt := tgt) (cs := cs)
    (rigid_singleton (by v2rigid)) hb
  refine finishFrom (P := P) (tgt := tgt) (s' := s) (f' := f)
    (Relation.TransGen.trans_right (Silmaril.Wasm.Execution.Core.Steps.label hsteps)
      (Relation.TransGen.single (Silmaril.Wasm.Execution.Core.Step.brLabelSucc
        (P := P) (host := tgt) (s := cs) (f := cf) (n := n) (cont := k)
        (vs := vs.map Val.toCore) (l := l) (rest := t) hl))) ?_ (sim_store hs) (sim_frame hs)
    ⟨(sim_wf hs).1, (sim_wf hs).2.1, by simp⟩
  rw [pv_map_norm_valsRigid _ _ (rigid_singleton (by v2rigid)), pv_labelPred]
  exact Admin.listToCore_append s (values_toCore s vs) (by v2img)

theorem pure_brIfTrue {cc : BitVec 32} {l : LabelIdx} (hc : cc ≠ 0) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 cc, .plain (.brIf l)]⟩ c) :
    Target P tgt ⟨s, f, [.plain (.br l)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.num ⟨.int .i32, cc⟩]) (R := [.plain (.brIf l)])
    (L' := [.plain (.br l)]) (by v2img) (by v2rigid) (by v2img) (by simp) (.brIfTrue hc)

theorem pure_brIfFalse {l : LabelIdx} {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 0, .plain (.brIf l)]⟩ c) : Target P tgt ⟨s, f, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.num ⟨.int .i32, 0⟩]) (R := [.plain (.brIf l)])
    (L' := []) (by v2img) (by v2rigid) (by v2img) (by simp) .brIfFalse

theorem pure_brTableLt {i : BitVec 32} {ls : List LabelIdx} {l' l : LabelIdx}
    (hi : ls[i.toNat]? = some l) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, .plain (.brTable ls l')]⟩ c) :
    Target P tgt ⟨s, f, [.plain (.br l)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩]) (R := [.plain (.brTable ls l')])
    (L' := [.plain (.br l)]) (by v2img) (by v2rigid) (by v2img) (by simp) (.brTableLt hi)

theorem pure_brTableGe {i : BitVec 32} {ls : List LabelIdx} {l' : LabelIdx}
    (hi : ls.length ≤ i.toNat) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, .plain (.brTable ls l')]⟩ c) :
    Target P tgt ⟨s, f, [.plain (.br l')]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩]) (R := [.plain (.brTable ls l')])
    (L' := [.plain (.br l')]) (by v2img) (by v2rigid) (by v2img) (by simp) (.brTableGe hi)

/-! ## Function instructions and traps (`8-reduction:117-158`) -/

theorem pure_frameVals {n : Nat} {fr : Frame} {vs : List Val} (hn : vs.length = n)
    {c : CConfig H} (hs : Sim ⟨s, f, [.frame n fr (vals vs)]⟩ c) :
    Target P tgt ⟨s, f, vals vs⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨fc, b, B, rfl, hfc, hB, hb⟩ := sim_frame_adm hs
  have hBv : B = cvals (vs.map Val.toCore) := by
    simpa [cvals] using (Option.some.inj ((values_toCore s vs).symm.trans hB)).symm
  subst hBv
  have hinner : Silmaril.Wasm.Execution.Core.Steps P tgt ⟨cs, fc, b⟩
      ⟨cs, fc, cvals (vs.map Val.toCore)⟩ := by
    simpa using catchUp (P := P) (tgt := tgt) (R := []) (by simp) (by simpa using hb)
  refine finishFrom (P := P) (tgt := tgt) (s' := s) (f' := f)
    (Relation.TransGen.trans_right (Silmaril.Wasm.Execution.Core.Steps.frame hinner)
      (Relation.TransGen.single (Silmaril.Wasm.Execution.Core.Step.frameVals
        (P := P) (host := tgt) (s := cs) (f := cf) (fi := fc) (n := n)
        (vs := vs.map Val.toCore) (by simpa using hn)))) ?_ (sim_store hs) (sim_frame hs)
    ⟨(sim_wf hs).1, (sim_wf hs).2.1, by simp⟩
  rw [values_toCore]
  exact congrArg some (map_norm_cvals _ _).symm

theorem pure_returnFrame {n : Nat} {fr : Frame} {vs' vs : List Val} {rest : List Admin}
    (hn : vs.length = n) {c : CConfig H}
    (hs : Sim ⟨s, f, [.frame n fr (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)]⟩ c) :
    Target P tgt ⟨s, f, vals vs⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨fc, b, B, rfl, -, hB, hb⟩ := sim_frame_adm hs
  obtain ⟨A₁, T, hA₁, hT, rfl⟩ := pv_split hB
  obtain ⟨A₂, A₃, hA₂, hA₃, rfl⟩ := pv_split hA₁
  obtain ⟨A₄, A₅, hA₄, hA₅, rfl⟩ := pv_split hA₂
  obtain rfl := pv_vals_eq hA₄
  obtain rfl := pv_vals_eq hA₅
  obtain rfl := pv_plain_eq (i := Instr.return_) rfl (by simp) hA₃
  rw [← pv_cvals_append] at hb
  obtain ⟨t, -, hsteps⟩ := catchUpSplit (P := P) (tgt := tgt) (cs := cs)
    (rigid_singleton (by v2rigid)) hb
  rw [pv_cvals_append] at hsteps
  refine finishFrom (P := P) (tgt := tgt) (s' := s) (f' := f)
    (Relation.TransGen.trans_right (Silmaril.Wasm.Execution.Core.Steps.frame hsteps)
      (Relation.TransGen.single (Silmaril.Wasm.Execution.Core.Step.returnFrame
        (P := P) (host := tgt) (s := cs) (f := cf) (fi := fc) (n := n)
        (vs' := vs'.map Val.toCore) (vs := vs.map Val.toCore) (rest := t)
        (by simpa using hn)))) ?_ (sim_store hs) (sim_frame hs)
    ⟨(sim_wf hs).1, (sim_wf hs).2.1, by simp⟩
  rw [values_toCore]
  exact congrArg some (map_norm_cvals _ _).symm

theorem pure_returnLabel {n : Nat} {cont : List Instr} {vs : List Val} {rest : List Admin}
    {c : CConfig H}
    (hs : Sim ⟨s, f, [.label n cont (vals vs ++ [.plain .return_] ++ rest)]⟩ c) :
    Target P tgt ⟨s, f, vals vs ++ [.plain .return_]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨k, b, B, rfl, hk, hB, hb⟩ := sim_label hs
  obtain ⟨A₁, T, hA₁, hT, rfl⟩ := pv_split hB
  obtain ⟨A₂, A₃, hA₂, hA₃, rfl⟩ := pv_split hA₁
  obtain rfl := pv_vals_eq hA₂
  obtain rfl := pv_plain_eq (i := Instr.return_) rfl (by simp) hA₃
  obtain ⟨t, -, hsteps⟩ := catchUpSplit (P := P) (tgt := tgt) (cs := cs)
    (rigid_singleton (by v2rigid)) hb
  refine finishFrom (P := P) (tgt := tgt) (s' := s) (f' := f)
    (Relation.TransGen.trans_right (Silmaril.Wasm.Execution.Core.Steps.label hsteps)
      (Relation.TransGen.single (Silmaril.Wasm.Execution.Core.Step.returnLabel
        (P := P) (host := tgt) (s := cs) (f := cf) (n := n) (cont := k)
        (vs := vs.map Val.toCore) (rest := t)))) ?_ (sim_store hs) (sim_frame hs)
    ⟨(sim_wf hs).1, (sim_wf hs).2.1, by simp⟩
  rw [pv_map_norm_valsRigid _ _ (rigid_singleton (by v2rigid))]
  exact Admin.listToCore_append s (values_toCore s vs) (by v2img)

theorem pure_trapVals {vs : List Val} {rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ [])
    {c : CConfig H} (hs : Sim ⟨s, f, vals vs ++ [.trap] ++ rest⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hcode := sim_code hs
  obtain ⟨A₁, T, hA₁, hT, hcl⟩ := pv_split hcode
  obtain ⟨A₂, A₃, hA₂, hA₃, rfl⟩ := pv_split hA₁
  obtain rfl := pv_vals_eq hA₂
  obtain rfl : A₃ = [(.trap : CAdmin)] := Option.some.inj (hA₃.symm.trans (by simp))
  obtain ⟨t, ht, hsteps⟩ := catchUpSplit (P := P) (tgt := tgt) (cs := cs)
    (rigid_singleton (by v2rigid)) hcl
  have hne' : vs.map Val.toCore ≠ [] ∨ t ≠ [] := by
    rcases hne with hv | hr
    · exact .inl (by simpa using hv)
    · right
      intro hnil
      rw [hnil] at ht
      simp only [List.map_nil] at ht
      exact hr (pv_eq_nil (s := s) (by rw [hT, ← ht]))
  refine finishFrom (P := P) (tgt := tgt) (s' := s) (f' := f)
    (Relation.TransGen.trans_right hsteps (Relation.TransGen.single
      (Silmaril.Wasm.Execution.Core.Step.trapInstrs (P := P) (host := tgt) (s := cs) (f := cf)
        (vs := vs.map Val.toCore) (rest := t) hne'))) ?_ (sim_store hs) (sim_frame hs)
    ⟨(sim_wf hs).1, (sim_wf hs).2.1, by simp⟩
  simp

theorem pure_trapLabel {n : Nat} {cont : List Instr} {c : CConfig H}
    (hs : Sim ⟨s, f, [.label n cont [.trap]]⟩ c) : Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨k, b, B, rfl, hk, hB, hb⟩ := sim_label hs
  have hBv : B = [.trap] := by simpa using hB.symm
  subst hBv
  have hbv : b = [.trap] := ToCore.map_norm_eq_of_rigid (by simp [ToCore.Rigid]) hb
  subst hbv
  refine finishFrom (P := P) (tgt := tgt) (s' := s) (f' := f)
    (Relation.TransGen.single (Silmaril.Wasm.Execution.Core.Step.trapLabel
      (P := P) (host := tgt) (s := cs) (f := cf) (n := n) (cont := k))) ?_
    (sim_store hs) (sim_frame hs) ⟨(sim_wf hs).1, (sim_wf hs).2.1, by simp⟩
  simp

theorem pure_trapFrame {n : Nat} {fr : Frame} {c : CConfig H}
    (hs : Sim ⟨s, f, [.frame n fr [.trap]]⟩ c) : Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨fc, b, B, rfl, hfc, hB, hb⟩ := sim_frame_adm hs
  have hBv : B = [.trap] := by simpa using hB.symm
  subst hBv
  have hbv : b = [.trap] := ToCore.map_norm_eq_of_rigid (by simp [ToCore.Rigid]) hb
  subst hbv
  refine finishFrom (P := P) (tgt := tgt) (s' := s) (f' := f)
    (Relation.TransGen.single (Silmaril.Wasm.Execution.Core.Step.trapFrame
      (P := P) (host := tgt) (s := cs) (f := cf) (fi := fc) (n := n))) ?_
    (sim_store hs) (sim_frame hs) ⟨(sim_wf hs).1, (sim_wf hs).2.1, by simp⟩
  simp

/-! ## Numeric instructions (`8-reduction:172-207`) -/

theorem pure_intUnOp {t : IntType} {op : IntUnOp} {x z : BitVec t.width}
    (h : IntUnOpResult t op x z) {c : CConfig H}
    (hs : Sim ⟨s, f, [.plain (.intConst t x), .plain (.intUnOp t op)]⟩ c) :
    Target P tgt ⟨s, f, [.plain (.intConst t z)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hz : z = Numerics.intUnOp t op x := h
  subst hz
  exact finishSame hs (vs := [.num ⟨.int t, x⟩]) (R := [.plain (.intUnOp t op)])
    (L' := [.plain (.intConst t (Numerics.intUnOp t op x))])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.numeric .intUnOp)

theorem pure_floatUnOp {t : FloatType} {op : FloatUnOp} {x z : BitVec t.width}
    (h : FloatUnOpResult P t op x z) {c : CConfig H}
    (hs : Sim ⟨s, f, [.plain (.floatConst t x), .plain (.floatUnOp t op)]⟩ c) :
    Target P tgt ⟨s, f, [.plain (.floatConst t z)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.num ⟨.float t, x⟩]) (R := [.plain (.floatUnOp t op)])
    (L' := [.plain (.floatConst t z)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.numeric (.floatUnOp h))

theorem pure_intUnOpTrap {t : IntType} {op : IntUnOp} {x : BitVec t.width}
    (h : ∀ z, ¬ IntUnOpResult t op x z) {c : CConfig H}
    (_hs : Sim ⟨s, f, [.plain (.intConst t x), .plain (.intUnOp t op)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c :=
  absurd (show IntUnOpResult t op x (Numerics.intUnOp t op x) from rfl) (h _)

theorem pure_floatUnOpTrap {t : FloatType} {op : FloatUnOp} {x : BitVec t.width}
    (h : ∀ z, ¬ FloatUnOpResult P t op x z) {c : CConfig H}
    (_hs : Sim ⟨s, f, [.plain (.floatConst t x), .plain (.floatUnOp t op)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨z, hz⟩ := FloatUnOpResult_nonempty P t op x
  exact absurd hz (h z)

theorem pure_intBinOp {t : IntType} {op : IntBinOp} {x y z : BitVec t.width}
    (h : IntBinOpResult t op x y z) {c : CConfig H}
    (hs : Sim ⟨s, f, [.plain (.intConst t x), .plain (.intConst t y), .plain (.intBinOp t op)]⟩ c) :
    Target P tgt ⟨s, f, [.plain (.intConst t z)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩])
    (R := [.plain (.intBinOp t op)]) (L' := [.plain (.intConst t z)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.numeric (.intBinOp h))

theorem pure_floatBinOp {t : FloatType} {op : FloatBinOp} {x y z : BitVec t.width}
    (h : FloatBinOpResult P t op x y z) {c : CConfig H}
    (hs : Sim ⟨s, f,
      [.plain (.floatConst t x), .plain (.floatConst t y), .plain (.floatBinOp t op)]⟩ c) :
    Target P tgt ⟨s, f, [.plain (.floatConst t z)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.num ⟨.float t, x⟩, .num ⟨.float t, y⟩])
    (R := [.plain (.floatBinOp t op)]) (L' := [.plain (.floatConst t z)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.numeric (.floatBinOp h))

theorem pure_intBinOpTrap {t : IntType} {op : IntBinOp} {x y : BitVec t.width}
    (h : IntBinOpTraps t op x y) {c : CConfig H}
    (hs : Sim ⟨s, f, [.plain (.intConst t x), .plain (.intConst t y), .plain (.intBinOp t op)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨e, he⟩ := h
  exact finishSame hs (vs := [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩])
    (R := [.plain (.intBinOp t op)]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.numeric (.intBinOpTrap he))

theorem pure_floatBinOpTrap {t : FloatType} {op : FloatBinOp} {x y : BitVec t.width}
    (h : ∀ z, ¬ FloatBinOpResult P t op x y z) {c : CConfig H}
    (_hs : Sim ⟨s, f,
      [.plain (.floatConst t x), .plain (.floatConst t y), .plain (.floatBinOp t op)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨z, hz⟩ := FloatBinOpResult_nonempty P t op x y
  exact absurd hz (h z)

theorem pure_testOp {t : IntType} {op : IntTestOp} {x : BitVec t.width} {c : CConfig H}
    (hs : Sim ⟨s, f, [.plain (.intConst t x), .plain (.intTestOp t op)]⟩ c) :
    Target P tgt ⟨s, f, [constI32 (testOp t op x)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.num ⟨.int t, x⟩]) (R := [.plain (.intTestOp t op)])
    (L' := [Silmaril.Wasm.Execution.Core.constI32 (Numerics.intTestOp t op x)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.numeric .intTestOp)

theorem pure_intRelOp {t : IntType} {op : IntRelOp} {x y : BitVec t.width} {c : CConfig H}
    (hs : Sim ⟨s, f, [.plain (.intConst t x), .plain (.intConst t y), .plain (.intRelOp t op)]⟩ c) :
    Target P tgt ⟨s, f, [constI32 (intRelOp t op x y)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩])
    (R := [.plain (.intRelOp t op)])
    (L' := [Silmaril.Wasm.Execution.Core.constI32 (Numerics.intRelOp t op x y)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.numeric .intRelOp)

theorem pure_floatRelOp {t : FloatType} {op : FloatRelOp} {x y : BitVec t.width} {c : CConfig H}
    (hs : Sim ⟨s, f,
      [.plain (.floatConst t x), .plain (.floatConst t y), .plain (.floatRelOp t op)]⟩ c) :
    Target P tgt ⟨s, f, [constI32 (floatRelOp t op x y)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.num ⟨.float t, x⟩, .num ⟨.float t, y⟩])
    (R := [.plain (.floatRelOp t op)])
    (L' := [Silmaril.Wasm.Execution.Core.constI32 (Numerics.floatRelOp t op x y)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.numeric .floatRelOp)

theorem pure_cvtOp {target source : NumType} {op : CvtOp} {x : BitVec source.width}
    {z : BitVec target.width} (h : CvtOpResult P target source op x z) {c : CConfig H}
    (hs : Sim ⟨s, f, [(Val.num ⟨source, x⟩).toAdmin, .plain (.cvtOp target source op)]⟩ c) :
    Target P tgt ⟨s, f, [(Val.num ⟨target, z⟩).toAdmin]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  cases hco : CvtOp.toShared target source op with
  | none => exact absurd h (cvtOpResult_eq_false P target source op hco x z)
  | some co =>
    obtain rfl := cvtOp_toShared_source hco
    obtain rfl := cvtOp_toShared_target hco
    have hz : Numerics.convertP P co x (.ok z) :=
      (cvtOpResult_iff_toShared P op co hco x z).mp h
    exact finishSame hs (vs := [.num ⟨co.source, x⟩]) (R := [.plain (.convert co)])
      (L' := [(Silmaril.Wasm.Execution.Core.Val.num ⟨co.target, z⟩).toAdmin])
      (by simp [cvals, Silmaril.Wasm.Execution.Core.vals, Instr.toCore, CvtOp.toCore,
        ToCore.plainOrNull, Val.toCore, hco])
      (by v2rigid) (by simp [Val.toCore]) (by simp) (.numeric (.convert hz))

theorem pure_cvtOpTrap {target source : NumType} {op : CvtOp} {x : BitVec source.width}
    (h : CvtOpTraps P target source op x) {c : CConfig H}
    (hs : Sim ⟨s, f, [(Val.num ⟨source, x⟩).toAdmin, .plain (.cvtOp target source op)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  rcases target with t | t <;> rcases source with sf | sf <;> cases op <;>
    try exact ((h : False)).elim
  obtain ⟨e, he⟩ : ∃ e, Numerics.convertP P (.trunc sf t _) x (.error e) := h
  exact finishSame hs (vs := [.num ⟨.float sf, x⟩])
    (R := [.plain (.convert (.trunc sf t _))]) (L' := [.trap])
    (by simp [cvals, Silmaril.Wasm.Execution.Core.vals, Instr.toCore, CvtOp.toCore,
      CvtOp.toShared, ToCore.plainOrNull, Val.toCore])
    (by v2rigid) (by simp) (by simp) (.numeric (.convertTrap he))

/-! ## Reference instructions (`8-reduction:210-222`) -/

theorem pure_refIsNullTrue {t : RefType} {c : CConfig H}
    (hs : Sim ⟨s, f, [aref (.null t), .plain .refIsNull]⟩ c) :
    Target P tgt ⟨s, f, [constI32 1]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.ref .null]) (R := [.plain .refIsNull])
    (L' := [Silmaril.Wasm.Execution.Core.constI32 1])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.reference .isNullTrue)

theorem pure_refIsNullFalse {r : Ref} (h : ∀ t, r ≠ .null t) {c : CConfig H}
    (hs : Sim ⟨s, f, [aref r, .plain .refIsNull]⟩ c) :
    Target P tgt ⟨s, f, [constI32 0]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hr : r.toCore ≠ .null := by
    cases r with
    | null t => exact absurd rfl (h t)
    | funcAddr a => simp [Ref.toCore]
    | hostAddr a => simp [Ref.toCore]
  exact finishSame hs (vs := [.ref r.toCore]) (R := [.plain .refIsNull])
    (L' := [Silmaril.Wasm.Execution.Core.constI32 0])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.reference (.isNullFalse hr))

/-! ## Vector instructions (`8-reduction:225-372`) -/

theorem pure_vvUnOp {op : VecUnOp} {cv : V128} {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst cv, .plain (.vvUnOp op)]⟩ c) :
    Target P tgt ⟨s, f, [vconst (VVUnOp op cv)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec cv]) (R := [.plain (.vecUnOp op)])
    (L' := [Silmaril.Wasm.Execution.Core.vconst (Numerics.vvunop op cv)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecUnOp op cv))

theorem pure_vvBinOp {op : VecBinOp} {c₁ c₂ : V128} {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst c₁, vconst c₂, .plain (.vvBinOp op)]⟩ c) :
    Target P tgt ⟨s, f, [vconst (VVBinOp op c₁ c₂)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec c₁, .vec c₂]) (R := [.plain (.vecBinOp op)])
    (L' := [Silmaril.Wasm.Execution.Core.vconst (Numerics.vvbinop op c₁ c₂)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecBinOp op c₁ c₂))

theorem pure_vvTernOp {op : VecTernOp} {c₁ c₂ c₃ : V128} {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst c₁, vconst c₂, vconst c₃, .plain (.vvTernOp op)]⟩ c) :
    Target P tgt ⟨s, f, [vconst (VVTernOp op c₁ c₂ c₃)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec c₁, .vec c₂, .vec c₃]) (R := [.plain (.vecTernOp op)])
    (L' := [Silmaril.Wasm.Execution.Core.vconst (Numerics.vvternop op c₁ c₂ c₃)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecTernOp op c₁ c₂ c₃))

theorem pure_vvTestOp {op : VecTestOp} {cv : V128} {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst cv, .plain (.vvTestOp op)]⟩ c) :
    Target P tgt ⟨s, f, [constI32 (VVTestOp op cv)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec cv]) (R := [.plain (.vecTestOp op)])
    (L' := [Silmaril.Wasm.Execution.Core.constI32 (Numerics.vvtestop op cv)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecTestOp op cv))

theorem pure_vecIntUnOp {sh : IntShape} {op : VecIntUnOp} {cv r : V128}
    (h : VecIntUnOpResult sh op cv r) {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst cv, .plain (.vecIntUnOp sh op)]⟩ c) :
    Target P tgt ⟨s, f, [vconst r]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hr : r = Numerics.vecIntUnOp sh op cv := h
  subst hr
  exact finishSame hs (vs := [.vec cv]) (R := [.plain (.vecIntUnOp sh op)])
    (L' := [Silmaril.Wasm.Execution.Core.vconst (Numerics.vecIntUnOp sh op cv)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecIntUnOp sh op cv))

theorem pure_vecFloatUnOp {sh : FloatShape} {op : FloatUnOp} {cv r : V128}
    (h : VecFloatUnOpResult P sh op cv r) {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst cv, .plain (.vecFloatUnOp sh op)]⟩ c) :
    Target P tgt ⟨s, f, [vconst r]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec cv]) (R := [.plain (.vecFloatUnOp sh op)])
    (L' := [Silmaril.Wasm.Execution.Core.vconst r])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecFloatUnOp h))

theorem pure_vecIntUnOpTrap {sh : IntShape} {op : VecIntUnOp} {cv : V128}
    (h : ∀ r, ¬ VecIntUnOpResult sh op cv r) {c : CConfig H}
    (_hs : Sim ⟨s, f, [vconst cv, .plain (.vecIntUnOp sh op)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c :=
  absurd (show VecIntUnOpResult sh op cv (Numerics.vecIntUnOp sh op cv) from rfl) (h _)

theorem pure_vecFloatUnOpTrap {sh : FloatShape} {op : FloatUnOp} {cv : V128}
    (h : ∀ r, ¬ VecFloatUnOpResult P sh op cv r) {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst cv, .plain (.vecFloatUnOp sh op)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec cv]) (R := [.plain (.vecFloatUnOp sh op)]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecFloatUnOpTrap h))

theorem pure_vecIntBinOp {sh : IntShape} {op : V2.VecIntBinOp} {c₁ c₂ r : V128}
    (h : VecIntBinOpResult P sh op c₁ c₂ r) {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst c₁, vconst c₂, .plain (.vecIntBinOp sh op)]⟩ c) :
    Target P tgt ⟨s, f, [vconst r]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hr : r = Numerics.vecIntBinOp P sh op.toShared c₁ c₂ := h
  subst hr
  exact finishSame hs (vs := [.vec c₁, .vec c₂]) (R := [.plain (.vecIntBinOp sh op.toCore)])
    (L' := [Silmaril.Wasm.Execution.Core.vconst (Numerics.vecIntBinOp P sh op.toCore c₁ c₂)])
    (by v2img) (by v2rigid) (by v2img) (by simp)
    (.vector (.vecIntBinOp sh op.toCore c₁ c₂))

theorem pure_vecFloatBinOp {sh : FloatShape} {op : V2.VecFloatBinOp} {c₁ c₂ r : V128}
    (h : VecFloatBinOpResult P sh op c₁ c₂ r) {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst c₁, vconst c₂, .plain (.vecFloatBinOp sh op)]⟩ c) :
    Target P tgt ⟨s, f, [vconst r]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec c₁, .vec c₂]) (R := [.plain (.vecFloatBinOp sh op.toCore)])
    (L' := [Silmaril.Wasm.Execution.Core.vconst r])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecFloatBinOp h))

theorem pure_vecIntBinOpTrap {sh : IntShape} {op : V2.VecIntBinOp} {c₁ c₂ : V128}
    (h : ∀ r, ¬ VecIntBinOpResult P sh op c₁ c₂ r) {c : CConfig H}
    (_hs : Sim ⟨s, f, [vconst c₁, vconst c₂, .plain (.vecIntBinOp sh op)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c :=
  absurd (show VecIntBinOpResult P sh op c₁ c₂ _ from rfl) (h _)

theorem pure_vecFloatBinOpTrap {sh : FloatShape} {op : V2.VecFloatBinOp} {c₁ c₂ : V128}
    (h : ∀ r, ¬ VecFloatBinOpResult P sh op c₁ c₂ r) {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst c₁, vconst c₂, .plain (.vecFloatBinOp sh op)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec c₁, .vec c₂]) (R := [.plain (.vecFloatBinOp sh op.toCore)])
    (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecFloatBinOpTrap h))

theorem pure_vecAllTrueTrue {sh : IntShape} {cv : V128} (h : ∀ l ∈ sh.lanesOf cv, l ≠ 0)
    {c : CConfig H} (hs : Sim ⟨s, f, [vconst cv, .plain (.vecAllTrue sh)]⟩ c) :
    Target P tgt ⟨s, f, [constI32 1]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hv : Numerics.vecAllTrue sh cv = 1 := by
    have hall : ((sh.lanesOf cv).all fun y => y != 0) = true :=
      List.all_eq_true.mpr fun y hy => by simpa using h y hy
    show Numerics.bool32 ((sh.lanesOf cv).all fun y => y != 0) = 1
    rw [hall]
    rfl
  refine finishSame hs (vs := [.vec cv]) (R := [.plain (.vecAllTrue sh)])
    (L' := [Silmaril.Wasm.Execution.Core.constI32 1])
    (by v2img) (by v2rigid) (by v2img) (by simp) ?_
  have h1 := Silmaril.Wasm.Execution.Core.Step.vector (P := P) (host := tgt) (s := cs)
    (f := cf) (Silmaril.Wasm.Execution.Core.VectorStep.vecAllTrue sh cv)
  rw [hv] at h1
  exact h1

theorem pure_vecAllTrueFalse {sh : IntShape} {cv : V128} (h : ∃ l ∈ sh.lanesOf cv, l = 0)
    {c : CConfig H} (hs : Sim ⟨s, f, [vconst cv, .plain (.vecAllTrue sh)]⟩ c) :
    Target P tgt ⟨s, f, [constI32 0]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hv : Numerics.vecAllTrue sh cv = 0 := by
    obtain ⟨y, hy, rfl⟩ := h
    have hall : ((sh.lanesOf cv).all fun z => z != 0) = false := by
      cases hb : (sh.lanesOf cv).all fun z => z != 0
      · rfl
      · exact absurd (List.all_eq_true.mp hb _ hy) (by simp)
    show Numerics.bool32 ((sh.lanesOf cv).all fun z => z != 0) = 0
    rw [hall]
    rfl
  refine finishSame hs (vs := [.vec cv]) (R := [.plain (.vecAllTrue sh)])
    (L' := [Silmaril.Wasm.Execution.Core.constI32 0])
    (by v2img) (by v2rigid) (by v2img) (by simp) ?_
  have h1 := Silmaril.Wasm.Execution.Core.Step.vector (P := P) (host := tgt) (s := cs)
    (f := cf) (Silmaril.Wasm.Execution.Core.VectorStep.vecAllTrue sh cv)
  rw [hv] at h1
  exact h1

theorem pure_vecIntRelOp {sh : IntShape} {op : IntRelOp} {c₁ c₂ : V128} {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst c₁, vconst c₂, .plain (.vecIntRelOp sh op)]⟩ c) :
    Target P tgt ⟨s, f, [vconst (VecIntRelOp sh op c₁ c₂)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec c₁, .vec c₂]) (R := [.plain (.vecIntRelOp sh op)])
    (L' := [Silmaril.Wasm.Execution.Core.vconst (Numerics.vecIntRelOp sh op c₁ c₂)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecIntRelOp sh op c₁ c₂))

theorem pure_vecFloatRelOp {sh : FloatShape} {op : FloatRelOp} {c₁ c₂ : V128} {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst c₁, vconst c₂, .plain (.vecFloatRelOp sh op)]⟩ c) :
    Target P tgt ⟨s, f, [vconst (VecFloatRelOp sh op c₁ c₂)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec c₁, .vec c₂]) (R := [.plain (.vecFloatRelOp sh op)])
    (L' := [Silmaril.Wasm.Execution.Core.vconst (Numerics.vecFloatRelOp sh op c₁ c₂)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecFloatRelOp sh op c₁ c₂))

theorem pure_vecShiftOp {sh : IntShape} {op : Wasm.VecShiftOp} {cv : V128} {n : BitVec 32}
    {c : CConfig H} (hs : Sim ⟨s, f, [vconst cv, constI32 n, .plain (.vecShiftOp sh op)]⟩ c) :
    Target P tgt ⟨s, f, [vconst (VecShiftOp sh op cv n)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec cv, .num ⟨.int .i32, n⟩]) (R := [.plain (.vecShiftOp sh op)])
    (L' := [Silmaril.Wasm.Execution.Core.vconst (Numerics.vecShiftOp sh op cv n)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecShiftOp sh op cv n))

theorem pure_vecBitmask {sh : IntShape} {cv : V128} {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst cv, .plain (.vecBitmask sh)]⟩ c) :
    Target P tgt ⟨s, f, [constI32 (VecBitmask sh cv)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec cv]) (R := [.plain (.vecBitmask sh)])
    (L' := [Silmaril.Wasm.Execution.Core.constI32 (Numerics.vecBitmask sh cv)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecBitmask sh cv))

theorem pure_vecSwizzle {c₁ c₂ : V128} {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst c₁, vconst c₂, .plain .vecSwizzle]⟩ c) :
    Target P tgt ⟨s, f, [vconst (VecSwizzle c₁ c₂)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec c₁, .vec c₂]) (R := [.plain (.vecSwizzle .swizzle)])
    (L' := [Silmaril.Wasm.Execution.Core.vconst (Numerics.vecSwizzle c₁ c₂)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecSwizzle c₁ c₂))

theorem pure_vecShuffle {idx : List LaneIdx} {c₁ c₂ : V128} (hidx : ∀ j ∈ idx, j.val < 32)
    {c : CConfig H} (hs : Sim ⟨s, f, [vconst c₁, vconst c₂, .plain (.vecShuffle idx)]⟩ c) :
    Target P tgt ⟨s, f, [vconst (VecShuffle idx c₁ c₂)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec c₁, .vec c₂]) (R := [.plain (.vecShuffle idx)])
    (L' := [Silmaril.Wasm.Execution.Core.vconst (Numerics.vecShuffle idx c₁ c₂)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecShuffle idx c₁ c₂ hidx))

theorem pure_vecSplat {sh : Shape} {x : BitVec sh.unpacked.width} {c : CConfig H}
    (hs : Sim ⟨s, f, [(Val.num ⟨sh.unpacked, x⟩).toAdmin, .plain (.vecSplat sh)]⟩ c) :
    Target P tgt ⟨s, f, [vconst (VecSplat sh x)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.num ⟨sh.unpacked, x⟩]) (R := [.plain (.vecSplat sh)])
    (L' := [Silmaril.Wasm.Execution.Core.vconst (Numerics.vecSplat sh x)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecSplat sh x))

theorem pure_vecExtractLane {sh : Shape} {sx : Option Signedness} {i : LaneIdx} {cv : V128}
    (hi : i.val < sh.lanes) {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst cv, .plain (.vecExtractLane sh sx i)]⟩ c) :
    Target P tgt ⟨s, f, [(Val.num ⟨sh.unpacked, VecExtractLane sh sx i.val cv⟩).toAdmin]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec cv]) (R := [.plain (.vecExtractLane sh sx i)])
    (L' := [(Silmaril.Wasm.Execution.Core.Val.num
      ⟨sh.unpacked, Numerics.vecExtractLane sh sx i.val cv⟩).toAdmin])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecExtractLane sh sx i cv hi))

theorem pure_vecReplaceLane {sh : Shape} {i : LaneIdx} {cv : V128}
    {x : BitVec sh.unpacked.width} (hi : i.val < sh.lanes) {c : CConfig H}
    (hs : Sim ⟨s, f,
      [vconst cv, (Val.num ⟨sh.unpacked, x⟩).toAdmin, .plain (.vecReplaceLane sh i)]⟩ c) :
    Target P tgt ⟨s, f, [vconst (VecReplaceLane sh i.val cv x)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec cv, .num ⟨sh.unpacked, x⟩])
    (R := [.plain (.vecReplaceLane sh i)])
    (L' := [Silmaril.Wasm.Execution.Core.vconst (Numerics.vecReplaceLane sh i.val cv x)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecReplaceLane sh i cv x hi))

theorem pure_vecExtUnOp {target source : IntShape} {op : VecExtUnOp} {cv r : V128}
    (h : VecExtUnOpResult target source op cv r) {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst cv, .plain (.vecExtUnOp target source op)]⟩ c) :
    Target P tgt ⟨s, f, [vconst r]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec cv]) (R := [.plain (.vecExtUnOp source target op)])
    (L' := [Silmaril.Wasm.Execution.Core.vconst r])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecExtUnOp h))

theorem pure_vecExtBinOp {target source : IntShape} {op : V2.VecExtBinOp} {c₁ c₂ r : V128}
    (h : VecExtBinOpResult P target source op c₁ c₂ r) {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst c₁, vconst c₂, .plain (.vecExtBinOp target source op)]⟩ c) :
    Target P tgt ⟨s, f, [vconst r]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec c₁, .vec c₂])
    (R := [.plain (.vecExtBinOp source target op.toCore)])
    (L' := [Silmaril.Wasm.Execution.Core.vconst r])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecExtBinOp h))

theorem pure_vecNarrow {target source : IntShape} {sx : Signedness} {c₁ c₂ : V128}
    {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst c₁, vconst c₂, .plain (.vecNarrow target source sx)]⟩ c) :
    Target P tgt ⟨s, f, [vconst (VecNarrow target source sx c₁ c₂)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec c₁, .vec c₂])
    (R := [.plain (.vecNarrow source target sx)])
    (L' := [Silmaril.Wasm.Execution.Core.vconst (Numerics.vnarrow source target sx c₁ c₂)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecNarrow rfl))

theorem pure_vecCvtOp {target source : Shape} {op : VecCvtOp} {cv r : V128}
    (h : VecCvtOpResult P target source op cv r) {c : CConfig H}
    (hs : Sim ⟨s, f, [vconst cv, .plain (.vecCvtOp target source op)]⟩ c) :
    Target P tgt ⟨s, f, [vconst r]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [.vec cv])
    (R := [.plain (.vecConvert source target op.toCore)])
    (L' := [Silmaril.Wasm.Execution.Core.vconst r])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.vector (.vecConvert h))

/-! ## Local instructions (`8-reduction:375-384`) -/

theorem pure_localTee {x : LocalIdx} {v : Val} {c : CConfig H}
    (hs : Sim ⟨s, f, [v.toAdmin, .plain (.localTee x)]⟩ c) :
    Target P tgt ⟨s, f, [v.toAdmin, v.toAdmin, .plain (.localSet x)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := [v.toCore]) (R := [.plain (.localTee x)])
    (L' := [(Val.toCore v).toAdmin, (Val.toCore v).toAdmin, .plain (.localSet x)])
    (by v2img) (by v2rigid) (by v2img) (by simp) (.variable .localTee)

end Silmaril.Wasm.V2.Execution.ToCoreSim
