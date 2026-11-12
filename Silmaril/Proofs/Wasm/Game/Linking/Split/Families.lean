module

public import Silmaril.Proofs.Wasm.Game.Linking.Split.Rel

/-!
# Static linking, separation: Families

Original module documentation:

# Part steps in the shared store: instruction families (M3 step B, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3, step (B).

A host-free step of a part (provider or consumer, in its own store) is matched by the same step
of the renamed configuration in the shared store (`Split.step_sim`, `Linking.Split.Step`). This
file treats the delegated instruction families: pure families are invariant under renaming, the
table and memory families cannot fire in a part (its module instances have no tables, memories,
element or data segments), and the variable, reference and aggregate families are transported
along `PartRel`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Game.Linking.Split

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Numerics

variable {H : Type}

/-- The empty host relation of host-free steps. -/
abbrev noHost : HostSemantics H := fun _ _ _ _ => False

/-- The conclusion of the simulation of one part step `c ⟶ c'` from a renamed configuration
`d` over the shared store `σ`. -/
def SimGoal (P : Profile) (ρ : Ren) (O : Own) (σ : Store H) (d c' : Config H) : Prop :=
  ∃ ρ' O' σ', Step P noHost d ⟨σ', ρ'.frame c'.frame, ρ'.code c'.code⟩ ∧
    PartRel ρ' O' c'.store σ' ∧ O'.FrameGood c'.frame ∧ O'.CodeGood c'.code ∧
    Grow ρ O ρ' O' σ ∧ Touch ρ O σ σ'

theorem SimGoal.same {P : Profile} {ρ : Ren} {O : Own} {σ : Store H} {d c' : Config H}
    (hR : PartRel ρ O c'.store σ) (hf : O.FrameGood c'.frame) (hc : O.CodeGood c'.code)
    (hs : Step P noHost d ⟨σ, ρ.frame c'.frame, ρ.code c'.code⟩) : SimGoal P ρ O σ d c' :=
  ⟨ρ, O, σ, hs, hR, hf, hc, .refl ρ O σ, .refl ρ O σ⟩

/-- Rebuild `CodeGood` for successor code. -/
theorem Own.CodeGood.sub {O : Own} {l l' : List Admin} (h : O.CodeGood l)
    (hr : ∀ r ∈ codeRefs l', r ∈ codeRefs l ∨ O.GoodRef r)
    (hf : ∀ fr ∈ codeFrames l', fr ∈ codeFrames l ∨ O.FrameGood fr) : O.CodeGood l' :=
  ⟨fun r hr' => (hr r hr').elim (h.1 r) id, fun fr hf' => (hf fr hf').elim (h.2 fr) id⟩

theorem global?_eq_some {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst} :
    s.global? f x = some (a, g) ↔ f.module.globals[x.toNat]? = some a ∧ s.globals[a]? = some g := by
  unfold Store.global?
  cases ha : f.module.globals[x.toNat]? with
  | none => simp
  | some b =>
    simp only [Option.some.injEq]
    constructor
    · intro h
      cases hb : s.globals[b]? with
      | none => simp [hb] at h
      | some c =>
        simp [hb] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hb⟩
    · rintro ⟨rfl, h⟩
      simp [h]

theorem Own.CodeGood.cons_left {O : Own} {a : Admin} {l : List Admin} (h : O.CodeGood (a :: l)) :
    O.CodeGood [a] := (O.codeGood_cons.mp h).1

theorem Own.CodeGood.cons_right {O : Own} {a : Admin} {l : List Admin}
    (h : O.CodeGood (a :: l)) : O.CodeGood l := (O.codeGood_cons.mp h).2

theorem Own.CodeGood.head_val {O : Own} {v : Val} {l : List Admin}
    (h : O.CodeGood (v.toAdmin :: l)) : O.GoodVal v := (O.codeGood_single_toAdmin v).mp h.cons_left

theorem Own.CodeGood.head_ref {O : Own} {r : Ref} {l : List Admin}
    (h : O.CodeGood (.ref r :: l)) : O.GoodRef r := (O.codeGood_single_ref r).mp h.cons_left

theorem Own.CodeGood.cons_val {O : Own} {v : Val} {l : List Admin} (hv : O.GoodVal v)
    (hl : O.CodeGood l) : O.CodeGood (v.toAdmin :: l) :=
  O.codeGood_cons.mpr ⟨(O.codeGood_single_toAdmin v).mpr hv, hl⟩

theorem Own.CodeGood.cons_ref {O : Own} {r : Ref} {l : List Admin} (hr : O.GoodRef r)
    (hl : O.CodeGood l) : O.CodeGood (.ref r :: l) :=
  O.codeGood_cons.mpr ⟨(O.codeGood_single_ref r).mpr hr, hl⟩

theorem Own.CodeGood.cons_plain {O : Own} (i : Instr) {l : List Admin}
    (hl : O.CodeGood l) : O.CodeGood (.plain i :: l) :=
  O.codeGood_cons.mpr ⟨O.codeGood_single_plain i, hl⟩

theorem Own.codeGood_constI32 (O : Own) (b : BitVec 32) : O.CodeGood [constI32 b] := by
  simp [Own.CodeGood, constI32, Val.i32, Val.toAdmin]

theorem tag?_none {s : Store H} {f : Frame} {x : TagIdx} (h : f.module.tags = []) :
    s.tag? f x = none := by
  simp [Store.tag?, h]

theorem elem?_none {s : Store H} {f : Frame} {y : ElemIdx} (h : f.module.elems = []) :
    s.elem? f y = none := by
  simp [Store.elem?, h]

theorem data?_none {s : Store H} {f : Frame} {y : DataIdx} (h : f.module.datas = []) :
    s.data? f y = none := by
  simp [Store.data?, h]

theorem table?_none {s : Store H} {f : Frame} {x : TableIdx} (h : f.module.tables = []) :
    s.table? f x = none := by
  simp [Store.table?, h]

theorem mem?_none {s : Store H} {f : Frame} {x : MemIdx} (h : f.module.mems = []) :
    s.mem? f x = none := by
  simp [Store.mem?, h]

/-! ### Tables and memories cannot fire -/

theorem TableStep.not_good {P : Profile} {O : Own} {c c' : Config H} (h : TableStep P c c')
    (hf : O.FrameGood c.frame) : False := by
  have h1 := hf.1.tables
  have h2 := hf.1.elems
  cases h <;> simp_all [table?_none, elem?_none]

theorem MemoryStep.not_good {P : Profile} {O : Own} {c c' : Config H} (h : MemoryStep P c c')
    (hf : O.FrameGood c.frame) : False := by
  have h1 := hf.1.mems
  have h2 := hf.1.datas
  cases h <;> simp_all [mem?_none, data?_none]

/-! ### Pure families -/

theorem ParametricStep.ren {is is' : List Admin} (h : ParametricStep is is') (ρ : Ren) :
    ParametricStep (ρ.code is) (ρ.code is') := by
  cases h with
  | unreachable => simpa using ParametricStep.unreachable
  | nop => simpa using ParametricStep.nop
  | drop v => simpa using ParametricStep.drop (ρ.val v)
  | selectTrue hc => simpa using ParametricStep.selectTrue (v₁ := ρ.val _) (v₂ := ρ.val _) hc
  | selectFalse v₁ v₂ ts => simpa using ParametricStep.selectFalse (ρ.val v₁) (ρ.val v₂) ts

theorem ParametricStep.good {O : Own} {is is' : List Admin} (h : ParametricStep is is')
    (hc : O.CodeGood is) : O.CodeGood is' := by
  obtain ⟨h1, h2⟩ := ParametricStep.reach h
  exact hc.sub (fun r hr => .inl (h1 r hr)) (fun f hf => .inl (h2 f hf))

theorem NumericStep.ren_eq {P : Profile} {is is' : List Admin} (h : NumericStep P is is')
    (ρ : Ren) : ρ.code is = is ∧ ρ.code is' = is' := by
  cases h <;> simp

theorem NumericStep.good {P : Profile} {O : Own} {is is' : List Admin} (h : NumericStep P is is')
    (hc : O.CodeGood is) : O.CodeGood is' := by
  obtain ⟨h1, h2⟩ := NumericStep.reach h
  exact hc.sub (fun r hr => .inl (h1 r hr)) (fun f hf => .inl (h2 f hf))

theorem VectorStep.ren_eq {P : Profile} {is is' : List Admin} (h : VectorStep P is is')
    (ρ : Ren) : ρ.code is = is ∧ ρ.code is' = is' := by
  cases h <;> simp

theorem VectorStep.good {P : Profile} {O : Own} {is is' : List Admin} (h : VectorStep P is is')
    (hc : O.CodeGood is) : O.CodeGood is' := by
  obtain ⟨h1, h2⟩ := VectorStep.reach h
  exact hc.sub (fun r hr => .inl (h1 r hr)) (fun f hf => .inl (h2 f hf))

/-! ### Frames and globals -/

@[simp] theorem Ren.frame_setLocal (ρ : Ren) (f : Frame) (x : LocalIdx) (v : Val) :
    ρ.frame (f.setLocal x v) = (ρ.frame f).setLocal x (ρ.val v) := by
  simp [Ren.frame, Frame.setLocal, List.map_set]

theorem Own.FrameGood.setLocal {O : Own} {f : Frame} (hf : O.FrameGood f) (x : LocalIdx)
    {v : Val} (hv : O.GoodVal v) : O.FrameGood (f.setLocal x v) := by
  refine ⟨hf.1, fun w hw => ?_⟩
  rcases List.mem_or_eq_of_mem_set hw with hw | hw
  · exact hf.2 w hw
  · cases hw; exact hv

theorem setGlobal_getElem? (s : Store H) (a b : Nat) (v : Val) :
    (s.setGlobal a v).globals[b]? =
      if a = b then s.globals[b]?.map (fun g => { g with value := v }) else s.globals[b]? := by
  by_cases h : a = b
  · subst h
    simp only [Store.setGlobal]
    cases hg : s.globals[a]? <;> simp [List.getElem?_modify, hg]
  · simp [Store.setGlobal, List.getElem?_modify, h]

namespace PartRel

variable {ρ : Ren} {O : Own} {p σ : Store H}

theorem setGlobal (hR : PartRel ρ O p σ) {a : Nat} {v : Val} (hv : O.GoodVal v) :
    PartRel ρ O (p.setGlobal a v) (σ.setGlobal a (ρ.val v)) where
  fn := hR.fn
  gl b hb := by
    obtain ⟨g, h1, h2, h3⟩ := hR.gl b hb
    rw [setGlobal_getElem?, setGlobal_getElem?]
    by_cases e : a = b
    · subst e
      simp only [eq_self_iff_true, ite_true, h1, h2, Option.map_some]
      exact ⟨_, rfl, rfl, hv⟩
    · simp only [e, ite_false]
      exact ⟨g, h1, h2, h3⟩
  st := hR.st
  ar := hR.ar
  stInj := hR.stInj
  arInj := hR.arInj

theorem touch_setGlobal {a : Nat} (ha : O.gl a) (v : Val) :
    Touch ρ O σ (σ.setGlobal a v) where
  funcs := rfl
  globals b hb := by
    have e : ¬ a = b := by rintro rfl; exact hb ha
    rw [setGlobal_getElem?]
    simp only [e, ite_false]
  structs _ _ _ := rfl
  arrays _ _ _ := rfl
  structs_len := le_rfl
  arrays_len := le_rfl

theorem global? (hR : PartRel ρ O p σ) {f : Frame} (hf : O.FrameGood f) {x : GlobalIdx}
    {a : Nat} {g : GlobalInst} (h : p.global? f x = some (a, g)) :
    O.gl a ∧ σ.global? f x = some (a, ρ.ginst g) ∧ O.GoodVal g.value := by
  rw [global?_eq_some] at h ⊢
  have ha : O.gl a := hf.1.globals a (List.mem_of_getElem? h.1)
  obtain ⟨g', h1, h2, h3⟩ := hR.gl a ha
  rw [h.2] at h1; cases h1
  exact ⟨ha, ⟨h.1, h2⟩, h3⟩

end PartRel

/-! ### Variable instructions -/

theorem VariableStep.sim {P : Profile} {c c' : Config H} (h : VariableStep c c') {ρ : Ren}
    {O : Own} {σ : Store H} (hR : PartRel ρ O c.store σ) (hf : O.FrameGood c.frame)
    (hc : O.CodeGood c.code) :
    SimGoal P ρ O σ ⟨σ, ρ.frame c.frame, ρ.code c.code⟩ c' := by
  cases h with
  | @localGet s f x v hl =>
    have hv : some v ∈ f.locals := List.mem_of_getElem? hl
    have hl' : (ρ.frame f).local? x = some (some (ρ.val v)) := by
      have hl₀ : f.locals[x.toNat]? = some (some v) := hl
      simp [Frame.local?, Ren.frame_locals, List.getElem?_map, hl₀]
    refine .same hR hf ((O.codeGood_single_toAdmin v).mpr (hf.2 v hv)) ?_
    simpa using Step.variable (P := P) (host := noHost) (VariableStep.localGet (s := σ) hl')
  | @localSet s f x v hx =>
    refine .same hR (hf.setLocal x hc.head_val) O.codeGood_nil ?_
    simpa using Step.variable (P := P) (host := noHost)
      (VariableStep.localSet (s := σ) (f := ρ.frame f) (v := ρ.val v) (x := x)
        (by simpa using hx))
  | @localTee s f x v =>
    have hv : O.GoodVal v := hc.head_val
    refine .same hR hf (.cons_val hv (.cons_val hv (O.codeGood_single_plain _))) ?_
    simpa using Step.variable (P := P) (host := noHost)
      (VariableStep.localTee (s := σ) (f := ρ.frame f) (v := ρ.val v) (x := x))
  | @globalGet s f x a g hg =>
    obtain ⟨-, hg', hv⟩ := hR.global? hf hg
    refine .same hR hf ((O.codeGood_single_toAdmin _).mpr hv) ?_
    simpa [Ren.ginst] using Step.variable (P := P) (host := noHost)
      (VariableStep.globalGet (s := σ) (f := ρ.frame f) hg')
  | @globalSet s f x a g v hg =>
    obtain ⟨ha, hg', -⟩ := hR.global? hf hg
    refine ⟨ρ, O, σ.setGlobal a (ρ.val v), ?_, hR.setGlobal hc.head_val, hf, O.codeGood_nil,
      .refl ρ O σ, PartRel.touch_setGlobal ha _⟩
    simpa using Step.variable (P := P) (host := noHost)
      (VariableStep.globalSet (s := σ) (f := ρ.frame f) (v := ρ.val v) hg')

/-! ### Reference instructions -/

theorem RefStep.sim {P : Profile} {c c' : Config H} (h : RefStep c c') {ρ : Ren}
    {O : Own} {σ : Store H} (hR : PartRel ρ O c.store σ) (hf : O.FrameGood c.frame)
    (hc : O.CodeGood c.code) :
    SimGoal P ρ O σ ⟨σ, ρ.frame c.frame, ρ.code c.code⟩ c' := by
  cases h with
  | @refNull s f ht =>
    refine .same hR hf (by simp) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.refNull (s := σ) (f := ρ.frame f) ht)
  | @refFunc s f x a hx =>
    refine .same hR hf ((O.codeGood_single_ref _).mpr (hf.1.funcs a (List.mem_of_getElem? hx))) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.refFunc (s := σ) (f := ρ.frame f) hx)
  | @refI31 s f i =>
    refine .same hR hf (by simp) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.refI31 (s := σ) (f := ρ.frame f) i)
  | @isNullTrue s f =>
    refine .same hR hf (O.codeGood_constI32 _) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.isNullTrue (s := σ) (f := ρ.frame f))
  | @isNullFalse s f r hr =>
    refine .same hR hf (O.codeGood_constI32 _) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.isNullFalse (s := σ) (f := ρ.frame f) (r := ρ.ref r)
        (by rwa [Ne, Ren.ref_eq_null_iff]))
  | @asNonNullNull s f =>
    refine .same hR hf (by simp) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.asNonNullNull (s := σ) (f := ρ.frame f))
  | @asNonNullAddr s f r hr =>
    refine .same hR hf ((O.codeGood_single_ref _).mpr hc.head_ref) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.asNonNullAddr (s := σ) (f := ρ.frame f) (r := ρ.ref r)
        (by rwa [Ne, Ren.ref_eq_null_iff]))
  | @eqNull s f =>
    refine .same hR hf (O.codeGood_constI32 _) ?_
    simpa using Step.reference (P := P) (host := noHost) (RefStep.eqNull (s := σ) (f := ρ.frame f))
  | @eqTrue s f r hr =>
    refine .same hR hf (O.codeGood_constI32 _) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.eqTrue (s := σ) (f := ρ.frame f) (r := ρ.ref r)
        (by rwa [Ne, Ren.ref_eq_null_iff]))
  | @eqFalse s f r₁ r₂ hr =>
    have h₁ : O.GoodRef r₁ := hc.head_ref
    have h₂ : O.GoodRef r₂ := hc.cons_right.head_ref
    refine .same hR hf (O.codeGood_constI32 _) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.eqFalse (s := σ) (f := ρ.frame f) (r₁ := ρ.ref r₁) (r₂ := ρ.ref r₂)
        (fun e => hr (hR.ref_injective h₁ h₂ e)))
  | @testTrue s f r rt hr =>
    refine .same hR hf (O.codeGood_constI32 _) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.testTrue (s := σ) (f := ρ.frame f) ((hR.refOk_iff hc.head_ref).mpr hr))
  | @testFalse s f r rt hr =>
    refine .same hR hf (O.codeGood_constI32 _) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.testFalse (s := σ) (f := ρ.frame f) (rt := rt)
        (fun h' => hr ((hR.refOk_iff hc.head_ref).mp h')))
  | @castSucceed s f r rt hr =>
    refine .same hR hf ((O.codeGood_single_ref _).mpr hc.head_ref) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.castSucceed (s := σ) (f := ρ.frame f) ((hR.refOk_iff hc.head_ref).mpr hr))
  | @castFail s f r rt hr =>
    refine .same hR hf (by simp) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.castFail (s := σ) (f := ρ.frame f) (rt := rt)
        (fun h' => hr ((hR.refOk_iff hc.head_ref).mp h')))
  | @i31GetNull s f sx =>
    refine .same hR hf (by simp) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.i31GetNull (s := σ) (f := ρ.frame f) sx)
  | @i31GetNum s f sx i =>
    refine .same hR hf (O.codeGood_constI32 _) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.i31GetNum (s := σ) (f := ρ.frame f) sx i)
  | @externConvertNull s f =>
    refine .same hR hf (by simp) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.externConvertNull (s := σ) (f := ρ.frame f))
  | @externConvertAddr s f r hr =>
    refine .same hR hf ((O.codeGood_single_ref _).mpr hc.head_ref) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.externConvertAddr (s := σ) (f := ρ.frame f) (r := ρ.ref r)
        (by rwa [Ne, Ren.ref_eq_null_iff]))
  | @anyConvertNull s f =>
    refine .same hR hf (by simp) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.anyConvertNull (s := σ) (f := ρ.frame f))
  | @anyConvertAddr s f r =>
    have hr : O.GoodRef (.extern r) := hc.head_ref
    refine .same hR hf ((O.codeGood_single_ref _).mpr hr) ?_
    simpa using Step.reference (P := P) (host := noHost)
      (RefStep.anyConvertAddr (s := σ) (f := ρ.frame f) (ρ.ref r))

end Silmaril.Proofs.Wasm.Game.Linking.Split
