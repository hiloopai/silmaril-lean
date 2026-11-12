module

public import Silmaril.Proofs.Wasm.Game.Linking.Split.Families

/-!
# Static linking, separation: Aggregate

Original module documentation:

# Part steps in the shared store: GC aggregates (M3 step B, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3, step (B).

Struct and array instructions of a part are transported along `PartRel`: reads and writes
follow the renaming, and an allocation extends the renaming by the pair of fresh addresses
(the next address of the part store and the next address of the shared store).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Game.Linking.Split

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Numerics

variable {H : Type}

/-! ### Packing commutes with renaming -/

theorem Ren.fval_packField (ρ : Ren) (z : CStorageType) (v : Val) :
    ρ.fval (packField z v) = packField z (ρ.val v) := by
  cases v with
  | num nv =>
    obtain ⟨t, b⟩ := nv
    cases t with
    | int it => cases it <;> rcases z with p | t <;> rfl
    | float ft => rcases z with p | t <;> rfl
  | vec b => rcases z with p | t <;> rfl
  | ref r => rcases z with p | t <;> rfl

theorem Ren.packable_val (ρ : Ren) (z : CStorageType) (v : Val) :
    packable z (ρ.val v) = packable z v := by
  cases v with
  | num nv =>
    obtain ⟨t, b⟩ := nv
    cases t with
    | int it => cases it <;> rcases z with p | t <;> rfl
    | float ft => rcases z with p | t <;> rfl
  | vec b => rcases z with p | t <;> rfl
  | ref r => rcases z with p | t <;> rfl

theorem Ren.unpackField_fval (ρ : Ren) (sx : Option Signedness) (fv : FieldVal) :
    unpackField sx (ρ.fval fv) = ρ.val (unpackField sx fv) := by
  cases fv with
  | val v => rfl
  | pack p b => cases sx with
    | none => rfl
    | some s => cases s <;> rfl

theorem Ren.unpackable_fval (ρ : Ren) (z : CStorageType) (sx : Option Signedness)
    (fv : FieldVal) : unpackable z sx (ρ.fval fv) = unpackable z sx fv := by
  cases fv <;> cases z <;> cases sx <;> rfl

theorem Own.goodVal_unpackField {O : Own} {sx : Option Signedness} {fv : FieldVal}
    (h : O.GoodFV fv) : O.GoodVal (unpackField sx fv) := by
  cases fv with
  | val v => exact h
  | pack p b => cases sx with
    | none => trivial
    | some s => cases s <;> trivial

theorem Own.goodFV_packField {O : Own} (z : CStorageType) {v : Val} (h : O.GoodVal v) :
    O.GoodFV (packField z v) := by
  cases v with
  | num nv =>
    obtain ⟨t, b⟩ := nv
    cases t with
    | int it => cases it <;> rcases z with p | t <;> trivial
    | float ft => rcases z with p | t <;> trivial
  | vec b => rcases z with p | t <;> trivial
  | ref r => rcases z with p | t <;> exact h

theorem defaultVal?_ren {t : CValType} {v : Val} (h : defaultVal? t = some v) (ρ : Ren) :
    ρ.val v = v := by
  unfold defaultVal? at h
  split at h <;> first | (cases h; rfl) | simp at h

theorem defaultVal?_good {O : Own} {t : CValType} {v : Val} (h : defaultVal? t = some v) :
    O.GoodVal v := by
  unfold defaultVal? at h
  split at h <;> first | (cases h; trivial) | simp at h

/-! ### Store updates -/

theorem setStructField_getElem? (s : Store H) (a b i : Nat) (fv : FieldVal) :
    (s.setStructField a i fv).structs[b]? =
      if a = b then s.structs[b]?.map (fun si => { si with fields := si.fields.set i fv })
      else s.structs[b]? := by
  by_cases h : a = b
  · subst h
    simp only [Store.setStructField]
    cases hg : s.structs[a]? <;> simp [List.getElem?_modify, hg]
  · simp [Store.setStructField, List.getElem?_modify, h]

theorem setArrayField_getElem? (s : Store H) (a b i : Nat) (fv : FieldVal) :
    (s.setArrayField a i fv).arrays[b]? =
      if a = b then s.arrays[b]?.map (fun ai => { ai with fields := ai.fields.set i fv })
      else s.arrays[b]? := by
  by_cases h : a = b
  · subst h
    simp only [Store.setArrayField]
    cases hg : s.arrays[a]? <;> simp [List.getElem?_modify, hg]
  · simp [Store.setArrayField, List.getElem?_modify, h]

namespace PartRel

variable {ρ : Ren} {O : Own} {p σ : Store H}

theorem setStructField (hR : PartRel ρ O p σ) {a : Nat} (ha : O.st a) (i : Nat) {fv : FieldVal}
    (hv : O.GoodFV fv) :
    PartRel ρ O (p.setStructField a i fv) (σ.setStructField (ρ.st a) i (ρ.fval fv)) where
  fn := hR.fn
  gl := hR.gl
  st b hb := by
    obtain ⟨si, h1, h2, h3⟩ := hR.st b hb
    rw [setStructField_getElem?, setStructField_getElem?]
    by_cases e : a = b
    · subst e
      simp only [eq_self_iff_true, ite_true, h1, h2, Option.map_some]
      refine ⟨_, rfl, by simp [Ren.sinst, List.map_set], fun fv' hfv => ?_⟩
      rcases List.mem_or_eq_of_mem_set hfv with h | h
      · exact h3 fv' h
      · subst h; exact hv
    · have e' : ρ.st a ≠ ρ.st b := fun e' => e (hR.stInj _ _ ha hb e')
      simp only [e, e', ite_false]
      exact ⟨si, h1, h2, h3⟩
  ar := hR.ar
  stInj := hR.stInj
  arInj := hR.arInj

theorem setArrayField (hR : PartRel ρ O p σ) {a : Nat} (ha : O.ar a) (i : Nat) {fv : FieldVal}
    (hv : O.GoodFV fv) :
    PartRel ρ O (p.setArrayField a i fv) (σ.setArrayField (ρ.ar a) i (ρ.fval fv)) where
  fn := hR.fn
  gl := hR.gl
  st := hR.st
  ar b hb := by
    obtain ⟨ai, h1, h2, h3⟩ := hR.ar b hb
    rw [setArrayField_getElem?, setArrayField_getElem?]
    by_cases e : a = b
    · subst e
      simp only [eq_self_iff_true, ite_true, h1, h2, Option.map_some]
      refine ⟨_, rfl, by simp [Ren.ainst, List.map_set], fun fv' hfv => ?_⟩
      rcases List.mem_or_eq_of_mem_set hfv with h | h
      · exact h3 fv' h
      · subst h; exact hv
    · have e' : ρ.ar a ≠ ρ.ar b := fun e' => e (hR.arInj _ _ ha hb e')
      simp only [e, e', ite_false]
      exact ⟨ai, h1, h2, h3⟩
  stInj := hR.stInj
  arInj := hR.arInj

theorem touch_setStructField {a : Nat} (ha : O.st a) (i : Nat) (fv : FieldVal) :
    Touch ρ O σ (σ.setStructField (ρ.st a) i fv) where
  funcs := rfl
  globals _ _ := rfl
  structs b hb _ := by
    rw [setStructField_getElem?]
    simp only [show ¬ ρ.st a = b from fun e => hb a ha e, ite_false]
  arrays _ _ _ := rfl
  structs_len := by simp [Store.setStructField]
  arrays_len := le_rfl

theorem touch_setArrayField {a : Nat} (ha : O.ar a) (i : Nat) (fv : FieldVal) :
    Touch ρ O σ (σ.setArrayField (ρ.ar a) i fv) where
  funcs := rfl
  globals _ _ := rfl
  structs _ _ _ := rfl
  arrays b hb _ := by
    rw [setArrayField_getElem?]
    simp only [show ¬ ρ.ar a = b from fun e => hb a ha e, ite_false]
  structs_len := le_rfl
  arrays_len := by simp [Store.setArrayField]

theorem struct (hR : PartRel ρ O p σ) {a : Nat} (ha : O.st a) {si : StructInst}
    (hs : p.structs[a]? = some si) :
    σ.structs[ρ.st a]? = some (ρ.sinst si) ∧ ∀ fv ∈ si.fields, O.GoodFV fv := by
  obtain ⟨si', h1, h2, h3⟩ := hR.st a ha
  rw [hs] at h1; cases h1
  exact ⟨h2, h3⟩

theorem array (hR : PartRel ρ O p σ) {a : Nat} (ha : O.ar a) {ai : ArrayInst}
    (hs : p.arrays[a]? = some ai) :
    σ.arrays[ρ.ar a]? = some (ρ.ainst ai) ∧ ∀ fv ∈ ai.fields, O.GoodFV fv := by
  obtain ⟨ai', h1, h2, h3⟩ := hR.ar a ha
  rw [hs] at h1; cases h1
  exact ⟨h2, h3⟩

/-- The renaming after allocating a struct. -/
def stAlloc (ρ : Ren) (p σ : Store H) : Ren :=
  { ρ with st := fun a => if a = p.structs.length then σ.structs.length else ρ.st a }

/-- The ownership after allocating a struct. -/
def stOwn (O : Own) (p : Store H) : Own :=
  { O with st := fun a => O.st a ∨ a = p.structs.length }

def arAlloc (ρ : Ren) (p σ : Store H) : Ren :=
  { ρ with ar := fun a => if a = p.arrays.length then σ.arrays.length else ρ.ar a }

def arOwn (O : Own) (p : Store H) : Own :=
  { O with ar := fun a => O.ar a ∨ a = p.arrays.length }

theorem grow_stAlloc (hR : PartRel ρ O p σ) :
    Grow ρ O (stAlloc ρ p σ) (stOwn O p) σ where
  fn := rfl
  gl := rfl
  st a ha := ⟨.inl ha, by simp [stAlloc, (hR.st_lt ha).1.ne]⟩
  ar a ha := ⟨ha, rfl⟩
  stNew a ha := by
    rcases ha with ha | rfl
    · exact .inl ha
    · exact .inr (by simp [stAlloc])
  arNew a ha := .inl ha

theorem grow_arAlloc (hR : PartRel ρ O p σ) :
    Grow ρ O (arAlloc ρ p σ) (arOwn O p) σ where
  fn := rfl
  gl := rfl
  st a ha := ⟨ha, rfl⟩
  ar a ha := ⟨.inl ha, by simp [arAlloc, (hR.ar_lt ha).1.ne]⟩
  stNew a ha := .inl ha
  arNew a ha := by
    rcases ha with ha | rfl
    · exact .inl ha
    · exact .inr (by simp [arAlloc])

private theorem grow_ginst {ρ' : Ren} {O' : Own} (hg : Grow ρ O ρ' O' σ) {g : GlobalInst}
    (hv : O.GoodVal g.value) : ρ'.ginst g = ρ.ginst g := by
  simp [Ren.ginst, (hg.goodVal hv).1]

private theorem grow_sinst {ρ' : Ren} {O' : Own} (hg : Grow ρ O ρ' O' σ) {s : StructInst}
    (hv : ∀ fv ∈ s.fields, O.GoodFV fv) : ρ'.sinst s = ρ.sinst s := by
  simp only [Ren.sinst, StructInst.mk.injEq, true_and]
  exact List.map_congr_left fun fv h => (hg.goodFV (hv fv h)).1

private theorem grow_ainst {ρ' : Ren} {O' : Own} (hg : Grow ρ O ρ' O' σ) {s : ArrayInst}
    (hv : ∀ fv ∈ s.fields, O.GoodFV fv) : ρ'.ainst s = ρ.ainst s := by
  simp only [Ren.ainst, ArrayInst.mk.injEq, true_and]
  exact List.map_congr_left fun fv h => (hg.goodFV (hv fv h)).1

/-- Extending an injective address map by one fresh pair `n ↦ m` keeps it injective. -/
private theorem inj_extend {own : Nat → Prop} {f : Nat → Nat} {n m : Nat}
    (hinj : ∀ a b, own a → own b → f a = f b → a = b) (hlt : ∀ a, own a → a < n ∧ f a < m) :
    ∀ a b, (own a ∨ a = n) → (own b ∨ b = n) →
      (if a = n then m else f a) = (if b = n then m else f b) → a = b := by
  intro a b ha hb e
  rcases ha with ha | ea <;> rcases hb with hb | eb
  · have e' : f a = f b := by
      simpa [(hlt a ha).1.ne, (hlt b hb).1.ne] using e
    exact hinj a b ha hb e'
  · have e' : f a = m := by simpa [(hlt a ha).1.ne, eb] using e
    exact absurd e' (hlt a ha).2.ne
  · have e' : m = f b := by simpa [ea, (hlt b hb).1.ne] using e
    exact absurd e'.symm (hlt b hb).2.ne
  · exact ea.trans eb.symm

/-- The struct component of `PartRel` after allocating a struct. -/
private theorem addStruct_st (hR : PartRel ρ O p σ) {si : StructInst}
    (hsi : ∀ fv ∈ si.fields, O.GoodFV fv) (a : Nat) (ha : (stOwn O p).st a) :
    ∃ s, (p.addStruct si).structs[a]? = some s ∧
      (σ.addStruct (ρ.sinst si)).structs[(stAlloc ρ p σ).st a]? =
        some ((stAlloc ρ p σ).sinst s) ∧
      ∀ fv ∈ s.fields, (stOwn O p).GoodFV fv := by
  have hg : Grow ρ O (stAlloc ρ p σ) (stOwn O p) σ := hR.grow_stAlloc
  rcases ha with ha | ha
  · obtain ⟨s, h1, h2, h3⟩ := hR.st a ha
    have hl : a < p.structs.length ∧ ρ.st a < σ.structs.length := hR.st_lt ha
    have hst : (stAlloc ρ p σ).st a = ρ.st a := (hg.st a ha).2
    refine ⟨s, by simp [Store.addStruct, List.getElem?_append_left hl.1, h1], ?_,
      fun fv hfv => (hg.goodFV (h3 fv hfv)).2⟩
    rw [hst, grow_sinst hg h3]
    simp [Store.addStruct, List.getElem?_append_left hl.2, h2]
  · have hst : (stAlloc ρ p σ).st a = σ.structs.length := by simp [stAlloc, ha]
    refine ⟨si, by simp [Store.addStruct, ha], ?_, fun fv hfv => (hg.goodFV (hsi fv hfv)).2⟩
    rw [hst, grow_sinst hg hsi]
    simp [Store.addStruct]

/-- The array component of `PartRel` after allocating an array. -/
private theorem addArray_ar (hR : PartRel ρ O p σ) {ai : ArrayInst}
    (hai : ∀ fv ∈ ai.fields, O.GoodFV fv) (a : Nat) (ha : (arOwn O p).ar a) :
    ∃ s, (p.addArray ai).arrays[a]? = some s ∧
      (σ.addArray (ρ.ainst ai)).arrays[(arAlloc ρ p σ).ar a]? =
        some ((arAlloc ρ p σ).ainst s) ∧
      ∀ fv ∈ s.fields, (arOwn O p).GoodFV fv := by
  have hg : Grow ρ O (arAlloc ρ p σ) (arOwn O p) σ := hR.grow_arAlloc
  rcases ha with ha | ha
  · obtain ⟨s, h1, h2, h3⟩ := hR.ar a ha
    have hl : a < p.arrays.length ∧ ρ.ar a < σ.arrays.length := hR.ar_lt ha
    have har : (arAlloc ρ p σ).ar a = ρ.ar a := (hg.ar a ha).2
    refine ⟨s, by simp [Store.addArray, List.getElem?_append_left hl.1, h1], ?_,
      fun fv hfv => (hg.goodFV (h3 fv hfv)).2⟩
    rw [har, grow_ainst hg h3]
    simp [Store.addArray, List.getElem?_append_left hl.2, h2]
  · have har : (arAlloc ρ p σ).ar a = σ.arrays.length := by simp [arAlloc, ha]
    refine ⟨ai, by simp [Store.addArray, ha], ?_, fun fv hfv => (hg.goodFV (hai fv hfv)).2⟩
    rw [har, grow_ainst hg hai]
    simp [Store.addArray]

theorem addStruct (hR : PartRel ρ O p σ) {si : StructInst} (hsi : ∀ fv ∈ si.fields, O.GoodFV fv) :
    PartRel (stAlloc ρ p σ) (stOwn O p) (p.addStruct si) (σ.addStruct (ρ.sinst si)) := by
  have hg : Grow ρ O (stAlloc ρ p σ) (stOwn O p) σ := hR.grow_stAlloc
  refine ⟨fun a ha => ?_, fun a ha => ?_, addStruct_st hR hsi, fun a ha => ?_,
    inj_extend hR.stInj fun a ha => hR.st_lt ha, hR.arInj⟩
  · obtain ⟨fi, h1, fi', h2, h3, h4⟩ := hR.fn a ha
    exact ⟨fi, h1, fi', h2, h3, fun c hc => ⟨(h4 c hc).1, hg.modGood (h4 c hc).2⟩⟩
  · obtain ⟨g, h1, h2, h3⟩ := hR.gl a ha
    exact ⟨g, h1, by rw [grow_ginst hg h3]; exact h2, (hg.goodVal h3).2⟩
  · obtain ⟨s, h1, h2, h3⟩ := hR.ar a ha
    exact ⟨s, h1, by rw [grow_ainst hg h3]; exact h2, fun fv hfv => (hg.goodFV (h3 fv hfv)).2⟩

theorem addArray (hR : PartRel ρ O p σ) {ai : ArrayInst} (hai : ∀ fv ∈ ai.fields, O.GoodFV fv) :
    PartRel (arAlloc ρ p σ) (arOwn O p) (p.addArray ai) (σ.addArray (ρ.ainst ai)) := by
  have hg : Grow ρ O (arAlloc ρ p σ) (arOwn O p) σ := hR.grow_arAlloc
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, addArray_ar hR hai, hR.stInj,
    inj_extend hR.arInj fun a ha => hR.ar_lt ha⟩
  · obtain ⟨fi, h1, fi', h2, h3, h4⟩ := hR.fn a ha
    exact ⟨fi, h1, fi', h2, h3, fun c hc => ⟨(h4 c hc).1, hg.modGood (h4 c hc).2⟩⟩
  · obtain ⟨g, h1, h2, h3⟩ := hR.gl a ha
    exact ⟨g, h1, by rw [grow_ginst hg h3]; exact h2, (hg.goodVal h3).2⟩
  · obtain ⟨s, h1, h2, h3⟩ := hR.st a ha
    exact ⟨s, h1, by rw [grow_sinst hg h3]; exact h2, fun fv hfv => (hg.goodFV (h3 fv hfv)).2⟩

theorem touch_addStruct (si : StructInst) : Touch ρ O σ (σ.addStruct si) where
  funcs := rfl
  globals _ _ := rfl
  structs b _ hb := by simp [Store.addStruct, List.getElem?_append_left hb]
  arrays _ _ _ := rfl
  structs_len := by simp [Store.addStruct]
  arrays_len := le_rfl

theorem touch_addArray (ai : ArrayInst) : Touch ρ O σ (σ.addArray ai) where
  funcs := rfl
  globals _ _ := rfl
  structs _ _ _ := rfl
  arrays b _ hb := by simp [Store.addArray, List.getElem?_append_left hb]
  structs_len := le_rfl
  arrays_len := by simp [Store.addArray]

end PartRel

@[simp] theorem Ren.frame_type? (ρ : Ren) (f : Frame) (x : TypeIdx) :
    (ρ.frame f).type? x = f.type? x := rfl

theorem Ren.sinst_new (ρ : Ren) (d : DefType) (fs : List CFieldType) (vs : List Val) :
    ρ.sinst ⟨d, (fs.zip vs).map fun (ft, v) => packField (fieldStorage ft) v⟩ =
      ⟨d, (fs.zip (vs.map ρ.val)).map fun (ft, v) => packField (fieldStorage ft) v⟩ := by
  simp only [Ren.sinst, List.map_map, StructInst.mk.injEq, true_and]
  induction fs generalizing vs with
  | nil => simp
  | cons ft fs ih =>
    cases vs with
    | nil => simp
    | cons v vs => simp [Ren.fval_packField, ih]

theorem Ren.ainst_new (ρ : Ren) (d : DefType) (z : CStorageType) (vs : List Val) :
    ρ.ainst ⟨d, vs.map (packField z)⟩ = ⟨d, (vs.map ρ.val).map (packField z)⟩ := by
  simp [Ren.ainst, List.map_map, Function.comp_def, Ren.fval_packField]

theorem mapM_defaultVal?_ren {ts : List CFieldType} {vs : List Val}
    (h : ts.mapM (fun ft => defaultVal? (fieldStorage ft).unpack) = some vs) (ρ : Ren) :
    vs.map ρ.val = vs ∧ ∀ (O : Own), ∀ v ∈ vs, O.GoodVal v := by
  have hm := SingleThreaded.mapM_some_mem h
  refine ⟨(List.map_congr_left fun v hv => ?_).trans (List.map_id vs), fun O v hv => ?_⟩
  · obtain ⟨_, _, h'⟩ := hm v hv
    exact defaultVal?_ren h' ρ
  · obtain ⟨_, _, h'⟩ := hm v hv
    exact defaultVal?_good h'

/-- Discharge goodness of successor code whose references and frames come from the
predecessor. -/
macro "sub_good" hc:term : tactic =>
  `(tactic| (refine Own.CodeGood.sub $hc (fun r hr => .inl ?_) (fun fr hfr => .inl ?_) <;>
    first | (simp at hr ⊢ <;> tauto) | (simp at hfr ⊢ <;> tauto)))

/-- An array referenced by good code of a part is related to its image in the shared store. -/
private theorem PartRel.array_code {ρ : Ren} {O : Own} {p σ : Store H} (hR : PartRel ρ O p σ)
    {l : List Admin} (hc : O.CodeGood l) {a : Nat} (hm : Ref.array a ∈ codeRefs l)
    {ai : ArrayInst} (hs : p.arrays[a]? = some ai) : σ.arrays[ρ.ar a]? = some (ρ.ainst ai) :=
  (hR.array (by simpa using hc.1 _ hm) hs).1

/-- The `struct.new` case of `AggregateStep.sim`: the struct is allocated at the next shared
address, extending the renaming. -/
private theorem structNew_sim {P : Profile} {s : Store H} {f : Frame} {x : TypeIdx} {d : DefType}
    {fs : Ty (.list .field)} {vs : List Val} (hd : f.type? x = some d)
    (he : Expand d (.struct fs)) (hn : vs.length = fs.length)
    (hp : ∀ p ∈ fs.toList.zip vs, packable (fieldStorage p.1) p.2) {ρ : Ren} {O : Own}
    {σ : Store H} (hR : PartRel ρ O s σ) (hf : O.FrameGood f)
    (hc : O.CodeGood (vals vs ++ [.plain (.structNew x)])) :
    SimGoal P ρ O σ ⟨σ, ρ.frame f, ρ.code (vals vs ++ [.plain (.structNew x)])⟩
      ⟨s.addStruct ⟨d, (fs.toList.zip vs).map fun (ft, v) => packField (fieldStorage ft) v⟩, f,
        [.ref (.struct s.structs.length)]⟩ := by
  have hvs : ∀ v ∈ vs, O.GoodVal v :=
    (Own.codeGood_vals O).mp ((Own.codeGood_append O).mp hc).1
  have hsi : ∀ fv ∈ ((fs.toList.zip vs).map fun (ft, v) => packField (fieldStorage ft) v),
      O.GoodFV fv := by
    intro fv hfv
    obtain ⟨⟨ft, v⟩, hm, hfv'⟩ := List.mem_map.mp hfv
    exact hfv' ▸ Own.goodFV_packField _ (hvs v (List.of_mem_zip hm).2)
  have hp' : ∀ q ∈ fs.toList.zip (vs.map ρ.val), packable (fieldStorage q.1) q.2 := by
    intro q hq
    have hq' : q ∈ (fs.toList.zip vs).map (Prod.map id ρ.val) := by
      simpa only [List.zip_map_right] using hq
    obtain ⟨⟨ft, v⟩, hm, hq''⟩ := List.mem_map.mp hq'
    exact hq'' ▸ by simpa [Ren.packable_val] using hp _ hm
  have hst : Step P noHost ⟨σ, ρ.frame f, vals (vs.map ρ.val) ++ [.plain (.structNew x)]⟩
      ⟨σ.addStruct ⟨d, (fs.toList.zip (vs.map ρ.val)).map
          fun (ft, v) => packField (fieldStorage ft) v⟩, ρ.frame f,
        [.ref (.struct σ.structs.length)]⟩ :=
    Step.aggregate (AggregateStep.structNew hd he (by simpa using hn) hp')
  have hg : Grow ρ O (PartRel.stAlloc ρ s σ) (PartRel.stOwn O s) σ := hR.grow_stAlloc
  refine ⟨_, _, _, ?_, hR.addStruct (si := ⟨d, _⟩) hsi, (hg.frameGood hf).2,
    by simp [PartRel.stOwn], hg, PartRel.touch_addStruct _⟩
  rw [Ren.code_append, Ren.code_vals, Ren.sinst_new, (hg.frameGood hf).1]
  simpa [PartRel.stAlloc] using hst

/-- The `array.new_fixed` case of `AggregateStep.sim`: the array is allocated at the next
shared address, extending the renaming. -/
private theorem arrayNewFixed_sim {P : Profile} {s : Store H} {f : Frame} {x : TypeIdx}
    {n : Fin (2 ^ 32)} {d : DefType} {ft : CFieldType} {vs : List Val}
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (hn : vs.length = n.val)
    (hp : ∀ v ∈ vs, packable (fieldStorage ft) v) {ρ : Ren} {O : Own}
    {σ : Store H} (hR : PartRel ρ O s σ) (hf : O.FrameGood f)
    (hc : O.CodeGood (vals vs ++ [.plain (.arrayNewFixed x n)])) :
    SimGoal P ρ O σ ⟨σ, ρ.frame f, ρ.code (vals vs ++ [.plain (.arrayNewFixed x n)])⟩
      ⟨s.addArray ⟨d, vs.map (packField (fieldStorage ft))⟩, f, [arrRef s.arrays.length]⟩ := by
  have hvs : ∀ v ∈ vs, O.GoodVal v :=
    (Own.codeGood_vals O).mp ((Own.codeGood_append O).mp hc).1
  have hai : ∀ fv ∈ vs.map (packField (fieldStorage ft)), O.GoodFV fv := by
    intro fv hfv
    obtain ⟨v, hv, hfv'⟩ := List.mem_map.mp hfv
    exact hfv' ▸ Own.goodFV_packField _ (hvs v hv)
  have hp' : ∀ v ∈ vs.map ρ.val, packable (fieldStorage ft) v := by
    intro v hv
    obtain ⟨w, hw, hv'⟩ := List.mem_map.mp hv
    exact hv' ▸ by simpa [Ren.packable_val] using hp w hw
  have hst : Step P noHost ⟨σ, ρ.frame f, vals (vs.map ρ.val) ++ [.plain (.arrayNewFixed x n)]⟩
      ⟨σ.addArray ⟨d, (vs.map ρ.val).map (packField (fieldStorage ft))⟩, ρ.frame f,
        [arrRef σ.arrays.length]⟩ :=
    Step.aggregate (AggregateStep.arrayNewFixed hd he (by simpa using hn) hp')
  have hg : Grow ρ O (PartRel.arAlloc ρ s σ) (PartRel.arOwn O s) σ := hR.grow_arAlloc
  refine ⟨_, _, _, ?_, hR.addArray (ai := ⟨d, _⟩) hai, (hg.frameGood hf).2,
    by simp [PartRel.arOwn], hg, PartRel.touch_addArray _⟩
  rw [Ren.code_append, Ren.code_vals, Ren.ainst_new, (hg.frameGood hf).1]
  simpa [PartRel.arAlloc] using hst

theorem AggregateStep.sim {P : Profile} {c c' : Config H} (h : AggregateStep c c') {ρ : Ren}
    {O : Own} {σ : Store H} (hR : PartRel ρ O c.store σ) (hf : O.FrameGood c.frame)
    (hc : O.CodeGood c.code) :
    SimGoal P ρ O σ ⟨σ, ρ.frame c.frame, ρ.code c.code⟩ c' := by
  have he₀ : c.frame.module.elems = [] := hf.1.elems
  have hd₀ : c.frame.module.datas = [] := hf.1.datas
  cases h with
  | structNew hd he hn hp => exact structNew_sim hd he hn hp hR hf hc
  | @structNewDefault s f x d fs vs hd he hdef =>
    obtain ⟨hmap, hgood⟩ := mapM_defaultVal?_ren hdef ρ
    refine .same hR hf ?_ ?_
    · rw [Own.codeGood_append, Own.codeGood_vals]
      exact ⟨hgood O, by simp⟩
    · simpa [hmap] using Step.aggregate (P := P) (host := noHost)
        (AggregateStep.structNewDefault (s := σ) (f := ρ.frame f) hd he hdef)
  | structGetNull =>
    exact .same hR hf (by simp)
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.structGetNull (s := σ) (f := ρ.frame _))))
  | @structGetStruct s f sx x i a si fv d fs ft hs hfv hd he hi hu =>
    have ha : O.st a := by simpa using hc.1 (.struct a) (by simp)
    obtain ⟨h1, h2⟩ := hR.struct ha hs
    refine .same hR hf (by simpa using (Own.goodVal_unpackField (sx := sx)
      (h2 fv (List.mem_of_getElem? hfv)))) ?_
    simpa [Ren.unpackField_fval] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.structGetStruct (s := σ) (f := ρ.frame f) (sx := sx) (i := i)
        (fv := ρ.fval fv) h1 (by simp [Ren.sinst, hfv]) hd he hi (by rwa [Ren.unpackable_fval]))
  | @structSetNull s f x i v =>
    exact .same hR hf (by simp)
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.structSetNull (s := σ) (f := ρ.frame f) (x := x) (i := i) (v := ρ.val v))))
  | @structSetStruct s f x i v a d fs ft si hd he hi hs hfl hp =>
    show SimGoal P ρ O σ
      ⟨σ, ρ.frame f, ρ.code [.ref (.struct a), v.toAdmin, .plain (.structSet x i)]⟩
      ⟨s.setStructField a i.toNat (packField (fieldStorage ft) v), f, []⟩
    have ha : O.st a := hc.head_ref
    have hv : O.GoodVal v := hc.cons_right.head_val
    have h1 : σ.structs[ρ.st a]? = some (ρ.sinst si) := (hR.struct ha hs).1
    refine ⟨ρ, O, _, ?_, hR.setStructField ha i.toNat (Own.goodFV_packField _ hv), hf,
      O.codeGood_nil, .refl ρ O σ, PartRel.touch_setStructField ha _ _⟩
    simpa [Ren.fval_packField] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.structSetStruct (s := σ) (f := ρ.frame f) (v := ρ.val v) hd he hi h1
        (by simpa [Ren.sinst] using hfl) (by rwa [Ren.packable_val]))
  | @arrayNew s f x v n =>
    have hv : O.GoodVal v := hc.head_val
    refine .same hR hf ?_ ?_
    · rw [Own.codeGood_append, Own.codeGood_vals]
      exact ⟨fun w hw => (List.eq_of_mem_replicate hw) ▸ hv, by simp⟩
    · simpa [List.map_replicate] using Step.aggregate (P := P) (host := noHost)
        (AggregateStep.arrayNew (s := σ) (f := ρ.frame f) (x := x) (ρ.val v) n)
  | @arrayNewDefault s f x n d ft v hd he hv =>
    refine .same hR hf ?_ ?_
    · rw [Own.codeGood_append, Own.codeGood_vals]
      exact ⟨fun w hw => (List.eq_of_mem_replicate hw) ▸ defaultVal?_good hv, by simp⟩
    · simpa [List.map_replicate, defaultVal?_ren hv ρ] using Step.aggregate (P := P)
        (host := noHost) (AggregateStep.arrayNewDefault (s := σ) (f := ρ.frame f) hd he hv)
  | arrayNewFixed hd he hn hp => exact arrayNewFixed_sim hd he hn hp hR hf hc
  | arrayNewElemOob he => exact nomatch (elem?_none he₀).symm.trans he
  | arrayNewElemAlloc he => exact nomatch (elem?_none he₀).symm.trans he
  | arrayNewDataOob _ _ hdat => exact nomatch (data?_none hd₀).symm.trans hdat
  | arrayNewDataNum _ _ hdat => exact nomatch (data?_none hd₀).symm.trans hdat
  | arrayGetNull =>
    exact .same hR hf (by simp)
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.arrayGetNull (s := σ) (f := ρ.frame _))))
  | @arrayGetOob s f sx x i a ai ha hl =>
    have h1 : σ.arrays[ρ.ar a]? = some (ρ.ainst ai) := hR.array_code hc (by simp) ha
    exact .same hR hf (by simp)
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.arrayGetOob (s := σ) (f := ρ.frame f) (sx := sx) (x := x) h1
          (by simpa [Ren.ainst] using hl))))
  | @arrayGetArray s f sx x i a ai fv d ft ha hfv hd he hu =>
    have ha' : O.ar a := by simpa using hc.1 (.array a) (by simp)
    obtain ⟨h1, h2⟩ := hR.array ha' ha
    refine .same hR hf (by simpa using (Own.goodVal_unpackField (sx := sx)
      (h2 fv (List.mem_of_getElem? hfv)))) ?_
    simpa [Ren.unpackField_fval] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayGetArray (s := σ) (f := ρ.frame f) (sx := sx) (i := i)
        (fv := ρ.fval fv) h1 (by simp [Ren.ainst, hfv]) hd he (by rwa [Ren.unpackable_fval]))
  | @arraySetNull s f x i v =>
    exact .same hR hf (by simp)
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.arraySetNull (s := σ) (f := ρ.frame f) (x := x) (i := i) (v := ρ.val v))))
  | @arraySetOob s f x i v a ai ha hl =>
    have h1 : σ.arrays[ρ.ar a]? = some (ρ.ainst ai) := hR.array_code hc (by simp) ha
    exact .same hR hf (by simp)
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.arraySetOob (s := σ) (f := ρ.frame f) (x := x) (v := ρ.val v) h1
          (by simpa [Ren.ainst] using hl))))
  | @arraySetArray s f x i v a ai d ft ha hl hd he hp =>
    show SimGoal P ρ O σ
      ⟨σ, ρ.frame f, ρ.code [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x)]⟩
      ⟨s.setArrayField a i.toNat (packField (fieldStorage ft) v), f, []⟩
    have ha' : O.ar a := hc.head_ref
    have hv : O.GoodVal v := hc.cons_right.cons_right.head_val
    have h1 : σ.arrays[ρ.ar a]? = some (ρ.ainst ai) := (hR.array ha' ha).1
    refine ⟨ρ, O, _, ?_, hR.setArrayField ha' i.toNat (Own.goodFV_packField _ hv), hf,
      O.codeGood_nil, .refl ρ O σ, PartRel.touch_setArrayField ha' _ _⟩
    simpa [Ren.fval_packField] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arraySetArray (s := σ) (f := ρ.frame f) (v := ρ.val v) h1
        (by simpa [Ren.ainst] using hl) hd he (by rwa [Ren.packable_val]))
  | arrayLenNull =>
    exact .same hR hf (by simp)
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.arrayLenNull (s := σ) (f := ρ.frame _))))
  | @arrayLenArray s f a ai ha =>
    have h1 : σ.arrays[ρ.ar a]? = some (ρ.ainst ai) := hR.array_code hc (by simp) ha
    refine .same hR hf (by simp [constI32, Val.i32, Val.toAdmin]) ?_
    simpa [Ren.ainst] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayLenArray (s := σ) (f := ρ.frame f) h1)
  | @arrayFillNull s f x i n v =>
    exact .same hR hf (by simp)
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.arrayFillNull (s := σ) (f := ρ.frame f) (x := x) (i := i) (n := n)
          (v := ρ.val v))))
  | @arrayFillOob s f x i n v a ai ha hl =>
    have h1 : σ.arrays[ρ.ar a]? = some (ρ.ainst ai) := hR.array_code hc (by simp) ha
    exact .same hR hf (by simp)
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.arrayFillOob (s := σ) (f := ρ.frame f) (x := x) (v := ρ.val v) h1
          (by simpa [Ren.ainst] using hl))))
  | @arrayFillZero s f x i v a ai ha hl =>
    have h1 : σ.arrays[ρ.ar a]? = some (ρ.ainst ai) := hR.array_code hc (by simp) ha
    exact .same hR hf O.codeGood_nil
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.arrayFillZero (s := σ) (f := ρ.frame f) (x := x) (v := ρ.val v) h1
          (by simpa [Ren.ainst] using hl))))
  | @arrayFillSucc s f x i n v a ai ha hl hn =>
    have h1 : σ.arrays[ρ.ar a]? = some (ρ.ainst ai) := hR.array_code hc (by simp) ha
    refine .same hR hf (by sub_good hc) ?_
    simpa using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayFillSucc (s := σ) (f := ρ.frame f) (x := x) (v := ρ.val v) h1
        (by simpa [Ren.ainst] using hl) hn)
  | @arrayCopyNull₁ s f x₁ x₂ i₁ i₂ n r =>
    exact .same hR hf (by simp)
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.arrayCopyNull₁ (s := σ) (f := ρ.frame f) (x₁ := x₁) (x₂ := x₂) (i₁ := i₁)
          (i₂ := i₂) (n := n) (r := ρ.ref r))))
  | @arrayCopyNull₂ s f x₁ x₂ i₁ i₂ n r =>
    exact .same hR hf (by simp)
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.arrayCopyNull₂ (s := σ) (f := ρ.frame f) (x₁ := x₁) (x₂ := x₂) (i₁ := i₁)
          (i₂ := i₂) (n := n) (r := ρ.ref r))))
  | @arrayCopyOob₁ s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₁ ha hl =>
    have h1 : σ.arrays[ρ.ar a₁]? = some (ρ.ainst ai₁) := hR.array_code hc (by simp) ha
    exact .same hR hf (by simp)
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.arrayCopyOob₁ (s := σ) (f := ρ.frame f) (x₁ := x₁) (x₂ := x₂)
          (i₂ := i₂) (a₂ := ρ.ar a₂) h1 (by simpa [Ren.ainst] using hl))))
  | @arrayCopyOob₂ s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₂ ha hl =>
    have h1 : σ.arrays[ρ.ar a₂]? = some (ρ.ainst ai₂) := hR.array_code hc (by simp) ha
    exact .same hR hf (by simp)
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.arrayCopyOob₂ (s := σ) (f := ρ.frame f) (x₁ := x₁) (x₂ := x₂)
          (i₁ := i₁) (a₁ := ρ.ar a₁) h1 (by simpa [Ren.ainst] using hl))))
  | @arrayCopyZero s f x₁ x₂ i₁ i₂ a₁ a₂ ai₁ ai₂ ha₁ ha₂ hl =>
    have h1 : σ.arrays[ρ.ar a₁]? = some (ρ.ainst ai₁) := hR.array_code hc (by simp) ha₁
    have h2 : σ.arrays[ρ.ar a₂]? = some (ρ.ainst ai₂) := hR.array_code hc (by simp) ha₂
    exact .same hR hf O.codeGood_nil
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.arrayCopyZero (s := σ) (f := ρ.frame f) (x₁ := x₁) (x₂ := x₂) h1 h2
          (by simpa [Ren.ainst] using hl))))
  | @arrayCopyLe s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₁ ai₂ d₂ ft₂ ha₁ ha₂ hl hn hd he hle =>
    have h1 : σ.arrays[ρ.ar a₁]? = some (ρ.ainst ai₁) := hR.array_code hc (by simp) ha₁
    have h2 : σ.arrays[ρ.ar a₂]? = some (ρ.ainst ai₂) := hR.array_code hc (by simp) ha₂
    refine .same hR hf (by sub_good hc) ?_
    simpa using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayCopyLe (s := σ) (f := ρ.frame f) h1 h2
        (by simpa [Ren.ainst] using hl) hn hd he hle)
  | @arrayCopyGt s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₁ ai₂ d₂ ft₂ ha₁ ha₂ hl hn hd he hgt =>
    have h1 : σ.arrays[ρ.ar a₁]? = some (ρ.ainst ai₁) := hR.array_code hc (by simp) ha₁
    have h2 : σ.arrays[ρ.ar a₂]? = some (ρ.ainst ai₂) := hR.array_code hc (by simp) ha₂
    refine .same hR hf (by sub_good hc) ?_
    simpa using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayCopyGt (s := σ) (f := ρ.frame f) h1 h2
        (by simpa [Ren.ainst] using hl) hn hd he hgt)
  | @arrayInitElemNull s f x y i j n =>
    exact .same hR hf (by simp)
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.arrayInitElemNull (s := σ) (f := ρ.frame f) (x := x) (y := y) (i := i)
          (j := j) (n := n))))
  | @arrayInitElemOob₁ s f x y i j n a ai ha hl =>
    have h1 : σ.arrays[ρ.ar a]? = some (ρ.ainst ai) := hR.array_code hc (by simp) ha
    exact .same hR hf (by simp)
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.arrayInitElemOob₁ (s := σ) (f := ρ.frame f) (x := x) (y := y) (j := j)
          h1 (by simpa [Ren.ainst] using hl))))
  | arrayInitElemOob₂ he => exact nomatch (elem?_none he₀).symm.trans he
  | arrayInitElemZero _ he => exact nomatch (elem?_none he₀).symm.trans he
  | arrayInitElemSucc _ he => exact nomatch (elem?_none he₀).symm.trans he
  | @arrayInitDataNull s f x y i j n =>
    exact .same hR hf (by simp)
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.arrayInitDataNull (s := σ) (f := ρ.frame f) (x := x) (y := y) (i := i)
          (j := j) (n := n))))
  | @arrayInitDataOob₁ s f x y i j n a ai ha hl =>
    have h1 : σ.arrays[ρ.ar a]? = some (ρ.ainst ai) := hR.array_code hc (by simp) ha
    exact .same hR hf (by simp)
      (by simpa using (Step.aggregate (P := P) (host := noHost)
        (AggregateStep.arrayInitDataOob₁ (s := σ) (f := ρ.frame f) (x := x) (y := y) (j := j)
          h1 (by simpa [Ren.ainst] using hl))))
  | arrayInitDataOob₂ _ _ hdat => exact nomatch (data?_none hd₀).symm.trans hdat
  | arrayInitDataZero _ hdat => exact nomatch (data?_none hd₀).symm.trans hdat
  | arrayInitDataNum _ _ _ hdat => exact nomatch (data?_none hd₀).symm.trans hdat

end Silmaril.Proofs.Wasm.Game.Linking.Split
