module

public import Silmaril.Wasm.Binaryen.VectorRen
public import Silmaril.Wasm.Validation.Instructions.Properties

@[expose] public section

/-! # Typing under function and global renaming

`Ren.instr ρ` renames the function and global indices of an instruction. If the
target context `{ C with funcs := F, globals := G, refs := R }` agrees with `C`
on every renamed index the code uses (`RenOk`), a profile instruction sequence
typed in `C` has its renaming typed in the target context at the same
instruction type. This is the typing half of RemoveUnusedModuleElements
(`Pass/RUME.lean`), where `F` and `G` are the kept functions and globals.

The profile hypothesis (`instrInProfile`) excludes `ref.func` (whose `REFS`
side condition would need a separate argument), tail calls, exceptions and the
table and reference families. Memory and stack-only vector instructions
retain their indices and typing under function/global renaming.
-/

namespace Silmaril.Wasm.Binaryen

open Validation

/-- The target context agrees with `C` on the renamed indices satisfying `kf`/`kg`. -/
structure RenOk (ρ : Ren) (kf kg : Nat → Prop) (C : Context) (F : List DefType)
    (G : List CGlobalType) : Prop where
  funcs : ∀ x : FuncIdx, kf x.toNat → ∀ d, C.funcs[x.toNat]? = some d →
    F[(ρ.funcIdx x).toNat]? = some d
  globals : ∀ x : GlobalIdx, kg x.toNat → ∀ g, C.globals[x.toNat]? = some g →
    G[(ρ.globalIdx x).toNat]? = some g

namespace RenTyping

variable {ρ : Ren} {kf kg : Nat → Prop} {C : Context} {F : List DefType}
  {G : List CGlobalType} {R : List Nat}

theorem renOk_withLabel (h : RenOk ρ kf kg C F G) (ts : List CValType) :
    RenOk ρ kf kg (C.withLabel ts) F G := ⟨h.funcs, h.globals⟩

theorem initLocals_funcs (C : Context) (xs : List Nat) : (C.initLocals xs).funcs = C.funcs := by
  obtain ⟨L, hL, -⟩ := C.initLocals_spec xs; rw [hL]

theorem initLocals_globals (C : Context) (xs : List Nat) :
    (C.initLocals xs).globals = C.globals := by
  obtain ⟨L, hL, -⟩ := C.initLocals_spec xs; rw [hL]

theorem renOk_initLocals (h : RenOk ρ kf kg C F G) (xs : List Nat) :
    RenOk ρ kf kg (C.initLocals xs) F G := by
  refine ⟨fun x hx d hd => h.funcs x hx d ?_, fun x hx g hg => h.globals x hx g ?_⟩
  · rwa [initLocals_funcs] at hd
  · rwa [initLocals_globals] at hg

theorem initLocals_ren (C : Context) (F : List DefType) (G : List CGlobalType) (R : List Nat)
    (xs : List Nat) :
    ({ C with funcs := F, globals := G, refs := R } : Context).initLocals xs =
      { C.initLocals xs with funcs := F, globals := G, refs := R } := by
  obtain ⟨L₁, h₁, hy₁⟩ :=
    ({ C with funcs := F, globals := G, refs := R } : Context).initLocals_spec xs
  obtain ⟨L₂, h₂, hy₂⟩ := C.initLocals_spec xs
  rw [h₁, h₂]
  have : L₁ = L₂ := List.ext_getElem? fun y => by rw [hy₁ y, hy₂ y]
  rw [this]

/-! ## Unfolding the traversals on structured instructions -/

theorem instrInProfile_block {bt : BlockType} {body : List Instr}
    (h : instrInProfile (.block bt body)) : ∀ i ∈ body, instrInProfile i := by
  unfold instrInProfile at h
  exact fun i hi => h.2 ⟨i, hi⟩ (List.mem_attach _ _)

theorem instrInProfile_loop {bt : BlockType} {body : List Instr}
    (h : instrInProfile (.loop bt body)) : ∀ i ∈ body, instrInProfile i := by
  unfold instrInProfile at h
  exact fun i hi => h.2 ⟨i, hi⟩ (List.mem_attach _ _)

theorem instrInProfile_if {bt : BlockType} {b₁ b₂ : List Instr}
    (h : instrInProfile (.if_ bt b₁ b₂)) :
    (∀ i ∈ b₁, instrInProfile i) ∧ ∀ i ∈ b₂, instrInProfile i := by
  unfold instrInProfile at h
  exact ⟨fun i hi => h.2.1 ⟨i, hi⟩ (List.mem_attach _ _),
    fun i hi => h.2.2 ⟨i, hi⟩ (List.mem_attach _ _)⟩

theorem freeFuncs_block {bt : BlockType} {body : List Instr} {x : Nat}
    (hx : x ∈ Expr.freeFuncs body) : x ∈ Instr.freeFuncs (.block bt body) := by
  rw [Instr.freeFuncs]
  simp only [Expr.freeFuncs, List.mem_flatMap] at hx ⊢
  obtain ⟨i, hi, hx⟩ := hx
  exact ⟨⟨i, hi⟩, List.mem_attach _ _, hx⟩

theorem freeFuncs_loop {bt : BlockType} {body : List Instr} {x : Nat}
    (hx : x ∈ Expr.freeFuncs body) : x ∈ Instr.freeFuncs (.loop bt body) := by
  rw [Instr.freeFuncs]
  simp only [Expr.freeFuncs, List.mem_flatMap] at hx ⊢
  obtain ⟨i, hi, hx⟩ := hx
  exact ⟨⟨i, hi⟩, List.mem_attach _ _, hx⟩

theorem freeFuncs_if₁ {bt : BlockType} {b₁ b₂ : List Instr} {x : Nat}
    (hx : x ∈ Expr.freeFuncs b₁) : x ∈ Instr.freeFuncs (.if_ bt b₁ b₂) := by
  rw [Instr.freeFuncs]
  simp only [Expr.freeFuncs, List.mem_flatMap] at hx
  simp only [List.mem_append, List.mem_flatMap]
  obtain ⟨i, hi, hx⟩ := hx
  exact Or.inl ⟨⟨i, hi⟩, List.mem_attach _ _, hx⟩

theorem freeFuncs_if₂ {bt : BlockType} {b₁ b₂ : List Instr} {x : Nat}
    (hx : x ∈ Expr.freeFuncs b₂) : x ∈ Instr.freeFuncs (.if_ bt b₁ b₂) := by
  rw [Instr.freeFuncs]
  simp only [Expr.freeFuncs, List.mem_flatMap] at hx
  simp only [List.mem_append, List.mem_flatMap]
  obtain ⟨i, hi, hx⟩ := hx
  exact Or.inr ⟨⟨i, hi⟩, List.mem_attach _ _, hx⟩

theorem globals_block {bt : BlockType} {body : List Instr} {x : Nat}
    (hx : x ∈ instrsGlobals body) : x ∈ instrGlobals (.block bt body) := by
  rw [instrGlobals]
  simp only [instrsGlobals, List.mem_flatMap] at hx ⊢
  obtain ⟨i, hi, hx⟩ := hx
  exact ⟨⟨i, hi⟩, List.mem_attach _ _, hx⟩

theorem globals_loop {bt : BlockType} {body : List Instr} {x : Nat}
    (hx : x ∈ instrsGlobals body) : x ∈ instrGlobals (.loop bt body) := by
  rw [instrGlobals]
  simp only [instrsGlobals, List.mem_flatMap] at hx ⊢
  obtain ⟨i, hi, hx⟩ := hx
  exact ⟨⟨i, hi⟩, List.mem_attach _ _, hx⟩

theorem globals_if₁ {bt : BlockType} {b₁ b₂ : List Instr} {x : Nat}
    (hx : x ∈ instrsGlobals b₁) : x ∈ instrGlobals (.if_ bt b₁ b₂) := by
  rw [instrGlobals]
  simp only [instrsGlobals, List.mem_flatMap] at hx
  simp only [List.mem_append, List.mem_flatMap]
  obtain ⟨i, hi, hx⟩ := hx
  exact Or.inl ⟨⟨i, hi⟩, List.mem_attach _ _, hx⟩

theorem globals_if₂ {bt : BlockType} {b₁ b₂ : List Instr} {x : Nat}
    (hx : x ∈ instrsGlobals b₂) : x ∈ instrGlobals (.if_ bt b₁ b₂) := by
  rw [instrGlobals]
  simp only [instrsGlobals, List.mem_flatMap] at hx
  simp only [List.mem_append, List.mem_flatMap]
  obtain ⟨i, hi, hx⟩ := hx
  exact Or.inr ⟨⟨i, hi⟩, List.mem_attach _ _, hx⟩

theorem ren_block (ρ : Ren) (bt : BlockType) (body : List Instr) :
    ρ.instr (.block bt body) = .block bt (ρ.instrs body) := by
  rw [Ren.instr]; simp [Ren.instrs]

theorem ren_loop (ρ : Ren) (bt : BlockType) (body : List Instr) :
    ρ.instr (.loop bt body) = .loop bt (ρ.instrs body) := by
  rw [Ren.instr]; simp [Ren.instrs]

theorem ren_if (ρ : Ren) (bt : BlockType) (b₁ b₂ : List Instr) :
    ρ.instr (.if_ bt b₁ b₂) = .if_ bt (ρ.instrs b₁) (ρ.instrs b₂) := by
  rw [Ren.instr]; simp [Ren.instrs]

theorem ren_call (ρ : Ren) (x : FuncIdx) : ρ.instr (.call x) = .call (ρ.funcIdx x) := by
  rw [Ren.instr]

theorem ren_refFunc (ρ : Ren) (x : FuncIdx) : ρ.instr (.refFunc x) = .refFunc (ρ.funcIdx x) := by
  rw [Ren.instr]

theorem ren_globalGet (ρ : Ren) (x : GlobalIdx) :
    ρ.instr (.globalGet x) = .globalGet (ρ.globalIdx x) := by
  rw [Ren.instr]

theorem ren_globalSet (ρ : Ren) (x : GlobalIdx) :
    ρ.instr (.globalSet x) = .globalSet (ρ.globalIdx x) := by
  rw [Ren.instr]

/-- Instructions that carry no function or global index and no body are fixed. -/
theorem ren_fixed (ρ : Ren) {i : Instr} (hs : structuredInstr i = false)
    (hf : Instr.freeFuncs i = []) (hg : instrGlobals i = []) : ρ.instr i = i := by
  unfold Ren.instr
  split <;> simp_all [structuredInstr, Instr.freeFuncs, instrGlobals]

/-- A profile instruction outside the structured forms satisfies `profileInstr`. -/
theorem profileInstr_of {i : Instr} (h : instrInProfile i) (hs : structuredInstr i = false) :
    profileInstr i = true := by
  unfold instrInProfile at h
  split at h <;> simp_all [structuredInstr]

/-! ## The families -/

section Families

variable {i : Instr} {it : InstrType}

theorem parametric_ren (h : ParametricInstrOk C i it) :
    ParametricInstrOk { C with funcs := F, globals := G, refs := R } i it ∧ ρ.instr i = i := by
  cases h <;> exact ⟨by constructor <;> assumption, ren_fixed ρ rfl (by simp [Instr.freeFuncs])
    (by simp [instrGlobals])⟩

theorem numeric_ren (h : NumericInstrOk C i it) :
    NumericInstrOk { C with funcs := F, globals := G, refs := R } i it ∧ ρ.instr i = i := by
  cases h <;> exact ⟨by constructor <;> assumption, ren_fixed ρ rfl (by simp [Instr.freeFuncs])
    (by simp [instrGlobals])⟩

-- FLAG(statement-change): vector_absurd is false after stack-only SIMD admission.
-- Replaced by vector_ren in the leaf VectorRen; see its checked counterexample.

theorem memory_ren (h : MemoryInstrOk C i it) :
    MemoryInstrOk { C with funcs := F, globals := G, refs := R } i it ∧ ρ.instr i = i := by
  cases h <;> exact ⟨by constructor <;> assumption,
    ren_fixed ρ rfl (by simp [Instr.freeFuncs]) (by simp [instrGlobals])⟩

theorem table_absurd (h : TableInstrOk C i it) (hp : instrInProfile i) : False := by
  cases h <;> simpa [profileInstr] using profileInstr_of hp rfl

theorem reference_absurd (h : RefInstrOk C i it) (hp : instrInProfile i) : False := by
  cases h <;> simpa [profileInstr] using profileInstr_of hp rfl

theorem variable_ren (h : VariableInstrOk C i it) (hρ : RenOk ρ kf kg C F G)
    (hg : ∀ x ∈ instrGlobals i, kg x) :
    VariableInstrOk { C with funcs := F, globals := G, refs := R } (ρ.instr i) it := by
  cases h with
  | localGet h =>
    rw [ren_fixed ρ rfl (by simp [Instr.freeFuncs]) (by simp [instrGlobals])]
    exact .localGet h
  | localSet h =>
    rw [ren_fixed ρ rfl (by simp [Instr.freeFuncs]) (by simp [instrGlobals])]
    exact .localSet h
  | localTee h =>
    rw [ren_fixed ρ rfl (by simp [Instr.freeFuncs]) (by simp [instrGlobals])]
    exact .localTee h
  | @globalGet x _ _ h =>
    rw [ren_globalGet]
    exact .globalGet (hρ.globals x (hg _ (by simp [instrGlobals])) _ h)
  | @globalSet x _ h =>
    rw [ren_globalSet]
    exact .globalSet (hρ.globals x (hg _ (by simp [instrGlobals])) _ h)

end Families

/-- Renaming preserves constant instructions. -/
theorem instrConst_ren {i : Instr} (h : InstrConst C i) (hρ : RenOk ρ kf kg C F G)
    (hg : ∀ x ∈ instrGlobals i, kg x) :
    InstrConst { C with funcs := F, globals := G, refs := R } (ρ.instr i) := by
  cases h with
  | refFunc x => rw [ren_refFunc]; exact .refFunc _
  | @globalGet x t h =>
    rw [ren_globalGet]
    exact .globalGet (hρ.globals x (hg _ (by simp [instrGlobals])) _ h)
  | _ =>
    rw [ren_fixed ρ rfl (by simp [Instr.freeFuncs]) (by simp [instrGlobals])]
    constructor <;> assumption

theorem blockType_ren {bt : BlockType} {t₁ t₂ : List CValType} (h : BlockTypeOk C bt t₁ t₂) :
    BlockTypeOk { C with funcs := F, globals := G, refs := R } bt t₁ t₂ := by
  cases h <;> constructor <;> assumption

/-- Instructions outside the profile carry no typing obligation here. -/
theorem absurd_of_not_profile {i : Instr} (hp : instrInProfile i) (hs : structuredInstr i = false)
    (hn : profileInstr i = false) : False := by
  have := profileInstr_of hp hs
  simp_all

mutual

/-- **Renaming preserves instruction typing** (profile instructions). -/
theorem instrOk_ren {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it)
    {F : List DefType} {G : List CGlobalType} (R : List Nat) (hρ : RenOk ρ kf kg C F G)
    (hf : ∀ x ∈ Instr.freeFuncs i, kf x) (hg : ∀ x ∈ instrGlobals i, kg x)
    (hp : instrInProfile i) :
    InstrOk { C with funcs := F, globals := G, refs := R } (ρ.instr i) it :=
  match h with
  | .parametric h => by
    obtain ⟨h', e⟩ := parametric_ren (F := F) (G := G) (R := R) (ρ := ρ) h
    rw [e]; exact .parametric h'
  | .numeric h => by
    obtain ⟨h', e⟩ := numeric_ren (F := F) (G := G) (R := R) (ρ := ρ) h
    rw [e]; exact .numeric h'
  | .vector h => by
    obtain ⟨h', e⟩ := vector_ren (F := F) (G := G) (R := R) (ρ := ρ) h
    rw [e]; exact .vector h'
  | .variable h => .variable (variable_ren h hρ hg)
  | .memory h => by
    obtain ⟨h', e⟩ := memory_ren (F := F) (G := G) (R := R) (ρ := ρ) h
    rw [e]; exact .memory h'
  | .table h => (table_absurd h hp).elim
  | .reference h => (reference_absurd h hp).elim
  | .block hbt hb => by
    rw [ren_block]
    exact .block (blockType_ren hbt)
      (instrsOk_ren hb R (renOk_withLabel hρ _) (fun x hx => hf x (freeFuncs_block hx))
        (fun x hx => hg x (globals_block hx)) (instrInProfile_block hp))
  | .loop hbt hb => by
    rw [ren_loop]
    exact .loop (blockType_ren hbt)
      (instrsOk_ren hb R (renOk_withLabel hρ _) (fun x hx => hf x (freeFuncs_loop hx))
        (fun x hx => hg x (globals_loop hx)) (instrInProfile_loop hp))
  | .if_ hbt h₁ h₂ => by
    rw [ren_if]
    exact .if_ (blockType_ren hbt)
      (instrsOk_ren h₁ R (renOk_withLabel hρ _) (fun x hx => hf x (freeFuncs_if₁ hx))
        (fun x hx => hg x (globals_if₁ hx)) (instrInProfile_if hp).1)
      (instrsOk_ren h₂ R (renOk_withLabel hρ _) (fun x hx => hf x (freeFuncs_if₂ hx))
        (fun x hx => hg x (globals_if₂ hx)) (instrInProfile_if hp).2)
  | .br hl hok => by
    rw [ren_fixed ρ rfl (by simp [Instr.freeFuncs]) (by simp [instrGlobals])]
    exact .br hl hok
  | .brIf hl => by
    rw [ren_fixed ρ rfl (by simp [Instr.freeFuncs]) (by simp [instrGlobals])]
    exact .brIf hl
  | .brTable hls hl' hok => by
    rw [ren_fixed ρ rfl (by simp [Instr.freeFuncs]) (by simp [instrGlobals])]
    exact .brTable hls hl' hok
  | .brOnNull _ _ => (absurd_of_not_profile hp rfl rfl).elim
  | .brOnNonNull _ => (absurd_of_not_profile hp rfl rfl).elim
  | .brOnCast _ _ _ _ _ => (absurd_of_not_profile hp rfl rfl).elim
  | .brOnCastFail _ _ _ _ _ => (absurd_of_not_profile hp rfl rfl).elim
  | @InstrOk.call _ x _ _ _ hfx he => by
    rw [ren_call]
    exact .call (hρ.funcs x (hf _ (by simp [Instr.freeFuncs])) _ hfx) he
  | .callRef _ _ => (absurd_of_not_profile hp rfl rfl).elim
  | .callIndirect _ _ _ _ => (absurd_of_not_profile hp rfl rfl).elim
  | .return_ hret hok => by
    rw [ren_fixed ρ rfl (by simp [Instr.freeFuncs]) (by simp [instrGlobals])]
    exact .return_ hret hok
  | .returnCall _ _ _ _ _ => (absurd_of_not_profile hp rfl rfl).elim
  | .returnCallRef _ _ _ _ _ => (absurd_of_not_profile hp rfl rfl).elim
  | .returnCallIndirect _ _ _ _ _ _ _ => (absurd_of_not_profile hp rfl rfl).elim
  | .throw _ _ _ => (absurd_of_not_profile hp rfl rfl).elim
  | .throwRef _ => (absurd_of_not_profile hp rfl rfl).elim
  | .tryTable _ _ _ => by
    unfold instrInProfile at hp
    simp [profileInstr] at hp

/-- **Renaming preserves instruction-sequence typing** (profile instructions). -/
theorem instrsOk_ren {C : Context} {is : List Instr} {it : InstrType} (h : InstrsOk C is it)
    {F : List DefType} {G : List CGlobalType} (R : List Nat) (hρ : RenOk ρ kf kg C F G)
    (hf : ∀ x ∈ Expr.freeFuncs is, kf x) (hg : ∀ x ∈ instrsGlobals is, kg x)
    (hp : ∀ i ∈ is, instrInProfile i) :
    InstrsOk { C with funcs := F, globals := G, refs := R } (ρ.instrs is) it :=
  match h with
  | .nil => .nil
  | .instr hi => .instr (instrOk_ren hi R hρ
      (fun x hx => hf x (by simp [Expr.freeFuncs, hx]))
      (fun x hx => hg x (by simp [instrsGlobals, hx])) (hp _ (List.mem_singleton_self _)))
  | .seq (xs₁ := xs₁) h₁ hx h₂ => by
    simp only [Ren.instrs, List.map_append]
    refine .seq (instrsOk_ren h₁ R hρ (fun x hx => hf x ?_) (fun x hx => hg x ?_)
      (fun i hi => hp i (List.mem_append_left _ hi))) hx ?_
    · simp only [Expr.freeFuncs, List.flatMap_append, List.mem_append] at hx ⊢; exact .inl hx
    · simp only [instrsGlobals, List.flatMap_append, List.mem_append] at hx ⊢; exact .inl hx
    · rw [initLocals_ren]
      exact instrsOk_ren h₂ R (renOk_initLocals hρ xs₁)
        (fun x hx => hf x (by
          simp only [Expr.freeFuncs, List.flatMap_append, List.mem_append] at hx ⊢
          exact .inr hx))
        (fun x hx => hg x (by
          simp only [instrsGlobals, List.flatMap_append, List.mem_append] at hx ⊢
          exact .inr hx))
        (fun i hi => hp i (List.mem_append_right _ hi))
  | .cons (xs₁ := xs₁) hi hx hs => by
    simp only [Ren.instrs, List.map_cons]
    refine .cons (instrOk_ren hi R hρ (fun x hx => hf x ?_) (fun x hx => hg x ?_)
      (hp _ List.mem_cons_self)) hx ?_
    · simp only [Expr.freeFuncs, List.flatMap_cons, List.mem_append]; exact .inl hx
    · simp only [instrsGlobals, List.flatMap_cons, List.mem_append]; exact .inl hx
    · rw [initLocals_ren]
      exact instrsOk_ren hs R (renOk_initLocals hρ xs₁)
        (fun x hx => hf x (by
          simp only [Expr.freeFuncs, List.flatMap_cons, List.mem_append]
          exact .inr hx))
        (fun x hx => hg x (by
          simp only [instrsGlobals, List.flatMap_cons, List.mem_append]
          exact .inr hx))
        (fun i hi => hp i (List.mem_cons_of_mem _ hi))
  | .sub h hs hok => .sub (instrsOk_ren h R hρ hf hg hp) hs hok
  | .frame h hok => .frame (instrsOk_ren h R hρ hf hg hp) hok

end

end RenTyping

end Silmaril.Wasm.Binaryen
