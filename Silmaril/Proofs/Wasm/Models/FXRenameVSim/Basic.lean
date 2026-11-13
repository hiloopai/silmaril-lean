module

public import Silmaril.Wasm.Models.FXRenameVSim.Defs
public import Silmaril.Wasm.Models.FXRenameV.Thms

/-!
# Exception renaming for `StepFX'`: the renaming on FX code

* the renaming of FX code is a `map` (`rnL_eq_map`) and commutes with the shapes the rules of
  `StepFX'` mention: FX values (`rnL_fvals`), Core values, thrown exceptions, source bodies
  (`rnL_instrs`, the identity), Core code (`rnL_map_core'`) and contexts (`rnCtx_plug`);
* inversions: `rnL n L = P`, for each such shape `P`, gives `L` of the same shape with the pieces
  of `P` renamed pieces of `L` (`rnL_eq_append_iff`, `rnL_eq_fvals_iff`, `rnA_eq_*_iff`,
  `rnL_eq_plug_iff`, …);
* contexts: `rnCtx` keeps the frame at the hole (renamed) and the handled tags;
* continuation stores: `KRn` at a slot, after `set` and after an append.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRenameVSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXRename
open Silmaril.Wasm.Models.FXRenameV Silmaril.Wasm.Models.FXRenameVSim
open Silmaril.Proofs.Wasm.Models.FXRenameSim (rnAdmins_eq_map rnAdmin_eq_toAdmin_iff
  rnAdmins_eq_vals_iff rnAdmins_eq_throwing_iff rnAdmin_eq_plain_iff)

variable {n : Nat}

/-! ## The renaming on FX code -/

@[simp] theorem rnL_nil : rnL n [] = [] := by simp [rnL]

@[simp] theorem rnL_cons (a : AdminFX) (l : List AdminFX) :
    rnL n (a :: l) = rnA n a :: rnL n l := by simp [rnL]

@[simp] theorem rnA_core (a : Admin) : rnA n (.core a) = .core (rnAdmin n a) := by simp [rnA]
@[simp] theorem rnA_fx (i : FXInstr) : rnA n (.fx i) = .fx i := by simp [rnA]
@[simp] theorem rnA_block (bt : BlockType) (b : List InstrFX) :
    rnA n (.block bt b) = .block bt b := by simp [rnA]
@[simp] theorem rnA_loop (bt : BlockType) (b : List InstrFX) :
    rnA n (.loop bt b) = .loop bt b := by simp [rnA]
@[simp] theorem rnA_if (bt : BlockType) (b₁ b₂ : List InstrFX) :
    rnA n (.if_ bt b₁ b₂) = .if_ bt b₁ b₂ := by simp [rnA]
@[simp] theorem rnA_label (m : Nat) (k : List InstrFX) (b : List AdminFX) :
    rnA n (.label m k b) = .label m k (rnL n b) := by simp [rnA]
@[simp] theorem rnA_frame (m : Nat) (f : Frame) (b : List AdminFX) :
    rnA n (.frame m f b) = .frame m (rnFrame n f) (rnL n b) := by simp [rnA]
@[simp] theorem rnA_handler (hs : List HClause) (b : List AdminFX) :
    rnA n (.handler hs b) = .handler hs (rnL n b) := by simp [rnA]
@[simp] theorem rnA_contRef (k : Nat) : rnA n (.contRef k) = .contRef k := by simp [rnA]

theorem rnL_eq_map (l : List AdminFX) : rnL n l = l.map (rnA n) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

@[simp] theorem rnL_append (l l' : List AdminFX) : rnL n (l ++ l') = rnL n l ++ rnL n l' := by
  simp [rnL_eq_map]

@[simp] theorem rnA_fval (v : FVal) : rnA n v.toAdmin = (rnFV n v).toAdmin := by
  cases v with
  | val v => simp [FVal.toAdmin, rnFV]
  | cont k => simp [FVal.toAdmin, rnFV]

@[simp] theorem rnL_fvals (vs : List FVal) : rnL n (fvals vs) = fvals (vs.map (rnFV n)) := by
  simp [rnL_eq_map, fvals]

@[simp] theorem rnFV_liftV (vs : List Val) : (liftV vs).map (rnFV n) = liftV (vs.map (rnVal n)) := by
  simp [liftV, rnFV]

@[simp] theorem rnL_cvals (vs : List Val) : rnL n (cvals vs) = cvals (vs.map (rnVal n)) := by
  rw [← fvals_liftV, rnL_fvals, rnFV_liftV, fvals_liftV]

theorem rnL_map_core' (cs : List Admin) : rnL n (cs.map .core) = (rnAdmins n cs).map .core := by
  simp [rnL_eq_map, rnAdmins_eq_map]

@[simp] theorem rnL_cthrowing (a : Nat) : rnL n (cthrowing a) = cthrowing (rnIdx n a) := by
  simp [cthrowing, throwing]

@[simp] theorem rnA_instr (i : InstrFX) : rnA n i.toAdmin = i.toAdmin := by
  cases i <;> simp [InstrFX.toAdmin]

@[simp] theorem rnL_instrs (b : List InstrFX) : rnL n (b.map InstrFX.toAdmin) = b.map InstrFX.toAdmin := by
  simp [rnL_eq_map]

theorem map_rnFV_length (vs : List FVal) : (vs.map (rnFV n)).length = vs.length := by simp

/-! ## Contexts -/

theorem rnCtx_plug (E : CtxV) (c : List AdminFX) :
    (rnCtx n E).plug (rnL n c) = rnL n (E.plug c) := by
  induction E with
  | hole => rfl
  | seq vs E rest ih => simp [rnCtx, CtxV.plug, ih]
  | label m k E ih => simp [rnCtx, CtxV.plug, ih]
  | frame m f E ih => simp [rnCtx, CtxV.plug, ih]
  | handler hs E ih => simp [rnCtx, CtxV.plug, ih]

theorem rnCtx_frameAt (E : CtxV) (f : Frame) :
    (rnCtx n E).frameAt (rnFrame n f) = rnFrame n (E.frameAt f) := by
  induction E generalizing f with
  | hole => rfl
  | seq vs E rest ih => exact ih f
  | label m k E ih => exact ih f
  | frame m fi E ih => exact ih fi
  | handler hs E ih => exact ih f

theorem rnCtx_handles (E : CtxV) (ta : Nat) : (rnCtx n E).Handles ta ↔ E.Handles ta := by
  induction E with
  | hole => exact Iff.rfl
  | seq vs E rest ih => exact ih
  | label m k E ih => exact ih
  | frame m fi E ih => exact ih
  | handler hs E ih => simp only [rnCtx, CtxV.Handles, ih]

/-! ## Inverting the renaming on FX code -/

@[simp] theorem rnL_eq_nil_iff {L : List AdminFX} : rnL n L = [] ↔ L = [] := by
  cases L <;> simp

theorem rnL_eq_cons_iff {L : List AdminFX} {a : AdminFX} {R : List AdminFX} :
    rnL n L = a :: R ↔ ∃ a₀ L₀, L = a₀ :: L₀ ∧ rnA n a₀ = a ∧ rnL n L₀ = R := by
  cases L <;> simp [and_assoc]

theorem rnL_eq_append_iff {L A B : List AdminFX} :
    rnL n L = A ++ B ↔ ∃ L₁ L₂, L = L₁ ++ L₂ ∧ rnL n L₁ = A ∧ rnL n L₂ = B := by
  simp only [rnL_eq_map, List.map_eq_append_iff]

theorem rnL_eq_singleton_iff {L : List AdminFX} {a : AdminFX} :
    rnL n L = [a] ↔ ∃ a₀, L = [a₀] ∧ rnA n a₀ = a := by
  rw [rnL_eq_cons_iff]
  constructor
  · rintro ⟨a₀, L₀, rfl, ha, hL⟩
    exact ⟨a₀, by rw [rnL_eq_nil_iff.mp hL], ha⟩
  · rintro ⟨a₀, rfl, ha⟩
    exact ⟨a₀, [], rfl, ha, rfl⟩

theorem rnA_eq_core_iff {a : AdminFX} {b : Admin} :
    rnA n a = .core b ↔ ∃ b₀, a = .core b₀ ∧ rnAdmin n b₀ = b := by
  cases a <;> simp

theorem rnA_eq_fx_iff {a : AdminFX} {i : FXInstr} : rnA n a = .fx i ↔ a = .fx i := by
  cases a <;> simp

theorem rnA_eq_block_iff {a : AdminFX} {bt : BlockType} {b : List InstrFX} :
    rnA n a = .block bt b ↔ a = .block bt b := by
  cases a <;> simp

theorem rnA_eq_loop_iff {a : AdminFX} {bt : BlockType} {b : List InstrFX} :
    rnA n a = .loop bt b ↔ a = .loop bt b := by
  cases a <;> simp

theorem rnA_eq_if_iff {a : AdminFX} {bt : BlockType} {b₁ b₂ : List InstrFX} :
    rnA n a = .if_ bt b₁ b₂ ↔ a = .if_ bt b₁ b₂ := by
  cases a <;> simp

theorem rnA_eq_contRef_iff {a : AdminFX} {k : Nat} : rnA n a = .contRef k ↔ a = .contRef k := by
  cases a <;> simp

theorem rnA_eq_label_iff {a : AdminFX} {m : Nat} {k : List InstrFX} {b : List AdminFX} :
    rnA n a = .label m k b ↔ ∃ b₀, a = .label m k b₀ ∧ rnL n b₀ = b := by
  cases a <;> simp [and_assoc, eq_comm]

theorem rnA_eq_frame_iff {a : AdminFX} {m : Nat} {fi : Frame} {b : List AdminFX} :
    rnA n a = .frame m fi b ↔
      ∃ fi₀ b₀, a = .frame m fi₀ b₀ ∧ rnFrame n fi₀ = fi ∧ rnL n b₀ = b := by
  cases a <;> simp [and_assoc, eq_comm]

theorem rnA_eq_handler_iff {a : AdminFX} {hs : List HClause} {b : List AdminFX} :
    rnA n a = .handler hs b ↔ ∃ b₀, a = .handler hs b₀ ∧ rnL n b₀ = b := by
  cases a <;> simp [and_assoc, eq_comm]

theorem rnA_eq_plain_iff {a : AdminFX} {i : Instr} :
    rnA n a = .core (.plain i) ↔ a = .core (.plain i) := by
  rw [rnA_eq_core_iff]
  constructor
  · rintro ⟨b₀, rfl, hb⟩
    rw [rnAdmin_eq_plain_iff.mp hb]
  · rintro rfl
    exact ⟨_, rfl, rfl⟩

theorem rnA_eq_fval_iff {a : AdminFX} {v : FVal} :
    rnA n a = v.toAdmin ↔ ∃ v₀, a = v₀.toAdmin ∧ rnFV n v₀ = v := by
  constructor
  · intro h
    cases v with
    | val v =>
      obtain ⟨b₀, rfl, hb⟩ := rnA_eq_core_iff.mp h
      obtain ⟨v₀, rfl, rfl⟩ := rnAdmin_eq_toAdmin_iff.mp hb
      exact ⟨.val v₀, rfl, rfl⟩
    | cont k => exact ⟨.cont k, rnA_eq_contRef_iff.mp h, rfl⟩
  · rintro ⟨v₀, rfl, rfl⟩; exact rnA_fval v₀

theorem rnL_eq_fvals_iff {L : List AdminFX} {vs : List FVal} :
    rnL n L = fvals vs ↔ ∃ vs₀, L = fvals vs₀ ∧ vs₀.map (rnFV n) = vs := by
  induction vs generalizing L with
  | nil => simp [fvals, rnL_eq_nil_iff]
  | cons v vs ih =>
    rw [show fvals (v :: vs) = v.toAdmin :: fvals vs from rfl, rnL_eq_cons_iff]
    constructor
    · rintro ⟨a₀, L₀, rfl, ha, hL⟩
      obtain ⟨v₀, rfl, rfl⟩ := rnA_eq_fval_iff.mp ha
      obtain ⟨vs₀, rfl, rfl⟩ := ih.mp hL
      exact ⟨v₀ :: vs₀, rfl, rfl⟩
    · rintro ⟨_ | ⟨v₀, vs₀⟩, rfl, hv⟩
      · simp at hv
      · simp only [List.map_cons, List.cons.injEq] at hv
        exact ⟨v₀.toAdmin, fvals vs₀, rfl, by rw [rnA_fval, hv.1], ih.mpr ⟨vs₀, rfl, hv.2⟩⟩

theorem rnL_eq_map_core_iff {L : List AdminFX} {cs : List Admin} :
    rnL n L = cs.map .core ↔ ∃ cs₀, L = cs₀.map .core ∧ rnAdmins n cs₀ = cs := by
  induction cs generalizing L with
  | nil =>
    rw [List.map_nil, rnL_eq_nil_iff]
    constructor
    · rintro rfl; exact ⟨[], rfl, rfl⟩
    · rintro ⟨cs₀, rfl, hcs⟩
      rw [Silmaril.Proofs.Wasm.Models.FXRenameSim.rnAdmins_eq_nil_iff'.mp hcs, List.map_nil]
  | cons b cs ih =>
    rw [List.map_cons, rnL_eq_cons_iff]
    constructor
    · rintro ⟨a₀, L₀, rfl, ha, hL⟩
      obtain ⟨b₀, rfl, rfl⟩ := rnA_eq_core_iff.mp ha
      obtain ⟨cs₀, rfl, rfl⟩ := ih.mp hL
      exact ⟨b₀ :: cs₀, rfl, rfl⟩
    · rintro ⟨_ | ⟨b₀, cs₀⟩, rfl, hb⟩
      · simp at hb
      · simp only [Silmaril.Proofs.Wasm.Models.FXRenameSim.rnAdmins_cons, List.cons.injEq] at hb
        exact ⟨.core b₀, cs₀.map .core, rfl, by rw [rnA_core, hb.1], ih.mpr ⟨cs₀, rfl, hb.2⟩⟩

theorem rnL_eq_cvals_iff {L : List AdminFX} {vs : List Val} :
    rnL n L = cvals vs ↔ ∃ vs₀, L = cvals vs₀ ∧ vs₀.map (rnVal n) = vs := by
  rw [cvals, rnL_eq_map_core_iff]
  constructor
  · rintro ⟨cs₀, rfl, hcs⟩
    obtain ⟨vs₀, rfl, rfl⟩ := rnAdmins_eq_vals_iff.mp hcs
    exact ⟨vs₀, rfl, rfl⟩
  · rintro ⟨vs₀, rfl, rfl⟩
    exact ⟨vals vs₀, rfl, Silmaril.Proofs.Wasm.Models.FXRename.rnAdmins_vals n vs₀⟩

theorem rnL_eq_cthrowing_iff {L : List AdminFX} {b : Nat} :
    rnL n L = cthrowing b ↔ ∃ a, L = cthrowing a ∧ rnIdx n a = b := by
  rw [cthrowing, rnL_eq_map_core_iff]
  constructor
  · rintro ⟨cs₀, rfl, hcs⟩
    obtain ⟨a, rfl, rfl⟩ := rnAdmins_eq_throwing_iff.mp hcs
    exact ⟨a, rfl, rfl⟩
  · rintro ⟨a, rfl, rfl⟩
    exact ⟨throwing a, rfl, by simp [throwing]⟩

theorem rnL_eq_instrs_iff {L : List AdminFX} {b : List InstrFX} :
    rnL n L = b.map InstrFX.toAdmin ↔ L = b.map InstrFX.toAdmin := by
  induction b generalizing L with
  | nil => simp [rnL_eq_nil_iff]
  | cons i b ih =>
    rw [List.map_cons, rnL_eq_cons_iff]
    constructor
    · rintro ⟨a₀, L₀, rfl, ha, hL⟩
      have h₀ : a₀ = i.toAdmin := by
        cases i with
        | core i => exact rnA_eq_plain_iff.mp ha
        | fx i => exact rnA_eq_fx_iff.mp ha
        | block bt b => exact rnA_eq_block_iff.mp ha
        | loop bt b => exact rnA_eq_loop_iff.mp ha
        | if_ bt b₁ b₂ => exact rnA_eq_if_iff.mp ha
      rw [h₀, ih.mp hL]
    · rintro rfl
      exact ⟨i.toAdmin, b.map InstrFX.toAdmin, rfl, rnA_instr i, rnL_instrs b⟩

/-- Renamed code under a context `E'` is renamed code under a source context. -/
def PlugBack (n : Nat) (E' : CtxV) : Prop :=
  ∀ {L X' : List AdminFX}, rnL n L = E'.plug X' →
    ∃ E X, L = E.plug X ∧ rnCtx n E = E' ∧ rnL n X = X'

theorem plugBack_seq {vs : List FVal} {E' : CtxV} {rest : List AdminFX} (ih : PlugBack n E') :
    PlugBack n (.seq vs E' rest) := by
  intro L X' h
  obtain ⟨L₁₂, L₃, rfl, h₁₂, h₃⟩ := rnL_eq_append_iff.mp h
  obtain ⟨L₁, L₂, rfl, h₁, h₂⟩ := rnL_eq_append_iff.mp h₁₂
  obtain ⟨vs₀, rfl, rfl⟩ := rnL_eq_fvals_iff.mp h₁
  obtain ⟨E, X, rfl, rfl, hX⟩ := ih h₂
  exact ⟨.seq vs₀ E L₃, X, rfl, by rw [rnCtx, h₃], hX⟩

theorem plugBack_label {m : Nat} {k : List InstrFX} {E' : CtxV} (ih : PlugBack n E') :
    PlugBack n (.label m k E') := by
  intro L X' h
  obtain ⟨a₀, rfl, ha⟩ := rnL_eq_singleton_iff.mp h
  obtain ⟨b₀, rfl, hb⟩ := rnA_eq_label_iff.mp ha
  obtain ⟨E, X, rfl, rfl, hX⟩ := ih hb
  exact ⟨.label m k E, X, rfl, rfl, hX⟩

theorem plugBack_frame {m : Nat} {fi : Frame} {E' : CtxV} (ih : PlugBack n E') :
    PlugBack n (.frame m fi E') := by
  intro L X' h
  obtain ⟨a₀, rfl, ha⟩ := rnL_eq_singleton_iff.mp h
  obtain ⟨fi₀, b₀, rfl, rfl, hb⟩ := rnA_eq_frame_iff.mp ha
  obtain ⟨E, X, rfl, rfl, hX⟩ := ih hb
  exact ⟨.frame m fi₀ E, X, rfl, rfl, hX⟩

theorem plugBack_handler {hs : List HClause} {E' : CtxV} (ih : PlugBack n E') :
    PlugBack n (.handler hs E') := by
  intro L X' h
  obtain ⟨a₀, rfl, ha⟩ := rnL_eq_singleton_iff.mp h
  obtain ⟨b₀, rfl, hb⟩ := rnA_eq_handler_iff.mp ha
  obtain ⟨E, X, rfl, rfl, hX⟩ := ih hb
  exact ⟨.handler hs E, X, rfl, rfl, hX⟩

theorem plugBack (E' : CtxV) : PlugBack n E' := by
  induction E' with
  | hole => exact fun {L} _ h => ⟨.hole, L, rfl, rfl, h⟩
  | seq vs E' rest ih => exact plugBack_seq ih
  | label m k E' ih => exact plugBack_label ih
  | frame m fi E' ih => exact plugBack_frame ih
  | handler hs E' ih => exact plugBack_handler ih

/-- **Inverting the renaming at a context.** -/
theorem rnL_eq_plug_iff {L : List AdminFX} {E' : CtxV} {X' : List AdminFX} :
    rnL n L = E'.plug X' → ∃ E X, L = E.plug X ∧ rnCtx n E = E' ∧ rnL n X = X' :=
  plugBack E'

/-! ## Continuation stores -/

theorem kRn_length {K₁ K₂ : List (Option ContFX)} (hK : KRn n K₁ K₂) : K₂.length = K₁.length :=
  hK.length_eq.symm

theorem kRn_get {K₁ K₂ : List (Option ContFX)} (hK : KRn n K₁ K₂) (k : Nat) :
    Option.Rel (Option.Rel (ContRn n)) K₁[k]? K₂[k]? := by
  induction hK generalizing k with
  | nil => exact Option.Rel.none
  | cons hab _ ih =>
    cases k with
    | zero => exact Option.Rel.some hab
    | succ k => exact ih k

theorem kRn_some {K₁ K₂ : List (Option ContFX)} (hK : KRn n K₁ K₂) {k : Nat} {C : ContFX}
    (hk : K₁[k]? = some (some C)) : ∃ C₂, K₂[k]? = some (some C₂) ∧ ContRn n C C₂ := by
  have hr : Option.Rel (Option.Rel (ContRn n)) (some (some C)) K₂[k]? := hk ▸ kRn_get hK k
  revert hr
  generalize K₂[k]? = o
  intro hr
  cases hr with
  | some h => cases h with
    | some hC => exact ⟨_, rfl, hC⟩

theorem kRn_none {K₁ K₂ : List (Option ContFX)} (hK : KRn n K₁ K₂) {k : Nat}
    (hk : K₁[k]? = some none) : K₂[k]? = some none := by
  have hr : Option.Rel (Option.Rel (ContRn n)) (some none) K₂[k]? := hk ▸ kRn_get hK k
  revert hr
  generalize K₂[k]? = o
  intro hr
  cases hr with
  | some h => cases h with
    | none => rfl

theorem kRn_some_back {K₁ K₂ : List (Option ContFX)} (hK : KRn n K₁ K₂) {k : Nat} {C₂ : ContFX}
    (hk : K₂[k]? = some (some C₂)) : ∃ C, K₁[k]? = some (some C) ∧ ContRn n C C₂ := by
  have hr : Option.Rel (Option.Rel (ContRn n)) K₁[k]? (some (some C₂)) := hk ▸ kRn_get hK k
  revert hr
  generalize K₁[k]? = o
  intro hr
  cases hr with
  | some h => cases h with
    | some hC => exact ⟨_, rfl, hC⟩

theorem kRn_none_back {K₁ K₂ : List (Option ContFX)} (hK : KRn n K₁ K₂) {k : Nat}
    (hk : K₂[k]? = some none) : K₁[k]? = some none := by
  have hr : Option.Rel (Option.Rel (ContRn n)) K₁[k]? (some none) := hk ▸ kRn_get hK k
  revert hr
  generalize K₁[k]? = o
  intro hr
  cases hr with
  | some h => cases h with
    | none => rfl

theorem kRn_set {K₁ K₂ : List (Option ContFX)} (hK : KRn n K₁ K₂) (k : Nat) :
    KRn n (K₁.set k none) (K₂.set k none) := by
  induction hK generalizing k with
  | nil => exact List.Forall₂.nil
  | cons hab hrest ih =>
    cases k with
    | zero => exact List.Forall₂.cons Option.Rel.none hrest
    | succ k => exact List.Forall₂.cons hab (ih k)

theorem kRn_push {K₁ K₂ : List (Option ContFX)} (hK : KRn n K₁ K₂) {C₁ C₂ : ContFX}
    (hC : ContRn n C₁ C₂) : KRn n (K₁ ++ [some C₁]) (K₂ ++ [some C₂]) :=
  List.rel_append hK (List.Forall₂.cons (Option.Rel.some hC) List.Forall₂.nil)

/-- The context captured from renamed code is the renamed continuation. -/
theorem contRn_ctx (E : CtxV) : ContRn n ⟨E.plug⟩ ⟨(rnCtx n E).plug⟩ :=
  fun c => rnCtx_plug E c

end Silmaril.Proofs.Wasm.Models.FXRenameVSim
