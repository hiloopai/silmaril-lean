module

public import Silmaril.Proofs.Wasm.Models.V2Core.ReflAtom2

/-!
# Reflecting Core typings of 2.0 instruction sequences

* the branch and call instructions (`r_br`, `r_brTable`, `r_call`, `r_callIndirect`, …);
* blocks, loops and conditionals, given the reflection of their bodies (`r_block`, `r_loop`,
  `r_if`);
* `seq_of`: if every instruction of a 2.0 sequence reflects (`GoodI`), so does the sequence
  (`Good`). This is an induction on the Core derivation: `Instrs_ok/seq` splits the image, and
  `Instrs_ok/sub` and `Instrs_ok/frame` read back through `ers_sub` (Core derivations in a
  well-formed context have well-formed types, `InstrsOk.regular`);
* **`goodI`**: every 2.0 instruction reflects, by well-founded recursion on its size, and
  **`instrs_refl`**: every Core typing of the image of a 2.0 sequence in an image context reads
  back as a 2.0 typing.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core.Reflect

open Silmaril.Wasm.V2.Validation (globalToC tableToC resultToC liftResult)
open Silmaril.Wasm.Validation (TypeCtx TyOk)

variable {C : VCtx} {D : KCtx} {it : Silmaril.Wasm.Validation.InstrType}

/-! ## Branches and calls -/

theorem ers_append (Δ : TypeCtx) (a b : List KVal) : ers Δ (a ++ b) = ers Δ a ++ ers Δ b :=
  List.map_append

theorem r_br (hR : Rel C D) {l} (h : KOk D (.br l) it) : VSeq C [.br l] (erT D.toTypeCtx it) := by
  cases h
  case br =>
    rename_i ts t₁ t₂ hok hl
    obtain ⟨us, hus, rfl⟩ := hR.labels_get hl
    simp only [erT, ers_append, ers_resultToC]
    exact vone (.br hus)
  all_goals (rename_i h; cases h)

theorem r_brIf (hR : Rel C D) {l} (h : KOk D (.brIf l) it) :
    VSeq C [.brIf l] (erT D.toTypeCtx it) := by
  cases h
  case brIf =>
    rename_i ts hl
    obtain ⟨us, hus, rfl⟩ := hR.labels_get hl
    simp only [erT, ers_append, ers_resultToC]
    exact vone (.brIf hus)
  all_goals (rename_i h; cases h)

/-- A `br_table` target reads back. -/
theorem brTable_target (hR : Rel C D) {ts lt : List KVal} {l : Nat}
    (hts : Silmaril.Wasm.Validation.ResultOk D.toTypeCtx ts) (hl : D.labels[l]? = some lt)
    (hs : Silmaril.Wasm.Validation.ResultSub D.toTypeCtx ts lt) :
    ∃ lt', C.labels[l]? = some lt' ∧
      Silmaril.Wasm.V2.Validation.CResultType.Sub (ers D.toTypeCtx ts) lt' := by
  obtain ⟨us, hus, rfl⟩ := hR.labels_get hl
  have hsub := ers_sub hR.typesOk hR.recs hts (hR.wf.label hl) hs
  rw [ers_resultToC] at hsub
  exact ⟨us, hus, hsub⟩

theorem r_brTable (hR : Rel C D) {ls l'} (h : KOk D (.brTable ls l') it) :
    VSeq C [.brTable ls l'] (erT D.toTypeCtx it) := by
  cases h
  case brTable =>
    rename_i ts t₁ t₂ hok hls hl'
    have hts : Silmaril.Wasm.Validation.ResultOk D.toTypeCtx ts :=
      fun t ht => hok.1 t (by simp [ht])
    have hls' : ∀ l ∈ ls, ∃ lt', C.labels[l.toNat]? = some lt' ∧
        Silmaril.Wasm.V2.Validation.CResultType.Sub (ers D.toTypeCtx ts) lt' := fun l hl =>
      let ⟨_, hlt, hs⟩ := hls l hl
      brTable_target hR hts hlt hs
    have hl'' : ∃ lt', C.labels[l'.toNat]? = some lt' ∧
        Silmaril.Wasm.V2.Validation.CResultType.Sub (ers D.toTypeCtx ts) lt' :=
      let ⟨_, hlt, hs⟩ := hl'
      brTable_target hR hts hlt hs
    simp only [erT, ers_append]
    exact vone (.brTable hls' hl'')
  all_goals (rename_i h; cases h)

theorem r_return (hR : Rel C D) (h : KOk D .return_ it) :
    VSeq C [.return_] (erT D.toTypeCtx it) := by
  cases h
  case return_ =>
    rename_i ts t₁ t₂ hr hok
    obtain ⟨us, hus, rfl⟩ := hR.return_get hr
    simp only [erT, ers_append, ers_resultToC]
    exact vone (.return_ hus)
  all_goals (rename_i h; cases h)

theorem r_call (hR : Rel C D) {x} (h : KOk D (.call x) it) :
    VSeq C [.call x] (erT D.toTypeCtx it) := by
  cases h
  case call =>
    rename_i d ps rs he hf
    obtain ⟨ft, hft, rfl⟩ := hR.funcs_get hf
    obtain ⟨hp, hr⟩ := expand_toDefType_inv he
    simp only [erT, hp, hr, ers_map_toC]
    exact vone (.call hft)
  all_goals (rename_i h; cases h)

theorem r_callIndirect (hR : Rel C D) {x y} (h : KOk D (.callIndirect x y) it) :
    VSeq C [.callIndirect x y] (erT D.toTypeCtx it) := by
  cases h
  case callIndirect =>
    rename_i a l rt d ps rs he hs ht hd
    obtain ⟨tt, htt, rfl, rfl⟩ := table_get hR ht
    have hrt : tt.element = .funcref := refToC_sub hR (r' := .funcref) hs
    obtain ⟨ft, hft, rfl⟩ := hR.types_get hd
    obtain ⟨hp, hr⟩ := expand_toDefType_inv he
    simp only [erT, ers_append, hp, hr, ers_map_toC]
    exact vone (.callIndirect htt hrt hft)
  all_goals (rename_i h; cases h)

/-! ## Expression images -/

theorem toCore_nil_inv {is : List Silmaril.Wasm.V2.Instr}
    (h : Silmaril.Wasm.V2.Expr.toCore is = some []) : is = [] := by
  cases is with
  | nil => rfl
  | cons i is =>
    simp only [Silmaril.Wasm.V2.Expr.toCore, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, e⟩ := h
    cases e

theorem toCore_cons_inv {is : List Silmaril.Wasm.V2.Instr} {c : Silmaril.Wasm.Instr}
    {l : List Silmaril.Wasm.Instr} (h : Silmaril.Wasm.V2.Expr.toCore is = some (c :: l)) :
    ∃ i is', is = i :: is' ∧ Silmaril.Wasm.V2.Instr.toCore i = some c ∧
      Silmaril.Wasm.V2.Expr.toCore is' = some l := by
  cases is with
  | nil => cases h
  | cons i is =>
    simp only [Silmaril.Wasm.V2.Expr.toCore, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨c', hc', l', hl', e⟩ := h
    obtain ⟨rfl, rfl⟩ := List.cons.inj e
    exact ⟨i, is, rfl, hc', hl'⟩

theorem toCore_append_inv : ∀ {is : List Silmaril.Wasm.V2.Instr} {l₁ l₂ : List Silmaril.Wasm.Instr},
    Silmaril.Wasm.V2.Expr.toCore is = some (l₁ ++ l₂) →
      ∃ is₁ is₂, is = is₁ ++ is₂ ∧ Silmaril.Wasm.V2.Expr.toCore is₁ = some l₁ ∧
        Silmaril.Wasm.V2.Expr.toCore is₂ = some l₂
  | is, [], l₂, h => ⟨[], is, rfl, rfl, h⟩
  | is, c :: l₁, l₂, h => by
    obtain ⟨i, is', rfl, hc, hl⟩ := toCore_cons_inv h
    obtain ⟨is₁, is₂, rfl, h₁, h₂⟩ := toCore_append_inv hl
    exact ⟨i :: is₁, is₂, rfl, by simp [Silmaril.Wasm.V2.Expr.toCore, hc, h₁], h₂⟩

/-! ## Sequences -/

/-- Every Core typing of the image of `i`, in an image context, reads back. -/
abbrev GoodI (i : Silmaril.Wasm.V2.Instr) : Prop :=
  ∀ {C : VCtx} {D : KCtx} {c : Silmaril.Wasm.Instr} {it : Silmaril.Wasm.Validation.InstrType},
    Rel C D → Silmaril.Wasm.V2.Instr.toCore i = some c → KOk D c it →
      VSeq C [i] (erT D.toTypeCtx it)

/-- Every Core typing of the image of `is`, in an image context, reads back. -/
abbrev Good (is : List Silmaril.Wasm.V2.Instr) : Prop :=
  ∀ {C : VCtx} {D : KCtx} {l : List Silmaril.Wasm.Instr} {it : Silmaril.Wasm.Validation.InstrType},
    Rel C D → Silmaril.Wasm.V2.Expr.toCore is = some l →
      Silmaril.Wasm.Validation.InstrsOk D l it → VSeq C is (erT D.toTypeCtx it)

/-- `Instrs_ok/sub` reads back. -/
theorem sub_er (hR : Rel C D) {is : List Silmaril.Wasm.V2.Instr}
    {it it' : Silmaril.Wasm.Validation.InstrType} (hv : VSeq C is (erT D.toTypeCtx it))
    (hok : Silmaril.Wasm.Validation.InstrTypeOk D it)
    (hok' : Silmaril.Wasm.Validation.InstrTypeOk D it')
    (hs : Silmaril.Wasm.Validation.InstrTypeSub D it it') : VSeq C is (erT D.toTypeCtx it') :=
  .sub hv ⟨ers_sub hR.typesOk hR.recs hok'.1 hok.1 hs.1,
    ers_sub hR.typesOk hR.recs hok.2.1 hok'.2.1 hs.2.1⟩

/-- The motive of `seq_of`. -/
abbrev SeqMotive (D : KCtx) (l : List Silmaril.Wasm.Instr) (it : Silmaril.Wasm.Validation.InstrType) :
    Prop :=
  ∀ {C : VCtx} {is : List Silmaril.Wasm.V2.Instr}, (∀ i ∈ is, GoodI i) → Rel C D →
    Silmaril.Wasm.V2.Expr.toCore is = some l → VSeq C is (erT D.toTypeCtx it)

theorem seq_nil : SeqMotive D [] (.plain [] []) := fun _ _ hc => by
  obtain rfl := toCore_nil_inv hc
  exact .empty

theorem seq_instr {c : Silmaril.Wasm.Instr} (h : KOk D c it) : SeqMotive D [c] it :=
  fun hg hR hc => by
    obtain ⟨i, is', rfl, hi, hnil⟩ := toCore_cons_inv hc
    obtain rfl := toCore_nil_inv hnil
    exact hg i (by simp) hR hi h

theorem seq_append {l₁ l₂ : List Silmaril.Wasm.Instr} {t₁ t₂ t₃ : List KVal} {xs₁ xs₂ : List Nat}
    (ih₁ : SeqMotive D l₁ ⟨t₁, xs₁, t₂⟩) (ih₂ : SeqMotive (D.initLocals xs₁) l₂ ⟨t₂, xs₂, t₃⟩) :
    SeqMotive D (l₁ ++ l₂) ⟨t₁, xs₁ ++ xs₂, t₃⟩ := fun hg hR hc => by
  obtain ⟨is₁, is₂, rfl, h₁, h₂⟩ := toCore_append_inv hc
  have v₁ : VSeq _ is₁ (erT D.toTypeCtx ⟨t₁, xs₁, t₂⟩) :=
    ih₁ (fun i hi => hg i (List.mem_append_left _ hi)) hR h₁
  have v₂ : VSeq _ is₂ (erT (D.initLocals xs₁).toTypeCtx ⟨t₂, xs₂, t₃⟩) :=
    ih₂ (fun i hi => hg i (List.mem_append_right _ hi)) (hR.initLocals xs₁) h₂
  rw [Silmaril.Wasm.Validation.Context.initLocals_toTypeCtx] at v₂
  exact .seq v₁ v₂

theorem seq_frame {l : List Silmaril.Wasm.Instr} {ts t₁ t₂ : List KVal} {xs : List Nat}
    (ih : SeqMotive D l ⟨t₁, xs, t₂⟩) : SeqMotive D l ⟨ts ++ t₁, xs, ts ++ t₂⟩ :=
  fun hg hR hc => by
    have v : VSeq _ _ (erT D.toTypeCtx ⟨t₁, xs, t₂⟩) := ih hg hR hc
    simp only [erT, ers_append]
    exact .frame v

/-- **Sequences reflect when their instructions do.** -/
theorem seq_of {D : KCtx} {l : List Silmaril.Wasm.Instr} {it : Silmaril.Wasm.Validation.InstrType}
    (h : Silmaril.Wasm.Validation.InstrsOk D l it) : SeqMotive D l it := by
  induction h using Silmaril.Wasm.Validation.InstrsOk.ind with
  | nil => exact seq_nil
  | instr h => exact seq_instr h
  | seq _ _ _ ih₁ ih₂ => exact seq_append ih₁ ih₂
  | cons hi _ _ ih => exact seq_append (seq_instr hi) ih
  | sub h hs hok ih =>
    exact fun hg hR hc => sub_er hR (ih hg hR hc) (h.regular hR.wf) hok hs
  | frame _ _ ih => exact seq_frame ih

/-- `Good` from `GoodI`. -/
theorem good_of {is : List Silmaril.Wasm.V2.Instr} (hg : ∀ i ∈ is, GoodI i) : Good is :=
  fun hR hc h => seq_of h hg hR hc

/-! ## Blocks -/

/-- `Blocktype_ok` on the image of a 2.0 block type. -/
theorem blockType_refl (hR : Rel C D) {bt : Silmaril.Wasm.V2.BlockType} {t₁ t₂ : List KVal}
    (h : Silmaril.Wasm.Validation.BlockTypeOk D bt.toCore t₁ t₂) :
    ∃ u₁ u₂ : List Silmaril.Wasm.V2.ValType,
      t₁ = u₁.map Silmaril.Wasm.V2.ValType.toC ∧ t₂ = u₂.map Silmaril.Wasm.V2.ValType.toC ∧
      Silmaril.Wasm.V2.Validation.BlockTypeOk C bt ⟨liftResult u₁, liftResult u₂⟩ := by
  match bt, h with
  | .result none, .empty => exact ⟨[], [], rfl, rfl, .result none⟩
  | .result (some t), .value _ =>
    refine ⟨[], [t], rfl, ?_, .result (some t)⟩
    simp [Silmaril.Wasm.V2.Validation.closeVal_toCore]
  | .typeIdx x, .typeIdx hd he =>
    obtain ⟨ft, hft, rfl⟩ := hR.types_get hd
    obtain ⟨hp, hr⟩ := expand_toDefType_inv he
    exact ⟨ft.params, ft.results, hp, hr, .typeIdx hft⟩

/-- A body checked under a pushed label reads back. -/
theorem body_refl (hR : Rel C D) {body : List Silmaril.Wasm.V2.Instr} (hg : Good body)
    {lb : List Silmaril.Wasm.V2.ValType} {l : List Silmaril.Wasm.Instr}
    (hc : Silmaril.Wasm.V2.Expr.toCore body = some l) {u₁ u₂ : List Silmaril.Wasm.V2.ValType}
    {xs : List Nat}
    (h : Silmaril.Wasm.Validation.InstrsOk (D.withLabel (lb.map Silmaril.Wasm.V2.ValType.toC)) l
      ⟨u₁.map Silmaril.Wasm.V2.ValType.toC, xs, u₂.map Silmaril.Wasm.V2.ValType.toC⟩) :
    VSeq (C.withLabel (liftResult lb)) body ⟨liftResult u₁, liftResult u₂⟩ := by
  have hR' : Rel (C.withLabel (liftResult lb)) (D.withLabel (lb.map Silmaril.Wasm.V2.ValType.toC)) := by
    have := hR.withLabel (liftResult lb)
    rwa [Silmaril.Wasm.V2.Validation.resultToC_liftResult] at this
  have v := hg hR' hc h
  simpa only [erT, ers_map_toC] using v

theorem r_block (hR : Rel C D) {bt : Silmaril.Wasm.V2.BlockType} {body : List Silmaril.Wasm.V2.Instr}
    (hg : Good body) {l : List Silmaril.Wasm.Instr} (hc : Silmaril.Wasm.V2.Expr.toCore body = some l)
    (h : KOk D (.block bt.toCore l) it) : VSeq C [.block bt body] (erT D.toTypeCtx it) := by
  cases h
  case block =>
    rename_i t₁ t₂ xs hbt hb
    obtain ⟨u₁, u₂, rfl, rfl, hbt'⟩ := blockType_refl hR hbt
    show VSeq C _ ⟨ers _ (u₁.map _), ers _ (u₂.map _)⟩
    rw [ers_map_toC, ers_map_toC]
    exact vone (.block hbt' (body_refl hR hg hc hb))
  all_goals (rename_i h; cases h)

theorem r_loop (hR : Rel C D) {bt : Silmaril.Wasm.V2.BlockType} {body : List Silmaril.Wasm.V2.Instr}
    (hg : Good body) {l : List Silmaril.Wasm.Instr} (hc : Silmaril.Wasm.V2.Expr.toCore body = some l)
    (h : KOk D (.loop bt.toCore l) it) : VSeq C [.loop bt body] (erT D.toTypeCtx it) := by
  cases h
  case loop =>
    rename_i t₁ t₂ xs hbt hb
    obtain ⟨u₁, u₂, rfl, rfl, hbt'⟩ := blockType_refl hR hbt
    show VSeq C _ ⟨ers _ (u₁.map _), ers _ (u₂.map _)⟩
    rw [ers_map_toC, ers_map_toC]
    exact vone (.loop hbt' (body_refl hR hg hc hb))
  all_goals (rename_i h; cases h)

theorem r_if (hR : Rel C D) {bt : Silmaril.Wasm.V2.BlockType} {b₁ b₂ : List Silmaril.Wasm.V2.Instr}
    (hg₁ : Good b₁) (hg₂ : Good b₂) {l₁ l₂ : List Silmaril.Wasm.Instr}
    (hc₁ : Silmaril.Wasm.V2.Expr.toCore b₁ = some l₁)
    (hc₂ : Silmaril.Wasm.V2.Expr.toCore b₂ = some l₂)
    (h : KOk D (.if_ bt.toCore l₁ l₂) it) : VSeq C [.if_ bt b₁ b₂] (erT D.toTypeCtx it) := by
  cases h
  case if_ =>
    rename_i t₁ t₂ xs₁ xs₂ hbt h₁ h₂
    obtain ⟨u₁, u₂, rfl, rfl, hbt'⟩ := blockType_refl hR hbt
    show VSeq C _ ⟨ers _ (u₁.map _ ++ _), ers _ (u₂.map _)⟩
    rw [ers_append, ers_map_toC, ers_map_toC]
    exact vone (.if_ hbt' (body_refl hR hg₁ hc₁ h₁) (body_refl hR hg₂ hc₂ h₂))
  all_goals (rename_i h; cases h)

end Silmaril.Proofs.Wasm.Models.V2Core.Reflect
