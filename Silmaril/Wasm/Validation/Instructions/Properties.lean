module

public import Silmaril.Wasm.Validation.Instructions
public import Silmaril.Wasm.Validation.Subtyping.Properties

@[expose] public section

/-! # Admissible spec rules and inversion for instruction typing

The spec's `Instrs_ok/instr` and `Instrs_ok/seq` rules are constructors
(`InstrsOk.single`, `InstrsOk.append` restate them). Inversion lemmas must
generalise over the `sub` and `frame` constructors; their shape is fixed here so
the soundness work (U8, U19, U20) can build on them.

Inversion needs a well-formed context (`Context.Wf`): in an ill-formed context
a derivation may mention ill-formed types (e.g. a label of an invalid reference
type), while the empty sequence and `Instrs_ok/sub` only ever produce valid
types, so a typed sequence need not split at every point.
-/

namespace Silmaril.Wasm.Validation

/-! ## Local initialisation -/

namespace Context

theorem withLocals_spec (C : Context) (xs : List Nat) (f : Nat → LocalType) :
    ∃ L, C.withLocals xs (xs.map f) = { C with locals := L } ∧
      ∀ y, L[y]? = if y ∈ xs then C.locals[y]?.map (fun _ => f y) else C.locals[y]? := by
  induction xs generalizing C with
  | nil => exact ⟨C.locals, rfl, fun y => by simp⟩
  | cons x xs ih =>
    obtain ⟨L, hL, hy⟩ := ih (C.setLocal x (f x))
    refine ⟨L, ?_, fun y => ?_⟩
    · simp only [List.map_cons, withLocals]
      rw [hL]; rfl
    · rw [hy y]
      simp only [setLocal, List.getElem?_set, List.mem_cons]
      by_cases hyx : y = x
      · subst hyx
        by_cases hlt : y < C.locals.length
        · simp [hlt]
        · simp [hlt]
      · have : x ≠ y := fun h => hyx h.symm
        by_cases hm : y ∈ xs <;> simp [hyx, this, hm]

theorem initLocals_spec (C : Context) (xs : List Nat) :
    ∃ L, C.initLocals xs = { C with locals := L } ∧
      ∀ y, L[y]? = if y ∈ xs then C.locals[y]?.map (fun lt => ⟨.set, lt.type⟩)
        else C.locals[y]? := by
  obtain ⟨L, hL, hy⟩ := C.withLocals_spec xs
    (fun x => ⟨.set, ((C.locals[x]?).map LocalType.type).getD default⟩)
  refine ⟨L, hL, fun y => ?_⟩
  rw [hy y]
  split
  · cases C.locals[y]? <;> simp
  · rfl

theorem initLocals_locals (C : Context) (xs : List Nat) (y : Nat) :
    (C.initLocals xs).locals[y]? = if y ∈ xs then C.locals[y]?.map (fun lt => ⟨.set, lt.type⟩)
      else C.locals[y]? := by
  obtain ⟨L, hL, hy⟩ := C.initLocals_spec xs
  rw [hL]; exact hy y

@[simp] theorem initLocals_toTypeCtx (C : Context) (xs : List Nat) :
    (C.initLocals xs).toTypeCtx = C.toTypeCtx := by
  obtain ⟨L, hL, -⟩ := C.initLocals_spec xs; rw [hL]

@[simp] theorem initLocals_labels (C : Context) (xs : List Nat) :
    (C.initLocals xs).labels = C.labels := by
  obtain ⟨L, hL, -⟩ := C.initLocals_spec xs; rw [hL]

@[simp] theorem initLocals_return (C : Context) (xs : List Nat) :
    (C.initLocals xs).return_ = C.return_ := by
  obtain ⟨L, hL, -⟩ := C.initLocals_spec xs; rw [hL]

@[simp] theorem initLocals_nil (C : Context) : C.initLocals [] = C := rfl

theorem initLocals_eq_locals {C C' : Context} {xs : List Nat}
    (h : ∀ y, C'.locals[y]? = if y ∈ xs then C.locals[y]?.map (fun lt => ⟨.set, lt.type⟩)
      else C.locals[y]?) (hC : C' = { C with locals := C'.locals }) : C.initLocals xs = C' := by
  obtain ⟨L, hL, hy⟩ := C.initLocals_spec xs
  rw [hL, hC]
  have : L = C'.locals := List.ext_getElem? fun y => by rw [hy y, h y]
  rw [this]

theorem initLocals_append (C : Context) (xs ys : List Nat) :
    C.initLocals (xs ++ ys) = (C.initLocals xs).initLocals ys := by
  obtain ⟨L₁, h₁, hy₁⟩ := C.initLocals_spec xs
  obtain ⟨L₂, h₂, hy₂⟩ := (C.initLocals xs).initLocals_spec ys
  rw [h₂, h₁]
  apply initLocals_eq_locals
  · intro y
    simp only
    rw [hy₂ y, h₁]
    simp only [hy₁ y, List.mem_append]
    by_cases hx : y ∈ xs <;> by_cases hy : y ∈ ys <;> simp [hx, hy]
    cases C.locals[y]? <;> rfl
  · rfl

theorem initLocals_of_set {C : Context} {xs : List Nat}
    (h : ∀ x ∈ xs, ∃ t, C.locals[x]? = some ⟨.set, t⟩) : C.initLocals xs = C := by
  apply initLocals_eq_locals _ rfl
  intro y
  split
  · next hy =>
    obtain ⟨t, ht⟩ := h y hy
    simp [ht]
  · rfl

theorem initLocals_isSome {C : Context} {xs : List Nat} {y : Nat} :
    ((C.initLocals xs).locals[y]?).isSome = (C.locals[y]?).isSome := by
  rw [initLocals_locals]; split <;> simp

theorem initLocals_exists {C : Context} {xs : List Nat} {y : Nat} :
    (∃ lt, (C.initLocals xs).locals[y]? = some lt) ↔ ∃ lt, C.locals[y]? = some lt := by
  simp only [← Option.isSome_iff_exists, initLocals_isSome]

/-- A local is set after `initLocals xs` iff it is in `xs` or was already set. -/
theorem initLocals_set {C : Context} {xs : List Nat} {y : Nat} {t : CValType}
    (h : (C.initLocals xs).locals[y]? = some ⟨.set, t⟩) :
    y ∈ xs ∨ C.locals[y]? = some ⟨.set, t⟩ := by
  rw [initLocals_locals] at h
  split at h
  · next hy => exact .inl hy
  · exact .inr h

theorem initLocals_set_of_mem {C : Context} {xs : List Nat} {y : Nat} (hy : y ∈ xs)
    {lt : LocalType} (h : C.locals[y]? = some lt) :
    (C.initLocals xs).locals[y]? = some ⟨.set, lt.type⟩ := by
  rw [initLocals_locals]; simp [hy, h]

theorem initLocals_set_of_set {C : Context} {xs : List Nat} {y : Nat} {t : CValType}
    (h : C.locals[y]? = some ⟨.set, t⟩) : (C.initLocals xs).locals[y]? = some ⟨.set, t⟩ := by
  rw [initLocals_locals]; split <;> simp [h]

end Context

/-! ## Result types and instruction types -/

theorem ResultSub.append {Δ : TypeCtx} {a b c d : List CValType}
    (h₁ : ResultSub Δ a b) (h₂ : ResultSub Δ c d) : ResultSub Δ (a ++ c) (b ++ d) :=
  List.rel_append h₁ h₂

theorem ResultSub.trans {Δ : TypeCtx} (hΔ : Δ.Ok) {a b c : List CValType}
    (hb : ResultOk Δ b) (h₁ : ResultSub Δ a b) (h₂ : ResultSub Δ b c) : ResultSub Δ a c := by
  induction h₁ generalizing c with
  | nil => cases h₂; exact .nil
  | cons hab _ ih =>
    cases h₂ with
    | cons hbc h₂ =>
      exact .cons (Sub.trans hΔ (hb _ (by simp)) hab hbc)
        (ih (fun t ht => hb t (by simp [ht])) h₂)

theorem ResultOk.append {Δ : TypeCtx} {a b : List CValType} (ha : ResultOk Δ a)
    (hb : ResultOk Δ b) : ResultOk Δ (a ++ b) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  exacts [ha t h, hb t h]

theorem ResultOk.left {Δ : TypeCtx} {a b : List CValType} (h : ResultOk Δ (a ++ b)) :
    ResultOk Δ a := fun t ht => h t (List.mem_append_left _ ht)

theorem ResultOk.right {Δ : TypeCtx} {a b : List CValType} (h : ResultOk Δ (a ++ b)) :
    ResultOk Δ b := fun t ht => h t (List.mem_append_right _ ht)

theorem InstrTypeSub.refl (C : Context) (it : InstrType) : InstrTypeSub C it it :=
  ⟨ResultSub.refl _ _, ResultSub.refl _ _, fun _ h hn => absurd h hn⟩

theorem InstrTypeSub.trans {C : Context} (hΔ : C.toTypeCtx.Ok) {a b c : InstrType}
    (hb : InstrTypeOk C b) (h₁ : InstrTypeSub C a b) (h₂ : InstrTypeSub C b c) :
    InstrTypeSub C a c := by
  refine ⟨ResultSub.trans hΔ hb.1 h₂.1 h₁.1, ResultSub.trans hΔ hb.2.1 h₁.2.1 h₂.2.1, ?_⟩
  intro x hc ha
  by_cases hbx : x ∈ b.inits
  · exact h₁.2.2 x hbx ha
  · exact h₂.2.2 x hc hbx

/-! ## Well-formedness of expanded types -/

theorem Ty.subst_ofList {k : TKind} (σ : Subst) (l : List (Ty k)) :
    (Ty.ofList l).subst σ = Ty.ofList (l.map (·.subst σ)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [Ty.ofList, Ty.subst, ih]

theorem Ty.subst_toList {k : TKind} (σ : Subst) (l : Ty (.list k)) :
    (l.subst σ).toList = l.toList.map (·.subst σ) := by
  conv_lhs => rw [← Ty.ofList_toList l]
  rw [Ty.subst_ofList, Ty.toList_ofList]

theorem TyOk.toList {Δ : TypeCtx} {k : TKind} (l : Ty (.list k)) (h : TyOk Δ l) :
    ∀ a ∈ l.toList, TyOk Δ a := by
  rw [← Ty.ofList_toList l] at h
  generalize l.toList = xs at h
  induction xs with
  | nil => simp
  | cons a l ih =>
    cases h with
    | cons ha hl =>
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      exacts [ha, ih hl b hb]

theorem TyOk.ofList {Δ : TypeCtx} {k : TKind} (l : List (Ty k)) (h : ∀ a ∈ l, TyOk Δ a) :
    TyOk Δ (Ty.ofList l) := by
  induction l with
  | nil => exact .nil
  | cons a l ih => exact .cons (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem ResultOk.of_tyOk {Δ : TypeCtx} {l : Ty (.list .val)} (h : TyOk Δ l) :
    ResultOk Δ l.toList := TyOk.toList l h

/-- Substituting the `REC` variables of a group by valid type uses. -/
theorem TyOk.subst_recs {Δ : TypeCtx} {R : List CSubType} {σ : Subst}
    (hidx : ∀ x, σ (.idx x) = none)
    (hrec : ∀ j, j < R.length → ∃ u, σ (.recv j) = some u ∧ TyOk Δ u) :
    ∀ {k : TKind} (t : Ty k), TyOk (Δ.withRecs R) t → TyOk Δ (t.subst σ) := by
  have hminus : ∀ v, σ.minusRecs v = none := by
    intro v; cases v <;> simp [Subst.minusRecs, hidx]
  intro k t
  induction t with
  | nil => intro _; exact .nil
  | cons a l iha ihl => intro h; cases h with | cons ha hl => exact .cons (iha ha) (ihl hl)
  | idx x =>
    intro h; cases h with
    | idx hx => simp only [Ty.subst, hidx]; exact .idx hx
  | recv i =>
    intro h; cases h with
    | recv hi =>
      obtain ⟨u, hu, hok⟩ := hrec i (by
        simp only [TypeCtx.withRecs] at hi
        exact (List.getElem?_eq_some_iff.mp hi).1)
      simp [Ty.subst, hu, hok]
  | dt d ih => intro h; cases h with | dt h => exact .dt (ih h)
  | defn g i _ =>
    intro h; cases h with
    | defn hg hi =>
      simp only [Ty.subst]
      rw [Ty.subst_of_none _ _ hminus]
      exact .defn hg hi
  | abs a => intro _; exact .abs a
  | bot => intro _; exact .bot
  | use u ih => intro h; cases h with | use h => exact .use (ih h)
  | ref n hh ih => intro h; cases h with | ref h => exact .ref (ih h)
  | num t => intro _; exact .num t
  | vec t => intro _; exact .vec t
  | refv r ih => intro h; cases h with | refv h => exact .refv (ih h)
  | botv => intro _; exact .botv
  | val t ih => intro h; cases h with | val h => exact .val (ih h)
  | pack p => intro _; exact .pack p
  | field m s ih => intro h; cases h with | field h => exact .field (ih h)
  | struct fs ih => intro h; cases h with | struct h => exact .struct (ih h)
  | array f ih => intro h; cases h with | array h => exact .array (ih h)
  | func ps rs ihp ihr => intro h; cases h with | func hp hr => exact .func (ihp hp) (ihr hr)
  | sub fin sups b => intro h; cases h
  | group subs => intro h; cases h

theorem GroupOk2.get_ofList {Δ : TypeCtx} :
    ∀ (l : List CSubType) (j : Nat), GroupOk2 Δ (.group (Ty.ofList l)) j →
      ∀ i st, l[i]? = some st → SubOk2 Δ st (j + i)
  | [], _, _, _, _, h => by simp at h
  | a :: l, j, hg, i, st, h => by
    cases hg with
    | cons ha hs =>
      cases i with
      | zero => simp at h; subst h; simpa using ha
      | succ i =>
        have := GroupOk2.get_ofList l (j + 1) hs i st (by simpa using h)
        rwa [Nat.add_assoc, Nat.add_comm 1 i] at this

theorem SubOk2.body {Δ : TypeCtx} {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType}
    {i : Nat} (h : SubOk2 Δ (.sub fin sups ct) i) : TyOk Δ ct := by
  cases h with
  | noSuper hct => exact hct
  | oneSuper _ _ _ hct _ => exact hct

/-- Expansion of a valid defined type is a valid composite type. -/
theorem Expand.tyOk {Δ : TypeCtx} {d : DefType} {ct : CCompType} (hd : TyOk Δ d)
    (he : Expand d ct) : TyOk Δ ct := by
  obtain ⟨hu⟩ := he
  rename_i fin sups
  cases d with
  | defn g i =>
    cases g with
    | group subs =>
      cases hd with
      | defn hg hi =>
        simp only [unrolldt, unrollrt, Ty.subs, Ty.subst_toList, List.getElem?_map] at hu
        cases hst : subs.toList[i]? with
        | none => simp [hst] at hu
        | some st =>
          rw [hst] at hu
          cases st with
          | sub fin' sups' ct' =>
            simp only [Option.map_some, Ty.subst, Option.some.injEq, Ty.sub.injEq] at hu
            obtain ⟨-, -, rfl⟩ := hu
            have hg' : GroupOk2 (Δ.withRecs subs.toList) (.group (Ty.ofList subs.toList)) 0 := by
              rwa [Ty.ofList_toList]
            have hsub := GroupOk2.get_ofList _ 0 hg' i _ hst
            refine TyOk.subst_recs (R := subs.toList) (fun _ => rfl) ?_ _ hsub.body
            intro j hj
            refine ⟨.dt (.defn (.group subs) j), ?_, .dt (.defn hg hj)⟩
            simp [Ty.length, hj]

/-! ## Monotonicity in locals and return type -/

/-- Locals keep their types, and set locals stay set. -/
def LocalsLe (L L' : List LocalType) : Prop :=
  ∀ (y : Nat) (a : LocalType), L[y]? = some a →
    ∃ i : Init, L'[y]? = some (⟨i, a.type⟩ : LocalType) ∧ (a.init = Init.set → i = Init.set)

theorem LocalsLe.refl (L : List LocalType) : LocalsLe L L := by
  intro y a h
  exact ⟨a.init, by rw [h], id⟩

theorem LocalsLe.set {L L' : List LocalType} (h : LocalsLe L L') {y : Nat} {t : CValType}
    (hy : L[y]? = some ⟨.set, t⟩) : L'[y]? = some ⟨.set, t⟩ := by
  obtain ⟨i, hi, hs⟩ := h y _ hy
  rw [hi, hs rfl]

theorem LocalsLe.exists {L L' : List LocalType} (h : LocalsLe L L') {y : Nat}
    (hy : ∃ lt, L[y]? = some lt) : ∃ lt, L'[y]? = some lt := by
  obtain ⟨lt, hy⟩ := hy
  obtain ⟨i, hi, -⟩ := h y _ hy
  exact ⟨_, hi⟩

theorem LocalsLe.initLocals {C C' : Context} (h : LocalsLe C.locals C'.locals) (xs : List Nat) :
    LocalsLe (C.initLocals xs).locals (C'.initLocals xs).locals := by
  intro y a hy
  rw [Context.initLocals_locals] at hy ⊢
  split
  · next hm =>
    simp only [hm, ite_true] at hy
    cases hC : C.locals[y]? with
    | none => simp [hC] at hy
    | some b =>
      rw [hC] at hy
      simp only [Option.map_some, Option.some.injEq] at hy
      subst hy
      obtain ⟨i, hi, -⟩ := h y b hC
      exact ⟨.set, by simp [hi], fun _ => rfl⟩
  · next hm =>
    simp only [hm, ite_false] at hy
    exact h y a hy

theorem Context.initLocals_relax (C : Context) (L : List LocalType)
    (r : Option (List CValType)) (xs : List Nat) :
    ({ C with locals := L, return_ := r } : Context).initLocals xs =
      { C.initLocals xs with
        locals := (({ C with locals := L, return_ := r } : Context).initLocals xs).locals,
        return_ := r } := by
  obtain ⟨L₁, h₁, -⟩ := ({ C with locals := L, return_ := r } : Context).initLocals_spec xs
  obtain ⟨L₂, h₂, -⟩ := C.initLocals_spec xs
  rw [h₁, h₂]

theorem InstrTypeOk.mono {C : Context} {it : InstrType} (h : InstrTypeOk C it)
    {L : List LocalType} {r : Option (List CValType)} (hL : LocalsLe C.locals L) :
    InstrTypeOk { C with locals := L, return_ := r } it :=
  ⟨h.1, h.2.1, fun x hx => hL.exists (h.2.2 x hx)⟩

theorem InstrTypeSub.mono {C : Context} {it it' : InstrType} (h : InstrTypeSub C it it')
    {L : List LocalType} {r : Option (List CValType)} (hL : LocalsLe C.locals L) :
    InstrTypeSub { C with locals := L, return_ := r } it it' := by
  refine ⟨h.1, h.2.1, fun x hx hn => ?_⟩
  obtain ⟨t, ht⟩ := h.2.2 x hx hn
  exact ⟨t, hL.set ht⟩

section FamilyMono

variable {C : Context} {i : Instr} {it : InstrType} {L : List LocalType}
  {r : Option (List CValType)}

theorem ParametricInstrOk.mono (h : ParametricInstrOk C i it) (hL : LocalsLe C.locals L) :
    ParametricInstrOk { C with locals := L, return_ := r } i it := by
  cases h with
  | unreachable h => exact .unreachable (h.mono hL)
  | _ => (constructor; all_goals assumption)

theorem NumericInstrOk.mono (h : NumericInstrOk C i it) :
    NumericInstrOk { C with locals := L, return_ := r } i it := by
  cases h <;> (constructor; all_goals assumption)

theorem VectorInstrOk.mono (h : VectorInstrOk C i it) :
    VectorInstrOk { C with locals := L, return_ := r } i it := by
  cases h <;> constructor <;> assumption

theorem VariableInstrOk.mono (h : VariableInstrOk C i it) (hL : LocalsLe C.locals L) :
    VariableInstrOk { C with locals := L, return_ := r } i it := by
  cases h with
  | localGet h => exact .localGet (hL.set h)
  | localSet h =>
    obtain ⟨i, hi, -⟩ := hL _ _ h
    exact .localSet hi
  | localTee h =>
    obtain ⟨i, hi, -⟩ := hL _ _ h
    exact .localTee hi
  | globalGet h => exact .globalGet h
  | globalSet h => exact .globalSet h

theorem MemoryInstrOk.mono (h : MemoryInstrOk C i it) :
    MemoryInstrOk { C with locals := L, return_ := r } i it := by
  cases h <;> constructor <;> assumption

theorem TableInstrOk.mono (h : TableInstrOk C i it) :
    TableInstrOk { C with locals := L, return_ := r } i it := by
  cases h <;> constructor <;> assumption

theorem RefInstrOk.mono (h : RefInstrOk C i it) :
    RefInstrOk { C with locals := L, return_ := r } i it := by
  cases h <;> constructor <;> assumption

end FamilyMono

theorem BlockTypeOk.mono {C : Context} {bt : BlockType} {t₁ t₂ : List CValType}
    {L : List LocalType} {r : Option (List CValType)} (h : BlockTypeOk C bt t₁ t₂) :
    BlockTypeOk { C with locals := L, return_ := r } bt t₁ t₂ := by
  cases h <;> constructor <;> assumption

theorem CatchOk.mono {C : Context} {c : Catch}
    {L : List LocalType} {r : Option (List CValType)} (h : CatchOk C c) :
    CatchOk { C with locals := L, return_ := r } c := by
  cases h <;> constructor <;> assumption

theorem ret_mono {C : Context} {r : Option (List CValType)} {ts : List CValType}
    (hr : C.return_ = none ∨ C.return_ = r) (h : C.return_ = some ts) : r = some ts := by
  rcases hr with hr | hr
  · rw [hr] at h; cases h
  · rw [← hr, h]

mutual

/-- Typing is monotone in the initialisation status of locals, and a context
without a return type may be given one. -/
theorem InstrOk.mono {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it)
    {L : List LocalType} {r : Option (List CValType)} (hL : LocalsLe C.locals L)
    (hr : C.return_ = none ∨ C.return_ = r) :
    InstrOk { C with locals := L, return_ := r } i it :=
  match h with
  | .parametric h => .parametric (h.mono hL)
  | .numeric h => .numeric h.mono
  | .vector h => .vector h.mono
  | .variable h => .variable (h.mono hL)
  | .memory h => .memory h.mono
  | .table h => .table h.mono
  | .reference h => .reference h.mono
  | .block hbt hb => .block hbt.mono (InstrsOk.mono hb hL hr)
  | .loop hbt hb => .loop hbt.mono (InstrsOk.mono hb hL hr)
  | .if_ hbt h₁ h₂ => .if_ hbt.mono (InstrsOk.mono h₁ hL hr) (InstrsOk.mono h₂ hL hr)
  | .br hl hok => .br hl (hok.mono hL)
  | .brIf hl => .brIf hl
  | .brTable hls hl' hok => .brTable hls hl' (hok.mono hL)
  | .brOnNull hl hh => .brOnNull hl hh
  | .brOnNonNull hl => .brOnNonNull hl
  | .brOnCast hl h₁ h₂ h₂₁ h₂l => .brOnCast hl h₁ h₂ h₂₁ h₂l
  | .brOnCastFail hl h₁ h₂ h₂₁ hdl => .brOnCastFail hl h₁ h₂ h₂₁ hdl
  | .call hf he => .call hf he
  | .callRef hd he => .callRef hd he
  | .callIndirect ht hs hd he => .callIndirect ht hs hd he
  | .return_ hret hok => .return_ (ret_mono hr hret) (hok.mono hL)
  | .returnCall hf he hret hs hok => .returnCall hf he (ret_mono hr hret) hs (hok.mono hL)
  | .returnCallRef hd he hret hs hok =>
      .returnCallRef hd he (ret_mono hr hret) hs (hok.mono hL)
  | .returnCallIndirect ht hs hd he hret hrs hok =>
      .returnCallIndirect ht hs hd he (ret_mono hr hret) hrs (hok.mono hL)
  | .throw hx he hok => .throw hx he (hok.mono hL)
  | .throwRef hok => .throwRef (hok.mono hL)
  | .tryTable hbt hb hc =>
      .tryTable hbt.mono (InstrsOk.mono hb hL hr) (fun c hc' => (hc c hc').mono)

theorem InstrsOk.mono {C : Context} {is : List Instr} {it : InstrType} (h : InstrsOk C is it)
    {L : List LocalType} {r : Option (List CValType)} (hL : LocalsLe C.locals L)
    (hr : C.return_ = none ∨ C.return_ = r) :
    InstrsOk { C with locals := L, return_ := r } is it :=
  match h with
  | .nil => .nil
  | .instr h => .instr (InstrOk.mono h hL hr)
  | .seq (xs₁ := xs₁) h₁ hx h₂ =>
      .seq (InstrsOk.mono h₁ hL hr) (fun x hx' => hL.exists (hx x hx'))
        (by
          rw [Context.initLocals_relax]
          exact InstrsOk.mono h₂ (LocalsLe.initLocals (C' := { C with locals := L, return_ := r })
            hL xs₁) (by simpa using hr))
  | .cons (xs₁ := xs₁) hi hx hs =>
      .cons (InstrOk.mono hi hL hr) (fun x hx' => hL.exists (hx x hx'))
        (by
          rw [Context.initLocals_relax]
          exact InstrsOk.mono hs (LocalsLe.initLocals (C' := { C with locals := L, return_ := r })
            hL xs₁) (by simpa using hr))
  | .sub h hs hok => .sub (InstrsOk.mono h hL hr) (hs.mono hL) (hok.mono hL)
  | .frame h hok => .frame (InstrsOk.mono h hL hr) hok

end

/-! ## Well-formed contexts and regularity -/

/-- The context well-formedness that instruction-typing inversion needs: every
type the context can hand to an instruction type is valid. (Implied by
`Context_ok`.) -/
structure Context.Wf (C : Context) : Prop where
  types : C.toTypeCtx.Ok
  tags : ∀ d ∈ C.tags, TyOk C.toTypeCtx d
  globals : ∀ g ∈ C.globals, TyOk C.toTypeCtx g.type
  tables : ∀ t ∈ C.tables, TyOk C.toTypeCtx t.element
  funcs : ∀ d ∈ C.funcs, TyOk C.toTypeCtx d
  locals : ∀ lt ∈ C.locals, TyOk C.toTypeCtx lt.type
  labels : ∀ ts ∈ C.labels, ResultOk C.toTypeCtx ts
  return_ : ∀ ts, C.return_ = some ts → ResultOk C.toTypeCtx ts
  elems : ∀ rt ∈ C.elems, TyOk C.toTypeCtx rt

theorem Context.Wf.initLocals {C : Context} (hC : C.Wf) (xs : List Nat) :
    (C.initLocals xs).Wf := by
  obtain ⟨L, hL, hy⟩ := C.initLocals_spec xs
  rw [hL]
  refine ⟨hC.types, hC.tags, hC.globals, hC.tables, hC.funcs, ?_, hC.labels, hC.return_, hC.elems⟩
  intro lt hlt
  obtain ⟨y, hly⟩ := List.mem_iff_getElem?.mp hlt
  rw [hy y] at hly
  split at hly
  · cases h : C.locals[y]? with
    | none => simp [h] at hly
    | some lt₀ =>
      rw [h] at hly
      simp only [Option.map_some, Option.some.injEq] at hly
      subst hly
      exact hC.locals lt₀ (List.mem_of_getElem? h)
  · exact hC.locals lt (List.mem_of_getElem? hly)

theorem Context.Wf.type {C : Context} (hC : C.Wf) {x : TypeIdx} {d : DefType}
    (h : C.type? x = some d) : TyOk C.toTypeCtx d :=
  (hC.types d (List.mem_of_getElem? h)).2

theorem Context.Wf.label {C : Context} (hC : C.Wf) {l : Nat} {ts : List CValType}
    (h : C.labels[l]? = some ts) : ResultOk C.toTypeCtx ts :=
  hC.labels ts (List.mem_of_getElem? h)

section Regularity

variable {Δ : TypeCtx}

@[simp] theorem ResultOk.nil_iff : ResultOk Δ [] ↔ True := by simp [ResultOk]
@[simp] theorem ResultOk.cons_iff {a : CValType} {l : List CValType} :
    ResultOk Δ (a :: l) ↔ TyOk Δ a ∧ ResultOk Δ l := by simp [ResultOk]
@[simp] theorem ResultOk.append_iff {a b : List CValType} :
    ResultOk Δ (a ++ b) ↔ ResultOk Δ a ∧ ResultOk Δ b := by
  simp [ResultOk, or_imp, forall_and]
@[simp] theorem ResultOk.replicate_iff {n : Nat} {a : CValType} :
    ResultOk Δ (List.replicate n a) ↔ n = 0 ∨ TyOk Δ a := by
  simp only [ResultOk, List.mem_replicate]
  constructor
  · intro h
    by_cases hn : n = 0
    · exact .inl hn
    · exact .inr (h a ⟨hn, rfl⟩)
  · rintro (h | h) t ⟨hn, rfl⟩
    · exact absurd h hn
    · exact h

@[simp] theorem TyOk.num' {t : NumType} : TyOk Δ (Ty.num t) := .num t
@[simp] theorem TyOk.vec' {t : VecType} : TyOk Δ (Ty.vec t) := .vec t
@[simp] theorem TyOk.i32 : TyOk Δ Ty.i32 := .num _
@[simp] theorem TyOk.v128 : TyOk Δ Ty.v128 := .vec _
@[simp] theorem TyOk.valType {a : AddrType} : TyOk Δ a.valType := .num _
@[simp] theorem TyOk.abs' {a : AbsHeapType} : TyOk Δ (Ty.abs a) := .abs a

@[simp] theorem TyOk.refT_iff {n : Bool} {h : CHeapType} :
    TyOk Δ (Ty.refT n h) ↔ TyOk Δ h := by
  constructor
  · intro hh; cases hh with | refv hh => cases hh with | ref hh => exact hh
  · intro hh; exact .refv (.ref hh)

@[simp] theorem TyOk.refv_iff {r : CRefType} : TyOk Δ (Ty.refv r) ↔ TyOk Δ r := by
  constructor
  · intro hh; cases hh with | refv hh => exact hh
  · exact .refv

@[simp] theorem TyOk.defHeap_iff {d : DefType} : TyOk Δ (Ty.defHeap d) ↔ TyOk Δ d := by
  constructor
  · intro hh; cases hh with | use hh => cases hh with | dt hh => exact hh
  · intro hh; exact .use (.dt hh)

theorem TyOk.unpack {z : CStorageType} (h : TyOk Δ z) : TyOk Δ z.unpack := by
  cases z with
  | val t => cases h with | val h => exact h
  | pack p => exact .num _

theorem TyOk.diffrt {r₁ r₂ : CRefType} (h : TyOk Δ r₁) : TyOk Δ (Ty.diffrt r₁ r₂) := by
  cases r₁ with
  | ref n₁ h₁ =>
    cases r₂ with
    | ref n₂ h₂ =>
      cases n₂
      · exact h
      · cases h with | ref hh => exact .ref hh

theorem Expand.func_ok {d : DefType} {ps rs : Ty (.list .val)} (hd : TyOk Δ d)
    (he : Expand d (.func ps rs)) : ResultOk Δ ps.toList ∧ ResultOk Δ rs.toList := by
  have h := Expand.tyOk hd he
  cases h with | func hp hr => exact ⟨ResultOk.of_tyOk hp, ResultOk.of_tyOk hr⟩

theorem Expand.struct_ok {d : DefType} {fs : Ty (.list .field)} (hd : TyOk Δ d)
    (he : Expand d (.struct fs)) : ∀ f ∈ fs.toList, TyOk Δ f := by
  have h := Expand.tyOk hd he
  cases h with | struct h => exact TyOk.toList _ h

theorem Expand.array_ok {d : DefType} {m : Mutability} {z : CStorageType} (hd : TyOk Δ d)
    (he : Expand d (.array (.field m z))) : TyOk Δ z := by
  have h := Expand.tyOk hd he
  cases h with | array h => cases h with | field h => exact h

theorem TyOk.fieldUnpack {f : CFieldType} (h : TyOk Δ f) : TyOk Δ (fieldUnpack f) := by
  cases f with
  | field m z => cases h with | field h => exact TyOk.unpack h

end Regularity

section FamilyRegular

variable {C : Context} {i : Instr} {it : InstrType}

theorem ParametricInstrOk.regular (_hC : C.Wf) (h : ParametricInstrOk C i it) :
    InstrTypeOk C it := by
  cases h with
  | unreachable h => exact h
  | _ => simp_all [InstrTypeOk]

theorem NumericInstrOk.regular (h : NumericInstrOk C i it) : InstrTypeOk C it := by
  cases h <;> simp [InstrTypeOk]

theorem VectorInstrOk.regular (h : VectorInstrOk C i it) : InstrTypeOk C it := by
  cases h <;> simp [InstrTypeOk]

theorem MemoryInstrOk.regular (h : MemoryInstrOk C i it) : InstrTypeOk C it := by
  cases h <;> simp [InstrTypeOk]

theorem VariableInstrOk.regular (hC : C.Wf) (h : VariableInstrOk C i it) :
    InstrTypeOk C it := by
  cases h with
  | localGet h => simpa [InstrTypeOk] using hC.locals _ (List.mem_of_getElem? h)
  | localSet h =>
    refine ⟨by simpa using hC.locals _ (List.mem_of_getElem? h), by simp, ?_⟩
    simp only [List.mem_singleton, forall_eq]; exact ⟨_, h⟩
  | localTee h =>
    have := hC.locals _ (List.mem_of_getElem? h)
    refine ⟨by simpa using this, by simpa using this, ?_⟩
    simp only [List.mem_singleton, forall_eq]; exact ⟨_, h⟩
  | globalGet h => simpa [InstrTypeOk] using hC.globals _ (List.mem_of_getElem? h)
  | globalSet h => simpa [InstrTypeOk] using hC.globals _ (List.mem_of_getElem? h)

theorem TableInstrOk.regular (hC : C.Wf) (h : TableInstrOk C i it) : InstrTypeOk C it := by
  cases h with
  | tableGet h => simpa [InstrTypeOk] using hC.tables _ (List.mem_of_getElem? h)
  | tableSet h => simpa [InstrTypeOk] using hC.tables _ (List.mem_of_getElem? h)
  | tableGrow h => simpa [InstrTypeOk] using hC.tables _ (List.mem_of_getElem? h)
  | tableFill h => simpa [InstrTypeOk] using hC.tables _ (List.mem_of_getElem? h)
  | _ => simp [InstrTypeOk]

theorem RefInstrOk.regular (hC : C.Wf) (h : RefInstrOk C i it) : InstrTypeOk C it := by
  cases h with
  | refNull h => simpa [InstrTypeOk] using h
  | refFunc h => simpa [InstrTypeOk] using hC.funcs _ (List.mem_of_getElem? h)
  | refIsNull h => simpa [InstrTypeOk] using h
  | refAsNonNull h => simpa [InstrTypeOk] using h
  | refTest _ h' => simpa [InstrTypeOk] using h'
  | refCast h h' => simp [InstrTypeOk, h, h']
  | structNew hd he =>
    refine ⟨?_, by simpa using hC.type hd, by simp⟩
    intro t ht
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ht
    exact TyOk.fieldUnpack (Expand.struct_ok (hC.type hd) he f hf)
  | structNewDefault hd => simpa [InstrTypeOk] using hC.type hd
  | structGet hd he hi =>
    have := Expand.struct_ok (hC.type hd) he _ (List.mem_of_getElem? hi)
    cases this with
    | field hz => simp [InstrTypeOk, hC.type hd, TyOk.unpack hz]
  | structSet hd he hi =>
    have := Expand.struct_ok (hC.type hd) he _ (List.mem_of_getElem? hi)
    cases this with
    | field hz => simp [InstrTypeOk, hC.type hd, TyOk.unpack hz]
  | arrayNew hd he =>
    simp [InstrTypeOk, hC.type hd, TyOk.unpack (Expand.array_ok (hC.type hd) he)]
  | arrayNewDefault hd => simpa [InstrTypeOk] using hC.type hd
  | arrayNewFixed hd he =>
    simp [InstrTypeOk, hC.type hd, TyOk.unpack (Expand.array_ok (hC.type hd) he)]
  | arrayNewElem hd => simpa [InstrTypeOk] using hC.type hd
  | arrayNewData hd => simpa [InstrTypeOk] using hC.type hd
  | arrayGet hd he =>
    simp [InstrTypeOk, hC.type hd, TyOk.unpack (Expand.array_ok (hC.type hd) he)]
  | arraySet hd he =>
    simp [InstrTypeOk, hC.type hd, TyOk.unpack (Expand.array_ok (hC.type hd) he)]
  | arrayFill hd he =>
    simp [InstrTypeOk, hC.type hd, TyOk.unpack (Expand.array_ok (hC.type hd) he)]
  | arrayCopy hd₁ _ hd₂ => simp [InstrTypeOk, hC.type hd₁, hC.type hd₂]
  | arrayInitElem hd => simpa [InstrTypeOk] using hC.type hd
  | arrayInitData hd => simpa [InstrTypeOk] using hC.type hd
  | _ => simp [InstrTypeOk]

end FamilyRegular

theorem BlockTypeOk.regular {C : Context} {bt : BlockType} {t₁ t₂ : List CValType}
    (hC : C.Wf) (h : BlockTypeOk C bt t₁ t₂) :
    ResultOk C.toTypeCtx t₁ ∧ ResultOk C.toTypeCtx t₂ := by
  cases h with
  | empty => simp
  | value h => simpa using h
  | typeIdx hd he => exact Expand.func_ok (hC.type hd) he

theorem InstrOk.regular {C : Context} {i : Instr} {it : InstrType} (hC : C.Wf)
    (h : InstrOk C i it) : InstrTypeOk C it := by
  cases h with
  | parametric h => exact h.regular hC
  | numeric h => exact h.regular
  | vector h => exact h.regular
  | «variable» h => exact h.regular hC
  | memory h => exact h.regular
  | table h => exact h.regular hC
  | reference h => exact h.regular hC
  | block hbt => have := hbt.regular hC; simp [InstrTypeOk, this]
  | loop hbt => have := hbt.regular hC; simp [InstrTypeOk, this]
  | if_ hbt => have := hbt.regular hC; simp [InstrTypeOk, this]
  | tryTable hbt => have := hbt.regular hC; simp [InstrTypeOk, this]
  | br hl hok => have := hC.label hl; simp_all [InstrTypeOk]
  | brIf hl => have := hC.label hl; simp_all [InstrTypeOk]
  | brTable _ _ hok => exact hok
  | brOnNull hl hh => have := hC.label hl; simp_all [InstrTypeOk]
  | brOnNonNull hl =>
    have := hC.label hl
    simp only [ResultOk.append_iff, ResultOk.cons_iff, TyOk.refT_iff] at this
    simp [InstrTypeOk, this]
  | brOnCast hl h₁ =>
    have := hC.label hl
    simp only [ResultOk.append_iff] at this
    simp [InstrTypeOk, this, h₁, TyOk.diffrt h₁]
  | brOnCastFail hl h₁ h₂ =>
    have := hC.label hl
    simp only [ResultOk.append_iff] at this
    simp [InstrTypeOk, this, h₁, h₂]
  | call hf he =>
    have := Expand.func_ok (hC.funcs _ (List.mem_of_getElem? hf)) he
    simp [InstrTypeOk, this]
  | callRef hd he =>
    have := Expand.func_ok (hC.type hd) he
    simp [InstrTypeOk, this, hC.type hd]
  | callIndirect _ _ hd he =>
    have := Expand.func_ok (hC.type hd) he
    simp [InstrTypeOk, this]
  | return_ hr hok => have := hC.return_ _ hr; simp_all [InstrTypeOk]
  | returnCall hf he _ _ hok =>
    have := Expand.func_ok (hC.funcs _ (List.mem_of_getElem? hf)) he
    simp_all [InstrTypeOk]
  | returnCallRef hd he _ _ hok =>
    have := Expand.func_ok (hC.type hd) he
    have := hC.type hd
    simp_all [InstrTypeOk]
  | returnCallIndirect _ _ hd he _ _ hok =>
    have := Expand.func_ok (hC.type hd) he
    simp_all [InstrTypeOk]
  | throw hx he hok =>
    have := Expand.func_ok (hC.tags _ (List.mem_of_getElem? hx)) he
    simp_all [InstrTypeOk]
  | throwRef hok => simp_all [InstrTypeOk]

theorem InstrsOk.regular {C : Context} {is : List Instr} {it : InstrType} (hC : C.Wf)
    (h : InstrsOk C is it) : InstrTypeOk C it :=
  match h with
  | .nil => by simp [InstrTypeOk]
  | .instr h => h.regular hC
  | .seq h₁ hx h₂ => by
      have r₁ := InstrsOk.regular hC h₁
      have r₂ := InstrsOk.regular (hC.initLocals _) h₂
      refine ⟨r₁.1, by simpa using r₂.2.1, ?_⟩
      intro x hx'
      rcases List.mem_append.mp hx' with h | h
      · exact hx x h
      · exact Context.initLocals_exists.mp (r₂.2.2 x h)
  | .cons hi hx hs => by
      have r₁ := hi.regular hC
      have r₂ := InstrsOk.regular (hC.initLocals _) hs
      refine ⟨r₁.1, by simpa using r₂.2.1, ?_⟩
      intro x hx'
      rcases List.mem_append.mp hx' with h | h
      · exact hx x h
      · exact Context.initLocals_exists.mp (r₂.2.2 x h)
  | .sub _ _ hok => hok
  | .frame h hok => by
      have r := InstrsOk.regular hC h
      exact ⟨ResultOk.append hok r.1, ResultOk.append hok r.2.1, r.2.2⟩

/-! ## Admissible rules, inversion and weakening -/

theorem LocalsLe.trans {L₁ L₂ L₃ : List LocalType} (h₁ : LocalsLe L₁ L₂) (h₂ : LocalsLe L₂ L₃) :
    LocalsLe L₁ L₃ := by
  intro y a hy
  obtain ⟨i, hi, hs⟩ := h₁ y a hy
  obtain ⟨j, hj, hs'⟩ := h₂ y _ hi
  exact ⟨j, hj, fun ha => hs' (hs ha)⟩

theorem LocalsLe.initLocals_of_sub {C : Context} {xs xs' : List Nat}
    (h : ∀ x ∈ xs', x ∉ xs → ∃ t, C.locals[x]? = some ⟨.set, t⟩) :
    LocalsLe (C.initLocals xs').locals (C.initLocals xs).locals := by
  intro y a hy
  rw [Context.initLocals_locals] at hy
  rw [Context.initLocals_locals]
  by_cases h' : y ∈ xs'
  · simp only [h', ite_true] at hy
    by_cases hx : y ∈ xs
    · simp only [hx, ite_true]
      cases hC : C.locals[y]? with
      | none => simp [hC] at hy
      | some b =>
        rw [hC] at hy
        simp only [Option.map_some, Option.some.injEq] at hy
        subst hy
        exact ⟨.set, rfl, fun _ => rfl⟩
    · simp only [hx, ite_false]
      obtain ⟨t, ht⟩ := h y h' hx
      rw [ht] at hy
      simp only [Option.map_some, Option.some.injEq] at hy
      subst hy
      exact ⟨.set, ht, fun _ => rfl⟩
  · simp only [h', ite_false] at hy
    by_cases hx : y ∈ xs
    · simp only [hx, ite_true, hy, Option.map_some]
      exact ⟨.set, rfl, fun _ => rfl⟩
    · simp only [hx, ite_false, hy]
      exact ⟨a.init, rfl, id⟩

theorem Context.initLocals_eq_with (C : Context) (xs : List Nat) :
    C.initLocals xs = { C with locals := (C.initLocals xs).locals } := by
  obtain ⟨L, hL, -⟩ := C.initLocals_spec xs
  rw [hL]

/-- Transport along a more-initialised locals list. -/
theorem InstrsOk.relocal {C C' : Context} {is : List Instr} {it : InstrType}
    (h : InstrsOk C is it) (hL : LocalsLe C.locals C'.locals)
    (hC : C' = { C with locals := C'.locals }) : InstrsOk C' is it := by
  have := InstrsOk.mono h hL (r := C.return_) (.inr rfl)
  rw [hC]; exact this

theorem InstrsOk.initLocals_relocal {C : Context} {xs ys : List Nat} {is : List Instr}
    {it : InstrType} (h : InstrsOk (C.initLocals xs) is it)
    (hL : LocalsLe (C.initLocals xs).locals (C.initLocals ys).locals) :
    InstrsOk (C.initLocals ys) is it := by
  refine h.relocal hL ?_
  rw [C.initLocals_eq_with ys, C.initLocals_eq_with xs]

theorem InstrTypeSub.frame {C : Context} {a b c d : List CValType} {x y : List Nat}
    (h : InstrTypeSub C ⟨a, x, b⟩ ⟨c, y, d⟩) (ts : List CValType) :
    InstrTypeSub C ⟨ts ++ a, x, ts ++ b⟩ ⟨ts ++ c, y, ts ++ d⟩ :=
  ⟨ResultSub.append (ResultSub.refl _ _) h.1, ResultSub.append (ResultSub.refl _ _) h.2.1, h.2.2⟩

theorem InstrsOk.id {C : Context} {ts : List CValType} (h : ResultOk C.toTypeCtx ts) :
    InstrsOk C [] ⟨ts, [], ts⟩ := by
  simpa using (InstrsOk.frame (C := C) (ts := ts) InstrsOk.nil h)

/-- Induction on `InstrsOk` alone (the nested `InstrOk` derivations get no
hypothesis). -/
theorem InstrsOk.ind {motive : (C : Context) → (is : List Instr) → (it : InstrType) →
      InstrsOk C is it → Prop}
    (nil : ∀ {C : Context}, motive C [] (.plain [] []) .nil)
    (instr : ∀ {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it),
      motive C [i] it (.instr h))
    (seq : ∀ {C : Context} {is₁ is₂ : List Instr} {t₁ t₂ t₃ : List CValType}
      {xs₁ xs₂ : List Nat}
      (h₁ : InstrsOk C is₁ ⟨t₁, xs₁, t₂⟩) (hx : ∀ x ∈ xs₁, ∃ lt, C.locals[x]? = some lt)
      (h₂ : InstrsOk (C.initLocals xs₁) is₂ ⟨t₂, xs₂, t₃⟩),
      motive C is₁ _ h₁ → motive (C.initLocals xs₁) is₂ _ h₂ →
        motive C (is₁ ++ is₂) ⟨t₁, xs₁ ++ xs₂, t₃⟩ (.seq h₁ hx h₂))
    (cons : ∀ {C : Context} {i : Instr} {is : List Instr} {t₁ t₂ t₃ : List CValType}
      {xs₁ xs₂ : List Nat}
      (hi : InstrOk C i ⟨t₁, xs₁, t₂⟩) (hx : ∀ x ∈ xs₁, ∃ lt, C.locals[x]? = some lt)
      (hs : InstrsOk (C.initLocals xs₁) is ⟨t₂, xs₂, t₃⟩),
      motive (C.initLocals xs₁) is _ hs →
        motive C (i :: is) ⟨t₁, xs₁ ++ xs₂, t₃⟩ (.cons hi hx hs))
    (sub : ∀ {C : Context} {is : List Instr} {it it' : InstrType}
      (h : InstrsOk C is it) (hs : InstrTypeSub C it it') (hok : InstrTypeOk C it'),
      motive C is it h → motive C is it' (.sub h hs hok))
    (frame : ∀ {C : Context} {is : List Instr} {ts t₁ t₂ : List CValType} {xs : List Nat}
      (h : InstrsOk C is ⟨t₁, xs, t₂⟩) (hok : ResultOk C.toTypeCtx ts),
      motive C is _ h → motive C is ⟨ts ++ t₁, xs, ts ++ t₂⟩ (.frame h hok)) :
    ∀ {C : Context} {is : List Instr} {it : InstrType} (h : InstrsOk C is it),
      motive C is it h := by
  intro C is it h
  apply InstrsOk.rec (motive_1 := fun _ _ _ _ => True) (motive_2 := motive) (t := h)
  all_goals first | (intros; trivial) | skip
  case nil => exact nil
  case instr => exact fun h _ => instr h
  case seq => exact fun h₁ hx h₂ ih₁ ih₂ => seq h₁ hx h₂ ih₁ ih₂
  case cons => exact fun hi hx hs _ ih => cons hi hx hs ih
  case sub => exact fun h hs hok ih => sub h hs hok ih
  case frame => exact fun h hok ih => frame h hok ih

/-- Inversion for the empty sequence. -/
theorem InstrsOk.nil_inv_aux {C : Context} {is : List Instr} {it : InstrType} (hC : C.Wf)
    (h : InstrsOk C is it) (his : is = []) :
    ResultSub C.toTypeCtx it.params it.results ∧
      ∀ x ∈ it.inits, ∃ t, C.locals[x]? = some ⟨.set, t⟩ := by
  induction h using InstrsOk.ind with
  | nil => exact ⟨ResultSub.refl _ _, by simp⟩
  | instr _ => cases his
  | cons _ _ _ _ => cases his
  | @seq C is₁ is₂ t₁ t₂ t₃ xs₁ xs₂ h₁ _ h₂ ih₁ ih₂ =>
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp his
      obtain ⟨s₁, i₁⟩ := ih₁ hC rfl
      have hC₁ : C.initLocals xs₁ = C := Context.initLocals_of_set i₁
      obtain ⟨s₂, i₂⟩ := ih₂ (hC.initLocals _) rfl
      rw [hC₁] at i₂
      simp only [Context.initLocals_toTypeCtx] at s₂
      refine ⟨ResultSub.trans hC.types (InstrsOk.regular hC h₁).2.1 s₁ s₂, ?_⟩
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      exacts [i₁ x hx, i₂ x hx]
  | @sub C is it₀ it' h hs hok ih =>
      obtain ⟨s, i⟩ := ih hC his
      have r := InstrsOk.regular hC h
      refine ⟨ResultSub.trans hC.types r.1 hs.1
        (ResultSub.trans hC.types r.2.1 s hs.2.1), ?_⟩
      intro x hx
      by_cases hx' : x ∈ it₀.inits
      · exact i x hx'
      · exact hs.2.2 x hx hx'
  | frame h hok ih =>
      obtain ⟨s, i⟩ := ih hC his
      exact ⟨ResultSub.append (ResultSub.refl _ _) s, i⟩

theorem InstrsOk.nil_inv {C : Context} {it : InstrType} (hC : C.Wf) (h : InstrsOk C [] it) :
    ResultSub C.toTypeCtx it.params it.results ∧
      ∀ x ∈ it.inits, ∃ t, C.locals[x]? = some ⟨.set, t⟩ :=
  InstrsOk.nil_inv_aux hC h rfl

/-- `Instrs_ok/instr`. -/
theorem InstrsOk.single {C : Context} {i : Instr} {it : InstrType}
    (h : InstrOk C i it) (_hx : ∀ x ∈ it.inits, ∃ lt, C.locals[x]? = some lt) :
    InstrsOk C [i] it :=
  .instr h

/-- `Instrs_ok/seq`. -/
theorem InstrsOk.append {C : Context} {is₁ is₂ : List Instr} {t₁ t₂ t₃ : List CValType}
    {xs₁ xs₂ : List Nat}
    (h₁ : InstrsOk C is₁ ⟨t₁, xs₁, t₂⟩) (hx : ∀ x ∈ xs₁, ∃ lt, C.locals[x]? = some lt)
    (h₂ : InstrsOk (C.initLocals xs₁) is₂ ⟨t₂, xs₂, t₃⟩) :
    InstrsOk C (is₁ ++ is₂) ⟨t₁, xs₁ ++ xs₂, t₃⟩ :=
  .seq h₁ hx h₂

/-- Composition of a sequence typing with an empty-sequence typing on the right. -/
theorem InstrTypeSub.seq_nil {C : Context} {t₁ t₂ t₃ : List CValType} {xs₁ xs₂ : List Nat}
    (s : ResultSub C.toTypeCtx t₂ t₃)
    (i : ∀ x ∈ xs₂, ∃ t, (C.initLocals xs₁).locals[x]? = some ⟨.set, t⟩) :
    InstrTypeSub C ⟨t₁, xs₁, t₂⟩ ⟨t₁, xs₁ ++ xs₂, t₃⟩ := by
  refine ⟨ResultSub.refl _ _, s, ?_⟩
  intro x hx hn
  rcases List.mem_append.mp hx with hx | hx
  · exact absurd hx hn
  · obtain ⟨t, ht⟩ := i x hx
    rcases Context.initLocals_set ht with h | h
    · exact absurd h hn
    · exact ⟨t, h⟩

theorem InstrsOk.single_inv_aux {C : Context} {is : List Instr} {i : Instr} {it : InstrType}
    (hC : C.Wf) (h : InstrsOk C is it) (his : is = [i]) :
    ∃ ts it₀, InstrOk C i it₀ ∧
      InstrTypeSub C ⟨ts ++ it₀.params, it₀.inits, ts ++ it₀.results⟩ it := by
  induction h using InstrsOk.ind with
  | nil => cases his
  | @instr C i' it₀ h =>
      cases his
      exact ⟨[], it₀, h, by simpa using InstrTypeSub.refl C it₀⟩
  | @cons C i' is t₁ t₂ t₃ xs₁ xs₂ hi _ hs _ =>
      obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp his
      obtain ⟨s, i₂⟩ := InstrsOk.nil_inv (hC.initLocals _) hs
      simp only [Context.initLocals_toTypeCtx] at s
      exact ⟨[], ⟨t₁, xs₁, t₂⟩, hi, by simpa using InstrTypeSub.seq_nil s i₂⟩
  | @seq C is₁ is₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ =>
      rcases List.append_eq_singleton_iff.mp his with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨s₁, i₁⟩ := InstrsOk.nil_inv hC h₁
        have hC₁ : C.initLocals xs₁ = C := Context.initLocals_of_set i₁
        obtain ⟨ts, it₀, hi, hsub⟩ := ih₂ (hC.initLocals _) rfl
        rw [hC₁] at hi hsub h₂
        refine ⟨ts, it₀, hi, InstrTypeSub.trans hC.types (InstrsOk.regular hC h₂) hsub ?_⟩
        refine ⟨s₁, ResultSub.refl _ _, ?_⟩
        intro x hx hn
        rcases List.mem_append.mp hx with hx | hx
        · exact i₁ x hx
        · exact absurd hx hn
      · obtain ⟨ts, it₀, hi, hsub⟩ := ih₁ hC rfl
        obtain ⟨s, i₂⟩ := InstrsOk.nil_inv (hC.initLocals _) h₂
        simp only [Context.initLocals_toTypeCtx] at s
        exact ⟨ts, it₀, hi, InstrTypeSub.trans hC.types (InstrsOk.regular hC h₁) hsub
          (InstrTypeSub.seq_nil s i₂)⟩
  | sub h hs hok ih =>
      obtain ⟨ts, it₀, hi, hsub⟩ := ih hC his
      exact ⟨ts, it₀, hi, InstrTypeSub.trans hC.types (InstrsOk.regular hC h) hsub hs⟩
  | @frame C is ts' t₁ t₂ xs h hok ih =>
      obtain ⟨ts, it₀, hi, hsub⟩ := ih hC his
      refine ⟨ts' ++ ts, it₀, hi, ?_⟩
      simpa using InstrTypeSub.frame hsub ts'

/-- Principal inversion for a single instruction: every typing of `[i]` factors
through an `InstrOk` typing, a frame, and a subsumption. -/
theorem InstrsOk.single_inv {C : Context} {i : Instr} {it : InstrType} (hC : C.Wf)
    (h : InstrsOk C [i] it) :
    ∃ ts it₀, InstrOk C i it₀ ∧
      InstrTypeSub C ⟨ts ++ it₀.params, it₀.inits, ts ++ it₀.results⟩ it :=
  InstrsOk.single_inv_aux hC h rfl

/-- Strengthened splitting: also tracks how the locals initialised by the parts
relate to those of the whole. -/
theorem InstrsOk.split {C : Context} {is is₁ is₂ : List Instr} {it : InstrType} (hC : C.Wf)
    (h : InstrsOk C is it) (his : is = is₁ ++ is₂) :
    ∃ t₂ xs₁ xs₂, InstrsOk C is₁ ⟨it.params, xs₁, t₂⟩ ∧
      InstrsOk (C.initLocals xs₁) is₂ ⟨t₂, xs₂, it.results⟩ ∧
      LocalsLe (C.initLocals it.inits).locals (C.initLocals (xs₁ ++ xs₂)).locals := by
  induction h using InstrsOk.ind generalizing is₁ is₂ with
  | nil =>
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp his.symm
      exact ⟨[], [], [], .nil, .nil, LocalsLe.refl _⟩
  | @instr C i it₀ hi =>
      have r := hi.regular hC
      rcases List.append_eq_singleton_iff.mp his.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨it₀.params, [], it₀.inits, InstrsOk.id r.1, ?_, by simpa using LocalsLe.refl _⟩
        simpa using (InstrsOk.instr hi : InstrsOk C [i] it₀)
      · refine ⟨it₀.results, it₀.inits, [], ?_, InstrsOk.id (by simpa using r.2.1),
          by simpa using LocalsLe.refl _⟩
        exact InstrsOk.instr hi
  | @cons C i is' t₁ t₂' t₃ xs₁' xs₂' hi hx hs ih =>
      rcases List.cons_eq_append_iff.mp his with ⟨rfl, rfl⟩ | ⟨a, rfl, rfl⟩
      · have hh : InstrsOk C (i :: is') ⟨t₁, xs₁' ++ xs₂', t₃⟩ := .cons hi hx hs
        exact ⟨t₁, [], xs₁' ++ xs₂', InstrsOk.id (InstrsOk.regular hC hh).1, hh,
          by simpa using LocalsLe.refl _⟩
      · obtain ⟨m, ya, yb, ha, hb, hL⟩ := ih (hC.initLocals _) rfl
        refine ⟨m, xs₁' ++ ya, yb, .cons hi hx ha, ?_, ?_⟩
        · rw [Context.initLocals_append]; exact hb
        · simpa [Context.initLocals_append] using hL
  | @seq C is₁' is₂' t₁ t₂' t₃ xs₁' xs₂' h₁ hx h₂ ih₁ ih₂ =>
      rcases List.append_eq_append_iff.mp his with ⟨a, rfl, rfl⟩ | ⟨c, rfl, rfl⟩
      · -- `is₁ = is₁' ++ a`, `is₂' = a ++ is₂`
        obtain ⟨m, ya, yb, ha, hb, hL⟩ := ih₂ (hC.initLocals _) rfl
        refine ⟨m, xs₁' ++ ya, yb, .seq h₁ hx ha, ?_, ?_⟩
        · rw [Context.initLocals_append]; exact hb
        · simpa [Context.initLocals_append] using hL
      · -- `is₁' = is₁ ++ c`, `is₂ = c ++ is₂'`
        obtain ⟨m, ya, yb, ha, hc, hL⟩ := ih₁ hC rfl
        have hcx : ∀ x ∈ yb, ∃ lt, (C.initLocals ya).locals[x]? = some lt :=
          (InstrsOk.regular (hC.initLocals _) hc).2.2
        have h₂' : InstrsOk ((C.initLocals ya).initLocals yb) is₂' ⟨t₂', xs₂', t₃⟩ := by
          rw [← Context.initLocals_append]; exact h₂.initLocals_relocal hL
        refine ⟨m, ya, yb ++ xs₂', ha, .seq hc hcx h₂', ?_⟩
        have := LocalsLe.initLocals (C := C.initLocals xs₁') (C' := C.initLocals (ya ++ yb))
          hL xs₂'
        simpa [← Context.initLocals_append] using this
  | @sub C is it₀ it' h hs hok ih =>
      obtain ⟨m, ya, yb, ha, hb, hL⟩ := ih hC his
      have ra := InstrsOk.regular hC ha
      have rb := InstrsOk.regular (hC.initLocals _) hb
      refine ⟨m, ya, yb, .sub ha ⟨hs.1, ResultSub.refl _ _, fun _ h hn => absurd h hn⟩
          ⟨hok.1, ra.2.1, ra.2.2⟩,
        .sub hb ⟨ResultSub.refl _ _, by simpa using hs.2.1, fun _ h hn => absurd h hn⟩
          ⟨rb.1, by simpa using hok.2.1, rb.2.2⟩, ?_⟩
      exact LocalsLe.trans (LocalsLe.initLocals_of_sub hs.2.2) hL
  | @frame C is ts t₁ t₂ xs h hok ih =>
      obtain ⟨m, ya, yb, ha, hb, hL⟩ := ih hC his
      exact ⟨ts ++ m, ya, yb, .frame ha hok, .frame hb (by simpa using hok), hL⟩

/-- Splitting a typed sequence (the converse of `append`, up to subsumption). -/
theorem InstrsOk.append_inv {C : Context} {is₁ is₂ : List Instr} {it : InstrType}
    (hC : C.Wf) (h : InstrsOk C (is₁ ++ is₂) it) :
    ∃ t₂ xs₁ xs₂, InstrsOk C is₁ ⟨it.params, xs₁, t₂⟩ ∧
      InstrsOk (C.initLocals xs₁) is₂ ⟨t₂, xs₂, it.results⟩ := by
  obtain ⟨t₂, xs₁, xs₂, h₁, h₂, -⟩ := InstrsOk.split hC h rfl
  exact ⟨t₂, xs₁, xs₂, h₁, h₂⟩

/-- Typing only depends on the type fields of the context through `TypeCtx`:
labels, locals and return may be changed without affecting `Sub`/`TyOk`. -/
@[simp] theorem Context.withLabel_toTypeCtx (C : Context) (ts : List CValType) :
    (C.withLabel ts).toTypeCtx = C.toTypeCtx := rfl

/-- Weakening by extra labels at the outside (used by the soundness proofs). -/
theorem InstrsOk.weaken_return {C : Context} {is : List Instr} {it : InstrType}
    (h : InstrsOk C is it) (hr : C.return_ = none) (ts : List CValType) :
    InstrsOk { C with return_ := some ts } is it :=
  InstrsOk.mono h (LocalsLe.refl _) (.inl hr)

end Silmaril.Wasm.Validation
