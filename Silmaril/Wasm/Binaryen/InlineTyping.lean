module

public import Silmaril.Wasm.Binaryen.Equiv
public import Silmaril.Wasm.Validation.Instructions.Properties
public import Silmaril.Wasm.Validation.RollClosed
public import Silmaril.Wasm.Validation.Check.ModuleCompleteWf
public import Silmaril.Wasm.Validation.Check.FuncComplete

@[expose] public section

/-! # Typing infrastructure for inlining

Two generic facts about Core 3.0 instruction typing that `inlineSite_valid`
(`Binaryen/Inline.lean`) is built from.

* **Relocating a function body** (`InstrsOk.xform`). `xform base d` shifts every
  local index by `base` and turns `return` at nesting depth `d` into `br d`. A body
  typed in a function context `C` stays typed in any context that agrees with `C`
  on the module part, holds `C`'s locals at `base ..` (`ShiftLe`), extends `C`'s
  labels (`relCtx`), and whose label `d` is `C`'s return type. Tail calls are
  excluded (`retGood`); depths must fit a label index.
* **Replacement in a one-hole context** (`plug_replace`). If every typing of `es`
  in a context of a class `P` (well formed, closed under `initLocals` and
  `withLabel`) is a typing of `es'`, then plugging `es'` instead of `es` into any
  `BCtx` preserves typing.
-/

namespace Silmaril.Wasm.Binaryen

open Validation

namespace InlineTy

/-! ## The relocation -/

/-- Shift a local index by `base` (unchanged on overflow). -/
def xIdx (base : Nat) (x : LocalIdx) : LocalIdx := (Idx.ofNat? (x.toNat + base)).getD x

/-- A label index from a depth (`0` on overflow). -/
def xLabel (d : Nat) : LabelIdx := (Idx.ofNat? d).getD ⟨⟨0, by decide⟩⟩

theorem xIdx_toNat {base : Nat} {x : LocalIdx} (h : base + x.toNat < 2 ^ 32) :
    (xIdx base x).toNat = base + x.toNat := by
  have h' : x.toNat + base < 2 ^ 32 := by omega
  unfold xIdx Idx.ofNat?
  split
  · show x.toNat + base = base + x.toNat
    omega
  · contradiction

theorem xLabel_toNat {d : Nat} (h : d < 2 ^ 32) : (xLabel d).toNat = d := by
  unfold xLabel Idx.ofNat?
  split
  · rfl
  · contradiction

mutual
/-- Relocate one instruction: locals shift by `base`, `return` at depth `d` becomes
`br d`. -/
def xform (base d : Nat) : Instr → Instr
  | .localGet x => .localGet (xIdx base x)
  | .localSet x => .localSet (xIdx base x)
  | .localTee x => .localTee (xIdx base x)
  | .return_ => .br (xLabel d)
  | .block bt body => .block bt (xformL base (d + 1) body)
  | .loop bt body => .loop bt (xformL base (d + 1) body)
  | .if_ bt b₁ b₂ => .if_ bt (xformL base (d + 1) b₁) (xformL base (d + 1) b₂)
  | .tryTable bt cs body => .tryTable bt cs (xformL base (d + 1) body)
  | i => i
/-- `xform` on a sequence. -/
def xformL (base d : Nat) : List Instr → List Instr
  | [] => []
  | i :: is => xform base d i :: xformL base d is
end

mutual
/-- No tail calls, and every `return` sits at a depth that fits a label index. -/
def retGood (d : Nat) : Instr → Prop
  | .return_ => d < 2 ^ 32
  | .returnCall _ => False
  | .returnCallRef _ => False
  | .returnCallIndirect _ _ => False
  | .block _ body => retGoodL (d + 1) body
  | .loop _ body => retGoodL (d + 1) body
  | .if_ _ b₁ b₂ => retGoodL (d + 1) b₁ ∧ retGoodL (d + 1) b₂
  | .tryTable _ _ body => retGoodL (d + 1) body
  | _ => True
/-- `retGood` on a sequence. -/
def retGoodL (d : Nat) : List Instr → Prop
  | [] => True
  | i :: is => retGood d i ∧ retGoodL d is
end

@[simp] theorem xformL_nil (base d : Nat) : xformL base d [] = [] := rfl

@[simp] theorem xformL_cons (base d : Nat) (i : Instr) (is : List Instr) :
    xformL base d (i :: is) = xform base d i :: xformL base d is := rfl

theorem xformL_append (base d : Nat) (is₁ is₂ : List Instr) :
    xformL base d (is₁ ++ is₂) = xformL base d is₁ ++ xformL base d is₂ := by
  induction is₁ with
  | nil => rfl
  | cons i is ih => simp [ih]

theorem xformL_eq_map (base d : Nat) (is : List Instr) :
    xformL base d is = is.map (xform base d) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [ih]

theorem retGoodL_iff {d : Nat} {is : List Instr} : retGoodL d is ↔ ∀ i ∈ is, retGood d i := by
  induction is with
  | nil => simp [retGoodL]
  | cons i is ih => simp [retGoodL, ih]

theorem retGoodL_append {d : Nat} {is₁ is₂ : List Instr} :
    retGoodL d (is₁ ++ is₂) ↔ retGoodL d is₁ ∧ retGoodL d is₂ := by
  simp only [retGoodL_iff, List.mem_append]
  constructor
  · intro h; exact ⟨fun i hi => h i (.inl hi), fun i hi => h i (.inr hi)⟩
  · rintro ⟨h₁, h₂⟩ i (hi | hi)
    · exact h₁ i hi
    · exact h₂ i hi

/-! ## Related contexts -/

/-- The target context: `C`'s module part, locals `L`, `C`'s labels followed by `X`,
return type `r`. -/
def relCtx (C : Context) (L : List LocalType) (X : List (List CValType))
    (r : Option (List CValType)) : Context :=
  { C with locals := L, labels := C.labels ++ X, return_ := r }

/-- `C`'s locals sit at `base ..` in `L`, with the same types and at least as set. -/
def ShiftLe (base : Nat) (L L' : List LocalType) : Prop :=
  ∀ (y : Nat) (a : LocalType), L[y]? = some a →
    base + y < 2 ^ 32 ∧ ∃ i : Init, L'[base + y]? = some ⟨i, a.type⟩ ∧ (a.init = .set → i = .set)

/-- Shift the initialised locals of an instruction type. -/
def shiftIT (base : Nat) (it : InstrType) : InstrType :=
  ⟨it.params, it.inits.map (base + ·), it.results⟩

@[simp] theorem shiftIT_plain (base : Nat) (a b : List CValType) :
    shiftIT base (.plain a b) = .plain a b := rfl

theorem relCtx_withLabel (C : Context) (L : List LocalType) (X : List (List CValType))
    (r : Option (List CValType)) (ts : List CValType) :
    (relCtx C L X r).withLabel ts = relCtx (C.withLabel ts) L X r := rfl

@[simp] theorem relCtx_toTypeCtx (C : Context) (L : List LocalType) (X : List (List CValType))
    (r : Option (List CValType)) : (relCtx C L X r).toTypeCtx = C.toTypeCtx := rfl

theorem relCtx_initLocals (C : Context) (L : List LocalType) (X : List (List CValType))
    (r : Option (List CValType)) (base : Nat) (xs : List Nat) :
    (relCtx C L X r).initLocals (xs.map (base + ·)) =
      relCtx (C.initLocals xs) ((relCtx C L X r).initLocals (xs.map (base + ·))).locals X r := by
  obtain ⟨L₁, h₁, -⟩ := (relCtx C L X r).initLocals_spec (xs.map (base + ·))
  obtain ⟨L₂, h₂, -⟩ := C.initLocals_spec xs
  rw [h₁, h₂]
  rfl

theorem ShiftLe.initLocals {base : Nat} {C : Context} {L : List LocalType}
    {X : List (List CValType)} {r : Option (List CValType)} (h : ShiftLe base C.locals L)
    (xs : List Nat) :
    ShiftLe base (C.initLocals xs).locals
      ((relCtx C L X r).initLocals (xs.map (base + ·))).locals := by
  intro y a hy
  rw [Context.initLocals_locals] at hy
  have hmem : (base + y ∈ xs.map (base + ·)) ↔ y ∈ xs := by simp
  by_cases hyx : y ∈ xs
  · simp only [hyx, ite_true] at hy
    cases hC : C.locals[y]? with
    | none => simp [hC] at hy
    | some b =>
      rw [hC] at hy
      simp only [Option.map_some, Option.some.injEq] at hy
      subst hy
      obtain ⟨hlt, i, hi, -⟩ := h y b hC
      refine ⟨hlt, .set, ?_, fun _ => rfl⟩
      rw [Context.initLocals_locals]
      simp only [hmem.mpr hyx, ite_true]
      show L[base + y]?.map _ = _
      rw [hi]; rfl
  · simp only [hyx, ite_false] at hy
    obtain ⟨hlt, i, hi, hs⟩ := h y a hy
    refine ⟨hlt, i, ?_, hs⟩
    rw [Context.initLocals_locals]
    simp only [show ¬ (base + y ∈ xs.map (base + ·)) from fun h' => hyx (hmem.mp h'), ite_false]
    exact hi

theorem ShiftLe.exists {base : Nat} {L L' : List LocalType} (h : ShiftLe base L L') {y : Nat}
    (hy : ∃ lt, L[y]? = some lt) : ∃ lt, L'[base + y]? = some lt := by
  obtain ⟨lt, hy⟩ := hy
  obtain ⟨-, i, hi, -⟩ := h y lt hy
  exact ⟨_, hi⟩

theorem labels_append {C : Context} {X : List (List CValType)} {l : Nat} {ts : List CValType}
    (h : C.labels[l]? = some ts) : (C.labels ++ X)[l]? = some ts := by
  have hl : l < C.labels.length := by
    rcases Nat.lt_or_ge l C.labels.length with h' | h'
    · exact h'
    · simp [List.getElem?_eq_none h'] at h
  rw [List.getElem?_append_left hl, h]

section Transfer

variable {base : Nat} {C : Context} {L : List LocalType} {X : List (List CValType)}
  {r : Option (List CValType)}

theorem InstrTypeOk.rel {it : InstrType} (h : InstrTypeOk C it) (hL : ShiftLe base C.locals L) :
    InstrTypeOk (relCtx C L X r) (shiftIT base it) := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro x hx
  simp only [shiftIT, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ShiftLe.exists hL (h.2.2 y hy)

theorem InstrTypeOk.rel_plain {a b : List CValType} (h : InstrTypeOk C (.plain a b)) :
    InstrTypeOk (relCtx C L X r) (.plain a b) :=
  ⟨h.1, h.2.1, by simp⟩

theorem InstrTypeSub.rel {it it' : InstrType} (h : InstrTypeSub C it it')
    (hL : ShiftLe base C.locals L) :
    InstrTypeSub (relCtx C L X r) (shiftIT base it) (shiftIT base it') := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro x hx hn
  simp only [shiftIT, List.mem_map] at hx hn
  obtain ⟨y, hy, rfl⟩ := hx
  have hny : y ∉ it.inits := fun h' => hn ⟨y, h', rfl⟩
  obtain ⟨t, ht⟩ := h.2.2 y hy hny
  obtain ⟨-, i, hi, hs⟩ := hL y _ ht
  exact ⟨t, by show L[base + y]? = _; rw [hi, hs rfl]⟩

theorem ParametricInstrOk.rel {i : Instr} {it : InstrType} (h : ParametricInstrOk C i it) :
    ParametricInstrOk (relCtx C L X r) i it := by
  cases h with
  | unreachable h => exact .unreachable (InstrTypeOk.rel_plain h)
  | _ => (constructor; all_goals assumption)

theorem NumericInstrOk.rel {i : Instr} {it : InstrType} (h : NumericInstrOk C i it) :
    NumericInstrOk (relCtx C L X r) i it := by
  cases h <;> (constructor; all_goals assumption)

theorem VectorInstrOk.rel {i : Instr} {it : InstrType} (h : VectorInstrOk C i it) :
    VectorInstrOk (relCtx C L X r) i it := by
  cases h <;> constructor <;> assumption

theorem MemoryInstrOk.rel {i : Instr} {it : InstrType} (h : MemoryInstrOk C i it) :
    MemoryInstrOk (relCtx C L X r) i it := by
  cases h <;> constructor <;> assumption

theorem TableInstrOk.rel {i : Instr} {it : InstrType} (h : TableInstrOk C i it) :
    TableInstrOk (relCtx C L X r) i it := by
  cases h <;> constructor <;> assumption

theorem RefInstrOk.rel {i : Instr} {it : InstrType} (h : RefInstrOk C i it) :
    RefInstrOk (relCtx C L X r) i it := by
  cases h <;> constructor <;> assumption

theorem BlockTypeOk.rel {bt : BlockType} {t₁ t₂ : List CValType} (h : BlockTypeOk C bt t₁ t₂) :
    BlockTypeOk (relCtx C L X r) bt t₁ t₂ := by
  cases h <;> constructor <;> assumption

theorem CatchOk.rel {c : Catch} (h : CatchOk C c) : CatchOk (relCtx C L X r) c := by
  cases h with
  | catch_ hx he hl hs => exact .catch_ hx he (labels_append hl) hs
  | catchRef hx he hl hs => exact .catchRef hx he (labels_append hl) hs
  | catchAll hl hs => exact .catchAll (labels_append hl) hs
  | catchAllRef hl hs => exact .catchAllRef (labels_append hl) hs

/-! Families other than `variable` neither mention locals nor are touched by
`xform`, and their instruction types initialise nothing. -/

theorem ParametricInstrOk.xform_eq {i : Instr} {it : InstrType} (h : ParametricInstrOk C i it)
    (d : Nat) : xform base d i = i ∧ shiftIT base it = it := by
  cases h <;> exact ⟨rfl, rfl⟩

theorem NumericInstrOk.xform_eq {i : Instr} {it : InstrType} (h : NumericInstrOk C i it)
    (d : Nat) : xform base d i = i ∧ shiftIT base it = it := by
  cases h <;> exact ⟨rfl, rfl⟩

theorem VectorInstrOk.xform_eq {i : Instr} {it : InstrType} (h : VectorInstrOk C i it)
    (d : Nat) : xform base d i = i ∧ shiftIT base it = it := by
  cases h <;> exact ⟨rfl, rfl⟩

theorem MemoryInstrOk.xform_eq {i : Instr} {it : InstrType} (h : MemoryInstrOk C i it)
    (d : Nat) : xform base d i = i ∧ shiftIT base it = it := by
  cases h <;> exact ⟨rfl, rfl⟩

theorem TableInstrOk.xform_eq {i : Instr} {it : InstrType} (h : TableInstrOk C i it)
    (d : Nat) : xform base d i = i ∧ shiftIT base it = it := by
  cases h <;> exact ⟨rfl, rfl⟩

theorem RefInstrOk.xform_eq {i : Instr} {it : InstrType} (h : RefInstrOk C i it)
    (d : Nat) : xform base d i = i ∧ shiftIT base it = it := by
  cases h <;> exact ⟨rfl, rfl⟩

theorem VariableInstrOk.xform {i : Instr} {it : InstrType} (h : VariableInstrOk C i it) (d : Nat)
    (hL : ShiftLe base C.locals L) :
    VariableInstrOk (relCtx C L X r) (xform base d i) (shiftIT base it) := by
  cases h with
  | @localGet x t h =>
    obtain ⟨hlt, i, hi, hs⟩ := hL _ _ h
    have e := xIdx_toNat hlt
    refine .localGet (x := xIdx base x) ?_
    show L[(xIdx base x).toNat]? = _
    rw [e, hi, hs rfl]
  | @localSet x i₀ t h =>
    obtain ⟨hlt, i, hi, -⟩ := hL _ _ h
    have e := xIdx_toNat hlt
    show VariableInstrOk _ (.localSet (xIdx base x)) ⟨[t], [base + x.toNat], []⟩
    rw [← e]
    exact .localSet (i := i) (by show L[(xIdx base x).toNat]? = _; rw [e, hi])
  | @localTee x i₀ t h =>
    obtain ⟨hlt, i, hi, -⟩ := hL _ _ h
    have e := xIdx_toNat hlt
    show VariableInstrOk _ (.localTee (xIdx base x)) ⟨[t], [base + x.toNat], [t]⟩
    rw [← e]
    exact .localTee (i := i) (by show L[(xIdx base x).toNat]? = _; rw [e, hi])
  | globalGet h => exact .globalGet h
  | globalSet h => exact .globalSet h

end Transfer

/-- The return hypothesis: the source context's return type is its label `d`. -/
def RetAt (C : Context) (d : Nat) : Prop :=
  ∃ rs, C.return_ = some rs ∧ C.labels[d]? = some rs

theorem RetAt.withLabel {C : Context} {d : Nat} (h : RetAt C d) (ts : List CValType) :
    RetAt (C.withLabel ts) (d + 1) := h

theorem RetAt.initLocals {C : Context} {d : Nat} (h : RetAt C d) (xs : List Nat) :
    RetAt (C.initLocals xs) d := by
  obtain ⟨rs, h₁, h₂⟩ := h
  exact ⟨rs, by rw [Context.initLocals_return, h₁], by rw [Context.initLocals_labels, h₂]⟩

mutual

/-- **Relocation preserves typing** (single instruction). -/
theorem InstrOk.xform {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it)
    {base d : Nat} {L : List LocalType} {X : List (List CValType)} {r : Option (List CValType)}
    (hL : ShiftLe base C.locals L) (hret : RetAt C d) (hg : retGood d i) :
    InstrOk (relCtx C L X r) (xform base d i) (shiftIT base it) :=
  match h with
  | .parametric h => by
    obtain ⟨e₁, e₂⟩ := ParametricInstrOk.xform_eq (base := base) h d
    rw [e₁, e₂]; exact .parametric (ParametricInstrOk.rel h)
  | .numeric h => by
    obtain ⟨e₁, e₂⟩ := NumericInstrOk.xform_eq (base := base) h d
    rw [e₁, e₂]; exact .numeric (NumericInstrOk.rel h)
  | .vector h => by
    obtain ⟨e₁, e₂⟩ := VectorInstrOk.xform_eq (base := base) h d
    rw [e₁, e₂]; exact .vector (VectorInstrOk.rel h)
  | .variable h => .variable (VariableInstrOk.xform h d hL)
  | .memory h => by
    obtain ⟨e₁, e₂⟩ := MemoryInstrOk.xform_eq (base := base) h d
    rw [e₁, e₂]; exact .memory (MemoryInstrOk.rel h)
  | .table h => by
    obtain ⟨e₁, e₂⟩ := TableInstrOk.xform_eq (base := base) h d
    rw [e₁, e₂]; exact .table (TableInstrOk.rel h)
  | .reference h => by
    obtain ⟨e₁, e₂⟩ := RefInstrOk.xform_eq (base := base) h d
    rw [e₁, e₂]; exact .reference (RefInstrOk.rel h)
  | .block hbt hb =>
    .block (BlockTypeOk.rel hbt) (InstrsOk.xform hb hL (RetAt.withLabel hret _) hg)
  | .loop hbt hb =>
    .loop (BlockTypeOk.rel hbt) (InstrsOk.xform hb hL (RetAt.withLabel hret _) hg)
  | .if_ hbt h₁ h₂ =>
    .if_ (BlockTypeOk.rel hbt) (InstrsOk.xform h₁ hL (RetAt.withLabel hret _) hg.1)
      (InstrsOk.xform h₂ hL (RetAt.withLabel hret _) hg.2)
  | .br hl hok => .br (labels_append hl) (InstrTypeOk.rel_plain hok)
  | .brIf hl => .brIf (labels_append hl)
  | .brTable hls hl' hok =>
    .brTable (fun l hl => let ⟨lt, h₁, h₂⟩ := hls l hl; ⟨lt, labels_append h₁, h₂⟩)
      (let ⟨lt, h₁, h₂⟩ := hl'; ⟨lt, labels_append h₁, h₂⟩) (InstrTypeOk.rel_plain hok)
  | .brOnNull hl hh => .brOnNull (labels_append hl) hh
  | .brOnNonNull hl => .brOnNonNull (labels_append hl)
  | .brOnCast hl h₁ h₂ h₂₁ h₂l => .brOnCast (labels_append hl) h₁ h₂ h₂₁ h₂l
  | .brOnCastFail hl h₁ h₂ h₂₁ hdl => .brOnCastFail (labels_append hl) h₁ h₂ h₂₁ hdl
  | .call hf he => .call hf he
  | .callRef hd he => .callRef hd he
  | .callIndirect ht hs hd he => .callIndirect ht hs hd he
  | .return_ hr hok => by
    obtain ⟨rs, h₁, h₂⟩ := hret
    rw [hr] at h₁
    cases h₁
    exact .br (l := xLabel d) (by rw [xLabel_toNat hg]; exact labels_append h₂)
      (InstrTypeOk.rel_plain hok)
  | .returnCall .. => hg.elim
  | .returnCallRef .. => hg.elim
  | .returnCallIndirect .. => hg.elim
  | .throw hx he hok => .throw hx he (InstrTypeOk.rel_plain hok)
  | .throwRef hok => .throwRef (InstrTypeOk.rel_plain hok)
  | .tryTable hbt hb hc =>
    .tryTable (BlockTypeOk.rel hbt) (InstrsOk.xform hb hL (RetAt.withLabel hret _) hg)
      (fun c hc' => CatchOk.rel (hc c hc'))

/-- **Relocation preserves typing** (sequences). -/
theorem InstrsOk.xform {C : Context} {is : List Instr} {it : InstrType} (h : InstrsOk C is it)
    {base d : Nat} {L : List LocalType} {X : List (List CValType)} {r : Option (List CValType)}
    (hL : ShiftLe base C.locals L) (hret : RetAt C d) (hg : retGoodL d is) :
    InstrsOk (relCtx C L X r) (xformL base d is) (shiftIT base it) :=
  match h with
  | .nil => .nil
  | .instr h => .instr (InstrOk.xform h hL hret hg.1)
  | .seq (xs₁ := xs₁) h₁ hx h₂ => by
    rw [xformL_append]
    have hg' := retGoodL_append.mp hg
    have h₂' := InstrsOk.xform h₂ (X := X) (r := r) (ShiftLe.initLocals (X := X) (r := r) hL xs₁)
      (RetAt.initLocals hret xs₁) hg'.2
    rw [← relCtx_initLocals C L X r base xs₁] at h₂'
    have h := InstrsOk.seq (InstrsOk.xform h₁ hL hret hg'.1 (X := X) (r := r))
      (fun x hx' => by
        simp only [List.mem_map] at hx'
        obtain ⟨y, hy, rfl⟩ := hx'
        exact ShiftLe.exists hL (hx y hy)) h₂'
    simpa [shiftIT] using h
  | .cons (xs₁ := xs₁) hi hx hs => by
    have h₂' := InstrsOk.xform hs (X := X) (r := r) (ShiftLe.initLocals (X := X) (r := r) hL xs₁)
      (RetAt.initLocals hret xs₁) hg.2
    rw [← relCtx_initLocals C L X r base xs₁] at h₂'
    have h := InstrsOk.cons (InstrOk.xform hi hL hret hg.1 (X := X) (r := r))
      (fun x hx' => by
        simp only [List.mem_map] at hx'
        obtain ⟨y, hy, rfl⟩ := hx'
        exact ShiftLe.exists hL (hx y hy)) h₂'
    simpa [shiftIT] using h
  | .sub h hs hok =>
    .sub (InstrsOk.xform h hL hret hg) (InstrTypeSub.rel hs hL) (InstrTypeOk.rel hok hL)
  | .frame h hok => by
    have h' := InstrsOk.frame (InstrsOk.xform h hL hret hg (X := X) (r := r)) hok
    simpa [shiftIT] using h'

end

/-! ## Replacement in one-hole contexts -/

/-- A class of contexts closed under the context updates of typing. -/
structure CtxClass (P : Context → Prop) : Prop where
  wf : ∀ C, P C → C.Wf
  initLocals : ∀ C xs, P C → P (C.initLocals xs)
  withLabel : ∀ C ts, P C → ResultOk C.toTypeCtx ts → P (C.withLabel ts)

/-- Replacing a suffix by one with the same typings. -/
theorem replace_right {P : Context → Prop} (hP : CtxClass P) {C : Context} (hC : P C)
    {is₁ is₂ is₂' : List Instr} {it : InstrType} (h : InstrsOk C (is₁ ++ is₂) it)
    (hr : ∀ C' it', P C' → InstrsOk C' is₂ it' → InstrsOk C' is₂' it') :
    InstrsOk C (is₁ ++ is₂') it := by
  have hW := hP.wf C hC
  obtain ⟨t₂, xs₁, xs₂, h₁, h₂, hLe⟩ := InstrsOk.split hW h rfl
  have hx : ∀ x ∈ xs₁, ∃ lt, C.locals[x]? = some lt := (InstrsOk.regular hW h₁).2.2
  have h' : InstrsOk C (is₁ ++ is₂') ⟨it.params, xs₁ ++ xs₂, it.results⟩ :=
    .seq h₁ hx (hr _ _ (hP.initLocals C xs₁ hC) h₂)
  have hreg := InstrsOk.regular hW h
  refine .sub h' ⟨ResultSub.refl _ _, ResultSub.refl _ _, ?_⟩ hreg
  intro x hx' hn
  obtain ⟨lt, hlt⟩ := hreg.2.2 x hx'
  have h1 : (C.initLocals it.inits).locals[x]? = some ⟨.set, lt.type⟩ :=
    Context.initLocals_set_of_mem hx' hlt
  obtain ⟨i, hi, hs⟩ := hLe x _ h1
  have hi' : (C.initLocals (xs₁ ++ xs₂)).locals[x]? = some ⟨.set, lt.type⟩ := by
    rw [hi, hs rfl]
  rcases Context.initLocals_set hi' with h | h
  · exact absurd h hn
  · exact ⟨_, h⟩

/-- Replacing a prefix by one with the same typings. -/
theorem replace_left {P : Context → Prop} (hP : CtxClass P) {C : Context} (hC : P C)
    {is₁ is₁' is₂ : List Instr} {it : InstrType} (h : InstrsOk C (is₁ ++ is₂) it)
    (hr : ∀ C' it', P C' → InstrsOk C' is₁ it' → InstrsOk C' is₁' it') :
    InstrsOk C (is₁' ++ is₂) it := by
  have hW := hP.wf C hC
  obtain ⟨t₂, xs₁, xs₂, h₁, h₂, hLe⟩ := InstrsOk.split hW h rfl
  have h₁' := hr _ _ hC h₁
  have hx : ∀ x ∈ xs₁, ∃ lt, C.locals[x]? = some lt := (InstrsOk.regular hW h₁).2.2
  have h' : InstrsOk C (is₁' ++ is₂) ⟨it.params, xs₁ ++ xs₂, it.results⟩ := .seq h₁' hx h₂
  have hreg := InstrsOk.regular hW h
  refine .sub h' ⟨ResultSub.refl _ _, ResultSub.refl _ _, ?_⟩ hreg
  intro x hx' hn
  obtain ⟨lt, hlt⟩ := hreg.2.2 x hx'
  have h1 : (C.initLocals it.inits).locals[x]? = some ⟨.set, lt.type⟩ :=
    Context.initLocals_set_of_mem hx' hlt
  obtain ⟨i, hi, hs⟩ := hLe x _ h1
  have hi' : (C.initLocals (xs₁ ++ xs₂)).locals[x]? = some ⟨.set, lt.type⟩ := by
    rw [hi, hs rfl]
  rcases Context.initLocals_set hi' with h | h
  · exact absurd h hn
  · exact ⟨_, h⟩

/-- Replacing a middle segment. -/
theorem replace_mid {P : Context → Prop} (hP : CtxClass P) {C : Context} (hC : P C)
    {a b b' c : List Instr} {it : InstrType} (h : InstrsOk C (a ++ (b ++ c)) it)
    (hr : ∀ C' it', P C' → InstrsOk C' b it' → InstrsOk C' b' it') :
    InstrsOk C (a ++ (b' ++ c)) it :=
  replace_right hP hC h fun _ _ hC' h' => replace_left hP hC' h' hr

/-- Replacing a single instruction by one with the same `InstrOk` typings. -/
theorem single_congr {P : Context → Prop} (hP : ∀ C xs, P C → P (C.initLocals xs))
    {i i' : Instr} (hi : ∀ C it₀, P C → InstrOk C i it₀ → InstrOk C i' it₀) :
    ∀ {C : Context} {is : List Instr} {it : InstrType}, P C → InstrsOk C is it → is = [i] →
      InstrsOk C [i'] it := by
  intro C is it hC h his
  induction h using InstrsOk.ind with
  | nil => cases his
  | instr h => cases his; exact .instr (hi _ _ hC h)
  | @cons C i₀ is t₁ t₂ t₃ xs₁ xs₂ h₀ hx hs _ =>
    obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp his
    exact .cons (hi _ _ hC h₀) hx hs
  | @seq C is₁ is₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ =>
    rcases List.append_eq_singleton_iff.mp his with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have := InstrsOk.seq h₁ hx (ih₂ (hP _ _ hC) rfl)
      simpa using this
    · have := InstrsOk.seq (ih₁ hC rfl) hx h₂
      simpa using this
  | sub h hs hok ih => exact .sub (ih hC his) hs hok
  | frame h hok ih => exact .frame (ih hC his) hok

/-- Single-instruction congruence for a typed singleton. -/
theorem replace_single {P : Context → Prop} (hP : CtxClass P) {i i' : Instr}
    (hi : ∀ C it₀, P C → InstrOk C i it₀ → InstrOk C i' it₀) {C : Context} {it : InstrType}
    (hC : P C) (h : InstrsOk C [i] it) : InstrsOk C [i'] it :=
  single_congr hP.initLocals hi hC h rfl

theorem Context.Wf.withLabel' {C : Context} (hC : C.Wf) {ts : List CValType}
    (h : ResultOk C.toTypeCtx ts) : (C.withLabel ts).Wf := by
  refine ⟨hC.types, hC.tags, hC.globals, hC.tables, hC.funcs, hC.locals, ?_, hC.return_,
    hC.elems⟩
  intro ts' hts'
  simp only [Context.withLabel, List.mem_cons] at hts'
  rcases hts' with rfl | hts'
  · exact h
  · exact hC.labels ts' hts'

open BExpr in
/-- **Replacement in a one-hole context.** -/
theorem plug_replace {P : Context → Prop} (hP : CtxClass P) {es es' : List BExpr}
    (hrep : ∀ C it, P C → InstrsOk C (lowerList es) it → InstrsOk C (lowerList es') it) :
    ∀ (K : BCtx) {C : Context} {it : InstrType}, P C →
      InstrsOk C (lowerList (K.plug es)) it → InstrsOk C (lowerList (K.plug es')) it := by
  intro K
  induction K with
  | hole => intro C it hC h; exact hrep C it hC h
  | seq pre k post ih =>
    intro C it hC h
    simp only [BCtx.plug, lowerList_append, List.append_assoc] at h ⊢
    exact replace_mid hP hC h fun C' it' hC' h' => ih hC' h'
  | op i pre k post ih =>
    intro C it hC h
    simp only [BCtx.plug, lowerList_singleton, lower_op, lowerList_append, List.append_assoc] at h ⊢
    exact replace_mid hP hC h fun C' it' hC' h' => ih hC' h'
  | block bt pre k post ih =>
    intro C it hC h
    simp only [BCtx.plug, lowerList_singleton, BExpr.lower, lowerList_append,
      List.append_assoc] at h ⊢
    refine replace_single hP (fun C' it₀ hC' hi => ?_) hC h
    cases hi with
    | block hbt hb =>
      have hW := hP.wf C' hC'
      exact .block hbt (replace_mid hP (hP.withLabel _ _ hC' (hbt.regular hW).2) hb
        fun C'' it'' hC'' h'' => ih hC'' h'')
    | parametric h => cases h
    | numeric h => cases h
    | vector h => cases h
    | «variable» h => cases h
    | memory h => cases h
    | table h => cases h
    | reference h => cases h
  | loop bt pre k post ih =>
    intro C it hC h
    simp only [BCtx.plug, lowerList_singleton, BExpr.lower, lowerList_append,
      List.append_assoc] at h ⊢
    refine replace_single hP (fun C' it₀ hC' hi => ?_) hC h
    cases hi with
    | loop hbt hb =>
      have hW := hP.wf C' hC'
      exact .loop hbt (replace_mid hP (hP.withLabel _ _ hC' (hbt.regular hW).1) hb
        fun C'' it'' hC'' h'' => ih hC'' h'')
    | parametric h => cases h
    | numeric h => cases h
    | vector h => cases h
    | «variable» h => cases h
    | memory h => cases h
    | table h => cases h
    | reference h => cases h
  | ifCond bt pre k post t e ih =>
    intro C it hC h
    simp only [BCtx.plug, lowerList_singleton, BExpr.lower, lowerList_append,
      List.append_assoc] at h ⊢
    exact replace_mid hP hC h fun C' it' hC' h' => ih hC' h'
  | ifThen bt c pre k post e ih =>
    intro C it hC h
    simp only [BCtx.plug, lowerList_singleton, BExpr.lower, lowerList_append,
      List.append_assoc] at h ⊢
    refine replace_right hP hC h fun C' it' hC' h' => ?_
    refine replace_single hP (fun C'' it₀ hC'' hi => ?_) hC' h'
    cases hi with
    | if_ hbt h₁ h₂ =>
      have hW := hP.wf C'' hC''
      exact .if_ hbt (replace_mid hP (hP.withLabel _ _ hC'' (hbt.regular hW).2) h₁
        fun C₃ it₃ hC₃ h₃ => ih hC₃ h₃) h₂
    | parametric h => cases h
    | numeric h => cases h
    | vector h => cases h
    | «variable» h => cases h
    | memory h => cases h
    | table h => cases h
    | reference h => cases h
  | ifElse bt c t pre k post ih =>
    intro C it hC h
    simp only [BCtx.plug, lowerList_singleton, BExpr.lower, lowerList_append,
      List.append_assoc] at h ⊢
    refine replace_right hP hC h fun C' it' hC' h' => ?_
    refine replace_single hP (fun C'' it₀ hC'' hi => ?_) hC' h'
    cases hi with
    | if_ hbt h₁ h₂ =>
      have hW := hP.wf C'' hC''
      exact .if_ hbt h₁ (replace_mid hP (hP.withLabel _ _ hC'' (hbt.regular hW).2) h₂
        fun C₃ it₃ hC₃ h₃ => ih hC₃ h₃)
    | parametric h => cases h
    | numeric h => cases h
    | vector h => cases h
    | «variable» h => cases h
    | memory h => cases h
    | table h => cases h
    | reference h => cases h
  | tryTable bt cs pre k post ih =>
    intro C it hC h
    simp only [BCtx.plug, lowerList_singleton, BExpr.lower, lowerList_append,
      List.append_assoc] at h ⊢
    refine replace_single hP (fun C' it₀ hC' hi => ?_) hC h
    cases hi with
    | tryTable hbt hb hc =>
      have hW := hP.wf C' hC'
      exact .tryTable hbt (replace_mid hP (hP.withLabel _ _ hC' (hbt.regular hW).2) hb
        fun C'' it'' hC'' h'' => ih hC'' h'') hc
    | parametric h => cases h
    | numeric h => cases h
    | vector h => cases h
    | «variable» h => cases h
    | memory h => cases h
    | table h => cases h
    | reference h => cases h

/-! ## Function types of a module's type section -/

open RollClosed in
/-- Substituting a source type against a longer list changes nothing once its free
indices are in range. -/
theorem substAll_append_of_bound {k : TKind} (t : Ty k) : Src t → ∀ (l l' : List CTypeUse),
    (∀ y ∈ t.freeIdx, y < l.length) → t.substAll (l ++ l') = t.substAll l := by
  induction t with
  | idx y =>
    intro _ l l' hy
    have hy := hy y (by simp [Ty.freeIdx])
    simp only [Ty.substAll, Ty.subst, Subst.all, List.getElem?_append_left hy]
  | recv _ => intro h; exact h.elim
  | dt _ _ => intro h; exact h.elim
  | defn _ _ _ => intro h; exact h.elim
  | group _ _ => intro h; exact h.elim
  | sub _ _ _ _ _ => intro h; exact h.elim
  | cons a l iha ihl =>
    intro hs l₁ l₂ hy
    simp only [Ty.substAll, Ty.subst] at iha ihl ⊢
    rw [iha hs.1 l₁ l₂ (fun y h => hy y (by simp [Ty.freeIdx, h])),
      ihl hs.2 l₁ l₂ (fun y h => hy y (by simp [Ty.freeIdx, h]))]
  | func a l iha ihl =>
    intro hs l₁ l₂ hy
    simp only [Ty.substAll, Ty.subst] at iha ihl ⊢
    rw [iha hs.1 l₁ l₂ (fun y h => hy y (by simp [Ty.freeIdx, h])),
      ihl hs.2 l₁ l₂ (fun y h => hy y (by simp [Ty.freeIdx, h]))]
  | use u ih =>
    intro hs l₁ l₂ hy; simp only [Ty.substAll, Ty.subst] at ih ⊢; rw [ih hs l₁ l₂ hy]
  | ref _ h ih =>
    intro hs l₁ l₂ hy; simp only [Ty.substAll, Ty.subst] at ih ⊢; rw [ih hs l₁ l₂ hy]
  | refv r ih =>
    intro hs l₁ l₂ hy; simp only [Ty.substAll, Ty.subst] at ih ⊢; rw [ih hs l₁ l₂ hy]
  | val t ih =>
    intro hs l₁ l₂ hy; simp only [Ty.substAll, Ty.subst] at ih ⊢; rw [ih hs l₁ l₂ hy]
  | field _ s ih =>
    intro hs l₁ l₂ hy; simp only [Ty.substAll, Ty.subst] at ih ⊢; rw [ih hs l₁ l₂ hy]
  | struct fs ih =>
    intro hs l₁ l₂ hy; simp only [Ty.substAll, Ty.subst] at ih ⊢; rw [ih hs l₁ l₂ hy]
  | array f ih =>
    intro hs l₁ l₂ hy; simp only [Ty.substAll, Ty.subst] at ih ⊢; rw [ih hs l₁ l₂ hy]
  | _ => intro _ _ _ _; rfl

open RollClosed in
/-- **Expansion of a defined type of the type section** is the closure of its source
composite type against all the types. -/
theorem TypesOk.expand_eq {C : Context} {rts : List RecType} {dts : List DefType}
    (h : TypesOk C rts dts) : ∀ {t : Nat} {st : SubType} {d : DefType} {ct : CCompType},
      (rts.flatMap RecType.types)[t]? = some st → dts[t]? = some d → Expand d ct →
      ct = (liftComp st.body).substAll ((C.types ++ dts).map .dt) := by
  induction h with
  | nil => intro t st d ct _ hd; simp at hd
  | @cons C rt rts dts hok hs ih =>
    intro t st d ct hst hd he
    have hlenG := C.length_rollGroup rt
    by_cases ht : t < rt.types.length
    · rw [List.flatMap_cons, List.getElem?_append_left ht, List.getElem?_eq_getElem ht,
        Option.some.injEq] at hst
      subst hst
      rw [List.getElem?_append_left (by rw [hlenG]; exact ht), RollClosed.rollGroup_eq,
        List.getElem?_map, List.getElem?_range ht, Option.map_some, Option.some.injEq] at hd
      subst hd
      have hC' : ({ C with types := C.types ++ C.rollGroup rt } : Context).types =
          Dof C.types rt.types := by
        show C.types ++ C.rollGroup rt = _
        rw [RollClosed.rollGroup_eq]
      obtain ⟨heu⟩ := he
      rw [unrolldt_defn, RollClosed.member_eq _ _ ht] at heu
      simp only [Option.map_some, Ty.subst, Option.some.injEq, Ty.sub.injEq] at heu
      obtain ⟨-, -, hct⟩ := heu
      rw [← hct, ← RollClosed.closeComp_eq hC' hok ht]
      simp only [Context.closeComp]
      show (liftComp rt.types[t].body).substAll ((C.types ++ C.rollGroup rt).map .dt) = _
      have hb : ∀ y ∈ (liftComp rt.types[t].body).freeIdx,
          y < ((C.types ++ C.rollGroup rt).map Ty.dt).length := by
        intro y hy
        have := (RollClosed.bound_of_ok hC' hok ht).1 y hy
        simp [hlenG]; omega
      rw [show (C.types ++ (C.rollGroup rt ++ dts)).map Ty.dt =
          (C.types ++ C.rollGroup rt).map Ty.dt ++ dts.map Ty.dt by simp,
        substAll_append_of_bound _ (src_liftComp _) _ _ hb]
    · have ht' : rt.types.length ≤ t := by omega
      rw [List.flatMap_cons, List.getElem?_append_right ht'] at hst
      rw [List.getElem?_append_right (by rw [hlenG]; exact ht'), hlenG] at hd
      rw [ih hst hd he]
      simp [List.append_assoc]

/-! ## Module plumbing -/

open ModuleWf in
/-- The function part of a valid module: its context is well formed and the function
list may be replaced by any other list with the same function types. -/
theorem ModuleOk.funcs_part {m : Module} {mt : CModuleType} (h : ModuleOk m mt) :
    ∃ (dts : List DefType) (xtI : List CExternType) (fdts : List DefType) (C : Context),
      TypesOk {} m.types dts ∧ C.Wf ∧ C.types = dts ∧ C.recs = [] ∧
      C.funcs = CExternType.funcs xtI ++ fdts ∧
      List.Forall₂ (ImportOk { types := dts }) m.imports xtI ∧
      List.Forall₂ (FuncOk C) m.funcs fdts ∧
      ∀ fs : List Func, List.Forall₂ (FuncOk C) fs fdts → ModuleOk { m with funcs := fs } mt := by
  obtain ⟨htypes, himports, hC', hC, htags, hglobals, hmems, htables, hfuncs, hdata,
    helems, hstart, hexports, hnd⟩ := h
  rename_i dts xtI jts gts tts fdts rts xtE C' C
  have hΔ := typeCtx_ok htypes
  have hX := externs_tyOk (Δ := { types := dts }) (xs := xtI) (fun xt hxt => by
    obtain ⟨_, _, hi⟩ := forall₂_mem_right himports xt hxt
    exact hi.2)
  obtain ⟨hXt, hXg, hXtb, hXf⟩ := hX
  have hFd := funcs_mem hfuncs
  have hCt : C.types = dts := by rw [hC, hC']
  have hFty : ∀ d ∈ fdts, TyOk ({ types := dts } : TypeCtx) d := fun d hd =>
    (hΔ d (hCt ▸ hFd d hd)).2
  have hW : C.Wf := by
    subst hC hC'
    refine ⟨hΔ, ?_, ?_, ?_, ?_, by simp, by simp, by simp, ?_⟩
    · intro d hd
      rcases List.mem_append.1 hd with hd | hd
      · exact hXt d hd
      · obtain ⟨_, _, ht⟩ := forall₂_mem_right htags d hd
        exact ht.2.1
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact hXg g hg
      · exact globalsOk_tyOk hglobals rfl g hg
    · intro t ht
      rcases List.mem_append.1 ht with ht | ht
      · exact hXtb t ht
      · obtain ⟨_, _, ht'⟩ := forall₂_mem_right htables t ht
        exact ht'.2.1.2
    · intro d hd
      rcases List.mem_append.1 hd with hd | hd
      · exact hXf d hd
      · exact hFty d hd
    · intro rt hrt
      obtain ⟨_, _, he⟩ := forall₂_mem_right helems rt hrt
      exact he.2.1
  refine ⟨dts, xtI, fdts, C, htypes, hW, hCt, by rw [hC, hC'], by rw [hC, hC'], himports, hfuncs,
    fun fs hfs => ?_⟩
  exact ModuleOk.mk htypes himports hC' hC htags hglobals hmems htables hfs hdata helems hstart
    hexports hnd

/-- Imported functions and the function part of the import types line up. -/
theorem importOk_funcs_length {C : Context} : ∀ {ims : List Import} {xts : List CExternType},
    List.Forall₂ (ImportOk C) ims xts →
      (CExternType.funcs xts).length =
        (ims.filterMap fun e => match e.type with | .func t => some t | _ => none).length
  | [], [], .nil => rfl
  | im :: ims, xt :: xts, .cons h hs => by
    have ih := importOk_funcs_length hs
    obtain ⟨h₁, -⟩ := h
    rcases im with ⟨mo, nm, ty⟩
    cases ty with
    | func x =>
      simp only [Context.closeExtern?, Option.map_eq_some_iff] at h₁
      obtain ⟨d, -, rfl⟩ := h₁
      simp [CExternType.funcs, ih]
    | tag x =>
      simp only [Context.closeExtern?, Option.map_eq_some_iff] at h₁
      obtain ⟨d, -, rfl⟩ := h₁
      simp [CExternType.funcs, ih]
    | global g =>
      simp only [Context.closeExtern?, Option.some.injEq] at h₁
      subst h₁
      simp [CExternType.funcs, ih]
    | memory mm =>
      simp only [Context.closeExtern?, Option.some.injEq] at h₁
      subst h₁
      simp [CExternType.funcs, ih]
    | table t =>
      simp only [Context.closeExtern?, Option.some.injEq] at h₁
      subst h₁
      simp [CExternType.funcs, ih]

/-- A successful `mapM` relates inputs and outputs pointwise. -/
theorem mapM_some_forall₂ {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → List.Forall₂ (fun a b => f a = some b) l l'
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact .nil
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hml : l.mapM f with
      | none => simp [hfa, hml] at h
      | some bs =>
        simp only [hfa, hml, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        exact .cons hfa (mapM_some_forall₂ hml)

/-- Every list of valid source types has local types. -/
theorem localsOk_of_tyOk {C : Context} : ∀ (ts : List ValType),
    (∀ t ∈ ts, TyOk C.toTypeCtx (C.closeVal t)) →
      ∃ lts, List.Forall₂ (LocalOk C) ts lts ∧ lts.map LocalType.type = ts.map C.closeVal
  | [], _ => ⟨[], .nil, rfl⟩
  | t :: ts, h => by
    obtain ⟨lts, h₁, h₂⟩ := localsOk_of_tyOk ts (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
    by_cases hd : Defaultable (C.closeVal t)
    · exact ⟨_ :: lts, .cons (.set (h t (List.mem_cons_self ..)) hd) h₁, by simp [h₂]⟩
    · exact ⟨_ :: lts, .cons (.unset (h t (List.mem_cons_self ..)) hd) h₁, by simp [h₂]⟩

theorem LocalsLe.append (L M : List LocalType) : LocalsLe L (L ++ M) := by
  intro y a hy
  have hl : y < L.length := by
    rcases Nat.lt_or_ge y L.length with h | h
    · exact h
    · simp [List.getElem?_eq_none h] at hy
  exact ⟨a.init, by rw [List.getElem?_append_left hl, hy], id⟩

theorem LocalsLe.initLocals_self (C : Context) (xs : List Nat) :
    LocalsLe C.locals (C.initLocals xs).locals := by
  intro y a hy
  rw [Context.initLocals_locals]
  split
  · exact ⟨.set, by simp [hy], fun _ => rfl⟩
  · exact ⟨a.init, by rw [hy], id⟩

/-- `Forall₂` survives replacing one element by a related one. -/
theorem forall₂_modifyAt {α β : Type} {R : α → β → Prop} (f : α → α) :
    ∀ (n : Nat) {l : List α} {l' : List β}, List.Forall₂ R l l' →
      (∀ a b, l[n]? = some a → l'[n]? = some b → R (f a) b) →
      List.Forall₂ R (modifyAt f n l) l'
  | n, [], [], .nil, _ => by cases n <;> exact .nil
  | 0, a :: l, b :: l', .cons h hs, hf => .cons (hf a b rfl rfl) hs
  | n + 1, a :: l, b :: l', .cons h hs, hf =>
    .cons h (forall₂_modifyAt f n hs fun a' b' h₁ h₂ => hf a' b' h₁ h₂)

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ {i : Nat} {a : α}, l[i]? = some a →
      ∃ b, l'[i]? = some b ∧ R a b
  | [], [], .nil, _, _, h => by simp at h
  | _ :: _, b :: _, .cons hab _, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; exact ⟨b, rfl, hab⟩
  | _ :: _, _ :: _, .cons _ hs, i + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact forall₂_getElem? hs h

theorem forall₂_exists_of_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ {a : α}, a ∈ l → ∃ b, R a b
  | [], [], .nil, _, h => by simp at h
  | _ :: _, b :: _, .cons hab hs, _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨b, hab⟩
    · exact forall₂_exists_of_mem hs h

theorem forall₂_append' {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {l₁' l₂' : List β}, List.Forall₂ R l₁ l₁' → List.Forall₂ R l₂ l₂' →
      List.Forall₂ R (l₁ ++ l₂) (l₁' ++ l₂')
  | [], _, [], _, .nil, h => h
  | _ :: _, _, _ :: _, _, .cons h hs, h₂ => .cons h (forall₂_append' hs h₂)

theorem forall₂_length {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → l.length = l'.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ hs => by simp [forall₂_length hs]

theorem ofNat?_some {k : IndexKind} {n : Nat} {x : Idx k} (h : Idx.ofNat? n = some x) :
    x.toNat = n ∧ n < 2 ^ 32 := by
  unfold Idx.ofNat? at h
  split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · cases h

/-- `initLocals` keeps the types of locals. -/
theorem initLocals_type {C : Context} {xs : List Nat} {y : Nat} {i : Init} {t : CValType}
    (h : C.locals[y]? = some ⟨i, t⟩) : ∃ i', (C.initLocals xs).locals[y]? = some ⟨i', t⟩ := by
  rw [Context.initLocals_locals]
  split
  · exact ⟨.set, by simp [h]⟩
  · exact ⟨i, h⟩

/-- `initLocals` sets a member of the list with its type. -/
theorem initLocals_mem_type {C : Context} {xs : List Nat} {y : Nat} {i : Init} {t : CValType}
    (hy : y ∈ xs) (h : C.locals[y]? = some ⟨i, t⟩) :
    (C.initLocals xs).locals[y]? = some ⟨.set, t⟩ := by
  rw [Context.initLocals_locals]
  simp [hy, h]

theorem expand_det {d : DefType} {ct ct' : CCompType} (h : Expand d ct) (h' : Expand d ct') :
    ct = ct' := by
  rw [Expand.iff] at h h'
  rw [h] at h'
  exact Option.some.inj h'

end InlineTy

end Silmaril.Wasm.Binaryen
