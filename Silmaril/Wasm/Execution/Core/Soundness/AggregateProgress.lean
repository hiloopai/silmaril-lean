module

public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Execution.Core.Soundness.StateFacts
public import Silmaril.Wasm.Execution.Core.Soundness.AggregatePres

@[expose] public section

/-! # Soundness, aggregate family: progress

`RefInstrOk.progress_aggregate'`: every well-typed GC aggregate instruction applied
to well-typed operands has an `AggregateStep`.

**Statement change.** The statement of `RefInstrOk.progress_aggregate` is false as
stated: `StoreOk` (like the spec's `Structinst_ok`/`Arrayinst_ok`) does not require the
defined type of a struct/array instance to be valid, and an invalid defined type can
declare an arbitrary supertype. E.g. an array instance whose type is
`rec (sub (dt d) (array ft))` with `d` a struct type is typed at `ref d` by
`Ref_ok/sub` (`Deftype_sub/super`), and `struct.get` on it is stuck. The theorem below
adds the hypotheses `hsty`/`haty` (instance types are valid), which are preserved by
reduction (instances are only allocated at types `f.type? x` of the current frame).
These are now `StoreOk` deviation fields (`structsClosed`/`arraysClosed`), so
`RefInstrOk.progress_aggregate` (Soundness/Aggregate.lean) keeps its original statement.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

namespace AP

/-! ## Struct widths and subtyping -/

def compWidth : CCompType → Nat
  | .struct fs => fs.length
  | _ => 0

theorem compWidth_subst (σ : Subst) (ct : CCompType) : compWidth (ct.subst σ) = compWidth ct := by
  cases ct <;> simp [compWidth, Ty.subst, Ty.length_subst]

def defWidth (d : DefType) : Nat := ((unrolldt d).map fun st => compWidth st.body).getD 0

theorem expand_defWidth {d : DefType} {ct : CCompType} (h : Expand d ct) :
    defWidth d = compWidth ct := by
  cases h with | mk h => simp [defWidth, h, Ty.body]

theorem defWidth_subst (σ : Subst) (hσ : ∀ i, σ (.recv i) = none)
    (hσu : ∀ x u, σ (.idx x) = some u → u.RecFree) (d : DefType) :
    defWidth (d.subst σ) = defWidth d := by
  simp only [defWidth, unrolldt_subst σ hσ hσu, Option.map_map]
  cases unrolldt d with
  | none => rfl
  | some st =>
    cases st with
    | sub fin sups b => simp [Ty.subst, Ty.body, compWidth_subst]

theorem defWidth_clos (T : List DefType) (d : DefType) : defWidth (d.clos T) = defWidth d :=
  defWidth_subst _ (fun _ => rfl)
    (fun x u h => by
      simp only [Subst.all, List.getElem?_map] at h
      cases hx : (closDefTypes T)[x]? with
      | none => simp [hx] at h
      | some e => simp [hx] at h; subst h; exact Ty.recFree_dt e) d

def useWidth (Δ : TypeCtx) : CTypeUse → Nat
  | .dt d => defWidth d
  | .idx x => ((Δ.types[x]?).map defWidth).getD 0
  | .recv _ => 0

def heapWidth (Δ : TypeCtx) : CHeapType → Nat
  | .use u => useWidth Δ u
  | _ => 0

theorem Sub.list_length {Δ : TypeCtx} {k : TKind} :
    ∀ {l l' : Ty (.list k)}, Sub Δ l l' → l.length = l'.length
  | _, _, .nil => rfl
  | _, _, .cons _ hl => by
    have := Sub.list_length hl
    simp only [Ty.length, Ty.toList_cons, List.length_cons] at this ⊢
    omega

theorem Sub.compWidth_le {Δ : TypeCtx} {a b : CCompType} (h : Sub Δ a b) :
    compWidth b ≤ compWidth a := by
  cases h with
  | struct h =>
    have := Sub.list_length h
    simp only [compWidth, Ty.length, Ty.toList_app, List.length_append] at this ⊢
    omega
  | array _ => simp [compWidth]
  | func _ _ => simp [compWidth]

/-- A valid defined type's declared supertypes are no wider. -/
theorem TyOk.super_width {Δ : TypeCtx} {d : DefType} (hd : TyOk Δ d) {fin : Bool}
    {sups : Ty (.list .use)} {ct : CCompType} (hu : unrolldt d = some (.sub fin sups ct))
    {j : Nat} {u : CTypeUse} (hj : sups.toList[j]? = some u) :
    useWidth Δ u ≤ compWidth ct := by
  cases hd with
  | @defn _ subs i hg hi =>
    simp only [unrolldt, unrollrt, Ty.subs] at hu
    rw [Ty.toList_subst, List.getElem?_map] at hu
    cases hst : subs.toList[i]? with
    | none => simp [hst] at hu
    | some st =>
      rw [hst] at hu
      simp only [Option.map_some, Option.some.injEq] at hu
      have hso := GroupOk2.get subs hg hst
      cases st with
      | sub fin0 sups0 ct0 =>
        simp only [Ty.subst, Ty.sub.injEq] at hu
        obtain ⟨-, rfl, rfl⟩ := hu
        cases hso with
        | noSuper =>
          have := (List.getElem?_eq_some_iff.1 hj).1
          exact absurd this (Nat.not_lt_zero _)
        | @oneSuper _ _ u0 _ _ sups' ct' hu0 hb hunroll hct hsub =>
          simp only [Ty.subst, Ty.toList_cons, Ty.toList_nil] at hj
          have hj0 : j = 0 := by
            rcases j with _ | j
            · rfl
            · simp at hj
          subst hj0
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          rw [compWidth_subst]
          refine le_trans (le_of_eq ?_) (Sub.compWidth_le hsub)
          cases u0 with
          | idx x =>
            cases hu0 with
            | idx hx =>
              try simp only [Ty.subst, Option.getD_none]
              obtain ⟨e, hx'⟩ : ∃ e, Δ.types[x]? = some e := ⟨_, hx⟩
              have h2 : (Δ.withRecs subs.toList).unrollUse (.idx x) = unrolldt e := by
                simp [TypeCtx.unrollUse, TypeCtx.withRecs, hx']
              rw [h2] at hunroll
              simp only [useWidth, hx']
              simp [defWidth, hunroll, Ty.body]
          | recv j' =>
            cases hu0 with
            | recv hr =>
              have hj' : j' < subs.length := by
                have := (List.getElem?_eq_some_iff.1 hr).1
                simpa [TypeCtx.withRecs, Ty.length] using this
              simp only [Ty.subst, hj', ite_true, Option.getD_some]
              simp only [TypeCtx.unrollUse, TypeCtx.withRecs] at hunroll
              simp only [useWidth, defWidth, unrolldt, unrollrt, Ty.subs, Ty.toList_subst,
                List.getElem?_map, hunroll, Option.map_some, Ty.subst, Ty.body, compWidth_subst,
                Option.getD_some]
          | dt e =>
            rw [Ty.recFree_dt e _ (fun _ => rfl)]
            cases hu0 with
            | dt he =>
              simp only [TypeCtx.unrollUse] at hunroll
              simp [useWidth, defWidth, hunroll, Ty.body]

/-- Motive of `Sub.width`, by sort. -/
def WMotive (Δ : TypeCtx) : (k : TKind) → Ty k → Ty k → Prop
  | .heap, a, b => HeapUpV Δ .struct a → heapWidth Δ b ≤ heapWidth Δ a
  | .def, a, b => TyOk Δ a → defKind a = some .struct → defWidth b ≤ defWidth a
  | _, _, _ => True

/-- **Width subtyping.** Supertypes of a valid struct type have no more fields. -/
theorem Sub.width {Δ : TypeCtx}
    (hT : ∀ (x : Nat) (d : DefType), Δ.types[x]? = some d → TyOk Δ d) :
    ∀ {k : TKind} {a b : Ty k}, Sub Δ a b → WMotive Δ k a b
  | _, _, _, .heapRefl => by intro _; exact le_refl _
  | _, _, _, .heapTrans hok h₁ h₂ => by
    have ih₁ := Sub.width hT h₁
    have ih₂ := Sub.width hT h₂
    have up₁ := Core.Sub.up hT h₁
    dsimp only [WMotive, UpMotive] at ih₁ ih₂ up₁ ⊢
    intro hc
    exact le_trans (ih₂ (HeapUpV.of_ok (up₁ _ hc) hok)) (ih₁ hc)
  | _, _, _, .eqAny => by intro _; simp [heapWidth]
  | _, _, _, .i31Eq => by intro _; simp [heapWidth]
  | _, _, _, .structEq => by intro _; simp [heapWidth]
  | _, _, _, .arrayEq => by intro _; simp [heapWidth]
  | _, _, _, .defStruct _ => by intro _; simp [heapWidth]
  | _, _, _, .defArray _ => by intro _; simp [heapWidth]
  | _, _, _, .defFunc _ => by intro _; simp [heapWidth]
  | _, _, _, @Sub.defDef _ d₁ d₂ h => by
    have ih := Sub.width hT h
    dsimp only [WMotive] at ih ⊢
    intro hc
    have hk : defKind d₁ = some AbsHeapType.struct := by simpa [HeapUp, useKind] using hc.1
    exact ih (hc.2 d₁ rfl) hk
  | _, _, _, .idxL hx hs => by
    have ih := Sub.width hT hs
    dsimp only [WMotive] at ih ⊢
    intro hc
    have := ih ⟨by
      have := hc.1
      simp only [HeapUp, useKind, hx] at this ⊢
      exact this, fun d hd => by cases hd; exact hT _ _ hx⟩
    simpa [heapWidth, useWidth, hx] using this
  | _, _, _, .idxR hx hs => by
    have ih := Sub.width hT hs
    dsimp only [WMotive] at ih ⊢
    intro hc
    simpa [heapWidth, useWidth, hx] using ih hc
  | _, _, _, .recStruct _ => by intro hc; exact absurd hc.1 (by simp [HeapUp, useKind])
  | _, _, _, .recArray _ => by intro hc; exact absurd hc.1 (by simp [HeapUp, useKind])
  | _, _, _, .recFunc _ => by intro hc; exact absurd hc.1 (by simp [HeapUp, useKind])
  | _, _, _, .recSub _ _ => by intro hc; exact absurd hc.1 (by simp [HeapUp, useKind])
  | _, _, _, .none _ _ => by intro hc; exact absurd hc.1 (by simp [HeapUp, absUp])
  | _, _, _, .nofunc _ _ => by intro hc; exact absurd hc.1 (by simp [HeapUp, absUp])
  | _, _, _, .noexn _ _ => by intro hc; exact absurd hc.1 (by simp [HeapUp, absUp])
  | _, _, _, .noextern _ _ => by intro hc; exact absurd hc.1 (by simp [HeapUp, absUp])
  | _, _, _, .bot => by intro hc; exact absurd hc.1 (by simp [HeapUp])
  | _, _, _, .refNonNull _ => trivial
  | _, _, _, .refNull _ => trivial
  | _, _, _, .num => trivial
  | _, _, _, .vec => trivial
  | _, _, _, .refv _ => trivial
  | _, _, _, .botv => trivial
  | _, _, _, .val _ => trivial
  | _, _, _, .pack => trivial
  | _, _, _, .fieldConst _ => trivial
  | _, _, _, .fieldVar _ _ => trivial
  | _, _, _, .struct _ => trivial
  | _, _, _, .array _ => trivial
  | _, _, _, .func _ _ => trivial
  | _, _, _, @Sub.defRefl _ d₁ d₂ h => by
    intro _ _
    show defWidth d₂ ≤ defWidth d₁
    rw [← defWidth_clos Δ.types d₂, ← h, defWidth_clos]
  | _, _, _, @Sub.defSuper _ d₁ d₂ _ _ ct _ u hu hj hs => by
    intro hd hc
    obtain ⟨hk, hok⟩ := TyOk.super_kind hd hu hj
    have hw := TyOk.super_width hd hu hj
    have ih := Sub.width hT hs
    dsimp only [WMotive] at ih
    have hc' : compKind ct = .struct := by simpa [defKind, hu, Ty.body] using hc
    rw [hc'] at hk
    have := ih (HeapUpV.of_ok hk hok)
    have e : defWidth d₁ = compWidth ct := by simp [defWidth, hu, Ty.body]
    have e2 : heapWidth Δ (.use (.dt d₂)) = defWidth d₂ := rfl
    have e3 : heapWidth Δ (.use u) = useWidth Δ u := rfl
    show defWidth d₂ ≤ defWidth d₁
    rw [e2, e3] at this
    omega
  | _, _, _, .nil => trivial
  | _, _, _, .cons _ _ => trivial

/-! ## Classification of typed references -/

def refClass : Ref → AbsHeapType
  | .i31 _ => .i31
  | .struct _ => .struct
  | .array _ => .array
  | .func _ => .func
  | .exn _ => .exn
  | .host _ => .any
  | .extern _ => .extern
  | .null => .none

theorem RefBase.heapUp {s : Store H} {f : Frame} {C : Context} (hst : StateOk s f C)
    (hsty : ∀ si ∈ s.structs, TyOk {} si.type) (haty : ∀ ai ∈ s.arrays, TyOk {} ai.type)
    {r : Ref} {n₀ : Bool} {h₀ h : CHeapType} (hb : RefBase s r (.ref n₀ h₀)) (hr : r ≠ .null)
    (hsub : Sub C.toTypeCtx h₀ h) : HeapUp C.toTypeCtx (refClass r) h := by
  have hT := hst.2.typesOk
  have up := Core.Sub.up hT hsub
  dsimp only [UpMotive] at up
  cases hb with
  | null => exact absurd rfl hr
  | i31 b => exact up _ ⟨by simp [HeapUp, absUp, refClass], fun d hd => by cases hd⟩
  | struct h =>
    obtain ⟨fs, he⟩ := hst.1.struct_expand h
    exact up _ ⟨by simpa [HeapUp, useKind, Ty.defHeap, refClass, compKind] using expand_defKind he,
      fun d hd => by
        simp only [Ty.defHeap] at hd; cases hd
        exact TyOk.ofEmpty (hsty _ (List.mem_of_getElem? h)) _⟩
  | array h =>
    obtain ⟨ft, he⟩ := hst.1.array_expand h
    exact up _ ⟨by simpa [HeapUp, useKind, Ty.defHeap, refClass, compKind] using expand_defKind he,
      fun d hd => by
        simp only [Ty.defHeap] at hd; cases hd
        exact TyOk.ofEmpty (haty _ (List.mem_of_getElem? h)) _⟩
  | func h =>
    obtain ⟨hok, hk⟩ := hst.1.func_kind h
    exact up _ ⟨by simpa [HeapUp, useKind, Ty.defHeap, refClass] using hk,
      fun d hd => by simp only [Ty.defHeap] at hd; cases hd; exact TyOk.ofEmpty hok _⟩
  | exn h => exact up _ ⟨by simp [HeapUp, absUp, refClass], fun d hd => by cases hd⟩
  | host a => exact up _ ⟨by simp [HeapUp, absUp, refClass], fun d hd => by cases hd⟩
  | extern h hn => exact up _ ⟨by simp [HeapUp, absUp, refClass], fun d hd => by cases hd⟩

theorem ValOk.array_inv {s : Store H} {f : Frame} {C : Context} (hst : StateOk s f C)
    (hsty : ∀ si ∈ s.structs, TyOk {} si.type) (haty : ∀ ai ∈ s.arrays, TyOk {} ai.type)
    {v : Val} {n : Bool} {h : CHeapType} (hv : ValOk s v (Ty.refT n h))
    (hh : ∀ c, HeapUp C.toTypeCtx c h → c = .array) :
    v = .ref .null ∨ ∃ a ai, v = .ref (.array a) ∧ s.arrays[a]? = some ai := by
  obtain ⟨r, rfl, hr⟩ := ValOk.refv_inv hv
  obtain ⟨rt₀, hb, hs₀⟩ := hr.principal_sub (Δ := C.toTypeCtx)
    (Sub.refl _ (k := .ref) trivial _)
  cases rt₀ with
  | ref n₀ h₀ =>
    by_cases hn : r = .null
    · subst hn; exact .inl rfl
    have hc := hh _ (RefBase.heapUp hst hsty haty hb hn (Core.Sub.ref_inv hs₀).1)
    cases hb with
    | array ha => exact .inr ⟨_, _, rfl, ha⟩
    | null => exact absurd rfl hn
    | _ => simp [refClass] at hc

theorem ValOk.struct_inv {s : Store H} {f : Frame} {C : Context} (hst : StateOk s f C)
    (hsty : ∀ si ∈ s.structs, TyOk {} si.type) (haty : ∀ ai ∈ s.arrays, TyOk {} ai.type)
    {v : Val} {n : Bool} {h : CHeapType} (hv : ValOk s v (Ty.refT n h))
    (hh : ∀ c, HeapUp C.toTypeCtx c h → c = .struct) :
    v = .ref .null ∨ ∃ a si, v = .ref (.struct a) ∧ s.structs[a]? = some si ∧
      Sub C.toTypeCtx (Ty.defHeap si.type) h := by
  obtain ⟨r, rfl, hr⟩ := ValOk.refv_inv hv
  obtain ⟨rt₀, hb, hs₀⟩ := hr.principal_sub (Δ := C.toTypeCtx)
    (Sub.refl _ (k := .ref) trivial _)
  cases rt₀ with
  | ref n₀ h₀ =>
    by_cases hn : r = .null
    · subst hn; exact .inl rfl
    have hc := hh _ (RefBase.heapUp hst hsty haty hb hn (Core.Sub.ref_inv hs₀).1)
    cases hb with
    | struct ha => exact .inr ⟨_, _, rfl, ha, (Core.Sub.ref_inv hs₀).1⟩
    | null => exact absurd rfl hn
    | _ => simp [refClass] at hc

theorem heapUp_def {Δ : TypeCtx} {d : DefType} {ct : CCompType} (he : Expand d ct) :
    ∀ c, HeapUp Δ c (Ty.defHeap d) → c = compKind ct := by
  intro c hc
  simp only [HeapUp, Ty.defHeap, useKind, expand_defKind he, Option.some.injEq] at hc
  exact hc.symm

theorem heapUp_array {Δ : TypeCtx} : ∀ c, HeapUp Δ c (.abs .array) → c = .array := by
  intro c hc; cases c <;> simp_all [HeapUp, absUp]

/-! ## Operand lists -/

theorem forall₂_one {α β : Type} {R : α → β → Prop} {l : List α} {b : β}
    (h : List.Forall₂ R l [b]) : ∃ a, l = [a] ∧ R a b := by
  cases h with | cons h1 h => cases h; exact ⟨_, rfl, h1⟩

theorem forall₂_two {α β : Type} {R : α → β → Prop} {l : List α} {b₁ b₂ : β}
    (h : List.Forall₂ R l [b₁, b₂]) : ∃ a₁ a₂, l = [a₁, a₂] ∧ R a₁ b₁ ∧ R a₂ b₂ := by
  cases h with | cons h1 h => cases h with | cons h2 h => cases h; exact ⟨_, _, rfl, h1, h2⟩

theorem forall₂_three {α β : Type} {R : α → β → Prop} {l : List α} {b₁ b₂ b₃ : β}
    (h : List.Forall₂ R l [b₁, b₂, b₃]) :
    ∃ a₁ a₂ a₃, l = [a₁, a₂, a₃] ∧ R a₁ b₁ ∧ R a₂ b₂ ∧ R a₃ b₃ := by
  cases h with
  | cons h1 h => cases h with
    | cons h2 h => cases h with
      | cons h3 h => cases h; exact ⟨_, _, _, rfl, h1, h2, h3⟩

theorem forall₂_four {α β : Type} {R : α → β → Prop} {l : List α} {b₁ b₂ b₃ b₄ : β}
    (h : List.Forall₂ R l [b₁, b₂, b₃, b₄]) :
    ∃ a₁ a₂ a₃ a₄, l = [a₁, a₂, a₃, a₄] ∧ R a₁ b₁ ∧ R a₂ b₂ ∧ R a₃ b₃ ∧ R a₄ b₄ := by
  cases h with
  | cons h1 h => cases h with
    | cons h2 h => cases h with
      | cons h3 h => cases h with
        | cons h4 h => cases h; exact ⟨_, _, _, _, rfl, h1, h2, h3, h4⟩

theorem forall₂_five {α β : Type} {R : α → β → Prop} {l : List α} {b₁ b₂ b₃ b₄ b₅ : β}
    (h : List.Forall₂ R l [b₁, b₂, b₃, b₄, b₅]) :
    ∃ a₁ a₂ a₃ a₄ a₅, l = [a₁, a₂, a₃, a₄, a₅] ∧ R a₁ b₁ ∧ R a₂ b₂ ∧ R a₃ b₃ ∧ R a₄ b₄ ∧
      R a₅ b₅ := by
  cases h with
  | cons h1 h => cases h with
    | cons h2 h => cases h with
      | cons h3 h => cases h with
        | cons h4 h => cases h with
          | cons h5 h => cases h; exact ⟨_, _, _, _, _, rfl, h1, h2, h3, h4, h5⟩

theorem mapM_some_of_isSome {α β : Type} (g : α → Option β) :
    ∀ (l : List α), (∀ x ∈ l, (g x).isSome) → ∃ r, l.mapM g = some r
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h x (by simp))
    obtain ⟨r, hr⟩ := mapM_some_of_isSome g l (fun y hy => h y (by simp [hy]))
    exact ⟨b :: r, by simp [List.mapM_cons, hb, hr]⟩

/-! ## Reading fields from data segments -/

theorem load_isSome {bytes : ByteArray} {off n : Nat} (h : off + n ≤ bytes.size) :
    (Memory.load bytes off n).isSome := by
  simp [Memory.load, Memory.readBytes, h]

theorem storageSize_mod {z : CStorageType} (hz : z.unpack.IsNumOrVec) :
    storageSize z % 8 = 0 := by
  cases z with
  | val t =>
    cases t with
    | num t => cases t with
      | int t => cases t <;> rfl
      | float t => cases t <;> rfl
    | vec _ => simp [storageSize]
    | refv _ => simp [Ty.unpack, Ty.IsNumOrVec] at hz
    | botv => simp [Ty.unpack, Ty.IsNumOrVec] at hz
  | pack p => cases p <;> rfl

theorem storageSize_pos {z : CStorageType} (hz : z.unpack.IsNumOrVec) : 0 < storageSize z := by
  cases z with
  | val t =>
    cases t with
    | num t => cases t with
      | int t => cases t <;> decide
      | float t => cases t <;> decide
    | vec _ => simp [storageSize]
    | refv _ => simp [Ty.unpack, Ty.IsNumOrVec] at hz
    | botv => simp [Ty.unpack, Ty.IsNumOrVec] at hz
  | pack p => cases p <;> decide

/-- A value typed at `$unpack(zt)` is in the domain of `$packfield_(zt, ·)`. -/
theorem packable_of_valOk {s : Store H} {z : CStorageType} {v : Val} (hv : ValOk s v z.unpack) :
    packable z v = true := by
  cases z with
  | val t => rfl
  | pack p => obtain ⟨b, rfl⟩ := ValOk.i32_invRT' hv; rfl

theorem packable_zip {s : Store H} {fts : List CFieldType} {vs : List Val}
    (h : List.Forall₂ (ValOk s) vs (fts.map fieldUnpack)) :
    ∀ p ∈ fts.zip vs, packable (fieldStorage p.1) p.2 = true := by
  induction fts generalizing vs with
  | nil => intro p hp; simp at hp
  | cons ft fts ih =>
    simp only [List.map_cons] at h
    cases h with
    | cons hv h =>
      intro p hp
      simp only [List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact packable_of_valOk (by rwa [fieldUnpack_eqAgg] at hv)
      · exact ih h p hp

theorem forall₂_replicate_memAP {α β : Type} {R : α → β → Prop} {b : β} {l : List α} {n : Nat}
    (h : List.Forall₂ R l (List.replicate n b)) : ∀ a ∈ l, R a b := by
  induction n generalizing l with
  | zero => simp only [List.replicate_zero, List.forall₂_nil_right_iff] at h; subst h; simp
  | succ n ih =>
    rw [List.replicate_succ] at h
    cases h with
    | cons hx h' =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hx
      · exact ih h' a ha

/-- A field value stored at a subtype of the static storage type `zt`, read with the
validated `sx?`, is in the domain of `$unpackfield_(zt, sx?, ·)`. -/
theorem unpackable_of_ok {s : Store H} {fv : FieldVal} {z' z : CStorageType}
    {sx : Option Signedness} (hfv : FieldValOk s fv z') (hz : Sub {} z' z)
    (hsx : sx.isSome = z.isPacked) : unpackable z sx fv = true := by
  cases hfv with
  | val hv =>
    cases hz with
    | val h =>
      cases sx with
      | none => rfl
      | some _ => simp [Ty.isPacked] at hsx
  | pack p b =>
    cases hz
    cases sx with
    | none => simp [Ty.isPacked] at hsx
    | some _ => simp [unpackable]

theorem readField?_isSome {z : CStorageType} (hz : z.unpack.IsNumOrVec) {bytes : ByteArray}
    {off : Nat} (h : off + storageSize z / 8 ≤ bytes.size) :
    (readField? z bytes off).isSome := by
  cases z with
  | val t =>
    cases t with
    | num t =>
      simp only [readField?, Option.isSome_map]
      exact load_isSome (by simpa [storageSize] using h)
    | vec _ =>
      simp only [readField?, Option.isSome_map]
      exact load_isSome (by simpa [storageSize] using h)
    | refv _ => simp [Ty.unpack, Ty.IsNumOrVec] at hz
    | botv => simp [Ty.unpack, Ty.IsNumOrVec] at hz
  | pack p =>
    simp only [readField?, Option.isSome_map]
    exact load_isSome (by simpa [storageSize] using h)

theorem readFields_some {z : CStorageType} (hz : z.unpack.IsNumOrVec) {bytes : ByteArray}
    {i n : Nat} (h : i + n * storageSize z / 8 ≤ bytes.size) :
    ∃ vs, (List.range n).mapM (fun k => readField? z bytes (i + k * (storageSize z / 8))) =
      some vs := by
  apply mapM_some_of_isSome
  intro k hk
  rw [List.mem_range] at hk
  apply readField?_isSome hz
  have hm := storageSize_mod hz
  rw [Nat.mul_div_assoc _ (Nat.dvd_of_mod_eq_zero hm)] at h
  have : (k + 1) * (storageSize z / 8) ≤ n * (storageSize z / 8) :=
    Nat.mul_le_mul_right _ hk
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

end AP

open AP

/-- **Progress (aggregate).** See the module doc for the added hypotheses `hsty`/`haty`. -/
theorem RefInstrOk.progress_aggregate' {P : Profile} {host : HostSemantics H} {s : Store H}
    {f : Frame} {C : Context} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    {vs : List Val} (hst : StateOk s f C)
    (hsty : ∀ si ∈ s.structs, TyOk {} si.type) (haty : ∀ ai ∈ s.arrays, TyOk {} ai.type)
    (hi : RefInstrOk C i ⟨t₁, xs, t₂⟩) (ha : i.IsAggregate)
    (hvs : List.Forall₂ (ValOk s) vs t₁) :
    ∃ c', Step P host ⟨s, f, vals vs ++ [.plain i]⟩ c' := by
  have htype : ∀ {x : TypeIdx} {d : DefType}, C.type? x = some d → f.type? x = some d :=
    fun hx => by rw [← hst.2.type?_eq]; exact hx
  cases hi with
  | structNew hd he =>
    have hl := hvs.length_eq
    simp only [List.length_map] at hl
    exact ⟨_, .aggregate (.structNew (htype hd) he (by simpa [Ty.length] using hl)
      (packable_zip hvs))⟩
  | structNewDefault hd he hdef =>
    cases hvs
    obtain ⟨r, hr⟩ := mapM_some_of_isSome (fun ft => defaultVal? (fieldStorage ft).unpack) _
      (fun ft hft => by
        rw [defaultVal?_isSome_iff]
        have := hdef ft hft
        cases ft with | field m z => exact this)
    exact ⟨_, .aggregate (.structNewDefault (htype hd) he hr)⟩
  | @structGet sx x fi d fs m z hd he hfi hsx =>
    obtain ⟨v, rfl, hv⟩ := forall₂_one hvs
    rcases ValOk.struct_inv hst hsty haty hv (heapUp_def he) with rfl | ⟨a, si, rfl, hsi, hsub⟩
    · exact ⟨_, .aggregate .structGetNull⟩
    · cases hv with | ref hr => ?_
      obtain ⟨si', fs', m', z', hsi', -, -, hz, -, -, hfvok⟩ :=
        structFieldAgg hst.1 ⟨hsty, haty⟩ hr (hst.typeAgg hd).2 he hfi
      rw [hsi] at hsi'; cases hsi'
      -- width: `si` has at least the fields of `d`
      have hT := hst.2.typesOk
      have hw := Sub.width hT hsub
      dsimp only [WMotive] at hw
      obtain ⟨fs₁, he₁, hf₁⟩ := hst.1.structs si (List.mem_of_getElem? hsi)
      have hw := hw ⟨by simpa [HeapUp, useKind, Ty.defHeap, compKind] using expand_defKind he₁,
        fun d' hd' => by
          simp only [Ty.defHeap] at hd'; cases hd'
          exact TyOk.ofEmpty (hsty _ (List.mem_of_getElem? hsi)) _⟩
      simp only [Ty.defHeap, heapWidth, useWidth, expand_defWidth he, expand_defWidth he₁,
        compWidth] at hw
      have hl := hf₁.length_eq
      simp only [List.length_map] at hl
      have hlt : fi.toNat < fs.toList.length := (List.getElem?_eq_some_iff.1 hfi).1
      have hlt' : fi.toNat < si.fields.length := by
        simp only [Ty.length] at hw; omega
      have hfv := List.getElem?_eq_getElem hlt'
      exact ⟨_, .aggregate (.structGetStruct hsi hfv (htype hd) he hfi
        (unpackable_of_ok (hfvok _ hfv) hz hsx))⟩
  | structSet hd he hfi =>
    obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := forall₂_two hvs
    rcases ValOk.struct_inv hst hsty haty hv₁ (heapUp_def he) with rfl | ⟨a, si, rfl, hsi, -⟩
    · exact ⟨_, .aggregate .structSetNull⟩
    · cases hv₁ with | ref hr => ?_
      obtain ⟨si', fs', m', z', hsi', he', hfi', -, -, -, -⟩ :=
        structFieldAgg hst.1 ⟨hsty, haty⟩ hr (hst.typeAgg hd).2 he hfi
      rw [hsi] at hsi'; cases hsi'
      obtain ⟨fs₁, he₁, hf₁⟩ := hst.1.structs si (List.mem_of_getElem? hsi)
      have e := Expand.func_eq he' he₁
      cases e
      have hlt := (List.getElem?_eq_some_iff.1 hfi').1
      have hl := hf₁.length_eq
      simp only [List.length_map] at hl
      rw [← hl] at hlt
      exact ⟨_, .aggregate (.structSetStruct (htype hd) he hfi hsi hlt (packable_of_valOk hv₂))⟩
  | arrayNew hd he =>
    obtain ⟨v, vn, rfl, -, hn⟩ := forall₂_two hvs
    obtain ⟨n, rfl⟩ := ValOk.i32_invRT' hn
    exact ⟨_, .aggregate (.arrayNew v n)⟩
  | @arrayNewDefault x d m z hd he hdef =>
    obtain ⟨vn, rfl, hn⟩ := forall₂_one hvs
    obtain ⟨n, rfl⟩ := ValOk.i32_invRT' hn
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1
      ((defaultVal?_isSome_iff z.unpack).2 hdef)
    exact ⟨_, .aggregate (.arrayNewDefault (n := n) (htype hd) he hv)⟩
  | arrayNewFixed hd he =>
    have hl := hvs.length_eq
    simp only [List.length_replicate] at hl
    exact ⟨_, .aggregate (.arrayNewFixed (htype hd) he hl
      (fun v hv => packable_of_valOk (forall₂_replicate_memAP hvs v hv)))⟩
  | arrayNewElem hd he hy hs =>
    obtain ⟨vi, vn, rfl, hi, hn⟩ := forall₂_two hvs
    obtain ⟨i, rfl⟩ := ValOk.i32_invRT' hi
    obtain ⟨n, rfl⟩ := ValOk.i32_invRT' hn
    obtain ⟨ea, ei, hei, -⟩ := hst.2.elem hy
    by_cases hle : i.toNat + n.toNat ≤ ei.refs.length
    · exact ⟨_, .aggregate (.arrayNewElemAlloc hei hle)⟩
    · exact ⟨_, .aggregate (.arrayNewElemOob hei (Nat.lt_of_not_le hle))⟩
  | @arrayNewData x y d m z hd he hnv hy =>
    obtain ⟨vi, vn, rfl, hi, hn⟩ := forall₂_two hvs
    obtain ⟨i, rfl⟩ := ValOk.i32_invRT' hi
    obtain ⟨n, rfl⟩ := ValOk.i32_invRT' hn
    obtain ⟨da, di, hdat⟩ := hst.2.data hy
    by_cases hb : i.toNat + n.toNat * storageSize (fieldStorage (.field m z)) / 8 ≤ di.bytes.size
    · obtain ⟨rs, hrs⟩ := readFields_some (z := z) hnv hb
      exact ⟨_, .aggregate (.arrayNewDataNum (htype hd) he hdat (storageSize_pos hnv) hb hrs)⟩
    · exact ⟨_, .aggregate (.arrayNewDataOob (htype hd) he hdat (storageSize_pos hnv)
        (Nat.lt_of_not_le hb))⟩
  | arrayGet hd he hsx =>
    obtain ⟨vr, vi, rfl, hr, hi⟩ := forall₂_two hvs
    obtain ⟨i, rfl⟩ := ValOk.i32_invRT' hi
    rcases ValOk.array_inv hst hsty haty hr (heapUp_def he) with rfl | ⟨a, ai, rfl, hai⟩
    · exact ⟨_, .aggregate .arrayGetNull⟩
    · by_cases hlt : i.toNat < ai.fields.length
      · cases hr with | ref hr => ?_
        obtain ⟨ai', m', z', hai', -, hz, -, -, hfields⟩ :=
          arrayFieldAgg hst.1 ⟨hsty, haty⟩ hr (hst.typeAgg hd).2 he
        rw [hai] at hai'; cases hai'
        have hfv := List.getElem?_eq_getElem hlt
        exact ⟨_, .aggregate (.arrayGetArray hai hfv (htype hd) he
          (unpackable_of_ok (hfields _ (List.mem_of_getElem? hfv)) hz hsx))⟩
      · exact ⟨_, .aggregate (.arrayGetOob hai (Nat.le_of_not_lt hlt))⟩
  | arraySet hd he =>
    obtain ⟨vr, vi, v, rfl, hr, hi, hv⟩ := forall₂_three hvs
    obtain ⟨i, rfl⟩ := ValOk.i32_invRT' hi
    rcases ValOk.array_inv hst hsty haty hr (heapUp_def he) with rfl | ⟨a, ai, rfl, hai⟩
    · exact ⟨_, .aggregate .arraySetNull⟩
    · by_cases hlt : i.toNat < ai.fields.length
      · exact ⟨_, .aggregate (.arraySetArray hai hlt (htype hd) he (packable_of_valOk hv))⟩
      · exact ⟨_, .aggregate (.arraySetOob hai (Nat.le_of_not_lt hlt))⟩
  | arrayLen =>
    obtain ⟨vr, rfl, hr⟩ := forall₂_one hvs
    rcases ValOk.array_inv hst hsty haty hr heapUp_array with rfl | ⟨a, ai, rfl, hai⟩
    · exact ⟨_, .aggregate .arrayLenNull⟩
    · exact ⟨_, .aggregate (.arrayLenArray hai)⟩
  | arrayFill hd he =>
    obtain ⟨vr, vi, v, vn, rfl, hr, hi, -, hn⟩ := forall₂_four hvs
    obtain ⟨i, rfl⟩ := ValOk.i32_invRT' hi
    obtain ⟨n, rfl⟩ := ValOk.i32_invRT' hn
    rcases ValOk.array_inv hst hsty haty hr (heapUp_def he) with rfl | ⟨a, ai, rfl, hai⟩
    · exact ⟨_, .aggregate .arrayFillNull⟩
    · by_cases hle : i.toNat + n.toNat ≤ ai.fields.length
      · by_cases hn0 : n = 0
        · subst hn0
          exact ⟨_, .aggregate (.arrayFillZero hai (by simpa using hle))⟩
        · exact ⟨_, .aggregate (.arrayFillSucc hai hle hn0)⟩
      · exact ⟨_, .aggregate (.arrayFillOob hai (Nat.lt_of_not_le hle))⟩
  | arrayCopy hd₁ he₁ hd₂ he₂ hs =>
    obtain ⟨vr₁, vi₁, vr₂, vi₂, vn, rfl, hr₁, hi₁, hr₂, hi₂, hn⟩ := forall₂_five hvs
    obtain ⟨i₁, rfl⟩ := ValOk.i32_invRT' hi₁
    obtain ⟨i₂, rfl⟩ := ValOk.i32_invRT' hi₂
    obtain ⟨n, rfl⟩ := ValOk.i32_invRT' hn
    have c₂ := ValOk.array_inv hst hsty haty hr₂ (heapUp_def he₂)
    obtain ⟨r₂, rfl⟩ : ∃ r₂, vr₂ = .ref r₂ := by
      rcases c₂ with rfl | ⟨_, _, rfl, _⟩ <;> exact ⟨_, rfl⟩
    rcases ValOk.array_inv hst hsty haty hr₁ (heapUp_def he₁) with rfl | ⟨a₁, ai₁, rfl, hai₁⟩
    · exact ⟨_, .aggregate .arrayCopyNull₁⟩
    rcases c₂ with h0 | ⟨a₂, ai₂, h0, hai₂⟩ <;> cases h0
    · exact ⟨_, .aggregate .arrayCopyNull₂⟩
    by_cases h₁ : i₁.toNat + n.toNat ≤ ai₁.fields.length
    swap
    · exact ⟨_, .aggregate (.arrayCopyOob₁ hai₁ (Nat.lt_of_not_le h₁))⟩
    by_cases h₂ : i₂.toNat + n.toNat ≤ ai₂.fields.length
    swap
    · exact ⟨_, .aggregate (.arrayCopyOob₂ hai₂ (Nat.lt_of_not_le h₂))⟩
    by_cases hn0 : n = 0
    · subst hn0
      exact ⟨_, .aggregate (.arrayCopyZero hai₁ hai₂ ⟨by simpa using h₁, by simpa using h₂⟩)⟩
    by_cases hle : i₁.toNat ≤ i₂.toNat
    · exact ⟨_, .aggregate (.arrayCopyLe hai₁ hai₂ ⟨h₁, h₂⟩ hn0 (htype hd₂) he₂ hle)⟩
    · exact ⟨_, .aggregate (.arrayCopyGt hai₁ hai₂ ⟨h₁, h₂⟩ hn0 (htype hd₂) he₂
        (Nat.lt_of_not_le hle))⟩
  | arrayInitElem hd he hy hs =>
    obtain ⟨vr, vi, vj, vn, rfl, hr, hi, hj, hn⟩ := forall₂_four hvs
    obtain ⟨i, rfl⟩ := ValOk.i32_invRT' hi
    obtain ⟨j, rfl⟩ := ValOk.i32_invRT' hj
    obtain ⟨n, rfl⟩ := ValOk.i32_invRT' hn
    obtain ⟨ea, ei, hei, -⟩ := hst.2.elem hy
    rcases ValOk.array_inv hst hsty haty hr (heapUp_def he) with rfl | ⟨a, ai, rfl, hai⟩
    · exact ⟨_, .aggregate .arrayInitElemNull⟩
    by_cases h₁ : i.toNat + n.toNat ≤ ai.fields.length
    swap
    · exact ⟨_, .aggregate (.arrayInitElemOob₁ hai (Nat.lt_of_not_le h₁))⟩
    by_cases h₂ : j.toNat + n.toNat ≤ ei.refs.length
    swap
    · exact ⟨_, .aggregate (.arrayInitElemOob₂ hei (Nat.lt_of_not_le h₂))⟩
    by_cases hn0 : n = 0
    · subst hn0
      exact ⟨_, .aggregate (.arrayInitElemZero hai hei ⟨by simpa using h₁, by simpa using h₂⟩)⟩
    have hn' : n.toNat ≠ 0 := fun h0 => hn0 (BitVec.eq_of_toNat_eq (by simp [h0]))
    have hlt : j.toNat < ei.refs.length := by omega
    exact ⟨_, .aggregate (.arrayInitElemSucc hai hei ⟨h₁, h₂⟩ hn0
      (List.getElem?_eq_getElem hlt))⟩
  | @arrayInitData x y d z hd he hnv hy =>
    obtain ⟨vr, vi, vj, vn, rfl, hr, hi, hj, hn⟩ := forall₂_four hvs
    obtain ⟨i, rfl⟩ := ValOk.i32_invRT' hi
    obtain ⟨j, rfl⟩ := ValOk.i32_invRT' hj
    obtain ⟨n, rfl⟩ := ValOk.i32_invRT' hn
    obtain ⟨da, di, hdat⟩ := hst.2.data hy
    rcases ValOk.array_inv hst hsty haty hr (heapUp_def he) with rfl | ⟨a, ai, rfl, hai⟩
    · exact ⟨_, .aggregate .arrayInitDataNull⟩
    by_cases h₁ : i.toNat + n.toNat ≤ ai.fields.length
    swap
    · exact ⟨_, .aggregate (.arrayInitDataOob₁ hai (Nat.lt_of_not_le h₁))⟩
    by_cases h₂ : j.toNat + n.toNat * storageSize (fieldStorage (.field .var z)) / 8 ≤
        di.bytes.size
    swap
    · exact ⟨_, .aggregate (.arrayInitDataOob₂ (htype hd) he hdat (storageSize_pos hnv)
        (Nat.lt_of_not_le h₂))⟩
    by_cases hn0 : n = 0
    · subst hn0
      exact ⟨_, .aggregate (.arrayInitDataZero hai hdat ⟨by simpa using h₁, by simpa using h₂⟩)⟩
    have hn' : n.toNat ≠ 0 := fun h0 => hn0 (BitVec.eq_of_toNat_eq (by simp [h0]))
    have hm := storageSize_mod hnv
    have hj' : j.toNat + storageSize z / 8 ≤ di.bytes.size := by
      have e : n.toNat * storageSize z / 8 = n.toNat * (storageSize z / 8) :=
        Nat.mul_div_assoc _ (Nat.dvd_of_mod_eq_zero hm)
      have : 1 * (storageSize z / 8) ≤ n.toNat * (storageSize z / 8) :=
        Nat.mul_le_mul_right _ (by omega)
      simp only [fieldStorage] at h₂
      omega
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (readField?_isSome hnv hj')
    exact ⟨_, .aggregate (.arrayInitDataNum hai (htype hd) he hdat ⟨h₁, h₂⟩ hn0 hv)⟩
  | _ => simp [Instr.IsAggregate] at ha

end Silmaril.Wasm.Execution.Core
