module

public import Silmaril.Data.Layout.Cerberus.Defs
public import Silmaril.Data.Layout.Thms

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-!
# Proofs: agreement with Cerberus on flat structs

For a struct whose members are integers, `_Bool` or pointers (through any typedefs), without
`_Alignas` or bit-fields, Cerberus' concrete layout (`Mem.Concrete.typeLayout`) and
`declLayout sysvX86_64` have the same size, alignment and member offsets (`flat_agree`).
-/

@[expose] public section

namespace Silmaril.Proofs.Data.Layout.Cerb

open Silmaril.Data.Layout Silmaril.Data.Layout.Cerb
open Silmaril.Cerberus
open Silmaril.Cerberus.Mem.Concrete (Tags TypeLayout typeLayout Failure roundUp integerLayout
  registeredIntegerLayout registeredInteger)

/-- Integers, `_Bool` and pointers, through typedefs. -/
def isScalar : CTy → Bool
  | .bool | .ptr _ => true
  | .int k s => (intType k s).isSome
  | .typedef _ t => isScalar t
  | _ => false

theorem intType_layout {k : IntKind} {sg : Sign} {it : IntegerType} (h : intType k sg = some it) :
    ∃ w b, sysvX86_64.intShape k = some ⟨w, w⟩ ∧ integerLayout it = some (w, b) ∧ 0 < w := by
  cases k with
  | exact n =>
    have hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by
      cases sg <;> simp only [intType, intBase] at h <;> split at h <;> first | assumption | simp at h
    rcases hn with rfl | rfl | rfl | rfl <;> cases sg <;>
      simp only [intType, intBase] at h <;> simp at h <;> subst h <;> exact ⟨_, _, rfl, rfl, by decide⟩
  | _ => cases sg <;> simp only [intType, intBase, Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq] at h <;> (try subst h) <;> (try contradiction) <;>
      exact ⟨_, _, rfl, rfl, by decide⟩

/-- The Cerberus layout of a scalar is its System V shape. -/
theorem scalar_layout (env : Env) (tags : Tags) (cf : Nat) :
    ∀ (n : Nat) (t : CTy) (s : Shape) (c : Ctype), isScalar t = true →
      layoutTy sysvX86_64 env n t = .ok s → toCtype env t = some c →
      typeLayout (cf + 1) tags c = .ok ⟨s.size, s.align, []⟩ ∧ s.size = s.align ∧ 0 < s.align := by
  intro n
  induction n with
  | zero => intro t s c _ h; simp [layoutTy] at h
  | succ n ih =>
    intro t s c hsc h hc
    cases t with
    | bool =>
      simp only [layoutTy] at h; cases h
      simp only [toCtype, Option.some.injEq] at hc; subst hc
      refine ⟨?_, rfl, by decide⟩
      simp [typeLayout, registeredIntegerLayout, registeredInteger, integerLayout, sysvX86_64]
      rfl
    | ptr t =>
      simp only [layoutTy] at h; cases h
      simp only [toCtype, Option.some.injEq] at hc; subst hc
      exact ⟨rfl, rfl, by decide⟩
    | int k sg =>
      simp only [isScalar, Option.isSome_iff_exists] at hsc
      obtain ⟨it, hit⟩ := hsc
      obtain ⟨w, b, hw, hl, hpos⟩ := intType_layout hit
      simp only [layoutTy, DataModel.intOf, hw] at h; cases h
      simp only [toCtype, hit, Option.map_some, Option.some.injEq] at hc; subst hc
      refine ⟨?_, rfl, hpos⟩
      have hr : registeredIntegerLayout tags it = some (w, b) := by
        cases it <;> simp_all [registeredIntegerLayout, registeredInteger]
        · simp [intType, intBase] at hit
          cases k <;> cases sg <;> simp at hit
      simp [typeLayout, hr]; rfl
    | typedef _ t => exact ih t s c hsc h hc
    | _ => simp [isScalar] at hsc

/-! ## The member fold -/

theorem foldlM_ok {σ α ε : Type} (F : σ → α → Except ε σ) (G : σ → α → σ) :
    ∀ (xs : List α) (s : σ), (∀ s, ∀ x ∈ xs, F s x = .ok (G s x)) →
      xs.foldlM F s = .ok (xs.foldl G s) := by
  intro xs
  induction xs with
  | nil => intro s _; rfl
  | cons x xs ih =>
    intro s h
    simp only [List.foldlM_cons, List.foldl_cons, h s x (by simp)]
    exact ih _ fun s y hy => h s y (by simp [hy])

theorem roundUp_cast (n a : Nat) (ha : 0 < a) :
    roundUp (n : Int) (a : Int) = ((alignUp n a : Nat) : Int) := by
  simp only [roundUp, alignUp, Nat.pos_iff_ne_zero.mp ha, ite_false]
  have h1 := Nat.div_add_mod n a
  have h2 := Nat.mod_lt n ha
  by_cases hm : n % a = 0
  · have : (n : Int) % (a : Int) = 0 := by exact_mod_cast hm
    simp only [this, ite_true]
    have : (n + a - 1) / a = n / a := by
      rw [show n + a - 1 = (a - 1) + a * (n / a) by omega, Nat.add_mul_div_left _ _ ha,
        Nat.div_eq_of_lt (by omega)]
      simp
    rw [this, Nat.mul_comm]; omega
  · have : ¬ ((n : Int) % (a : Int) = 0) := by exact_mod_cast hm
    simp only [this, ite_false]
    have hq : (n + a - 1) / a = n / a + 1 := by
      rw [show n + a - 1 = (n % a - 1) + a * (n / a + 1) by
        rw [Nat.mul_add]; omega, Nat.add_mul_div_left _ _ ha, Nat.div_eq_of_lt (by omega)]
      simp
    rw [hq]
    have hmod : ((n : Int) % (a : Int)) = ((n % a : Nat) : Int) := by exact_mod_cast rfl
    rw [hmod]
    have key : (n / a + 1) * a = n + a - n % a := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
      generalize a * (n / a) = P at h1 ⊢
      omega
    rw [key]
    omega

/-- The largest alignment, starting from 0 (Cerberus' fold). -/
def maxA0 : List Shape → Nat
  | [] => 0
  | s :: ss => max s.align (maxA0 ss)

theorem maxAlign_eq_maxA0 {ms : List Shape} (hne : ms ≠ []) (h : ∀ s ∈ ms, 0 < s.align) :
    maxAlign ms = maxA0 ms := by
  induction ms with
  | nil => exact absurd rfl hne
  | cons s ss ih =>
    cases ss with
    | nil => simp only [maxAlign, maxA0]; have := h s (by simp); omega
    | cons t ts =>
      simp only [maxAlign, maxA0] at ih ⊢
      rw [ih (by simp) (fun u hu => h u (by simp [hu]))]

/-- What one Cerberus member step does to a member whose layout is `⟨w, w, []⟩`. -/
def cerbG (fuel : Nat) (tags : Tags) (s : List (Identifier × Ctype × Int) × Int × Int)
    (x : Identifier × Attributes × Option Alignment × Qualifiers × Ctype) :
    List (Identifier × Ctype × Int) × Int × Int :=
  let w : Int := match typeLayout fuel tags x.2.2.2.2 with
    | .ok l => l.align
    | .error _ => 0
  (s.1 ++ [(x.1, x.2.2.2.2, roundUp s.2.1 w)], roundUp s.2.1 w + w, max s.2.2 w)

def cOf (env : Env) (f : Field) : Ctype := (toCtype env f.ty).getD ⟨[], .void⟩

def memOf (env : Env) (f : Field) : Identifier × Attributes × Option Alignment × Qualifiers × Ctype :=
  (ident f.name, .mk [], none, noQuals, cOf env f)

/-- A flat member: scalar, no `_Alignas`, no bit-field. -/
def FlatField (f : Field) : Prop := isScalar f.ty = true ∧ f.alignas = none ∧ f.bits = none

theorem toCtype_scalar (env : Env) : ∀ t : CTy, isScalar t = true → ∃ c, toCtype env t = some c := by
  intro t
  induction t with
  | bool => intro _; exact ⟨_, rfl⟩
  | ptr _ _ => intro _; exact ⟨_, rfl⟩
  | int k sg =>
    intro h
    simp only [isScalar, Option.isSome_iff_exists] at h
    obtain ⟨it, hit⟩ := h
    exact ⟨⟨[], .basic (.integer it)⟩, by simp [toCtype, hit]⟩
  | typedef _ t ih => intro h; exact ih h
  | _ => intro h; simp [isScalar] at h

theorem fold_members (env : Env) (tags : Tags) (cf : Nat) :
    ∀ (fs : List Field) (ms : List Shape), fieldShapes (layoutTy sysvX86_64 env defaultFuel) fs = .ok ms →
      (∀ f ∈ fs, FlatField f) →
      ∀ (acc : List (Identifier × Ctype × Int)) (off : Nat) (mx : Int), 0 ≤ mx →
        (fs.map (memOf env)).foldl (cerbG (cf + 1) tags) (acc, (off : Int), mx) =
          (acc ++ (fs.zip (place off ms)).map (fun p => (ident p.1.name, cOf env p.1, (p.2.off : Int))),
            ((placeEnd off ms : Nat) : Int), max mx ((maxA0 ms : Nat) : Int)) ∧
        (∀ x ∈ fs.map (memOf env),
          ∃ l : TypeLayout, typeLayout (cf + 1) tags x.2.2.2.2 = .ok l ∧ l.size = l.align ∧ 0 < l.align) := by
  intro fs
  induction fs with
  | nil =>
    intro ms h _ acc off mx hmx
    cases h
    refine ⟨?_, by simp⟩
    simp [place, placeEnd, maxA0]
    omega
  | cons f fs ih =>
    intro ms h hflat acc off mx hmx
    obtain ⟨hsc, hal, hbits⟩ := hflat f (by simp)
    simp only [fieldShapes, hbits, Option.isSome_none, Bool.false_eq_true, ite_false] at h
    split at h; · cases h
    rename_i s hs
    simp only [hal, memberAlign] at h
    split at h; · cases h
    rename_i ss hss
    cases h
    obtain ⟨c, hc⟩ := toCtype_scalar env f.ty hsc
    obtain ⟨hl, hsa, hpos⟩ := scalar_layout env tags cf _ _ _ _ hsc hs hc
    have hcOf : cOf env f = c := by simp [cOf, hc]
    have hstep : cerbG (cf + 1) tags (acc, (off : Int), mx) (memOf env f) =
        (acc ++ [(ident f.name, c, ((alignUp off s.align : Nat) : Int))],
          ((alignUp off s.align + s.size : Nat) : Int), max mx (s.align : Int)) := by
      simp only [cerbG, memOf, hcOf, hl, roundUp_cast off s.align hpos]
      push_cast; rw [hsa]
    obtain ⟨ih1, ih2⟩ := ih ss hss (fun g hg => hflat g (by simp [hg]))
      (acc ++ [(ident f.name, c, ((alignUp off s.align : Nat) : Int))])
      (alignUp off s.align + s.size) (max mx (s.align : Int)) (by omega)
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.foldl_cons, hstep, ih1]
      simp only [place, placeEnd, maxA0, List.zip_cons_cons, List.map_cons, List.append_assoc,
        List.cons_append, List.nil_append, hcOf]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      simp only
      push_cast
      rw [max_assoc]
    · intro x hx
      simp only [List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · refine ⟨_, by simpa [memOf, hcOf] using hl, by simp [hsa], ?_⟩
        show (0 : Int) < s.align
        exact_mod_cast hpos
      · exact ih2 x hx

/-! ## Flat structs -/

theorem toMember_flat (env : Env) {f : Field} (h : FlatField f) :
    toMember env f = some (memOf env f) := by
  obtain ⟨hsc, hal, hbits⟩ := h
  obtain ⟨c, hc⟩ := toCtype_scalar env f.ty hsc
  simp [toMember, hbits, hal, hc, memOf, cOf]

theorem mapM_toMember (env : Env) :
    ∀ (fs : List Field), (∀ f ∈ fs, FlatField f) →
      fs.mapM (toMember env) = some (fs.map (memOf env)) := by
  intro fs
  induction fs with
  | nil => intro _; rfl
  | cons f fs ih =>
    intro h
    simp [List.mapM_cons, toMember_flat env (h f (by simp)), ih (fun g hg => h g (by simp [hg]))]

theorem maxA0_pos {ms : List Shape} (hne : ms ≠ []) (h : ∀ s ∈ ms, 0 < s.align) : 0 < maxA0 ms := by
  cases ms with
  | nil => exact absurd rfl hne
  | cons s ss => simp only [maxA0]; have := h s (by simp); omega

theorem fieldShapes_pos {fs : List Field} {ms : List Shape} {env : Env}
    (h : fieldShapes (layoutTy sysvX86_64 env defaultFuel) fs = .ok ms) : ∀ s ∈ ms, 0 < s.align :=
  fun s hs => (fieldShapes_pow2 (fun t s h => (layoutTy_wf sysvX86_64_wf env _ t s h).pow2) h s hs).pos

/-- The Cerberus tags of a one-struct environment. -/
def flatTags (d : Decl) : Tags :=
  { definitions := Map.ofList [(tagSym [d] .struct d.tag,
      (Loc.unknown, TagDefinition.struct (d.fields.map (memOf [d])) none))] }

/-- **Agreement on flat structs.** For a struct whose members are integers, `_Bool` or
pointers (through typedefs), without `_Alignas` or bit-fields, Cerberus' concrete layout has the
System V size, alignment and member offsets. -/
theorem flat_agree (d : Decl) (hk : d.kind = .struct) (hne : d.fields ≠ [])
    (hflat : ∀ f ∈ d.fields, FlatField f) {r : Int × Int × List (String × Int)}
    (h : ourLayout sysvX86_64 [d] .struct d.tag = some r) :
    cerberusLayout [d] .struct d.tag = some r := by
  have hfind : Env.find? [d] .struct d.tag = some d := by simp [Env.find?, hk]
  cases hms : fieldShapes (layoutTy sysvX86_64 [d] defaultFuel) d.fields with
  | error e =>
    simp [ourLayout, tagLayout, hfind, declLayout, hms, Except.toOption] at h
  | ok ms =>
    have hlen := fieldShapes_length hms
    have hmsne : ms ≠ [] := by
      intro he; rw [he] at hlen; exact hne (List.eq_nil_of_length_eq_zero hlen.symm)
    have hpos := fieldShapes_pos hms
    simp only [ourLayout, tagLayout, hfind, declLayout, hms, hk, kindPlace, structPlace,
      Except.toOption, Option.map_some, Option.some.injEq] at h
    subst h
    -- the Cerberus side
    have htags : toTags [d] = some (flatTags d) := by
      simp [toTags, toTagDef, mapM_toMember [d] d.fields hflat, hk, flatTags]
    obtain ⟨hfold, hlay⟩ := fold_members [d] (flatTags d) 63 d.fields ms hms hflat [] 0 0
      (Int.le_refl 0)
    have hmax := maxA0_pos hmsne hpos
    simp only [cerberusLayout, htags, Option.bind_some]
    have hlook : (flatTags d).lookup (tagSym [d] .struct d.tag) =
        some (Loc.unknown, TagDefinition.struct (d.fields.map (memOf [d])) none) := by
      simp [flatTags, Silmaril.Cerberus.Mem.Concrete.Tags.lookup, Map.ofList]
    simp only [defaultFuel, typeLayout, hlook, pure_bind]
    rw [foldlM_ok _ (cerbG (63 + 1) (flatTags d)) _ _ ?hF]
    · simp only [Nat.cast_zero, List.nil_append] at hfold
      rw [hfold]
      have hm0 : max (0 : Int) ((maxA0 ms : Nat) : Int) = ((maxA0 ms : Nat) : Int) := by omega
      have hmA := maxAlign_eq_maxA0 hmsne hpos
      have hnle : ¬ (((maxA0 ms : Nat) : Int) ≤ 0) := by omega
      simp only [hm0, hnle, bind, Except.bind, pure, Except.pure, ite_false, summary,
        roundUp_cast _ _ hmax, hmA, List.map_map, Option.some.injEq, Prod.mk.injEq, true_and]
      apply List.map_congr_left
      intro p _
      rfl
    · intro st x hx
      obtain ⟨l, hl, hsa, hl0⟩ := hlay x hx
      simp only [List.mem_map] at hx
      obtain ⟨f, -, rfl⟩ := hx
      have hnle : ¬ (l.align ≤ 0) := by omega
      simp only [memOf] at hl ⊢
      simp only [hl, cerbG, hsa, hnle, bind, Except.bind, pure, Except.pure, ite_false]

end Silmaril.Proofs.Data.Layout.Cerb
