module

public import Silmaril.Wasm.SingleThreaded.Determinism

@[expose] public section

/-! # Reference interpreter: the reference family

A computable cast decision `refOk?` (sound for valid target types, complete in
a well-typed store) and the head-step function `referenceStep?` for the
`RefStep` rules (`ref.null`, `ref.func`, `ref.i31`, `ref.is_null`,
`ref.as_non_null`, `ref.eq`, `ref.test`, `ref.cast`, `i31.get`,
`extern.convert_any`, `any.convert_extern`).
-/

namespace Silmaril.Wasm.SingleThreaded.Exec

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

/-! ## Cast decision -/

/-- Decide `RefOk s r rt` (for valid `rt`, in a well-typed store). -/
def refOk? (s : Store H) (r : Ref) (rt : CRefType) : Bool :=
  (match Ref.type? s r with
   | none => false
   | some rt₀ => Sub.check {} rt₀ rt) &&
  (match r with
   | .extern r' => refOk? s r' (.ref false (.abs .any)) && decide (r' ≠ .null)
   | _ => true)

namespace Ref

theorem tyOk_any : TyOk {} (.ref false (.abs .any) : CRefType) := .ref (.abs _)

/-- In a well-typed store, principal types are closed-valid. -/
theorem type?_tyOk {s : Store H} (hs : StoreOk s) {r : Ref} {rt₀ : CRefType}
    (e : Ref.type? s r = some rt₀) : TyOk {} rt₀ := by
  cases r with
  | null => cases e; exact .ref .bot
  | i31 b => cases e; exact .ref (.abs _)
  | struct a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨si, h, rfl⟩ := e
    exact .ref (.use (.dt (hs.structsClosed si (List.mem_of_getElem? h))))
  | array a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨ai, h, rfl⟩ := e
    exact .ref (.use (.dt (hs.arraysClosed ai (List.mem_of_getElem? h))))
  | func a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨fi, h, rfl⟩ := e
    have hdt : TyOk {} fi.type := by
      cases hs.funcs fi (List.mem_of_getElem? h) <;> assumption
    exact .ref (.use (.dt hdt))
  | exn a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨ei, h, rfl⟩ := e
    exact .ref (.abs _)
  | host a => cases e; exact .ref (.abs _)
  | extern r' => cases e; exact .ref (.abs _)

end Ref

theorem refOk?_sound {s : Store H} {r : Ref} {rt : CRefType} (hrt : TyOk {} rt) :
    refOk? s r rt = true → RefOk s r rt := by
  induction r generalizing rt with
  | extern r' ih =>
    intro h
    unfold refOk? at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h₁, h₂, h₃⟩ := h
    have hr' := ih Ref.tyOk_any h₂
    refine (RefOk.iff_principal s _ rt hrt).mpr ⟨_, rfl, ?_, ?_⟩
    · simpa [Ref.type?] using Sub.check_sound (by simpa [Ref.type?] using h₁)
    · intro r'' e; cases e; exact ⟨hr', h₃⟩
  | _ =>
    intro h
    unfold refOk? at h
    simp only [Bool.and_true] at h
    split at h
    · simp at h
    · rename_i rt₀ e
      refine (RefOk.iff_principal s _ rt hrt).mpr ⟨rt₀, e, Sub.check_sound (by simpa using h), ?_⟩
      intro r' e'; cases e'

theorem refOk?_complete {s : Store H} {r : Ref} {rt : CRefType} (hs : StoreOk s)
    (hrt : TyOk {} rt) : RefOk s r rt → refOk? s r rt = true := by
  intro h
  induction r generalizing rt with
  | extern r' ih =>
    obtain ⟨rt₀, e, hsub, hx⟩ := (RefOk.iff_principal s _ rt hrt).mp h
    obtain ⟨hr', hn⟩ := hx r' rfl
    unfold refOk?
    simp only [e, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(Sub.check_iff TypeCtx.ok_empty rfl (Ref.type?_tyOk hs e) hrt).mpr hsub,
      ih Ref.tyOk_any hr', hn⟩
  | _ =>
    obtain ⟨rt₀, e, hsub, -⟩ := (RefOk.iff_principal s _ rt hrt).mp h
    unfold refOk?
    simp only [e, Bool.and_true]
    exact (Sub.check_iff TypeCtx.ok_empty rfl (Ref.type?_tyOk hs e) hrt).mpr hsub

theorem refOk?_iff {s : Store H} (hs : StoreOk s) :
    ∀ r rt, TyOk {} rt → (refOk? s r rt = true ↔ RefOk s r rt) :=
  fun _ _ hrt => ⟨refOk?_sound hrt, refOk?_complete hs hrt⟩

/-! ## The reference family -/

/-- The reference family on the reversed (top-first) value stack. -/
def refStepRev? (s : Store H) (f : Frame) : List Val → Admin → Option (Nat × Config H)
  | _, .plain (.refNull _) => some (0, ⟨s, f, [.ref .null]⟩)
  | _, .plain (.refFunc x) =>
    match f.module.funcs[x.toNat]? with
    | some a => some (0, ⟨s, f, [.ref (.func a)]⟩)
    | none => none
  | .num ⟨.int .i32, i⟩ :: _, .plain .refI31 => some (1, ⟨s, f, [.ref (.i31 (i.setWidth 31))]⟩)
  | .ref r :: _, .plain .refIsNull =>
    some (1, ⟨s, f, [constI32 (if r = .null then 1 else 0)]⟩)
  | .ref r :: _, .plain .refAsNonNull =>
    some (1, ⟨s, f, [if r = .null then .trap else .ref r]⟩)
  | .ref r₂ :: .ref r₁ :: _, .plain .refEq =>
    some (2, ⟨s, f, [constI32 (if r₁ = r₂ then 1 else 0)]⟩)
  | .ref r :: _, .plain (.refTest rt) =>
    some (1, ⟨s, f, [constI32 (if refOk? s r (f.module.instRef rt) then 1 else 0)]⟩)
  | .ref r :: _, .plain (.refCast rt) =>
    some (1, ⟨s, f, [if refOk? s r (f.module.instRef rt) then .ref r else .trap]⟩)
  | .ref .null :: _, .plain (.i31Get _) => some (1, ⟨s, f, [.trap]⟩)
  | .ref (.i31 i) :: _, .plain (.i31Get sx) =>
    some (1, ⟨s, f, [constI32 (match sx with
      | .signed => i.signExtend 32 | .unsigned => i.setWidth 32)]⟩)
  | .ref r :: _, .plain .externConvertAny =>
    some (1, ⟨s, f, [.ref (if r = .null then .null else .extern r)]⟩)
  | .ref .null :: _, .plain .anyConvertExtern => some (1, ⟨s, f, [.ref .null]⟩)
  | .ref (.extern r) :: _, .plain .anyConvertExtern => some (1, ⟨s, f, [.ref r]⟩)
  | _, _ => none

/-- The reference-family head step. -/
def referenceStep? (_o : GrowOracle) (s : Store H) (f : Frame) (vs : List Val) (e : Admin) :
    Option (Nat × Config H) :=
  refStepRev? s f vs.reverse e

theorem Ref.drop_of_reverse {vs top rest : List Val} (h : vs.reverse = top ++ rest) :
    top.length ≤ vs.length ∧ vs.drop (vs.length - top.length) = top.reverse := by
  have : vs = rest.reverse ++ top.reverse := by
    rw [← List.reverse_reverse vs, h]; simp
  subst this
  simp

theorem Ref.eqStep {s : Store H} {f : Frame} (r₁ r₂ : Ref) :
    RefStep ⟨s, f, [.ref r₁, .ref r₂, .plain .refEq]⟩
      ⟨s, f, [constI32 (if r₁ = r₂ then 1 else 0)]⟩ := by
  by_cases h : r₁ = r₂
  · subst h
    simp only [↓reduceIte]
    by_cases hn : r₁ = .null
    · subst hn; exact .eqNull
    · exact .eqTrue hn
  · simp only [h, ↓reduceIte]; exact .eqFalse h

theorem refStepRev?_sound {s : Store H} {f : Frame} {rvs : List Val} {e : Admin} {k : Nat}
    {c : Config H} (hs : StoreOk s)
    (hcast : ∀ rt, (e = .plain (.refTest rt) ∨ e = .plain (.refCast rt)) →
      TyOk {} (f.module.instRef rt))
    (h : refStepRev? s f rvs e = some (k, c)) :
    ∃ top rest, rvs = top ++ rest ∧ top.length = k ∧ RefStep ⟨s, f, vals top.reverse ++ [e]⟩ c := by
  have hT : ∀ {rt r}, e = .plain (.refTest rt) → refOk? s r (f.module.instRef rt) = true →
      RefOk s r (f.module.instRef rt) := fun he => refOk?_sound (hcast _ (.inl he))
  have hF : ∀ {rt r}, e = .plain (.refTest rt) → ¬ refOk? s r (f.module.instRef rt) = true →
      ¬ RefOk s r (f.module.instRef rt) := fun he h h' => h (refOk?_complete hs (hcast _ (.inl he)) h')
  have cT : ∀ {rt r}, e = .plain (.refCast rt) → refOk? s r (f.module.instRef rt) = true →
      RefOk s r (f.module.instRef rt) := fun he => refOk?_sound (hcast _ (.inr he))
  have cF : ∀ {rt r}, e = .plain (.refCast rt) → ¬ refOk? s r (f.module.instRef rt) = true →
      ¬ RefOk s r (f.module.instRef rt) := fun he h h' => h (refOk?_complete hs (hcast _ (.inr he)) h')
  unfold refStepRev? at h
  split at h
  · cases h; exact ⟨[], _, rfl, rfl, .refNull _⟩
  · split at h
    · cases h; exact ⟨[], _, rfl, rfl, .refFunc (by assumption)⟩
    · cases h
  · cases h; exact ⟨[_], _, rfl, rfl, .refI31 _⟩
  · cases h; refine ⟨[_], _, rfl, rfl, ?_⟩
    split
    · subst_vars; exact .isNullTrue
    · exact .isNullFalse (by assumption)
  · cases h; refine ⟨[_], _, rfl, rfl, ?_⟩
    split
    · subst_vars; exact .asNonNullNull
    · exact .asNonNullAddr (by assumption)
  · cases h; refine ⟨[_, _], _, rfl, rfl, ?_⟩
    exact Ref.eqStep _ _
  · cases h; refine ⟨[_], _, rfl, rfl, ?_⟩
    split
    · exact .testTrue (hT rfl (by assumption))
    · exact .testFalse (hF rfl (by assumption))
  · cases h; refine ⟨[_], _, rfl, rfl, ?_⟩
    split
    · exact .castSucceed (cT rfl (by assumption))
    · exact .castFail (cF rfl (by assumption))
  · cases h; exact ⟨[_], _, rfl, rfl, .i31GetNull _⟩
  · cases h; refine ⟨[_], _, rfl, rfl, ?_⟩
    rename_i sx _
    cases sx <;> exact .i31GetNum _ _
  · cases h; refine ⟨[_], _, rfl, rfl, ?_⟩
    split
    · subst_vars; exact .externConvertNull
    · exact .externConvertAddr (by assumption)
  · cases h; exact ⟨[_], _, rfl, rfl, .anyConvertNull⟩
  · cases h; exact ⟨[_], _, rfl, rfl, .anyConvertAddr _⟩
  · cases h

theorem Ref.snoc_eq {args l : List Val} {e e' : Admin} (h : vals args ++ [e] = vals l ++ [e']) :
    args = l ∧ e = e' := by
  have := List.append_inj' h rfl
  exact ⟨vals_inj.mp this.1, by simpa using this.2⟩

theorem referenceStep?_sound {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val}
    {e : Admin} {k : Nat} {c : Config H} (hs : StoreOk s)
    (hcast : ∀ rt, (e = .plain (.refTest rt) ∨ e = .plain (.refCast rt)) →
      TyOk {} (f.module.instRef rt)) :
    referenceStep? o s f vs e = some (k, c) →
      k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) e c := by
  intro h
  obtain ⟨top, rest, hr, rfl, hstep⟩ := refStepRev?_sound hs hcast h
  obtain ⟨hle, hd⟩ := Ref.drop_of_reverse hr
  refine ⟨hle, ?_⟩
  rw [hd]
  exact .reference hstep

theorem referenceStep?_complete {o : GrowOracle} {s : Store H} {f : Frame} {vs args : List Val}
    {e : Admin} {c : Config H} (hs : StoreOk s)
    (hcast : ∀ rt, (e = .plain (.refTest rt) ∨ e = .plain (.refCast rt)) →
      TyOk {} (f.module.instRef rt)) :
    Head (profile o) s f args e c → famOf e = .reference → (∃ q, vs = q ++ args) →
      referenceStep? o s f vs e = some (args.length, c) := by
  intro h hf ⟨q, hq⟩
  have h' := h.fam_inv (by rw [hf]; decide)
  rw [hf] at h'
  simp only [FamRel] at h'
  subst hq
  unfold referenceStep?
  rw [List.reverse_append]
  generalize hl : vals args ++ [e] = l at h'
  cases h' <;> first
    | obtain ⟨rfl, rfl⟩ := Ref.snoc_eq (l := []) hl
    | obtain ⟨rfl, rfl⟩ := Ref.snoc_eq (l := [.ref _]) hl
    | obtain ⟨rfl, rfl⟩ := Ref.snoc_eq (l := [.num ⟨.int .i32, _⟩]) hl
    | obtain ⟨rfl, rfl⟩ := Ref.snoc_eq (l := [.ref _, .ref _]) hl
  all_goals first
    | (simp [refStepRev?, *]; done)
    | simp [refStepRev?, refOk?_complete hs (hcast _ (.inl rfl)) ‹_›]
    | simp [refStepRev?, refOk?_complete hs (hcast _ (.inr rfl)) ‹_›]
    | simp [refStepRev?, Bool.eq_false_iff.mpr (fun h => ‹¬_› (refOk?_sound (hcast _ (.inl rfl)) h))]
    | simp [refStepRev?, Bool.eq_false_iff.mpr (fun h => ‹¬_› (refOk?_sound (hcast _ (.inr rfl)) h))]
    | rfl

end Silmaril.Wasm.SingleThreaded.Exec
