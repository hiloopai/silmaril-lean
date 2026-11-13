module

public import Silmaril.Proofs.Wasm.Game.Linking.Split.Ren

/-!
# Static linking, separation: Rel

Original module documentation:

# The part-store relation (M3 step B, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3, step (B).

`PartRel ρ O p σ`: the part store `p` (provider or consumer) embeds into the shared store `σ`
along the renaming `ρ`, for everything the part owns (`O`): owned functions have the same type
(and, when the part runs their code, the same instance), owned globals hold renamed values,
owned structs and arrays are stored at renamed addresses with renamed fields, and the renaming
is injective on owned addresses.

* `Grow ρ O ρ' O' σ`: ownership grows and the renaming is kept on old addresses; new addresses
  are fresh in `σ`.
* `Touch ρ O σ σ'`: the shared store changes only at what the part owns (globals, renamed
  structs and arrays) and by allocation.
* `PartRel.touch`: a relation of the *other* part, whose image is disjoint, survives a `Touch`.
* `PartRel.refOk_iff`: run-time type checks agree on owned references.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Game.Linking.Split

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

variable {H : Type}

/-- The part store `p` embeds in the shared store `σ` along `ρ` for what `O` owns. -/
structure PartRel (ρ : Ren) (O : Own) (p σ : Store H) : Prop where
  fn : ∀ a, O.fn a → ∃ fi, p.funcs[a]? = some fi ∧ ∃ fi', σ.funcs[a]? = some fi' ∧
    fi'.type = fi.type ∧ ∀ c, fi.code = .wasm c → fi' = fi ∧ O.ModGood fi.module
  gl : ∀ a, O.gl a → ∃ g, p.globals[a]? = some g ∧ σ.globals[a]? = some (ρ.ginst g) ∧
    O.GoodVal g.value
  st : ∀ a, O.st a → ∃ si, p.structs[a]? = some si ∧ σ.structs[ρ.st a]? = some (ρ.sinst si) ∧
    ∀ fv ∈ si.fields, O.GoodFV fv
  ar : ∀ a, O.ar a → ∃ ai, p.arrays[a]? = some ai ∧ σ.arrays[ρ.ar a]? = some (ρ.ainst ai) ∧
    ∀ fv ∈ ai.fields, O.GoodFV fv
  stInj : ∀ a b, O.st a → O.st b → ρ.st a = ρ.st b → a = b
  arInj : ∀ a b, O.ar a → O.ar b → ρ.ar a = ρ.ar b → a = b

/-- Ownership grows; the renaming is kept on old addresses; new images are fresh in `σ`. -/
structure Grow (ρ : Ren) (O : Own) (ρ' : Ren) (O' : Own) (σ : Store H) : Prop where
  fn : O'.fn = O.fn
  gl : O'.gl = O.gl
  st : ∀ a, O.st a → O'.st a ∧ ρ'.st a = ρ.st a
  ar : ∀ a, O.ar a → O'.ar a ∧ ρ'.ar a = ρ.ar a
  stNew : ∀ a, O'.st a → O.st a ∨ σ.structs.length ≤ ρ'.st a
  arNew : ∀ a, O'.ar a → O.ar a ∨ σ.arrays.length ≤ ρ'.ar a

/-- The shared store changes only at what the part owns, and by allocation. -/
structure Touch (ρ : Ren) (O : Own) (σ σ' : Store H) : Prop where
  funcs : σ'.funcs = σ.funcs
  globals : ∀ a, ¬ O.gl a → σ'.globals[a]? = σ.globals[a]?
  structs : ∀ a, (∀ b, O.st b → ρ.st b ≠ a) → a < σ.structs.length →
    σ'.structs[a]? = σ.structs[a]?
  arrays : ∀ a, (∀ b, O.ar b → ρ.ar b ≠ a) → a < σ.arrays.length →
    σ'.arrays[a]? = σ.arrays[a]?
  structs_len : σ.structs.length ≤ σ'.structs.length
  arrays_len : σ.arrays.length ≤ σ'.arrays.length

namespace Grow

variable {ρ ρ' ρ'' : Ren} {O O' O'' : Own} {σ σ' : Store H}

theorem refl (ρ : Ren) (O : Own) (σ : Store H) : Grow ρ O ρ O σ :=
  ⟨rfl, rfl, fun _ h => ⟨h, rfl⟩, fun _ h => ⟨h, rfl⟩, fun _ h => .inl h, fun _ h => .inl h⟩

theorem trans (h : Grow ρ O ρ' O' σ) (h' : Grow ρ' O' ρ'' O'' σ')
    (hs : σ.structs.length ≤ σ'.structs.length) (ha : σ.arrays.length ≤ σ'.arrays.length) :
    Grow ρ O ρ'' O'' σ where
  fn := h'.fn.trans h.fn
  gl := h'.gl.trans h.gl
  st a ha' := by
    obtain ⟨h1, h2⟩ := h.st a ha'
    obtain ⟨h3, h4⟩ := h'.st a h1
    exact ⟨h3, h4.trans h2⟩
  ar a ha' := by
    obtain ⟨h1, h2⟩ := h.ar a ha'
    obtain ⟨h3, h4⟩ := h'.ar a h1
    exact ⟨h3, h4.trans h2⟩
  stNew a ha' := by
    rcases h'.stNew a ha' with h1 | h1
    · rcases h.stNew a h1 with h2 | h2
      · exact .inl h2
      · exact .inr ((h'.st a h1).2 ▸ h2)
    · exact .inr (le_trans hs h1)
  arNew a ha' := by
    rcases h'.arNew a ha' with h1 | h1
    · rcases h.arNew a h1 with h2 | h2
      · exact .inl h2
      · exact .inr ((h'.ar a h1).2 ▸ h2)
    · exact .inr (le_trans ha h1)

theorem goodRef (h : Grow ρ O ρ' O' σ) : ∀ {r : Ref}, O.GoodRef r → ρ'.ref r = ρ.ref r ∧ O'.GoodRef r
  | .i31 _, _ => ⟨rfl, trivial⟩
  | .null, _ => ⟨rfl, trivial⟩
  | .struct a, hr => by
    obtain ⟨h1, h2⟩ := h.st a hr
    exact ⟨by simp [h2], h1⟩
  | .array a, hr => by
    obtain ⟨h1, h2⟩ := h.ar a hr
    exact ⟨by simp [h2], h1⟩
  | .func a, hr => ⟨rfl, by simpa [Own.GoodRef, h.fn] using hr⟩
  | .exn _, hr => hr.elim
  | .host _, hr => hr.elim
  | .extern r, hr => by
    obtain ⟨h1, h2⟩ := goodRef h (r := r) hr
    exact ⟨by simp [h1], h2⟩

theorem goodVal (h : Grow ρ O ρ' O' σ) {v : Val} (hv : O.GoodVal v) :
    ρ'.val v = ρ.val v ∧ O'.GoodVal v := by
  cases v with
  | ref r =>
    obtain ⟨h1, h2⟩ := h.goodRef hv
    exact ⟨by simp [h1], h2⟩
  | num => exact ⟨rfl, trivial⟩
  | vec => exact ⟨rfl, trivial⟩

theorem goodFV (h : Grow ρ O ρ' O' σ) {v : FieldVal} (hv : O.GoodFV v) :
    ρ'.fval v = ρ.fval v ∧ O'.GoodFV v := by
  cases v with
  | val v =>
    obtain ⟨h1, h2⟩ := h.goodVal hv
    exact ⟨by simp [h1], h2⟩
  | pack => exact ⟨rfl, trivial⟩

theorem modGood (h : Grow ρ O ρ' O' σ) {m : ModuleInst} (hm : O.ModGood m) : O'.ModGood m :=
  ⟨hm.tags, hm.mems, hm.tables, hm.elems, hm.datas, by rw [h.gl]; exact hm.globals,
    by rw [h.fn]; exact hm.funcs⟩

theorem frameGood (h : Grow ρ O ρ' O' σ) {f : Frame} (hf : O.FrameGood f) :
    ρ'.frame f = ρ.frame f ∧ O'.FrameGood f := by
  refine ⟨?_, h.modGood hf.1, fun v hv => (h.goodVal (hf.2 v hv)).2⟩
  simp only [Ren.frame, Frame.mk.injEq, and_true]
  apply List.map_congr_left
  intro x hx
  cases x with
  | none => rfl
  | some v => simp [(h.goodVal (hf.2 v hx)).1]

end Grow

/-! ### Renaming of code depends only on the references and frames it contains -/

theorem Ren.code_congr (ρ ρ' : Ren) : ∀ (l : List Admin),
    (∀ r ∈ codeRefs l, ρ'.ref r = ρ.ref r) →
    (∀ f ∈ codeFrames l, ρ'.frame f = ρ.frame f) → ρ'.code l = ρ.code l
  | [], _, _ => by simp
  | .ref r :: l, hr, hf => by
    simp only [codeRefs_ref, List.mem_cons, codeFrames_ref] at hr hf
    simp [hr r (.inl rfl), Ren.code_congr ρ ρ' l (fun r h => hr r (.inr h)) hf]
  | .label n c b :: l, hr, hf => by
    simp only [codeRefs_label, List.mem_append, codeFrames_label] at hr hf
    simp [Ren.code_congr ρ ρ' b (fun r h => hr r (.inl h)) (fun f h => hf f (.inl h)),
      Ren.code_congr ρ ρ' l (fun r h => hr r (.inr h)) (fun f h => hf f (.inr h))]
  | .handler n cs b :: l, hr, hf => by
    simp only [codeRefs_handler, List.mem_append, codeFrames_handler] at hr hf
    simp [Ren.code_congr ρ ρ' b (fun r h => hr r (.inl h)) (fun f h => hf f (.inl h)),
      Ren.code_congr ρ ρ' l (fun r h => hr r (.inr h)) (fun f h => hf f (.inr h))]
  | .frame n f b :: l, hr, hf => by
    simp only [codeRefs_frame, List.mem_append, codeFrames_frame, List.mem_cons] at hr hf
    simp [hf f (.inl rfl),
      Ren.code_congr ρ ρ' b (fun r h => hr r (.inl h)) (fun g h => hf g (.inr (.inl h))),
      Ren.code_congr ρ ρ' l (fun r h => hr r (.inr h)) (fun g h => hf g (.inr (.inr h)))]
  | .plain i :: l, hr, hf => by
    simp only [codeRefs_plain, codeFrames_plain] at hr hf
    simp [Ren.code_congr ρ ρ' l hr hf]
  | .callRefType d :: l, hr, hf => by
    simp only [codeRefs_callRefType, codeFrames_callRefType] at hr hf
    simp [Ren.code_congr ρ ρ' l hr hf]
  | .returnCallRefType d :: l, hr, hf => by
    simp only [codeRefs_returnCallRefType, codeFrames_returnCallRefType] at hr hf
    simp [Ren.code_congr ρ ρ' l hr hf]
  | .trap :: l, hr, hf => by
    simp only [codeRefs_trap, codeFrames_trap] at hr hf
    simp [Ren.code_congr ρ ρ' l hr hf]

theorem Grow.code {ρ ρ' : Ren} {O O' : Own} {σ : Store H} (h : Grow ρ O ρ' O' σ)
    {l : List Admin} (hl : O.CodeGood l) : ρ'.code l = ρ.code l ∧ O'.CodeGood l :=
  ⟨Ren.code_congr ρ ρ' l (fun r hr => (h.goodRef (hl.1 r hr)).1)
      (fun f hf => (h.frameGood (hl.2 f hf)).1),
    fun r hr => (h.goodRef (hl.1 r hr)).2, fun f hf => (h.frameGood (hl.2 f hf)).2⟩

theorem Ren.code_eq_nil_iff (ρ : Ren) {l : List Admin} : ρ.code l = [] ↔ l = [] := by
  cases l with
  | nil => simp
  | cons a l => cases a <;> simp

/-! ### Injectivity on owned references -/

namespace PartRel

variable {ρ : Ren} {O : Own} {p σ : Store H}

theorem ref_injective (hR : PartRel ρ O p σ) :
    ∀ {r₁ r₂ : Ref}, O.GoodRef r₁ → O.GoodRef r₂ → ρ.ref r₁ = ρ.ref r₂ → r₁ = r₂
  | .i31 _, r₂, _, _, h => by cases r₂ <;> simp_all [Ren.ref]
  | .null, r₂, _, _, h => by cases r₂ <;> simp_all [Ren.ref]
  | .struct a, r₂, h₁, h₂, h => by
    cases r₂ <;> simp_all [Ren.ref]
    exact hR.stInj _ _ h₁ h₂ h
  | .array a, r₂, h₁, h₂, h => by
    cases r₂ <;> simp_all [Ren.ref]
    exact hR.arInj _ _ h₁ h₂ h
  | .func a, r₂, _, _, h => by cases r₂ <;> simp_all [Ren.ref]
  | .exn _, _, h₁, _, _ => h₁.elim
  | .host _, _, h₁, _, _ => h₁.elim
  | .extern r, r₂, h₁, h₂, h => by
    cases r₂ with
    | extern r' =>
      simp only [Ren.ref_extern, Ref.extern.injEq] at h
      have h₁' : O.GoodRef r := h₁
      have h₂' : O.GoodRef r' := h₂
      rw [ref_injective hR (r₁ := r) (r₂ := r') h₁' h₂' h]
    | _ => simp_all [Ren.ref]

/-! Inversion of `Ren.ref` at each reference constructor. -/

private theorem ref_eq_i31_inv {r : Ref} {b : BitVec 31} (h : ρ.ref r = .i31 b) :
    r = .i31 b := by
  cases r <;> simp_all [Ren.ref]

private theorem ref_eq_struct_inv {r : Ref} {a' : Nat} (h : ρ.ref r = .struct a') :
    ∃ a, r = .struct a ∧ ρ.st a = a' := by
  cases r <;> simp_all [Ren.ref]

private theorem ref_eq_array_inv {r : Ref} {a' : Nat} (h : ρ.ref r = .array a') :
    ∃ a, r = .array a ∧ ρ.ar a = a' := by
  cases r <;> simp_all [Ren.ref]

private theorem ref_eq_func_inv {r : Ref} {a : Nat} (h : ρ.ref r = .func a) :
    r = .func a := by
  cases r <;> simp_all [Ren.ref]

private theorem ref_eq_exn_inv {r : Ref} {a : Nat} (h : ρ.ref r = .exn a) :
    r = .exn a := by
  cases r <;> simp_all [Ren.ref]

private theorem ref_eq_host_inv {r : Ref} {a : Nat} (h : ρ.ref r = .host a) :
    r = .host a := by
  cases r <;> simp_all [Ren.ref]

private theorem ref_eq_extern_inv {r r' : Ref} (h : ρ.ref r = .extern r') :
    ∃ r₀, r = .extern r₀ ∧ ρ.ref r₀ = r' := by
  cases r <;> simp_all [Ren.ref]

/-- Run-time type checks agree on owned references (forward direction). -/
theorem refOk_of (hR : PartRel ρ O p σ) {r : Ref} {t : CRefType} (h : RefOk p r t) :
    O.GoodRef r → RefOk σ (ρ.ref r) t := by
  induction h with
  | null => intro _; exact .null
  | i31 b => intro _; exact .i31 b
  | @struct a si₀ hs =>
    intro hr
    obtain ⟨si, h1, h2, -⟩ := hR.st _ hr
    have hsi : si₀ = si := Option.some.inj (hs.symm.trans h1)
    have hok : RefOk σ (.struct (ρ.st a)) (.ref false (.defHeap (ρ.sinst si).type)) := .struct h2
    simpa [Ren.sinst, hsi] using hok
  | @array a ai₀ hs =>
    intro hr
    obtain ⟨ai, h1, h2, -⟩ := hR.ar _ hr
    have hai : ai₀ = ai := Option.some.inj (hs.symm.trans h1)
    have hok : RefOk σ (.array (ρ.ar a)) (.ref false (.defHeap (ρ.ainst ai).type)) := .array h2
    simpa [Ren.ainst, hai] using hok
  | @func a fi₀ hf =>
    intro hr
    obtain ⟨fi, h1, fi', h2, h3, -⟩ := hR.fn _ hr
    have hfi : fi₀ = fi := Option.some.inj (hf.symm.trans h1)
    have hok : RefOk σ (.func a) (.ref false (.defHeap fi'.type)) := .func h2
    rw [Ren.ref_func, hfi, ← h3]
    exact hok
  | exn _ => intro hr; exact hr.elim
  | host a => intro _; exact .host a
  | extern _ hn ih =>
    intro hr
    exact .extern (ih hr) (by rwa [Ne, Ren.ref_eq_null_iff])
  | sub _ hok hs ih => intro hr; exact .sub (ih hr) hok hs

/-- Run-time type checks agree on owned references (backward direction). -/
theorem refOk_back (hR : PartRel ρ O p σ) {r' : Ref} {t : CRefType} (h : RefOk σ r' t) :
    ∀ r, ρ.ref r = r' → O.GoodRef r → RefOk p r t := by
  induction h with
  | null =>
    intro r hr _
    have hr0 : r = .null := (Ren.ref_eq_null_iff _).mp hr
    rw [hr0]
    exact .null
  | i31 b =>
    intro r hr _
    have hr0 : r = .i31 b := ref_eq_i31_inv hr
    rw [hr0]
    exact .i31 b
  | @struct a' si' hs =>
    show ∀ r, ρ.ref r = .struct a' → O.GoodRef r →
      RefOk p r (.ref false (.defHeap si'.type))
    intro r hr hg
    obtain ⟨a, hr0, ha⟩ : ∃ a, r = .struct a ∧ ρ.st a = a' := ref_eq_struct_inv hr
    have hga : O.st a := by simpa [hr0, Own.GoodRef] using hg
    obtain ⟨si, h1, h2, -⟩ := hR.st _ hga
    have hsi : ρ.sinst si = si' := Option.some.inj (by rw [← h2, ha, hs])
    have hok : RefOk p (.struct a) (.ref false (.defHeap si.type)) := .struct h1
    rw [hr0, ← hsi]
    simpa [Ren.sinst] using hok
  | @array a' ai' hs =>
    show ∀ r, ρ.ref r = .array a' → O.GoodRef r →
      RefOk p r (.ref false (.defHeap ai'.type))
    intro r hr hg
    obtain ⟨a, hr0, ha⟩ : ∃ a, r = .array a ∧ ρ.ar a = a' := ref_eq_array_inv hr
    have hga : O.ar a := by simpa [hr0, Own.GoodRef] using hg
    obtain ⟨ai, h1, h2, -⟩ := hR.ar _ hga
    have hai : ρ.ainst ai = ai' := Option.some.inj (by rw [← h2, ha, hs])
    have hok : RefOk p (.array a) (.ref false (.defHeap ai.type)) := .array h1
    rw [hr0, ← hai]
    simpa [Ren.ainst] using hok
  | @func a fi' hf =>
    show ∀ r, ρ.ref r = .func a → O.GoodRef r →
      RefOk p r (.ref false (.defHeap fi'.type))
    intro r hr hg
    have hr0 : r = .func a := ref_eq_func_inv hr
    have hga : O.fn a := by simpa [hr0, Own.GoodRef] using hg
    obtain ⟨fi, h1, fi'', h2, h3, -⟩ := hR.fn _ hga
    have hfi : fi'' = fi' := Option.some.inj (h2.symm.trans hf)
    have hok : RefOk p (.func a) (.ref false (.defHeap fi.type)) := .func h1
    rw [hr0, ← hfi, h3]
    exact hok
  | @exn a _ _ =>
    intro r hr hg
    have hr0 : r = .exn a := ref_eq_exn_inv hr
    exact absurd hg (by simp [hr0, Own.GoodRef])
  | host a =>
    intro r hr hg
    have hr0 : r = .host a := ref_eq_host_inv hr
    exact absurd hg (by simp [hr0, Own.GoodRef])
  | @extern r₁ _ hn ih =>
    intro r hr hg
    obtain ⟨r₀, hr0, hr₀⟩ : ∃ r₀, r = .extern r₀ ∧ ρ.ref r₀ = r₁ := ref_eq_extern_inv hr
    have hg₀ : O.GoodRef r₀ := by simpa [hr0, Own.GoodRef] using hg
    have hn₀ : r₀ ≠ .null := fun h0 => hn (by rw [← hr₀, h0]; rfl)
    rw [hr0]
    exact .extern (ih r₀ hr₀ hg₀) hn₀
  | sub _ hok hs ih => intro r hr hg; exact .sub (ih r hr hg) hok hs

theorem refOk_iff (hR : PartRel ρ O p σ) {r : Ref} {t : CRefType} (hr : O.GoodRef r) :
    RefOk σ (ρ.ref r) t ↔ RefOk p r t :=
  ⟨fun h => hR.refOk_back h r rfl hr, fun h => hR.refOk_of h hr⟩

/-- A relation of a part survives a `Touch` of the shared store by another part whose image
is disjoint. -/
theorem touch {ρ₁ : Ren} {O₁ : Own} {σ' : Store H} (hR : PartRel ρ O p σ)
    (ht : Touch ρ₁ O₁ σ σ')
    (hgl : ∀ a, O.gl a → ¬ O₁.gl a)
    (hst : ∀ a b, O.st a → O₁.st b → ρ₁.st b ≠ ρ.st a)
    (har : ∀ a b, O.ar a → O₁.ar b → ρ₁.ar b ≠ ρ.ar a) : PartRel ρ O p σ' where
  fn a ha := by rw [ht.funcs]; exact hR.fn a ha
  gl a ha := by rw [ht.globals a (hgl a ha)]; exact hR.gl a ha
  st a ha := by
    obtain ⟨si, h1, h2, h3⟩ := hR.st a ha
    refine ⟨si, h1, ?_, h3⟩
    rw [ht.structs _ (fun b hb => hst a b ha hb) ((List.getElem?_eq_some_iff.mp h2).1)]
    exact h2
  ar a ha := by
    obtain ⟨ai, h1, h2, h3⟩ := hR.ar a ha
    refine ⟨ai, h1, ?_, h3⟩
    rw [ht.arrays _ (fun b hb => har a b ha hb) ((List.getElem?_eq_some_iff.mp h2).1)]
    exact h2
  stInj := hR.stInj
  arInj := hR.arInj

theorem st_lt (hR : PartRel ρ O p σ) {a : Nat} (ha : O.st a) :
    a < p.structs.length ∧ ρ.st a < σ.structs.length := by
  obtain ⟨si, h1, h2, -⟩ := hR.st a ha
  exact ⟨(List.getElem?_eq_some_iff.mp h1).1, (List.getElem?_eq_some_iff.mp h2).1⟩

theorem ar_lt (hR : PartRel ρ O p σ) {a : Nat} (ha : O.ar a) :
    a < p.arrays.length ∧ ρ.ar a < σ.arrays.length := by
  obtain ⟨ai, h1, h2, -⟩ := hR.ar a ha
  exact ⟨(List.getElem?_eq_some_iff.mp h1).1, (List.getElem?_eq_some_iff.mp h2).1⟩

end PartRel

namespace Touch

variable {ρ : Ren} {O : Own} {σ σ' σ'' : Store H}

theorem refl (ρ : Ren) (O : Own) (σ : Store H) : Touch ρ O σ σ :=
  ⟨rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, le_rfl, le_rfl⟩

/-- Touches compose when the ownership grows (new addresses are fresh). -/
theorem trans {ρ' : Ren} {O' : Own} (h : Touch ρ O σ σ') (hg : Grow ρ O ρ' O' σ)
    (h' : Touch ρ' O' σ' σ'') : Touch ρ O σ σ'' where
  funcs := h'.funcs.trans h.funcs
  globals a ha := by
    rw [h'.globals a (by rwa [hg.gl]), h.globals a ha]
  structs a ha hl := by
    rw [h'.structs a ?_ (lt_of_lt_of_le hl h.structs_len), h.structs a ha hl]
    intro b hb e
    rcases hg.stNew b hb with h1 | h1
    · exact ha b h1 ((hg.st b h1).2 ▸ e)
    · omega
  arrays a ha hl := by
    rw [h'.arrays a ?_ (lt_of_lt_of_le hl h.arrays_len), h.arrays a ha hl]
    intro b hb e
    rcases hg.arNew b hb with h1 | h1
    · exact ha b h1 ((hg.ar b h1).2 ▸ e)
    · omega
  structs_len := le_trans h.structs_len h'.structs_len
  arrays_len := le_trans h.arrays_len h'.arrays_len

end Touch

end Silmaril.Proofs.Wasm.Game.Linking.Split
