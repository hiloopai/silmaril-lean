module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.Basic

/-!
# Round 7, REH route 2: lists of conforming values (unrefined)

From `List.Forall₂ (EOk S T Γ)` between expressions and their values, the list judgments of the
flow check (`ckL`, `ckT`, `ckFs`, `ckFsN`, `nxEs`, `nxDs`, `nxFs`) give conformance of the values.
Also the value operations that only produce numbers or Booleans, the row scopes of an
iteration, and the type of each domain variable.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

variable {S : Sig} {T : TSig} {Γ : List (String × AT)}

theorem ckL_sound {a : AT} : ∀ {es : List Exp} {vs : List Value},
    List.Forall₂ (EOk S T Γ) es vs → ckL S T Γ a es = true → ∀ w ∈ vs, vtB S a w = true
  | _, _, .nil, _, w, hw => by simp at hw
  | e :: es, v :: vs, .cons h hs, hc, w, hw => by
    simp only [ckL, Bool.and_eq_true] at hc
    rcases List.mem_cons.1 hw with rfl | hw
    · exact h.ck a hc.1
    · exact ckL_sound hs hc.2 w hw

theorem ckT_sound : ∀ {xs : List AT} {es : List Exp} {vs : List Value},
    List.Forall₂ (EOk S T Γ) es vs → ckT S T Γ xs es = true → vtT S xs vs = true
  | _, _, _, .nil, _ => by simp [vtT]
  | xs, e :: es, v :: vs, .cons h hs, hc => by
    simp only [ckT, Bool.and_eq_true] at hc
    simp only [vtT, Bool.and_eq_true]
    exact ⟨h.ck _ hc.1, ckT_sound hs hc.2⟩

theorem nxDs_sound : ∀ {es : List Exp} {vs : List Value},
    List.Forall₂ (EOk S T Γ) es vs → nxDs S Γ es = true → nxBs vs = true
  | _, _, .nil, _ => by simp [nxBs]
  | e :: es, v :: vs, .cons h hs, hc => by
    simp only [nxDs, Bool.and_eq_true] at hc
    simp only [nxBs, Bool.and_eq_true]
    exact ⟨h.nx hc.1, nxDs_sound hs hc.2⟩

theorem nxEs_sound : ∀ {es : List Exp} {vs : List Value},
    List.Forall₂ (EOk S T Γ) es vs → nxEs S Γ es = true → nxBs vs = true
  | _, _, .nil, _ => by simp [nxBs]
  | e :: es, v :: vs, .cons h hs, hc => by
    simp only [nxEs, Bool.and_eq_true] at hc
    simp only [nxBs, Bool.and_eq_true]
    exact ⟨h.nx (nxD_of_nxE e hc.1), nxEs_sound hs hc.2⟩

/-- The relation between record fields and their values. -/
def FOk (S : Sig) (T : TSig) (Γ : List (String × AT)) (f : ExpField) (g : AtomS × Value) :
    Prop :=
  match f with
  | .mk a e => g.1 = a ∧ EOk S T Γ e g.2

theorem ckFs_sound {n : String} : ∀ {fs : List ExpField} {gs : List (AtomS × Value)},
    List.Forall₂ (FOk S T Γ) fs gs → ckFs S T Γ n fs = true → vtF S n gs = true
  | _, _, .nil, _ => by simp [vtF]
  | .mk a e :: fs, (k, v) :: gs, .cons h hs, hc => by
    simp only [ckFs, Bool.and_eq_true] at hc
    obtain ⟨hk, he⟩ := h
    simp only at hk he
    subst hk
    simp only [vtF, Bool.and_eq_true]
    exact ⟨he.ck _ hc.1, ckFs_sound hs hc.2⟩

theorem ckFsN_sound : ∀ {fs : List ExpField} {gs : List (AtomS × Value)},
    List.Forall₂ (FOk S T Γ) fs gs → ckFsN S T Γ fs = true → nxBf gs = true
  | _, _, .nil, _ => by simp [nxBf]
  | .mk a e :: fs, (k, v) :: gs, .cons h hs, hc => by
    simp only [ckFsN, Bool.and_eq_true] at hc
    obtain ⟨hk, he⟩ := h
    simp only at hk he
    subst hk
    simp only [nxBf, Bool.and_eq_true]
    exact ⟨⟨(vtB_base_iff).1 (he.ck _ hc.1.2), hc.1.1⟩, ckFsN_sound hs hc.2⟩

theorem nxFs_sound : ∀ {fs : List ExpField} {gs : List (AtomS × Value)},
    List.Forall₂ (FOk S T Γ) fs gs → nxFs S Γ fs = true → nxBf gs = true
  | _, _, .nil, _ => by simp [nxBf]
  | .mk a e :: fs, (k, v) :: gs, .cons h hs, hc => by
    simp only [nxFs, Bool.and_eq_true] at hc
    obtain ⟨hk, he⟩ := h
    simp only at hk he
    subst hk
    simp only [nxBf, Bool.and_eq_true]
    exact ⟨⟨he.nx (nxD_of_nxE e hc.1.2), hc.1.1⟩, nxFs_sound hs hc.2⟩

/-! ## Values of operators -/

theorem nxB_bool (b : Bool) : nxB (.bool b) = true := by simp [nxB]

theorem nxB_num (m : Num) : nxB (.num m) = true := by simp [nxB]

theorem unValue_nx {op : UnOp} {v w : Value} (h : unValue op v = .ok w) : nxB w = true := by
  unfold unValue at h
  split at h
  · cases h; exact nxB_bool _
  · simp only [Res.ofOption_eq_ok, Option.map_eq_some_iff] at h
    obtain ⟨m, _, rfl⟩ := h; exact nxB_num _
  · cases h

theorem binValues_nx {op : BinOp} {v₁ v₂ w : Value} (h : binValues op v₁ v₂ = .ok w) :
    nxB w = true := by
  unfold binValues at h
  split at h
  · simp only [Res.ofOption_eq_ok, Option.map_eq_some_iff] at h
    obtain ⟨m, _, rfl⟩ := h; exact nxB_bool _
  · simp only [Res.ofOption_eq_ok, Option.map_eq_some_iff] at h
    obtain ⟨m, _, rfl⟩ := h; exact nxB_num _
  · cases h

theorem cmpValues_nx {op : CmpOp} {v₁ v₂ w : Value} (h : cmpValues op v₁ v₂ = .ok w) :
    nxB w = true := by
  unfold cmpValues at h
  split at h
  · cases h; exact nxB_bool _
  · cases h; exact nxB_bool _
  · simp only [Res.ofOption_eq_ok, Option.map_eq_some_iff] at h
    obtain ⟨m, _, rfl⟩ := h; exact nxB_bool _
  · cases h

theorem memValue_nx {v₁ v₂ w : Value} (h : memValue v₁ v₂ = .ok w) : nxB w = true := by
  unfold memValue at h
  split at h <;> first | (cases h; exact nxB_bool _) | cases h

theorem boolShort_nx {op : BinOp} {v w : Value} (h : boolShort op v = some w) :
    nxB w = true := by
  unfold boolShort at h
  split at h <;> first | (cases h; exact nxB_bool _) | cases h

/-! ## Reading values -/

theorem vtB_idx? {a : AT} {v w : Value} {i : Nat} (h : vtB S a v = true)
    (hi : v.idx? i = some w) : vtB S (elemOf S a) w = true := by
  cases v with
  | list vs => exact vtB_elem h w (List.mem_of_getElem? hi)
  | _ => simp [Value.idx?] at hi

theorem nxB_field? {v w : Value} {k : AtomS} (h : nxB v = true) (hf : v.field? k = some w) :
    nxB w = true := by
  cases v with
  | struct gs =>
    simp only [Value.field?_struct, Option.map_eq_some_iff] at hf
    obtain ⟨g, hg, rfl⟩ := hf
    simp only [nxB] at h
    exact nxBf_find h hg
  | _ => simp [Value.field?] at hf

theorem nxB_of_base {v : Value} (h : vtB S .base v = true) : nxB v = true := (vtB_base_iff).1 h

theorem base_of_nxB {v : Value} (h : nxB v = true) : vtB S .base v = true := (vtB_base_iff).2 h

/-! ## Domain variables -/

theorem domsΓ_nil : domsΓ S Γ [] = [] := by rw [domsΓ]

theorem domsΓ_cons (y : IL.Id) (e : Exp) (ds : List Dom) :
    domsΓ S Γ (.mk y e :: ds) = (y, elemAT S (tyOf S Γ e)) :: domsΓ S Γ ds := by rw [domsΓ]

theorem domsΓ_lookup_some : ∀ {ds : List Dom} {x : String} {a : AT},
    (domsΓ S Γ ds).lookup x = some a → ∃ d ∈ ds, domVar d = x
  | [], _, _, h => by rw [domsΓ_nil] at h; cases h
  | .mk y e :: ds, x, a, h => by
    rw [domsΓ_cons, List.lookup_cons] at h
    split at h
    · rename_i hy
      exact ⟨.mk y e, List.mem_cons_self .., (beq_iff_eq.1 hy).symm⟩
    · obtain ⟨d, hd, hx⟩ := domsΓ_lookup_some h
      exact ⟨d, List.mem_cons_of_mem _ hd, hx⟩

theorem domsΓ_lookup_mem : ∀ {ds : List Dom}, nodupB (ds.map domVar) = true →
    ∀ d ∈ ds, (domsΓ S Γ ds).lookup (domVar d) = some (elemAT S (tyOf S Γ (domSrc d)))
  | [], _, d, hd => by simp at hd
  | .mk y e :: ds, hnd, d, hd => by
    simp only [List.map_cons, nodupB, Bool.and_eq_true] at hnd
    obtain ⟨h1, h2⟩ := hnd
    rw [domsΓ_cons, List.lookup_cons]
    rcases List.mem_cons.1 hd with rfl | hd
    · simp [domVar, domSrc]
    · have hne : (domVar d == y) = false := by
        have hm : domVar d ∈ ds.map domVar := List.mem_map_of_mem hd
        cases h : (domVar d == y)
        · rfl
        · have : domVar d = y := by simpa using h
          rw [this] at hm
          have hc : (ds.map domVar).contains y = true := List.contains_iff_mem.2 hm
          simp only [show domVar (Dom.mk y e) = y from rfl, hc, Bool.not_true] at h1
          cases h1
      rw [hne]
      exact domsΓ_lookup_mem h2 d hd

/-- Composing two pointwise relations. -/
theorem forall₂_trans {α β γ : Type} {R₁ : α → β → Prop} {R₂ : β → γ → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ}, List.Forall₂ R₁ l₁ l₂ → List.Forall₂ R₂ l₂ l₃ →
      List.Forall₂ (fun a c => ∃ b, R₁ a b ∧ R₂ b c) l₁ l₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ hs₁, .cons h₂ hs₂ => .cons ⟨_, h₁, h₂⟩ (forall₂_trans hs₁ hs₂)

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ a ∈ l, ∃ b ∈ l', R a b
  | _, _, .nil, _, ha => by simp at ha
  | _ :: _, b :: _, .cons h hs, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b, List.mem_cons_self .., h⟩
    · obtain ⟨b', hb', h'⟩ := forall₂_mem_left hs a ha
      exact ⟨b', List.mem_cons_of_mem _ hb', h'⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
