module

public import Silmaril.Wasm.Binaryen.Typing
public import Silmaril.Wasm.Validation.Instructions.Properties

@[expose] public section

/-! # Typing-preserving replacement of Core instruction sequences

`TyRepl X Y`: in every well-formed context, every typing of `X` is a typing of
`Y`. It is a preorder, a congruence for concatenation (`TyRepl.append`, through
`InstrsOk.split`) and for the bodies of structured instructions
(`TyRepl.block`/`loop`/`if_`/`tryTable`). A replacement of one instruction is
justified by its `InstrOk` typings alone (`TyRepl.of_instr`), by induction on the
sequence derivation (no splitting needed).

These are the typing halves of the local rewrites of the passes: since typing is
by lowering (`SeqOk`), a pass preserves typing when its rewrites do.
-/

namespace Silmaril.Wasm.Binaryen

open Validation

/-- `Y` may replace `X` in every well-formed context. -/
def TyRepl (X Y : List Instr) : Prop :=
  ∀ (C : Context) (it : InstrType), C.Wf → InstrsOk C X it → InstrsOk C Y it

/-- Adding a label of a valid result type keeps a context well formed. -/
theorem wf_withLabel {C : Context} (hC : C.Wf) {t : List CValType}
    (ht : ResultOk C.toTypeCtx t) : (C.withLabel t).Wf := by
  refine ⟨hC.types, hC.tags, hC.globals, hC.tables, hC.funcs, hC.locals, ?_, hC.return_,
    hC.elems⟩
  intro ts h
  simp only [Context.withLabel, List.mem_cons] at h
  rcases h with rfl | h
  · exact ht
  · exact hC.labels _ h

/-- The empty sequence at a regular subtype-of-identity type whose initialised
locals are already set. -/
theorem nil_typed {C : Context} {p r : List CValType} {xs : List Nat}
    (hok : InstrTypeOk C ⟨p, xs, r⟩) (hs : ResultSub C.toTypeCtx p r)
    (hx : ∀ x ∈ xs, ∃ t, C.locals[x]? = some ⟨.set, t⟩) : InstrsOk C [] ⟨p, xs, r⟩ :=
  .sub (InstrsOk.id hok.1) ⟨ResultSub.refl _ _, hs, fun x hx' _ => hx x hx'⟩ hok

/-- Locals of a regular type that a split initialises from already-set locals. -/
theorem inits_set_of_split {C : Context} {it : InstrType} {xs : List Nat}
    (hreg : InstrTypeOk C it)
    (hL : LocalsLe (C.initLocals it.inits).locals (C.initLocals xs).locals)
    (hxs : ∀ x ∈ xs, ∃ t, C.locals[x]? = some ⟨.set, t⟩) :
    ∀ x ∈ it.inits, ∃ t, C.locals[x]? = some ⟨.set, t⟩ := by
  intro x hx
  obtain ⟨lt, hlt⟩ := hreg.2.2 x hx
  have h2 := hL.set (Context.initLocals_set_of_mem hx hlt)
  rw [Context.initLocals_of_set hxs] at h2
  exact ⟨_, h2⟩

/-- Splitting a `Forall₂` at a length. -/
theorem forall₂_append_inv {α β : Type _} {R : α → β → Prop} {a b : List α} {c d : List β}
    (h : List.Forall₂ R (a ++ b) (c ++ d)) (hl : a.length = c.length) :
    List.Forall₂ R a c ∧ List.Forall₂ R b d := by
  induction a generalizing c with
  | nil =>
    cases c with
    | nil => exact ⟨.nil, by simpa using h⟩
    | cons _ _ => simp at hl
  | cons x a ih =>
    cases c with
    | nil => simp at hl
    | cons y c =>
      cases h with
      | cons hxy h' =>
        obtain ⟨h1, h2⟩ := ih h' (by simpa using hl)
        exact ⟨.cons hxy h1, h2⟩

/-- Splitting a result-type subtyping at a length. -/
theorem resultSub_append_inv {Δ : TypeCtx} {a b c d : List CValType}
    (h : ResultSub Δ (a ++ b) (c ++ d)) (hl : a.length = c.length) :
    ResultSub Δ a c ∧ ResultSub Δ b d := by
  induction a generalizing c with
  | nil =>
    cases c with
    | nil => exact ⟨.nil, by simpa using h⟩
    | cons _ _ => simp at hl
  | cons x a ih =>
    cases c with
    | nil => simp at hl
    | cons y c =>
      cases h with
      | cons hxy h' =>
        obtain ⟨h1, h2⟩ := ih h' (by simpa using hl)
        exact ⟨.cons hxy h1, h2⟩

theorem resultSub_length {Δ : TypeCtx} {a b : List CValType} (h : ResultSub Δ a b) :
    a.length = b.length := List.Forall₂.length_eq h

/-- Inversion for one instruction, also recording that the frame is valid. -/
theorem single_inv_aux' {C : Context} {is : List Instr} {i : Instr} {it : InstrType}
    (hC : C.Wf) (h : InstrsOk C is it) (his : is = [i]) :
    ∃ ts it₀, ResultOk C.toTypeCtx ts ∧ InstrOk C i it₀ ∧
      InstrTypeSub C ⟨ts ++ it₀.params, it₀.inits, ts ++ it₀.results⟩ it := by
  induction h using InstrsOk.ind with
  | nil => cases his
  | @instr C i' it₀ h =>
      cases his
      exact ⟨[], it₀, by simp [ResultOk], h, by simpa using InstrTypeSub.refl C it₀⟩
  | @cons C i' is t₁ t₂ t₃ xs₁ xs₂ hi _ hs _ =>
      obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp his
      obtain ⟨s, i₂⟩ := InstrsOk.nil_inv (hC.initLocals _) hs
      simp only [Context.initLocals_toTypeCtx] at s
      exact ⟨[], ⟨t₁, xs₁, t₂⟩, by simp [ResultOk], hi, by simpa using InstrTypeSub.seq_nil s i₂⟩
  | @seq C is₁ is₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ =>
      rcases List.append_eq_singleton_iff.mp his with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨s₁, i₁⟩ := InstrsOk.nil_inv hC h₁
        have hC₁ : C.initLocals xs₁ = C := Context.initLocals_of_set i₁
        obtain ⟨ts, it₀, hts, hi, hsub⟩ := ih₂ (hC.initLocals _) rfl
        rw [hC₁] at hi hsub h₂ hts
        refine ⟨ts, it₀, hts, hi, InstrTypeSub.trans hC.types (InstrsOk.regular hC h₂) hsub ?_⟩
        refine ⟨s₁, ResultSub.refl _ _, ?_⟩
        intro x hx hn
        rcases List.mem_append.mp hx with hx | hx
        · exact i₁ x hx
        · exact absurd hx hn
      · obtain ⟨ts, it₀, hts, hi, hsub⟩ := ih₁ hC rfl
        obtain ⟨s, i₂⟩ := InstrsOk.nil_inv (hC.initLocals _) h₂
        simp only [Context.initLocals_toTypeCtx] at s
        exact ⟨ts, it₀, hts, hi, InstrTypeSub.trans hC.types (InstrsOk.regular hC h₁) hsub
          (InstrTypeSub.seq_nil s i₂)⟩
  | sub h hs hok ih =>
      obtain ⟨ts, it₀, hts, hi, hsub⟩ := ih hC his
      exact ⟨ts, it₀, hts, hi, InstrTypeSub.trans hC.types (InstrsOk.regular hC h) hsub hs⟩
  | @frame C is ts' t₁ t₂ xs h hok ih =>
      obtain ⟨ts, it₀, hts, hi, hsub⟩ := ih hC his
      refine ⟨ts' ++ ts, it₀, ResultOk.append hok hts, hi, ?_⟩
      simpa using InstrTypeSub.frame hsub ts'

theorem single_inv' {C : Context} {i : Instr} {it : InstrType} (hC : C.Wf)
    (h : InstrsOk C [i] it) :
    ∃ ts it₀, ResultOk C.toTypeCtx ts ∧ InstrOk C i it₀ ∧
      InstrTypeSub C ⟨ts ++ it₀.params, it₀.inits, ts ++ it₀.results⟩ it :=
  single_inv_aux' hC h rfl

/-- Replacing one occurrence of an instruction, by induction on the derivation. -/
theorem replace_one {i : Instr} {Y : List Instr}
    (h : ∀ C it, C.Wf → InstrOk C i it → InstrsOk C Y it) :
    ∀ {C : Context} {L : List Instr} {it : InstrType}, InstrsOk C L it → C.Wf →
      ∀ P Q, L = P ++ i :: Q → InstrsOk C (P ++ Y ++ Q) it := by
  intro C L it hL
  induction hL using InstrsOk.ind with
  | nil => intro _ P Q hPQ; cases P <;> simp at hPQ
  | @instr C i' it' hi =>
      intro hC P Q hPQ
      match P, Q, hPQ with
      | [], [], hPQ =>
          simp only [List.nil_append, List.cons.injEq, and_true] at hPQ
          subst hPQ
          simpa using h C it' hC hi
      | [], _ :: _, hPQ => simp at hPQ
      | _ :: P', _, hPQ => simp at hPQ
  | @seq C is₁ is₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ =>
      intro hC P Q hPQ
      rcases List.append_eq_append_iff.mp hPQ with ⟨a, rfl, ha⟩ | ⟨c, hc, hQ⟩
      · have := InstrsOk.seq h₁ hx (ih₂ (hC.initLocals _) a Q ha)
        simpa [List.append_assoc] using this
      · cases c with
        | nil =>
          simp only [List.append_nil, List.nil_append] at hc hQ
          subst hc
          have := InstrsOk.seq h₁ hx (ih₂ (hC.initLocals _) [] Q hQ.symm)
          simpa [List.append_assoc] using this
        | cons j c' =>
          simp only [List.cons_append, List.cons.injEq] at hQ
          obtain ⟨rfl, rfl⟩ := hQ
          have := InstrsOk.seq (ih₁ hC P c' hc) hx h₂
          simpa [List.append_assoc] using this
  | @cons C i' is t₁ t₂ t₃ xs₁ xs₂ hi hx hs ih =>
      intro hC P Q hPQ
      cases P with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hPQ
        obtain ⟨rfl, rfl⟩ := hPQ
        simpa using InstrsOk.seq (h C _ hC hi) hx hs
      | cons a P' =>
        simp only [List.cons_append, List.cons.injEq] at hPQ
        obtain ⟨rfl, hPQ⟩ := hPQ
        simpa using InstrsOk.cons hi hx (ih (hC.initLocals _) P' Q hPQ)
  | sub h hs hok ih => intro hC P Q hPQ; exact .sub (ih hC P Q hPQ) hs hok
  | frame h hok ih => intro hC P Q hPQ; exact .frame (ih hC P Q hPQ) hok

namespace TyRepl

theorem refl (X : List Instr) : TyRepl X X := fun _ _ _ h => h

theorem trans {X Y Z : List Instr} (h₁ : TyRepl X Y) (h₂ : TyRepl Y Z) : TyRepl X Z :=
  fun C it hC h => h₂ C it hC (h₁ C it hC h)

/-- One instruction, justified by its own typings. -/
theorem of_instr {i : Instr} {Y : List Instr}
    (h : ∀ C it, C.Wf → InstrOk C i it → InstrsOk C Y it) : TyRepl [i] Y :=
  fun _ _ hC hX => by simpa using replace_one h hX hC [] [] rfl

/-- **Congruence for concatenation.** -/
theorem append {X Y X' Y' : List Instr} (h : TyRepl X Y) (h' : TyRepl X' Y') :
    TyRepl (X ++ X') (Y ++ Y') := by
  intro C it hC hX
  obtain ⟨t₂, xs₁, xs₂, h₁, h₂, hL⟩ := InstrsOk.split hC hX rfl
  have r₁ := InstrsOk.regular hC h₁
  have hY := InstrsOk.seq (h C _ hC h₁) r₁.2.2 (h' _ _ (hC.initLocals _) h₂)
  have hreg := InstrsOk.regular hC hX
  refine .sub hY ⟨ResultSub.refl _ _, ResultSub.refl _ _, ?_⟩ hreg
  intro x hx hn
  obtain ⟨lt, hlt⟩ := hreg.2.2 x hx
  have h2 := hL.set (Context.initLocals_set_of_mem hx hlt)
  rcases Context.initLocals_set h2 with hm | hm
  · exact absurd hm hn
  · exact ⟨_, hm⟩

theorem append_left {X Y : List Instr} (P : List Instr) (h : TyRepl X Y) :
    TyRepl (P ++ X) (P ++ Y) := append (refl P) h

theorem append_right {X Y : List Instr} (h : TyRepl X Y) (Q : List Instr) :
    TyRepl (X ++ Q) (Y ++ Q) := append h (refl Q)

theorem block {B B' : List Instr} (h : TyRepl B B') (bt : BlockType) :
    TyRepl [.block bt B] [.block bt B'] :=
  of_instr fun C it hC hi => by
    cases hi with
    | block hbt hb => exact .instr (.block hbt (h _ _ (wf_withLabel hC (hbt.regular hC).2) hb))
    | _ => rename_i h; cases h

theorem loop {B B' : List Instr} (h : TyRepl B B') (bt : BlockType) :
    TyRepl [.loop bt B] [.loop bt B'] :=
  of_instr fun C it hC hi => by
    cases hi with
    | loop hbt hb => exact .instr (.loop hbt (h _ _ (wf_withLabel hC (hbt.regular hC).1) hb))
    | _ => rename_i h; cases h

theorem if_ {B₁ B₁' B₂ B₂' : List Instr} (h₁ : TyRepl B₁ B₁') (h₂ : TyRepl B₂ B₂')
    (bt : BlockType) : TyRepl [.if_ bt B₁ B₂] [.if_ bt B₁' B₂'] :=
  of_instr fun C it hC hi => by
    cases hi with
    | if_ hbt hb₁ hb₂ =>
      have hW := wf_withLabel hC (hbt.regular hC).2
      exact .instr (.if_ hbt (h₁ _ _ hW hb₁) (h₂ _ _ hW hb₂))
    | _ => rename_i h; cases h

theorem tryTable {B B' : List Instr} (h : TyRepl B B') (bt : BlockType) (cs : List Catch) :
    TyRepl [.tryTable bt cs B] [.tryTable bt cs B'] :=
  of_instr fun C it hC hi => by
    cases hi with
    | tryTable hbt hb hc =>
      exact .instr (.tryTable hbt (h _ _ (wf_withLabel hC (hbt.regular hC).2) hb) hc)
    | _ => rename_i h; cases h

end TyRepl

/-! ## Local initialisation -/

/-- Instructions that initialise a local. -/
def initsLocal : Instr → Bool
  | .localSet _ | .localTee _ => true
  | _ => false

theorem InstrOk.inits_nil {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it)
    (hi : initsLocal i = false) : it.inits = [] := by
  cases h with
  | «variable» h => cases h <;> first | rfl | simp [initsLocal] at hi
  | parametric h => cases h <;> rfl
  | numeric h => cases h <;> rfl
  | vector h => cases h <;> rfl
  | memory h => cases h <;> rfl
  | table h => cases h <;> rfl
  | reference h => cases h <;> rfl
  | _ => rfl

/-- Code initialising no local can only claim locals that are already set. -/
theorem InstrsOk.inits_set {C : Context} {L : List Instr} {it : InstrType} (h : InstrsOk C L it)
    (hL : ∀ i ∈ L, initsLocal i = false) :
    ∀ x ∈ it.inits, ∃ t, C.locals[x]? = some ⟨.set, t⟩ := by
  induction h using InstrsOk.ind with
  | nil => simp
  | instr hi => simp [InstrOk.inits_nil hi (hL _ (by simp))]
  | @seq C is₁ is₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ =>
      have i₁ := ih₁ (fun i hi => hL i (List.mem_append_left _ hi))
      have i₂ := ih₂ (fun i hi => hL i (List.mem_append_right _ hi))
      rw [Context.initLocals_of_set i₁] at i₂
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      exacts [i₁ x hx, i₂ x hx]
  | @cons C i is t₁ t₂ t₃ xs₁ xs₂ hi hx hs ih =>
      have e := InstrOk.inits_nil hi (hL i (by simp))
      simp only at e
      subst e
      have i₂ := ih (fun j hj => hL j (List.mem_cons_of_mem _ hj))
      simpa using i₂
  | @sub C is it₀ it' h hs hok ih =>
      intro x hx
      by_cases hx' : x ∈ it₀.inits
      · exact ih hL x hx'
      · exact hs.2.2 x hx hx'
  | frame h hok ih => exact ih hL

end Silmaril.Wasm.Binaryen
