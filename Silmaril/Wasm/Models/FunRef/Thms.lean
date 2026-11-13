module

public import Silmaril.Wasm.Models.FunRef.Defs
public import Silmaril.Wasm.Models.Game.Thms
public import Mathlib.Data.List.Forall2

/-!
# FunRef: type soundness and the game reading

* `eval_sound`: in a typed heap and environment, a well-typed term evaluates to a value of its
  type, in a larger typed heap (type safety and normalisation; there is no recursion, and cells
  hold no functions, so no recursion through the heap either).
* `Prog.run_sound`, `Prog.obs_eq_word`: a well-typed program returns one word on every argument.
* `strat_answers`: `funRefModel.strat p ⊨ □ AnsIs p` in `GInst`.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunRef

open Silmaril.Wasm (Behaviour)
open Silmaril.Games
open Silmaril.Wasm.Models.FunLang (Arith Cmp)

/-! ## Typed values and heaps -/

theorem getElem?_of_prefix {α : Type} {l l' : List α} (h : l <+: l') {i : Nat} {x : α}
    (hi : l[i]? = some x) : l'[i]? = some x := by
  obtain ⟨t, rfl⟩ := h
  have hlt : i < l.length := (List.getElem?_eq_some_iff.1 hi).1
  rw [List.getElem?_append_left hlt]
  exact hi

/-- Typing survives heap growth. -/
theorem ValTy.mono {Ψ Ψ' : List Ty} (h : Ψ <+: Ψ') {v : Val} {τ : Ty} (hv : ValTy Ψ v τ) :
    ValTy Ψ' v τ := by
  induction hv with
  | int n => exact .int n
  | bool b => exact .bool b
  | pair _ _ iha ihb => exact .pair iha ihb
  | inl τ _ ih => exact .inl τ ih
  | inr σ _ ih => exact .inr σ ih
  | loc hl => exact .loc (getElem?_of_prefix h hl)

theorem env_mono {Ψ Ψ' : List Ty} (h : Ψ <+: Ψ') {ρ : List Val} {Γ : List Ty}
    (hρ : List.Forall₂ (ValTy Ψ) ρ Γ) : List.Forall₂ (ValTy Ψ') ρ Γ :=
  hρ.imp fun _ _ hv => hv.mono h

theorem ValTy.int_inv {Ψ : List Ty} {v : Val} (h : ValTy Ψ v .int) : ∃ n, v = .int n := by
  cases h
  exact ⟨_, rfl⟩

theorem ValTy.bool_inv {Ψ : List Ty} {v : Val} (h : ValTy Ψ v .bool) : ∃ b, v = .bool b := by
  cases h
  exact ⟨_, rfl⟩

theorem ValTy.prod_inv {Ψ : List Ty} {v : Val} {σ τ : Ty} (h : ValTy Ψ v (.prod σ τ)) :
    ∃ a b, v = .pair a b ∧ ValTy Ψ a σ ∧ ValTy Ψ b τ := by
  cases h with
  | pair ha hb => exact ⟨_, _, rfl, ha, hb⟩

theorem ValTy.sum_inv {Ψ : List Ty} {v : Val} {σ τ : Ty} (h : ValTy Ψ v (.sum σ τ)) :
    (∃ a, v = .inl a ∧ ValTy Ψ a σ) ∨ (∃ b, v = .inr b ∧ ValTy Ψ b τ) := by
  cases h with
  | inl _ ha => exact .inl ⟨_, rfl, ha⟩
  | inr _ hb => exact .inr ⟨_, rfl, hb⟩

theorem ValTy.ref_inv {Ψ : List Ty} {v : Val} {τ : Ty} (h : ValTy Ψ v (.ref τ)) :
    ∃ l, v = .loc l ∧ Ψ[l]? = some τ := by
  cases h with
  | loc hl => exact ⟨_, rfl, hl⟩

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : List.Forall₂ R as bs) {i : Nat} {b : β} (hi : bs[i]? = some b) :
    ∃ a, as[i]? = some a ∧ R a b := by
  induction h generalizing i with
  | nil => exact absurd hi (by simp)
  | cons hab _ ih =>
    cases i with
    | zero => exact ⟨_, rfl, (Option.some.inj hi) ▸ hab⟩
    | succ i => exact ih hi

theorem HeapTy.alloc {Ψ : List Ty} {σ : Heap} (h : HeapTy Ψ σ) {v : Val} {τ : Ty}
    (hv : ValTy Ψ v τ) : HeapTy (Ψ ++ [τ]) (σ ++ [v]) :=
  List.rel_append (env_mono (List.prefix_append _ _) h)
    (.cons (hv.mono (List.prefix_append _ _)) .nil)

theorem forall₂_set {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : List.Forall₂ R as bs) {l : Nat} {b : β} (hl : bs[l]? = some b) {a : α} (ha : R a b) :
    List.Forall₂ R (as.set l a) bs := by
  induction h generalizing l with
  | nil => exact absurd hl (by simp)
  | cons hab _ ih =>
    cases l with
    | zero =>
      have hb : _ = b := Option.some.inj hl
      exact .cons (hb ▸ ha) (by assumption)
    | succ l => exact .cons hab (ih hl)

theorem HeapTy.set {Ψ : List Ty} {σ : Heap} (h : HeapTy Ψ σ) {l : Nat} {τ : Ty}
    (hl : Ψ[l]? = some τ) {v : Val} (hv : ValTy Ψ v τ) : HeapTy Ψ (σ.set l v) :=
  forall₂_set h hl hv

/-! ## Type soundness, case by case -/

/-- A typed outcome: a value of type `τ` in a typed heap extending `Ψ`. -/
def Out (Ψ : List Ty) (r : Option (Val × Heap)) (τ : Ty) : Prop :=
  ∃ v σ' Ψ', Ψ <+: Ψ' ∧ r = some (v, σ') ∧ HeapTy Ψ' σ' ∧ ValTy Ψ' v τ

/-- What type soundness says of a term in a context. -/
def Sound (Γ : List Ty) (e : Tm) (τ : Ty) : Prop :=
  ∀ Ψ σ ρ, HeapTy Ψ σ → List.Forall₂ (ValTy Ψ) ρ Γ → Out Ψ (eval σ ρ e) τ

theorem sound_var {Γ : List Ty} {i : Nat} {τ : Ty} (hi : Γ[i]? = some τ) :
    Sound Γ (.var i) τ := by
  intro Ψ σ ρ hσ hρ
  obtain ⟨v, hv, hty⟩ := forall₂_getElem? hρ hi
  exact ⟨v, σ, Ψ, List.prefix_refl _, by simp [eval, hv], hσ, hty⟩

theorem sound_arith {Γ : List Ty} {a b : Tm} (op : Arith) (ha : Sound Γ a .int)
    (hb : Sound Γ b .int) : Sound Γ (.arith op a b) .int := by
  intro Ψ σ ρ hσ hρ
  obtain ⟨va, σ₁, Ψ₁, hΨ₁, hea, hσ₁, hta⟩ := ha Ψ σ ρ hσ hρ
  obtain ⟨vb, σ₂, Ψ₂, hΨ₂, heb, hσ₂, htb⟩ := hb Ψ₁ σ₁ ρ hσ₁ (env_mono hΨ₁ hρ)
  obtain ⟨x, rfl⟩ := hta.int_inv
  obtain ⟨y, rfl⟩ := htb.int_inv
  exact ⟨.int (op.eval x y), σ₂, Ψ₂, hΨ₁.trans hΨ₂, by simp [eval, hea, heb], hσ₂, .int _⟩

theorem sound_cmp {Γ : List Ty} {a b : Tm} (op : Cmp) (ha : Sound Γ a .int)
    (hb : Sound Γ b .int) : Sound Γ (.cmp op a b) .bool := by
  intro Ψ σ ρ hσ hρ
  obtain ⟨va, σ₁, Ψ₁, hΨ₁, hea, hσ₁, hta⟩ := ha Ψ σ ρ hσ hρ
  obtain ⟨vb, σ₂, Ψ₂, hΨ₂, heb, hσ₂, htb⟩ := hb Ψ₁ σ₁ ρ hσ₁ (env_mono hΨ₁ hρ)
  obtain ⟨x, rfl⟩ := hta.int_inv
  obtain ⟨y, rfl⟩ := htb.int_inv
  exact ⟨.bool (op.eval x y), σ₂, Ψ₂, hΨ₁.trans hΨ₂, by simp [eval, hea, heb], hσ₂, .bool _⟩

/-- An outcome seen from a smaller heap typing. -/
theorem Out.of_prefix {Ψ Ψ₁ : List Ty} (h : Ψ <+: Ψ₁) {r : Option (Val × Heap)} {τ : Ty}
    (ho : Out Ψ₁ r τ) : Out Ψ r τ := by
  obtain ⟨v, σ', Ψ', hΨ', hr, hσ', hv⟩ := ho
  exact ⟨v, σ', Ψ', h.trans hΨ', hr, hσ', hv⟩

theorem sound_ite {Γ : List Ty} {c t e : Tm} {τ : Ty} (hc : Sound Γ c .bool) (ht : Sound Γ t τ)
    (he : Sound Γ e τ) : Sound Γ (.ite c t e) τ := by
  intro Ψ σ ρ hσ hρ
  obtain ⟨vc, σ₁, Ψ₁, hΨ₁, hec, hσ₁, htc⟩ := hc Ψ σ ρ hσ hρ
  obtain ⟨b, rfl⟩ := htc.bool_inv
  cases b with
  | true =>
    have h := ht Ψ₁ σ₁ ρ hσ₁ (env_mono hΨ₁ hρ)
    simpa [eval, hec] using h.of_prefix hΨ₁
  | false =>
    have h := he Ψ₁ σ₁ ρ hσ₁ (env_mono hΨ₁ hρ)
    simpa [eval, hec] using h.of_prefix hΨ₁

theorem sound_let {Γ : List Ty} {a b : Tm} {σ τ : Ty} (ha : Sound Γ a σ)
    (hb : Sound (σ :: Γ) b τ) : Sound Γ (.let_ a b) τ := by
  intro Ψ h ρ hh hρ
  obtain ⟨va, h₁, Ψ₁, hΨ₁, hea, hh₁, hta⟩ := ha Ψ h ρ hh hρ
  have hb' := hb Ψ₁ h₁ (va :: ρ) hh₁ (.cons hta (env_mono hΨ₁ hρ))
  simpa [eval, hea] using hb'.of_prefix hΨ₁

theorem sound_pair {Γ : List Ty} {a b : Tm} {σ τ : Ty} (ha : Sound Γ a σ) (hb : Sound Γ b τ) :
    Sound Γ (.pair a b) (.prod σ τ) := by
  intro Ψ h ρ hh hρ
  obtain ⟨va, h₁, Ψ₁, hΨ₁, hea, hh₁, hta⟩ := ha Ψ h ρ hh hρ
  obtain ⟨vb, h₂, Ψ₂, hΨ₂, heb, hh₂, htb⟩ := hb Ψ₁ h₁ ρ hh₁ (env_mono hΨ₁ hρ)
  exact ⟨.pair va vb, h₂, Ψ₂, hΨ₁.trans hΨ₂, by simp [eval, hea, heb], hh₂,
    .pair (hta.mono hΨ₂) htb⟩

theorem sound_fst {Γ : List Ty} {e : Tm} {σ τ : Ty} (he : Sound Γ e (.prod σ τ)) :
    Sound Γ (.fst e) σ := by
  intro Ψ h ρ hh hρ
  obtain ⟨v, h₁, Ψ₁, hΨ₁, hev, hh₁, htv⟩ := he Ψ h ρ hh hρ
  obtain ⟨a, b, rfl, ha, -⟩ := htv.prod_inv
  exact ⟨a, h₁, Ψ₁, hΨ₁, by simp [eval, hev], hh₁, ha⟩

theorem sound_snd {Γ : List Ty} {e : Tm} {σ τ : Ty} (he : Sound Γ e (.prod σ τ)) :
    Sound Γ (.snd e) τ := by
  intro Ψ h ρ hh hρ
  obtain ⟨v, h₁, Ψ₁, hΨ₁, hev, hh₁, htv⟩ := he Ψ h ρ hh hρ
  obtain ⟨a, b, rfl, -, hb⟩ := htv.prod_inv
  exact ⟨b, h₁, Ψ₁, hΨ₁, by simp [eval, hev], hh₁, hb⟩

theorem sound_inl {Γ : List Ty} {e : Tm} {σ : Ty} (τ : Ty) (he : Sound Γ e σ) :
    Sound Γ (.inl e) (.sum σ τ) := by
  intro Ψ h ρ hh hρ
  obtain ⟨v, h₁, Ψ₁, hΨ₁, hev, hh₁, htv⟩ := he Ψ h ρ hh hρ
  exact ⟨.inl v, h₁, Ψ₁, hΨ₁, by simp [eval, hev], hh₁, .inl τ htv⟩

theorem sound_inr {Γ : List Ty} {e : Tm} {τ : Ty} (σ : Ty) (he : Sound Γ e τ) :
    Sound Γ (.inr e) (.sum σ τ) := by
  intro Ψ h ρ hh hρ
  obtain ⟨v, h₁, Ψ₁, hΨ₁, hev, hh₁, htv⟩ := he Ψ h ρ hh hρ
  exact ⟨.inr v, h₁, Ψ₁, hΨ₁, by simp [eval, hev], hh₁, .inr σ htv⟩

theorem sound_case {Γ : List Ty} {e l r : Tm} {σ τ υ : Ty} (he : Sound Γ e (.sum σ τ))
    (hl : Sound (σ :: Γ) l υ) (hr : Sound (τ :: Γ) r υ) : Sound Γ (.case e l r) υ := by
  intro Ψ h ρ hh hρ
  obtain ⟨v, h₁, Ψ₁, hΨ₁, hev, hh₁, htv⟩ := he Ψ h ρ hh hρ
  rcases htv.sum_inv with ⟨a, rfl, ha⟩ | ⟨b, rfl, hb⟩
  · have h' := hl Ψ₁ h₁ (a :: ρ) hh₁ (.cons ha (env_mono hΨ₁ hρ))
    simpa [eval, hev] using h'.of_prefix hΨ₁
  · have h' := hr Ψ₁ h₁ (b :: ρ) hh₁ (.cons hb (env_mono hΨ₁ hρ))
    simpa [eval, hev] using h'.of_prefix hΨ₁

theorem sound_ref {Γ : List Ty} {e : Tm} {τ : Ty} (he : Sound Γ e τ) :
    Sound Γ (.ref e) (.ref τ) := by
  intro Ψ h ρ hh hρ
  obtain ⟨v, h₁, Ψ₁, hΨ₁, hev, hh₁, htv⟩ := he Ψ h ρ hh hρ
  have hlen : h₁.length = Ψ₁.length := hh₁.length_eq
  have hloc : (Ψ₁ ++ [τ])[h₁.length]? = some τ := by simp [hlen]
  exact ⟨.loc h₁.length, h₁ ++ [v], Ψ₁ ++ [τ], hΨ₁.trans (List.prefix_append _ _),
    by simp [eval, hev], hh₁.alloc htv, .loc hloc⟩

theorem sound_get {Γ : List Ty} {e : Tm} {τ : Ty} (he : Sound Γ e (.ref τ)) :
    Sound Γ (.get e) τ := by
  intro Ψ h ρ hh hρ
  obtain ⟨v, h₁, Ψ₁, hΨ₁, hev, hh₁, htv⟩ := he Ψ h ρ hh hρ
  obtain ⟨l, rfl, hl⟩ := htv.ref_inv
  obtain ⟨u, hu, htu⟩ := forall₂_getElem? hh₁ hl
  exact ⟨u, h₁, Ψ₁, hΨ₁, by simp [eval, hev, hu], hh₁, htu⟩

theorem sound_set {Γ : List Ty} {a b : Tm} {τ : Ty} (ha : Sound Γ a (.ref τ))
    (hb : Sound Γ b τ) : Sound Γ (.set a b) .bool := by
  intro Ψ h ρ hh hρ
  obtain ⟨va, h₁, Ψ₁, hΨ₁, hea, hh₁, hta⟩ := ha Ψ h ρ hh hρ
  obtain ⟨l, rfl, hl⟩ := hta.ref_inv
  obtain ⟨vb, h₂, Ψ₂, hΨ₂, heb, hh₂, htb⟩ := hb Ψ₁ h₁ ρ hh₁ (env_mono hΨ₁ hρ)
  have hl₂ : Ψ₂[l]? = some τ := getElem?_of_prefix hΨ₂ hl
  have hlt : l < h₂.length := by
    rw [hh₂.length_eq]; exact (List.getElem?_eq_some_iff.1 hl₂).1
  exact ⟨.bool true, h₂.set l vb, Ψ₂, hΨ₁.trans hΨ₂, by simp [eval, hea, heb, hlt],
    hh₂.set hl₂ htb, .bool true⟩

/-- **Type soundness and normalisation.** -/
theorem eval_sound {Γ : List Ty} {e : Tm} {τ : Ty} (h : HasTy Γ e τ) : Sound Γ e τ := by
  induction h with
  | var hi => exact sound_var hi
  | int n => exact fun Ψ σ _ hσ _ => ⟨_, σ, Ψ, List.prefix_refl _, rfl, hσ, .int n⟩
  | bool b => exact fun Ψ σ _ hσ _ => ⟨_, σ, Ψ, List.prefix_refl _, rfl, hσ, .bool b⟩
  | arith op _ _ iha ihb => exact sound_arith op iha ihb
  | cmp op _ _ iha ihb => exact sound_cmp op iha ihb
  | ite _ _ _ ihc iht ihe => exact sound_ite ihc iht ihe
  | let_ _ _ iha ihb => exact sound_let iha ihb
  | pair _ _ iha ihb => exact sound_pair iha ihb
  | fst _ ih => exact sound_fst ih
  | snd _ ih => exact sound_snd ih
  | inl τ _ ih => exact sound_inl τ ih
  | inr σ _ ih => exact sound_inr σ ih
  | case _ _ _ ihe ihl ihr => exact sound_case ihe ihl ihr
  | ref _ ih => exact sound_ref ih
  | get _ ih => exact sound_get ih
  | set _ _ iha ihb => exact sound_set iha ihb

/-! ## Programs and the game reading -/

/-- A well-typed program returns a value of its result type on every argument. -/
theorem Prog.run_sound {p : Prog} (hp : p.WellTyped) (n : BitVec 31) :
    ∃ v σ Ψ, p.run n = some (v, σ) ∧ ValTy Ψ v p.res := by
  obtain ⟨v, σ, Ψ, -, hr, -, hv⟩ := eval_sound hp.1 [] [] [.int n] .nil (.cons (.int n) .nil)
  exact ⟨v, σ, Ψ, hr, hv⟩

/-- The word a program computes on `n` (`0` if it does not evaluate). -/
def Prog.word (p : Prog) (n : BitVec 31) : BitVec 31 := ((p.run n).map (obsWord ·.1)).getD 0

theorem Prog.obs_eq_word {p : Prog} (hp : p.WellTyped) (n : BitVec 31) :
    p.obs n = {.returns [p.word n]} := by
  obtain ⟨v, σ, -, hv, -⟩ := p.run_sound hp n
  ext b
  simp [Prog.obs, Prog.word, hv]

/-- Every answer to the call `n` returns the program's word on `n`. -/
def AnsIs (p : Prog) : Set (List (Move Sig.empty (callSig (BitVec 31) (Behaviour (BitVec 31))))) :=
  {s | ∀ n o, (.inr (.ans n o) : Move Sig.empty (callSig (BitVec 31) (Behaviour (BitVec 31)))) ∈ s →
    o = .returns [p.word n]}

/-- `funRefModel.strat p ⊨ □ AnsIs p` in `GInst`. -/
theorem strat_answers {p : Prog} (hp : p.WellTyped) :
    (GSen.box (AnsIs p)).holds (funRefModel.strat p) := by
  intro s hs n o hm
  have ho : o ∈ p.obs n := hs.2 n o hm
  rw [Prog.obs_eq_word hp n] at ho
  exact ho

end Silmaril.Wasm.Models.FunRef
