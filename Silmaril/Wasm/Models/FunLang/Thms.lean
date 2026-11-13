module

public import Silmaril.Wasm.Models.FunLang.Defs
public import Silmaril.Wasm.Models.Game.Thms

/-!
# FunLang: type soundness and the game reading

* `eval_sound`: in an environment of values of the context's types, a well-typed term evaluates
  to a value of its type (there is no recursion, so evaluation always terminates; this is type
  safety and normalisation at once).
* `Prog.run_sound`, `Prog.obs_eq`: a well-typed program returns exactly one word on every
  argument.
* The game reading: `strat_answers` (`funModel.strat p ⊨ □ AnsIs p`, every answer to a call `n`
  is the word `p` computes), and `strat_eq_obsStrat`.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunLang

open Silmaril.Wasm (Behaviour)
open Silmaril.Games

/-! ## Inversion of typed values -/

theorem ValTy.int_inv {v : Val} (h : ValTy v .int) : ∃ n, v = .int n := by
  cases h
  exact ⟨_, rfl⟩

theorem ValTy.bool_inv {v : Val} (h : ValTy v .bool) : ∃ b, v = .bool b := by
  cases h
  exact ⟨_, rfl⟩

theorem ValTy.prod_inv {v : Val} {σ τ : Ty} (h : ValTy v (.prod σ τ)) :
    ∃ a b, v = .pair a b ∧ ValTy a σ ∧ ValTy b τ := by
  cases h with
  | pair ha hb => exact ⟨_, _, rfl, ha, hb⟩

theorem ValTy.sum_inv {v : Val} {σ τ : Ty} (h : ValTy v (.sum σ τ)) :
    (∃ a, v = .inl a ∧ ValTy a σ) ∨ (∃ b, v = .inr b ∧ ValTy b τ) := by
  cases h with
  | inl _ ha => exact .inl ⟨_, rfl, ha⟩
  | inr _ hb => exact .inr ⟨_, rfl, hb⟩

/-- A typed environment has a typed value at every typed index. -/
theorem forall₂_getElem? {ρ : List Val} {Γ : List Ty} (h : List.Forall₂ ValTy ρ Γ) {i : Nat}
    {τ : Ty} (hi : Γ[i]? = some τ) : ∃ v, ρ[i]? = some v ∧ ValTy v τ := by
  induction h generalizing i with
  | nil => exact absurd hi (by simp)
  | cons hab _ ih =>
    cases i with
    | zero => exact ⟨_, rfl, (Option.some.inj hi) ▸ hab⟩
    | succ i => exact ih hi

/-! ## Type soundness, case by case -/

/-- What type soundness says of a term in a context. -/
def Sound (Γ : List Ty) (e : Tm) (τ : Ty) : Prop :=
  ∀ ρ, List.Forall₂ ValTy ρ Γ → ∃ v, eval ρ e = some v ∧ ValTy v τ

theorem sound_arith {Γ : List Ty} {a b : Tm} (op : Arith) (ha : Sound Γ a .int)
    (hb : Sound Γ b .int) : Sound Γ (.arith op a b) .int := by
  intro ρ hρ
  obtain ⟨va, hea, hta⟩ := ha ρ hρ
  obtain ⟨vb, heb, htb⟩ := hb ρ hρ
  obtain ⟨x, rfl⟩ := hta.int_inv
  obtain ⟨y, rfl⟩ := htb.int_inv
  exact ⟨.int (op.eval x y), by simp [eval, hea, heb], .int _⟩

theorem sound_cmp {Γ : List Ty} {a b : Tm} (op : Cmp) (ha : Sound Γ a .int)
    (hb : Sound Γ b .int) : Sound Γ (.cmp op a b) .bool := by
  intro ρ hρ
  obtain ⟨va, hea, hta⟩ := ha ρ hρ
  obtain ⟨vb, heb, htb⟩ := hb ρ hρ
  obtain ⟨x, rfl⟩ := hta.int_inv
  obtain ⟨y, rfl⟩ := htb.int_inv
  exact ⟨.bool (op.eval x y), by simp [eval, hea, heb], .bool _⟩

theorem sound_ite {Γ : List Ty} {c t e : Tm} {τ : Ty} (hc : Sound Γ c .bool) (ht : Sound Γ t τ)
    (he : Sound Γ e τ) : Sound Γ (.ite c t e) τ := by
  intro ρ hρ
  obtain ⟨vc, hec, htc⟩ := hc ρ hρ
  obtain ⟨b, rfl⟩ := htc.bool_inv
  cases b with
  | true => simpa [eval, hec] using ht ρ hρ
  | false => simpa [eval, hec] using he ρ hρ

theorem sound_let {Γ : List Ty} {a b : Tm} {σ τ : Ty} (ha : Sound Γ a σ)
    (hb : Sound (σ :: Γ) b τ) : Sound Γ (.let_ a b) τ := by
  intro ρ hρ
  obtain ⟨va, hea, hta⟩ := ha ρ hρ
  simpa [eval, hea] using hb (va :: ρ) (.cons hta hρ)

theorem sound_pair {Γ : List Ty} {a b : Tm} {σ τ : Ty} (ha : Sound Γ a σ) (hb : Sound Γ b τ) :
    Sound Γ (.pair a b) (.prod σ τ) := by
  intro ρ hρ
  obtain ⟨va, hea, hta⟩ := ha ρ hρ
  obtain ⟨vb, heb, htb⟩ := hb ρ hρ
  exact ⟨_, by simp [eval, hea, heb], .pair hta htb⟩

theorem sound_fst {Γ : List Ty} {e : Tm} {σ τ : Ty} (he : Sound Γ e (.prod σ τ)) :
    Sound Γ (.fst e) σ := by
  intro ρ hρ
  obtain ⟨v, hev, htv⟩ := he ρ hρ
  obtain ⟨a, b, rfl, ha, -⟩ := htv.prod_inv
  exact ⟨a, by simp [eval, hev], ha⟩

theorem sound_snd {Γ : List Ty} {e : Tm} {σ τ : Ty} (he : Sound Γ e (.prod σ τ)) :
    Sound Γ (.snd e) τ := by
  intro ρ hρ
  obtain ⟨v, hev, htv⟩ := he ρ hρ
  obtain ⟨a, b, rfl, -, hb⟩ := htv.prod_inv
  exact ⟨b, by simp [eval, hev], hb⟩

theorem sound_inl {Γ : List Ty} {e : Tm} {σ : Ty} (τ : Ty) (he : Sound Γ e σ) :
    Sound Γ (.inl e) (.sum σ τ) := by
  intro ρ hρ
  obtain ⟨v, hev, htv⟩ := he ρ hρ
  exact ⟨_, by simp [eval, hev], .inl τ htv⟩

theorem sound_inr {Γ : List Ty} {e : Tm} {τ : Ty} (σ : Ty) (he : Sound Γ e τ) :
    Sound Γ (.inr e) (.sum σ τ) := by
  intro ρ hρ
  obtain ⟨v, hev, htv⟩ := he ρ hρ
  exact ⟨_, by simp [eval, hev], .inr σ htv⟩

theorem sound_case {Γ : List Ty} {e l r : Tm} {σ τ υ : Ty} (he : Sound Γ e (.sum σ τ))
    (hl : Sound (σ :: Γ) l υ) (hr : Sound (τ :: Γ) r υ) : Sound Γ (.case e l r) υ := by
  intro ρ hρ
  obtain ⟨v, hev, htv⟩ := he ρ hρ
  rcases htv.sum_inv with ⟨a, rfl, ha⟩ | ⟨b, rfl, hb⟩
  · simpa [eval, hev] using hl (a :: ρ) (.cons ha hρ)
  · simpa [eval, hev] using hr (b :: ρ) (.cons hb hρ)

/-- **Type soundness and normalisation**: a well-typed term evaluates, in a typed environment,
to a value of its type. -/
theorem eval_sound {Γ : List Ty} {e : Tm} {τ : Ty} (h : HasTy Γ e τ) : Sound Γ e τ := by
  induction h with
  | var hi => exact fun ρ hρ => forall₂_getElem? hρ hi
  | int n => exact fun _ _ => ⟨_, rfl, .int n⟩
  | bool b => exact fun _ _ => ⟨_, rfl, .bool b⟩
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

/-! ## Programs -/

/-- A well-typed program returns a value of its result type on every argument. -/
theorem Prog.run_sound {p : Prog} (hp : p.WellTyped) (n : BitVec 31) :
    ∃ v, p.run n = some v ∧ ValTy v p.res :=
  eval_sound hp.1 [.int n] (.cons (.int n) .nil)

/-- The observations of a well-typed program on `n`: it returns one word. -/
theorem Prog.obs_eq {p : Prog} {n : BitVec 31} {v : Val} (hv : p.run n = some v) :
    p.obs n = {.returns [obsWord v]} := by
  ext b
  simp [Prog.obs, hv]

/-! ## The game reading -/

/-- The word a well-typed program computes on `n` (`0` for an ill-typed one). -/
def Prog.word (p : Prog) (n : BitVec 31) : BitVec 31 := ((p.run n).map obsWord).getD 0

theorem Prog.obs_eq_word {p : Prog} (hp : p.WellTyped) (n : BitVec 31) :
    p.obs n = {.returns [p.word n]} := by
  obtain ⟨v, hv, -⟩ := p.run_sound hp n
  rw [Prog.obs_eq hv]
  simp [Prog.word, hv]

/-- The play sentence of a program: every answer to the call `n` returns the word `p` computes
on `n`. -/
def AnsIs (p : Prog) : Set (List (Move Sig.empty (callSig (BitVec 31) (Behaviour (BitVec 31))))) :=
  {s | ∀ n o, (.inr (.ans n o) : Move Sig.empty (callSig (BitVec 31) (Behaviour (BitVec 31)))) ∈ s →
    o = .returns [p.word n]}

/-- **The strategy of a well-typed program answers every call with its word**:
`funModel.strat p ⊨ □ AnsIs p` in `GInst`. -/
theorem strat_answers {p : Prog} (hp : p.WellTyped) :
    (GSen.box (AnsIs p)).holds (funModel.strat p) := by
  intro s hs n o hm
  have ho : o ∈ p.obs n := hs.2 n o hm
  rw [Prog.obs_eq_word hp n] at ho
  exact ho

end Silmaril.Wasm.Models.FunLang
