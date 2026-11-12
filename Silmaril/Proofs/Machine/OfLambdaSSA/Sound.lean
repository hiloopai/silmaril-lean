module

public import Silmaril.Proofs.Machine.OfLambdaSSA.Terms

/-!
# Shapes are sound

Evaluating a term of the fragment, in an environment whose values have the
shapes of the context, gives a value of the term's shape; evaluating a region
leaves through one of its labels, with a tuple of that label's width.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.OfLambdaSSA

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (extend)

variable {sigs : List Silmaril.Machine.RTL.Signature} {oracle : CallOracle}

/-- Every variable of the context holds a value of its shape. -/
def EnvFits (Γ : List Shape) (env : Semantics.Env Word) : Prop :=
  ∀ (i : ℕ) (s : Shape), Γ[i]? = some s → ∃ ws, s.Holds (env i) ws

theorem EnvFits.cons {Γ : List Shape} {env : Semantics.Env Word} (h : EnvFits Γ env) {s : Shape}
    {v : Value Word} {ws : List Word} (hv : s.Holds v ws) : EnvFits (s :: Γ) (extend env v) := by
  intro i s' hi
  cases i with
  | zero =>
    have same : s = s' := by simpa using hi
    exact ⟨ws, same ▸ hv⟩
  | succ i => exact h i s' (by simpa using hi)

/-- An opcode steps from a tuple of its arity to a tuple of its result count. -/
theorem step_holds (hsigs : CallOracle.MatchesSigs oracle sigs) {f : Opcode sigs} (hf : f ≠ .test)
    {va : Value Word} {m m' : Memory} {v : Value Word}
    (h : Opcode.step oracle f va m v m') : ∃ rs, (Shape.tuple f.results).Holds v rs := by
  cases h with
  | const => exact ⟨_, rfl, rfl⟩
  | move => exact ⟨_, rfl, rfl⟩
  | unary => exact ⟨_, rfl, rfl⟩
  | binary => exact ⟨_, rfl, rfl⟩
  | load => exact ⟨_, rfl, rfl⟩
  | store => exact ⟨_, rfl, rfl⟩
  | call horacle => exact ⟨_, rfl, hsigs _ _ _ _ _ horacle⟩
  | test_nonzero => exact absurd rfl hf
  | test_zero => exact absurd rfl hf

variable (oracle) in
/-- Soundness for terms: values of the term's shape. -/
def TmSound (Γ : List Shape) (a : Tm (Opcode sigs)) (s : Shape) : Prop :=
  ∀ {env : Semantics.Env Word} {m m' : Memory} {v : Value Word}, EnvFits Γ env →
    Semantics.Tm.Eval (Opcode.step oracle) env a m v m' → ∃ ws, s.Holds v ws

theorem snd_var {Γ : List Shape} {i : ℕ} {s : Shape} (hΓ : Γ[i]? = some s) :
    TmSound oracle Γ (.var i : Tm (Opcode sigs)) s := by
  intro env m m' v henv hev
  obtain ⟨rfl, -⟩ := eval_var_inv hev
  exact henv _ _ hΓ

theorem snd_unit {Γ : List Shape} : TmSound oracle Γ (.unit : Tm (Opcode sigs)) (.tuple 0) := by
  intro env m m' v henv hev
  obtain ⟨rfl, -⟩ := eval_unit_inv hev
  exact ⟨[], rfl, rfl⟩

theorem snd_pair {Γ : List Shape} {a b : Tm (Opcode sigs)} {n : ℕ} (iha : TmSound oracle Γ a .word)
    (ihb : TmSound oracle Γ b (.tuple n)) : TmSound oracle Γ (.pair a b) (.tuple (n + 1)) := by
  intro env m m' v henv hev
  obtain ⟨va, vb, m₁, eva, evb, rfl⟩ := eval_pair_inv hev
  obtain ⟨wa, ha⟩ := iha henv eva
  obtain ⟨wb, hb⟩ := ihb henv evb
  exact ⟨_, holds_pair ha hb⟩

theorem snd_op (hsigs : CallOracle.MatchesSigs oracle sigs) {Γ : List Shape} {f : Opcode sigs}
    (hf : f ≠ .test) {a : Tm (Opcode sigs)} : TmSound oracle Γ (.op f a) (.tuple f.results) := by
  intro env m m' v henv hev
  obtain ⟨va, m₁, eva, hstep⟩ := eval_op_inv hev
  exact step_holds hsigs hf hstep

theorem snd_let₁ {Γ : List Shape} {a b : Tm (Opcode sigs)} {s s' : Shape}
    (iha : TmSound oracle Γ a s) (ihb : TmSound oracle (s :: Γ) b s') :
    TmSound oracle Γ (.let₁ a b) s' := by
  intro env m m' v henv hev
  cases hev with
  | let₁ eva evb =>
    obtain ⟨wa, ha⟩ := iha henv eva
    exact ihb (henv.cons ha) evb

theorem snd_let₂ {Γ : List Shape} {a b : Tm (Opcode sigs)} {n : ℕ} {s' : Shape}
    (iha : TmSound oracle Γ a (.tuple (n + 1))) (ihb : TmSound oracle (.tuple n :: .word :: Γ) b s') :
    TmSound oracle Γ (.let₂ a b) s' := by
  intro env m m' v henv hev
  obtain ⟨va, vb, m₁, eva, evb⟩ := eval_let₂_inv hev
  obtain ⟨wa, ha⟩ := iha henv eva
  obtain ⟨w, ws', rfl, hw, hws'⟩ := holds_split ha
  exact ihb ((henv.cons hw).cons hws') evb

/-- **Terms of the fragment evaluate to values of their shape.** -/
theorem tm_sound (hsigs : CallOracle.MatchesSigs oracle sigs) {Γ : List Shape}
    {a : Tm (Opcode sigs)} {s : Shape} (h : TmFits sigs Γ a s) : TmSound oracle Γ a s := by
  induction h with
  | var hΓ => exact snd_var hΓ
  | unit => exact snd_unit
  | pair _ _ iha ihb => exact snd_pair iha ihb
  | op hf _ _ => exact snd_op hsigs hf
  | let₁ _ _ iha ihb => exact snd_let₁ iha ihb
  | let₂ _ _ iha ihb => exact snd_let₂ iha ihb

/-- Leaving through label `ℓ` of widths `Lw` with a tuple of its width. -/
def ExitOk (Lw : List ℕ) (ℓ : ℕ) (v : Value Word) : Prop :=
  ∃ w ws, Lw[ℓ]? = some w ∧ v = packValues ws ∧ ws.length = w

/-- Soundness for regions: their exits. -/
def RegSound (env : Semantics.Env Word) (r : Region (Opcode sigs)) (ℓ : ℕ) (v : Value Word) :
    Prop :=
  ∀ {Γ : List Shape} {a : Ann} {Lw : List ℕ}, RegionFits sigs Γ r a Lw → EnvFits Γ env → ExitOk Lw ℓ v

/-- Soundness for the blocks of a `cfg`, entered with a tuple of the entry label's width. -/
def FolSound (env : Semantics.Env Word) {k : ℕ} (blocks : Fin k → Region (Opcode sigs))
    (first : ℕ) (initial : Value Word) (ℓ : ℕ) (v : Value Word) : Prop :=
  ∀ {Γ : List Shape} {ws : List ℕ} {abs : List Ann} {Lw : List ℕ},
    (∀ i : Fin k, RegionFits sigs (.tuple (ws.getD i 0) :: Γ) (blocks i) (abs.getD i .br) (ws ++ Lw)) →
    ws.length = k → EnvFits Γ env → ExitOk (ws ++ Lw) first initial → ExitOk Lw ℓ v

theorem sound_br (hsigs : CallOracle.MatchesSigs oracle sigs) {env : Semantics.Env Word}
    {ℓ : ℕ} {arg : Tm (Opcode sigs)} {m m' : Memory} {v : Value Word}
    (harg : Semantics.Tm.Eval (Opcode.step oracle) env arg m v m') : RegSound env (.br ℓ arg) ℓ v := by
  intro Γ a Lw hfit henv
  cases hfit with
  | br hw hfa =>
    obtain ⟨ws, rfl, hlen⟩ := tm_sound hsigs hfa henv harg
    exact ⟨_, ws, hw, rfl, hlen⟩

theorem sound_let₁ (hsigs : CallOracle.MatchesSigs oracle sigs) {env : Semantics.Env Word}
    {a : Tm (Opcode sigs)} {r : Region (Opcode sigs)} {m m₁ : Memory} {va v : Value Word} {ℓ : ℕ}
    (ha : Semantics.Tm.Eval (Opcode.step oracle) env a m va m₁) (ih : RegSound (extend env va) r ℓ v) :
    RegSound env (.let₁ a r) ℓ v := by
  intro Γ ab Lw hfit henv
  cases hfit with
  | let₁ hfa hr =>
    obtain ⟨ws, hh⟩ := tm_sound hsigs hfa henv ha
    exact ih hr (henv.cons hh)

theorem sound_let₂ (hsigs : CallOracle.MatchesSigs oracle sigs) {env : Semantics.Env Word}
    {a : Tm (Opcode sigs)} {r : Region (Opcode sigs)} {m m₁ : Memory} {va vb v : Value Word}
    {ℓ : ℕ} (ha : Semantics.Tm.Eval (Opcode.step oracle) env a m (.pair va vb) m₁)
    (ih : RegSound (extend (extend env va) vb) r ℓ v) : RegSound env (.let₂ a r) ℓ v := by
  intro Γ ab Lw hfit henv
  cases hfit with
  | let₂ hfa hr =>
    obtain ⟨ws, hh⟩ := tm_sound hsigs hfa henv ha
    obtain ⟨w, ws', rfl, hw, hws'⟩ := holds_split hh
    exact ih hr ((henv.cons hw).cons hws')

/-- The branch test of a `case` of the fragment selects by its one word. -/
theorem sound_test (hsigs : CallOracle.MatchesSigs oracle sigs) {Γ : List Shape}
    {env : Semantics.Env Word} {arg : Tm (Opcode sigs)} (harg : TmFits sigs Γ arg (.tuple 1))
    (henv : EnvFits Γ env) {m m₁ : Memory} {d : Value Word}
    (ha : Semantics.Tm.Eval (Opcode.step oracle) env (.op .test arg) m d m₁) :
    ∃ x : Word, d = if x = 0 then .inr .unit else .inl .unit := by
  obtain ⟨vx, m₀, evx, hstep⟩ := eval_op_inv ha
  obtain ⟨ws, rfl, hlen⟩ := tm_sound hsigs harg henv evx
  match ws, hlen with
  | [x], _ => exact ⟨x, (Opcode.step_test_iff.mp hstep).2⟩

theorem sound_case_inl (hsigs : CallOracle.MatchesSigs oracle sigs) {env : Semantics.Env Word}
    {d : Tm (Opcode sigs)} {l r : Region (Opcode sigs)} {m m₁ : Memory} {va v : Value Word} {ℓ : ℕ}
    (ha : Semantics.Tm.Eval (Opcode.step oracle) env d m (.inl va) m₁)
    (ih : RegSound (extend env va) l ℓ v) : RegSound env (.case d l r) ℓ v := by
  intro Γ ab Lw hfit henv
  cases hfit with
  | case harg hl hr =>
    obtain ⟨x, hsel⟩ := sound_test hsigs harg henv ha
    by_cases hx0 : x = 0
    · rw [ite_eq_left hx0] at hsel
      cases hsel
    · rw [ite_eq_right hx0] at hsel
      obtain rfl := Value.inl.inj hsel
      exact ih hl (henv.cons (⟨rfl, rfl⟩ : (Shape.tuple 0).Holds .unit []))

theorem sound_case_inr (hsigs : CallOracle.MatchesSigs oracle sigs) {env : Semantics.Env Word}
    {d : Tm (Opcode sigs)} {l r : Region (Opcode sigs)} {m m₁ : Memory} {va v : Value Word} {ℓ : ℕ}
    (ha : Semantics.Tm.Eval (Opcode.step oracle) env d m (.inr va) m₁)
    (ih : RegSound (extend env va) r ℓ v) : RegSound env (.case d l r) ℓ v := by
  intro Γ ab Lw hfit henv
  cases hfit with
  | case harg hl hr =>
    obtain ⟨x, hsel⟩ := sound_test hsigs harg henv ha
    by_cases hx0 : x = 0
    · rw [ite_eq_left hx0] at hsel
      obtain rfl := Value.inr.inj hsel
      exact ih hr (henv.cons (⟨rfl, rfl⟩ : (Shape.tuple 0).Holds .unit []))
    · rw [ite_eq_right hx0] at hsel
      cases hsel

theorem sound_cfg {env : Semantics.Env Word} {entry : Region (Opcode sigs)} {k : ℕ}
    {blocks : Fin k → Region (Opcode sigs)} {first ℓ : ℕ} {initial v : Value Word}
    (ihE : RegSound env entry first initial) (ihF : FolSound env blocks first initial ℓ v) :
    RegSound env (.cfg entry k blocks) ℓ v := by
  intro Γ a Lw hfit henv
  cases hfit with
  | cfg hws hentry hblocks => exact ihF hblocks hws henv (ihE hentry henv)

theorem soundF_exit {env : Semantics.Env Word} {k : ℕ} {blocks : Fin k → Region (Opcode sigs)}
    {first : ℕ} {v : Value Word} (outside : k ≤ first) : FolSound env blocks first v (first - k) v := by
  intro Γ ws abs Lw hfits hws henv hok
  obtain ⟨w, vs, hw, rfl, hlen⟩ := hok
  refine ⟨w, vs, ?_, rfl, hlen⟩
  rw [List.getElem?_append_right (by omega), hws] at hw
  exact hw

theorem soundF_step {env : Semantics.Env Word} {k : ℕ} {blocks : Fin k → Region (Opcode sigs)}
    {first next ℓ : ℕ} {initial middle v : Value Word} (inside : first < k)
    (ihH : RegSound (extend env initial) (blocks ⟨first, inside⟩) next middle)
    (ihT : FolSound env blocks next middle ℓ v) : FolSound env blocks first initial ℓ v := by
  intro Γ ws abs Lw hfits hws henv hok
  obtain ⟨w, vs, hw, rfl, hlen⟩ := hok
  have width : w = ws.getD first 0 := by
    rw [List.getElem?_append_left (by omega)] at hw
    simp [List.getD_eq_getElem?_getD, hw]
  have hold : (Shape.tuple (ws.getD first 0)).Holds (packValues vs) vs := ⟨rfl, hlen.trans width⟩
  exact ihT hfits hws henv (ihH (hfits ⟨first, inside⟩) (henv.cons hold))

/-- **Regions of the fragment leave through one of their labels with a tuple of
its width.** -/
theorem region_sound (hsigs : CallOracle.MatchesSigs oracle sigs) {env : Semantics.Env Word}
    {r : Region (Opcode sigs)} {m m' : Memory} {ℓ : ℕ} {v : Value Word}
    (h : Semantics.Region.Eval (Opcode.step oracle) env r m ℓ v m') : RegSound env r ℓ v := by
  induction h using Semantics.Region.Eval.rec
      (motive_2 := fun env _ blocks first initial _ ℓ v _ _ =>
        FolSound env blocks first initial ℓ v) with
  | br harg => exact sound_br hsigs harg
  | let₁ ha _ ih => exact sound_let₁ hsigs ha ih
  | let₂ ha _ ih => exact sound_let₂ hsigs ha ih
  | case_inl ha _ ih => exact sound_case_inl hsigs ha ih
  | case_inr ha _ ih => exact sound_case_inr hsigs ha ih
  | cfg _ _ ihE ihF => exact sound_cfg ihE ihF
  | exit outside => exact soundF_exit outside
  | step inside _ _ ihH ihT => exact soundF_step inside ihH ihT

/-- The same, for the blocks of a `cfg` evaluated on their own. -/
theorem follow_sound (hsigs : CallOracle.MatchesSigs oracle sigs) {env : Semantics.Env Word}
    {k : ℕ} {blocks : Fin k → Region (Opcode sigs)} {first ℓ : ℕ} {initial v : Value Word}
    {m m' : Memory}
    (h : Semantics.Region.Follow (Opcode.step oracle) env blocks first initial m ℓ v m') :
    FolSound env blocks first initial ℓ v := by
  induction h using Semantics.Region.Follow.rec
      (motive_1 := fun env r _ ℓ v _ _ => RegSound env r ℓ v) with
  | br harg => exact sound_br hsigs harg
  | let₁ ha _ ih => exact sound_let₁ hsigs ha ih
  | let₂ ha _ ih => exact sound_let₂ hsigs ha ih
  | case_inl ha _ ih => exact sound_case_inl hsigs ha ih
  | case_inr ha _ ih => exact sound_case_inr hsigs ha ih
  | cfg _ _ ihE ihF => exact sound_cfg ihE ihF
  | exit outside => exact soundF_exit outside
  | step inside _ _ ihH ihT => exact soundF_step inside ihH ihT

end Silmaril.Proofs.Machine.OfLambdaSSA
