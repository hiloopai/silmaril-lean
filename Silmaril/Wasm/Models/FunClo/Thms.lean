module

public import Silmaril.Wasm.Models.FunClo.Defs
public import Silmaril.Wasm.Models.FunLang.Thms

/-!
# FunClo: fuel, type soundness and the game reading

* `eval_mono`, `eval_le`: more fuel gives the same result; `Prog.Eval.unique`: a program returns
  at most one value on an argument.
* `eval_sound`: type preservation. A well-typed term that evaluates, in a typed environment,
  evaluates to a value of its type. There is no termination: `fix` gives general recursion.
* `Prog.obs_eq`: a program that returns `v` on `n` has exactly the observation
  `returns [obsWord v]`. `Prog.word` is the word a program returns (`0` when it diverges).
* `eval_ofFun`: FunLang is a fragment of FunClo. A FunLang term evaluates in FunClo, with fuel
  its height, to its FunLang value.
* `strat_answers`: the observation strategy of a terminating program answers every call with
  its word (`□ AnsIs p` in `GInst`).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunClo

open Silmaril.Wasm (Behaviour)
open Silmaril.Games
open Silmaril.Wasm.Models.FunLang (Arith Cmp)

/-! ## Fuel -/

/-- One more unit of fuel gives the same result. -/
theorem eval_succ : ∀ {k : Nat} {ρ : List Val} {e : Tm} {v : Val},
    eval k ρ e = some v → eval (k + 1) ρ e = some v
  | 0, _, _, _, h => by simp [eval] at h
  | k + 1, ρ, e, v, h => by
    cases e with
    | var i => exact h
    | int n => exact h
    | bool b => exact h
    | fix b => exact h
    | arith op a b =>
      simp only [eval] at h ⊢
      split at h
      · next x y ha hb => rw [eval_succ ha, eval_succ hb]; exact h
      · cases h
    | cmp op a b =>
      simp only [eval] at h ⊢
      split at h
      · next x y ha hb => rw [eval_succ ha, eval_succ hb]; exact h
      · cases h
    | ite c t e =>
      simp only [eval] at h ⊢
      split at h
      · next hc => rw [eval_succ hc]; exact eval_succ h
      · next hc => rw [eval_succ hc]; exact eval_succ h
      · cases h
    | let_ a b =>
      simp only [eval] at h ⊢
      split at h
      · next u hu => rw [eval_succ hu]; exact eval_succ h
      · cases h
    | pair a b =>
      simp only [eval] at h ⊢
      split at h
      · next x y ha hb => rw [eval_succ ha, eval_succ hb]; exact h
      · cases h
    | fst e =>
      simp only [eval] at h ⊢
      split at h
      · next x y he => rw [eval_succ he]; exact h
      · cases h
    | snd e =>
      simp only [eval] at h ⊢
      split at h
      · next x y he => rw [eval_succ he]; exact h
      · cases h
    | inl e =>
      simp only [eval, Option.map_eq_some_iff] at h ⊢
      obtain ⟨u, hu, rfl⟩ := h
      exact ⟨u, eval_succ hu, rfl⟩
    | inr e =>
      simp only [eval, Option.map_eq_some_iff] at h ⊢
      obtain ⟨u, hu, rfl⟩ := h
      exact ⟨u, eval_succ hu, rfl⟩
    | case e l r =>
      simp only [eval] at h ⊢
      split at h
      · next u hu => rw [eval_succ hu]; exact eval_succ h
      · next u hu => rw [eval_succ hu]; exact eval_succ h
      · cases h
    | app f a =>
      simp only [eval] at h ⊢
      split at h
      · next b ρ' u hf ha => rw [eval_succ hf, eval_succ ha]; exact eval_succ h
      · cases h

/-- **More fuel gives the same result.** -/
theorem eval_le {k k' : Nat} {ρ : List Val} {e : Tm} {v : Val} (h : eval k ρ e = some v)
    (hk : k ≤ k') : eval k' ρ e = some v := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction j with
  | zero => exact h
  | succ j ih => exact eval_succ (ih (Nat.le_add_right _ _))

/-- Evaluation with two amounts of fuel agrees where both succeed. -/
theorem eval_det {k k' : Nat} {ρ : List Val} {e : Tm} {v v' : Val} (h : eval k ρ e = some v)
    (h' : eval k' ρ e = some v') : v = v' := by
  have h₁ := eval_le h (Nat.le_max_left k k')
  have h₂ := eval_le h' (Nat.le_max_right k k')
  exact Option.some.inj (h₁.symm.trans h₂)

/-- A program returns at most one value on an argument. -/
theorem Prog.Eval.unique {p : Prog} {n : BitVec 31} {v v' : Val} (h : p.Eval n v)
    (h' : p.Eval n v') : v = v' := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨k', hk'⟩ := h'
  exact eval_det hk hk'

/-! ## Type preservation -/

theorem EnvTy.getElem? : ∀ {ρ : List Val} {Γ : List Ty}, EnvTy ρ Γ → ∀ {i : Nat} {τ : Ty},
    Γ[i]? = some τ → ∀ {v : Val}, ρ[i]? = some v → ValTy v τ
  | _, _, .nil, _, _, hi, _, _ => absurd hi (by simp)
  | _, _, .cons hab _, 0, _, hi, _, hv => by
    have hτ := Option.some.inj hi
    have hv' := Option.some.inj hv
    subst hτ hv'
    exact hab
  | _, _, .cons _ h, i + 1, _, hi, _, hv => EnvTy.getElem? h hi hv

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

theorem ValTy.arr_inv {v : Val} {σ τ : Ty} (h : ValTy v (.arr σ τ)) :
    ∃ b ρ Γ, v = .clo b ρ ∧ EnvTy ρ Γ ∧ HasTy (σ :: .arr σ τ :: Γ) b τ := by
  cases h with
  | clo hρ hb => exact ⟨_, _, _, rfl, hρ, hb⟩

/-- What type preservation says at fuel `k`. -/
def Pres (k : Nat) : Prop :=
  ∀ ⦃Γ : List Ty⦄ ⦃e : Tm⦄ ⦃τ : Ty⦄, HasTy Γ e τ → ∀ ⦃ρ : List Val⦄ ⦃v : Val⦄, EnvTy ρ Γ →
    eval k ρ e = some v → ValTy v τ

theorem pres_app {k : Nat} (ih : Pres k) {Γ : List Ty} {f a : Tm} {σ τ : Ty}
    (hf : HasTy Γ f (.arr σ τ)) (ha : HasTy Γ a σ) {ρ : List Val} {v : Val} (hρ : EnvTy ρ Γ)
    (h : eval (k + 1) ρ (.app f a) = some v) : ValTy v τ := by
  simp only [eval] at h
  split at h
  · next b ρ' u hef hea =>
    obtain ⟨b', ρ'', Γ', he, hρ', hb⟩ := (ih hf hρ hef).arr_inv
    cases he
    exact ih hb (.cons (ih ha hρ hea) (.cons (ih hf hρ hef) hρ')) h
  · cases h

theorem pres_case {k : Nat} (ih : Pres k) {Γ : List Ty} {e l r : Tm} {σ τ υ : Ty}
    (he : HasTy Γ e (.sum σ τ)) (hl : HasTy (σ :: Γ) l υ) (hr : HasTy (τ :: Γ) r υ)
    {ρ : List Val} {v : Val} (hρ : EnvTy ρ Γ) (h : eval (k + 1) ρ (.case e l r) = some v) :
    ValTy v υ := by
  simp only [eval] at h
  split at h
  · next u hu =>
    obtain ⟨a, ha, hta⟩ | ⟨b, hb, -⟩ := (ih he hρ hu).sum_inv
    · cases ha
      exact ih hl (.cons hta hρ) h
    · cases hb
  · next u hu =>
    obtain ⟨a, ha, -⟩ | ⟨b, hb, htb⟩ := (ih he hρ hu).sum_inv
    · cases ha
    · cases hb
      exact ih hr (.cons htb hρ) h
  · cases h

theorem pres_arith {k : Nat} {op : Arith} {a b : Tm} {ρ : List Val} {v : Val}
    (h : eval (k + 1) ρ (.arith op a b) = some v) : ValTy v .int := by
  simp only [eval] at h
  split at h
  · cases h; exact .int _
  · cases h

theorem pres_cmp {k : Nat} {op : Cmp} {a b : Tm} {ρ : List Val} {v : Val}
    (h : eval (k + 1) ρ (.cmp op a b) = some v) : ValTy v .bool := by
  simp only [eval] at h
  split at h
  · cases h; exact .bool _
  · cases h

theorem pres_ite {k : Nat} (ih : Pres k) {Γ : List Ty} {c t e : Tm} {τ : Ty}
    (ht : HasTy Γ t τ) (he : HasTy Γ e τ) {ρ : List Val} {v : Val} (hρ : EnvTy ρ Γ)
    (h : eval (k + 1) ρ (.ite c t e) = some v) : ValTy v τ := by
  simp only [eval] at h
  split at h
  · exact ih ht hρ h
  · exact ih he hρ h
  · cases h

theorem pres_let {k : Nat} (ih : Pres k) {Γ : List Ty} {a b : Tm} {σ τ : Ty}
    (ha : HasTy Γ a σ) (hb : HasTy (σ :: Γ) b τ) {ρ : List Val} {v : Val} (hρ : EnvTy ρ Γ)
    (h : eval (k + 1) ρ (.let_ a b) = some v) : ValTy v τ := by
  simp only [eval] at h
  split at h
  · next u hu => exact ih hb (.cons (ih ha hρ hu) hρ) h
  · cases h

theorem pres_pair {k : Nat} (ih : Pres k) {Γ : List Ty} {a b : Tm} {σ τ : Ty}
    (ha : HasTy Γ a σ) (hb : HasTy Γ b τ) {ρ : List Val} {v : Val} (hρ : EnvTy ρ Γ)
    (h : eval (k + 1) ρ (.pair a b) = some v) : ValTy v (.prod σ τ) := by
  simp only [eval] at h
  split at h
  · next x y hx hy => cases h; exact .pair (ih ha hρ hx) (ih hb hρ hy)
  · cases h

theorem pres_fst {k : Nat} (ih : Pres k) {Γ : List Ty} {e : Tm} {σ τ : Ty}
    (he : HasTy Γ e (.prod σ τ)) {ρ : List Val} {v : Val} (hρ : EnvTy ρ Γ)
    (h : eval (k + 1) ρ (.fst e) = some v) : ValTy v σ := by
  simp only [eval] at h
  split at h
  · next x y hx =>
    cases h
    obtain ⟨a, b, hab, hta, -⟩ := (ih he hρ hx).prod_inv
    cases hab
    exact hta
  · cases h

theorem pres_snd {k : Nat} (ih : Pres k) {Γ : List Ty} {e : Tm} {σ τ : Ty}
    (he : HasTy Γ e (.prod σ τ)) {ρ : List Val} {v : Val} (hρ : EnvTy ρ Γ)
    (h : eval (k + 1) ρ (.snd e) = some v) : ValTy v τ := by
  simp only [eval] at h
  split at h
  · next x y hx =>
    cases h
    obtain ⟨a, b, hab, -, htb⟩ := (ih he hρ hx).prod_inv
    cases hab
    exact htb
  · cases h

theorem pres_inl {k : Nat} (ih : Pres k) {Γ : List Ty} {e : Tm} {σ : Ty} (τ : Ty)
    (he : HasTy Γ e σ) {ρ : List Val} {v : Val} (hρ : EnvTy ρ Γ)
    (h : eval (k + 1) ρ (.inl e) = some v) : ValTy v (.sum σ τ) := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, eval k ρ e = some u ∧ Val.inl u = v := by
    simpa only [eval, Option.map_eq_some_iff] using h
  exact .inl τ (ih he hρ hu)

theorem pres_inr {k : Nat} (ih : Pres k) {Γ : List Ty} {e : Tm} {τ : Ty} (σ : Ty)
    (he : HasTy Γ e τ) {ρ : List Val} {v : Val} (hρ : EnvTy ρ Γ)
    (h : eval (k + 1) ρ (.inr e) = some v) : ValTy v (.sum σ τ) := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, eval k ρ e = some u ∧ Val.inr u = v := by
    simpa only [eval, Option.map_eq_some_iff] using h
  exact .inr σ (ih he hρ hu)

theorem pres_succ {k : Nat} (ih : Pres k) : Pres (k + 1) := by
  intro Γ e τ ht ρ v hρ h
  cases ht with
  | var hi => exact hρ.getElem? hi h
  | int n => cases h; exact .int n
  | bool b => cases h; exact .bool b
  | arith op => exact pres_arith h
  | cmp op => exact pres_cmp h
  | ite _ htt hte => exact pres_ite ih htt hte hρ h
  | let_ ha hb => exact pres_let ih ha hb hρ h
  | pair ha hb => exact pres_pair ih ha hb hρ h
  | fst he => exact pres_fst ih he hρ h
  | snd he => exact pres_snd ih he hρ h
  | inl τ' he => exact pres_inl ih τ' he hρ h
  | inr σ' he => exact pres_inr ih σ' he hρ h
  | case he hl hr => exact pres_case ih he hl hr hρ h
  | fix hb => cases h; exact .clo hρ hb
  | app hf ha => exact pres_app ih hf ha hρ h

/-- **Type preservation**: a well-typed term that evaluates in a typed environment evaluates to
a value of its type. -/
theorem eval_sound : ∀ k, Pres k
  | 0 => fun _ _ _ _ _ _ _ h => by simp [eval] at h
  | k + 1 => pres_succ (eval_sound k)

/-- A well-typed program returns a value of its result type. -/
theorem Prog.Eval.sound {p : Prog} (hp : p.WellTyped) {n : BitVec 31} {v : Val}
    (h : p.Eval n v) : ValTy v p.res := by
  obtain ⟨k, hk⟩ := h
  exact eval_sound k hp.1 (.cons (.int n) .nil) hk

/-! ## Observations -/

/-- **The observations of a program that returns `v` on `n`.** -/
theorem Prog.obs_eq {p : Prog} {n : BitVec 31} {v : Val} (hv : p.Eval n v) :
    p.obs n = {.returns [obsWord v]} := by
  ext b
  constructor
  · rintro ⟨v', hv', rfl⟩
    rw [hv.unique hv']
    rfl
  · intro hb
    exact ⟨v, hv, hb⟩

open Classical in
/-- The word a program returns on `n` (`0` if it does not terminate). -/
noncomputable def Prog.word (p : Prog) (n : BitVec 31) : BitVec 31 :=
  if h : ∃ v, p.Eval n v then obsWord h.choose else 0

theorem Prog.word_eq {p : Prog} {n : BitVec 31} {v : Val} (hv : p.Eval n v) :
    p.word n = obsWord v := by
  have h : ∃ v, p.Eval n v := ⟨v, hv⟩
  simp only [Prog.word, h, ↓reduceDIte]
  rw [h.choose_spec.unique hv]

theorem Prog.obs_eq_word {p : Prog} (ht : p.Terminates) (n : BitVec 31) :
    p.obs n = {.returns [p.word n]} := by
  obtain ⟨v, hv⟩ := ht n
  rw [Prog.obs_eq hv, Prog.word_eq hv]

/-- The play sentence of a program: every answer to the call `n` returns the word `p` computes
on `n`. -/
def AnsIs (p : Prog) : Set (List (Move Sig.empty (callSig (BitVec 31) (Behaviour (BitVec 31))))) :=
  {s | ∀ n o, (.inr (.ans n o) : Move Sig.empty (callSig (BitVec 31) (Behaviour (BitVec 31)))) ∈ s →
    o = .returns [p.word n]}

/-- **The strategy of a terminating program answers every call with its word**:
`funCloModel.strat p ⊨ □ AnsIs p` in `GInst`. -/
theorem strat_answers {p : Prog} (ht : p.Terminates) :
    (GSen.box (AnsIs p)).holds (funCloModel.strat p) := by
  intro s hs n o hm
  have ho : o ∈ p.obs n := hs.2 n o hm
  rw [Prog.obs_eq_word ht n] at ho
  exact ho

/-! ## FunLang inside FunClo -/

theorem maxL {a b k : Nat} (h : max a b ≤ k) : a ≤ k := (Nat.max_le.1 h).1

theorem maxR {a b k : Nat} (h : max a b ≤ k) : b ≤ k := (Nat.max_le.1 h).2

/-- The height of a FunLang term: the fuel FunClo needs to evaluate it. -/
def height : FunLang.Tm → Nat
  | .var _ | .int _ | .bool _ => 1
  | .arith _ a b | .cmp _ a b | .pair a b | .let_ a b => max (height a) (height b) + 1
  | .ite c t e | .case c t e => max (height c) (max (height t) (height e)) + 1
  | .fst e | .snd e | .inl e | .inr e => height e + 1

theorem getElem?_map_ofFun (ρ : List FunLang.Val) (i : Nat) :
    (ρ.map Val.ofFun)[i]? = (ρ[i]?).map Val.ofFun := by
  simp

/-- What `eval_ofFun` says of a FunLang term. -/
def OfFun (e : FunLang.Tm) : Prop :=
  ∀ ⦃ρ : List FunLang.Val⦄ ⦃v : FunLang.Val⦄, FunLang.eval ρ e = some v → ∀ k, height e ≤ k →
    eval k (ρ.map Val.ofFun) (Tm.ofFun e) = some (Val.ofFun v)

theorem height_pos (e : FunLang.Tm) : 1 ≤ height e := by
  cases e <;> simp [height]

theorem fuel_succ {e : FunLang.Tm} {k : Nat} (hk : height e ≤ k) : ∃ k', k = k' + 1 :=
  ⟨k - 1, by have := height_pos e; omega⟩

theorem ofFun_var (i : Nat) : OfFun (.var i) := by
  intro ρ v h k hk
  obtain ⟨k, rfl⟩ := fuel_succ hk
  have h' : ρ[i]? = some v := h
  show (ρ.map Val.ofFun)[i]? = some (Val.ofFun v)
  rw [getElem?_map_ofFun, h']
  rfl

theorem ofFun_int (n : BitVec 31) : OfFun (.int n) := by
  intro ρ v h k hk
  obtain ⟨k, rfl⟩ := fuel_succ hk
  cases h
  rfl

theorem ofFun_bool (b : Bool) : OfFun (.bool b) := by
  intro ρ v h k hk
  obtain ⟨k, rfl⟩ := fuel_succ hk
  cases h
  rfl

theorem ofFun_arith {op : Arith} {a b : FunLang.Tm} (ha : OfFun a) (hb : OfFun b) :
    OfFun (.arith op a b) := by
  intro ρ v h k hk
  obtain ⟨k, rfl⟩ := fuel_succ hk
  have hk' : max (height a) (height b) ≤ k := by simp only [height] at hk; omega
  simp only [FunLang.eval] at h
  split at h
  · next x y hxa hyb =>
    cases h
    simp only [eval, Tm.ofFun]
    rw [ha hxa k (maxL hk'), hb hyb k (maxR hk')]
    rfl
  · cases h

theorem ofFun_cmp {op : Cmp} {a b : FunLang.Tm} (ha : OfFun a) (hb : OfFun b) :
    OfFun (.cmp op a b) := by
  intro ρ v h k hk
  obtain ⟨k, rfl⟩ := fuel_succ hk
  have hk' : max (height a) (height b) ≤ k := by simp only [height] at hk; omega
  simp only [FunLang.eval] at h
  split at h
  · next x y hxa hyb =>
    cases h
    simp only [eval, Tm.ofFun]
    rw [ha hxa k (maxL hk'), hb hyb k (maxR hk')]
    rfl
  · cases h

theorem ofFun_ite {c t e : FunLang.Tm} (hc : OfFun c) (ht : OfFun t) (he : OfFun e) :
    OfFun (.ite c t e) := by
  intro ρ v h k hk
  obtain ⟨k, rfl⟩ := fuel_succ hk
  have hk' : max (height c) (max (height t) (height e)) ≤ k := by simp only [height] at hk; omega
  simp only [FunLang.eval] at h
  split at h
  · next hcb =>
    simp only [eval, Tm.ofFun]
    rw [hc hcb k (maxL hk')]
    exact ht h k (maxL (maxR hk'))
  · next hcb =>
    simp only [eval, Tm.ofFun]
    rw [hc hcb k (maxL hk')]
    exact he h k (maxR (maxR hk'))
  · cases h

theorem ofFun_let {a b : FunLang.Tm} (ha : OfFun a) (hb : OfFun b) : OfFun (.let_ a b) := by
  intro ρ v h k hk
  obtain ⟨k, rfl⟩ := fuel_succ hk
  have hk' : max (height a) (height b) ≤ k := by simp only [height] at hk; omega
  simp only [FunLang.eval] at h
  split at h
  · next u hu =>
    simp only [eval, Tm.ofFun]
    rw [ha hu k (maxL hk')]
    exact hb (ρ := u :: ρ) h k (maxR hk')
  · cases h

theorem ofFun_pair {a b : FunLang.Tm} (ha : OfFun a) (hb : OfFun b) : OfFun (.pair a b) := by
  intro ρ v h k hk
  obtain ⟨k, rfl⟩ := fuel_succ hk
  have hk' : max (height a) (height b) ≤ k := by simp only [height] at hk; omega
  simp only [FunLang.eval] at h
  split at h
  · next x y hxa hyb =>
    cases h
    simp only [eval, Tm.ofFun]
    rw [ha hxa k (maxL hk'), hb hyb k (maxR hk')]
    rfl
  · cases h

theorem ofFun_fst {e : FunLang.Tm} (he : OfFun e) : OfFun (.fst e) := by
  intro ρ v h k hk
  obtain ⟨k, rfl⟩ := fuel_succ hk
  have hk' : height e ≤ k := by simp only [height] at hk; omega
  simp only [FunLang.eval] at h
  split at h
  · next x y hxe =>
    cases h
    simp only [eval, Tm.ofFun]
    rw [he hxe k hk']
    rfl
  · cases h

theorem ofFun_snd {e : FunLang.Tm} (he : OfFun e) : OfFun (.snd e) := by
  intro ρ v h k hk
  obtain ⟨k, rfl⟩ := fuel_succ hk
  have hk' : height e ≤ k := by simp only [height] at hk; omega
  simp only [FunLang.eval] at h
  split at h
  · next x y hxe =>
    cases h
    simp only [eval, Tm.ofFun]
    rw [he hxe k hk']
    rfl
  · cases h

theorem ofFun_inl {e : FunLang.Tm} (he : OfFun e) : OfFun (.inl e) := by
  intro ρ v h k hk
  obtain ⟨k, rfl⟩ := fuel_succ hk
  have hk' : height e ≤ k := by simp only [height] at hk; omega
  obtain ⟨u, hu, rfl⟩ : ∃ u, FunLang.eval ρ e = some u ∧ FunLang.Val.inl u = v := by
    simpa only [FunLang.eval, Option.map_eq_some_iff] using h
  show (eval k (ρ.map Val.ofFun) (Tm.ofFun e)).map Val.inl = some (Val.inl (Val.ofFun u))
  rw [he hu k hk']
  rfl

theorem ofFun_inr {e : FunLang.Tm} (he : OfFun e) : OfFun (.inr e) := by
  intro ρ v h k hk
  obtain ⟨k, rfl⟩ := fuel_succ hk
  have hk' : height e ≤ k := by simp only [height] at hk; omega
  obtain ⟨u, hu, rfl⟩ : ∃ u, FunLang.eval ρ e = some u ∧ FunLang.Val.inr u = v := by
    simpa only [FunLang.eval, Option.map_eq_some_iff] using h
  show (eval k (ρ.map Val.ofFun) (Tm.ofFun e)).map Val.inr = some (Val.inr (Val.ofFun u))
  rw [he hu k hk']
  rfl

theorem ofFun_case {e l r : FunLang.Tm} (he : OfFun e) (hl : OfFun l) (hr : OfFun r) :
    OfFun (.case e l r) := by
  intro ρ v h k hk
  obtain ⟨k, rfl⟩ := fuel_succ hk
  have hk' : max (height e) (max (height l) (height r)) ≤ k := by simp only [height] at hk; omega
  simp only [FunLang.eval] at h
  split at h
  · next u hu =>
    simp only [eval, Tm.ofFun]
    rw [he hu k (maxL hk')]
    exact hl (ρ := u :: ρ) h k (maxL (maxR hk'))
  · next u hu =>
    simp only [eval, Tm.ofFun]
    rw [he hu k (maxL hk')]
    exact hr (ρ := u :: ρ) h k (maxR (maxR hk'))
  · cases h

/-- **FunLang is a fragment of FunClo**: a FunLang term evaluates in FunClo, with any fuel from
its height on, to its FunLang value. -/
theorem eval_ofFun : ∀ (e : FunLang.Tm), OfFun e
  | .var i => ofFun_var i
  | .int n => ofFun_int n
  | .bool b => ofFun_bool b
  | .arith _ a b => ofFun_arith (eval_ofFun a) (eval_ofFun b)
  | .cmp _ a b => ofFun_cmp (eval_ofFun a) (eval_ofFun b)
  | .ite c t e => ofFun_ite (eval_ofFun c) (eval_ofFun t) (eval_ofFun e)
  | .let_ a b => ofFun_let (eval_ofFun a) (eval_ofFun b)
  | .pair a b => ofFun_pair (eval_ofFun a) (eval_ofFun b)
  | .fst e => ofFun_fst (eval_ofFun e)
  | .snd e => ofFun_snd (eval_ofFun e)
  | .inl e => ofFun_inl (eval_ofFun e)
  | .inr e => ofFun_inr (eval_ofFun e)
  | .case e l r => ofFun_case (eval_ofFun e) (eval_ofFun l) (eval_ofFun r)

end Silmaril.Wasm.Models.FunClo

