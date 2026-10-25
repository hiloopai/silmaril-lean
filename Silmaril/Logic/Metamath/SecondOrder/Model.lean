module

public import Silmaril.Logic.Metamath.SecondOrder.Semantics
public import Silmaril.Logic.Metamath.SecondOrder.Syntax
public import Silmaril.Logic.Metamath.Model.Basic
public import Mathlib.Data.Finset.Preimage

@[expose] public section

/-!
# ω-models of the language of second-order arithmetic

The ω-model with second-order part `𝒮 ⊆ 𝒫(ℕ)` over an infinite type of names
`N`, as a Carneiro model of `SecondOrder.grammar` (`SecondOrder.model 𝒮 N`):

* number and set variables denote names (`inl x` and `inr X`);
* terms denote polynomial functions of environments into `ℕ`, and formulas
  definable functions into `Prop` (`Sem.IsPoly`, `Sem.IsDef`), with the
  operations of `Silmaril.Logic.Metamath.SecondOrder.Sem`;
* a name is fresh for a term or formula that ignores it, distinct names are
  fresh for each other (a number name and a set name always are), and terms
  and formulas are fresh for each other;
* `|- ph` holds when `ph` is valid, and `bnd ph`, `sig1 ph`, `pi1 ph`,
  `arith ph` when `ph` is bounded, Σ⁰₁, Π⁰₁, arithmetical.

The values of trees are computed by the `val_*` lemmas, one per syntax rule.
The full model `fullModel N` has `𝒮 = 𝒫(ℕ)`.
-/

namespace Silmaril.Logic.Metamath.SecondOrder

open Grammar Sem Function

/-- The kinds of values. -/
inductive Kind
  | nname | sname | term | formula | unit

/-- The kind of the values of each typecode. -/
def kind : C → Kind
  | .nvar => .nname
  | .svar => .sname
  | .term => .term
  | .wff => .formula
  | _ => .unit

namespace Kind

variable (𝒮 : Set (Set ℕ)) (N : Type) [DecidableEq N]

/-- The values of a kind. -/
abbrev Carrier : Kind → Type
  | .nname => N
  | .sname => N
  | .term => {a : Env 𝒮 N → ℕ // IsPoly a}
  | .formula => {φ : Env 𝒮 N → Prop // IsDef φ}
  | .unit => PUnit

variable {𝒮 N}

/-- The name a value is, if it is one. -/
def nameOf : (k : Kind) → k.Carrier 𝒮 N → Option (N ⊕ N)
  | .nname, x => some (.inl x)
  | .sname, X => some (.inr X)
  | .term, _ => none
  | .formula, _ => none
  | .unit, _ => none

/-- The value ignores the name `n`. Names ignore every name. -/
def Ignores : (k : Kind) → k.Carrier 𝒮 N → N ⊕ N → Prop
  | .term, a, n => Sem.Ignores a.1 n
  | .formula, φ, n => Sem.Ignores φ.1 n
  | _, _, _ => True

/-- Freshness: the names of the two values are distinct and each value
ignores the name of the other. -/
def Fresh (k k' : Kind) (a : k.Carrier 𝒮 N) (b : k'.Carrier 𝒮 N) : Prop :=
  (∀ n ∈ k.nameOf a, ∀ m ∈ k'.nameOf b, n ≠ m) ∧ (∀ n ∈ k.nameOf a, k'.Ignores b n) ∧
    ∀ m ∈ k'.nameOf b, k.Ignores a m

theorem fresh_symm {k k' : Kind} {a : k.Carrier 𝒮 N} {b : k'.Carrier 𝒮 N}
    (h : Fresh k k' a b) : Fresh k' k b a :=
  ⟨fun m hm n hn => (h.1 n hn m hm).symm, h.2.2, h.2.1⟩

/-- A value without a name is fresh for `a` when it ignores the name of `a`. -/
theorem fresh_of_ignores {k k' : Kind} {a : k.Carrier 𝒮 N} {b : k'.Carrier 𝒮 N}
    (hb : k'.nameOf b = none) (h : ∀ n ∈ k.nameOf a, k'.Ignores b n) : Fresh k k' a b :=
  ⟨fun _ _ _ hm => by simp [hb] at hm, h, fun _ hm => by simp [hb] at hm⟩

/-- The finitely many names a value involves. -/
noncomputable def support : (k : Kind) → k.Carrier 𝒮 N → Finset (N ⊕ N)
  | .nname, x => {.inl x}
  | .sname, X => {.inr X}
  | .term, a => Classical.choose a.2.exists_dependsOn
  | .formula, φ => Classical.choose φ.2.exists_dependsOn
  | .unit, _ => ∅

theorem ignores_of_notMem_support {n : N ⊕ N} :
    ∀ {k : Kind} (b : k.Carrier 𝒮 N), n ∉ support k b → k.Ignores b n
  | .nname, _, _ => trivial
  | .sname, _, _ => trivial
  | .term, a, hn => (Classical.choose_spec a.2.exists_dependsOn).ignores hn
  | .formula, φ, hn => (Classical.choose_spec φ.2.exists_dependsOn).ignores hn
  | .unit, _, _ => trivial

theorem mem_support_of_nameOf {n : N ⊕ N} :
    ∀ {k : Kind} (b : k.Carrier 𝒮 N), n ∈ k.nameOf b → n ∈ support k b
  | .nname, _, h => by cases h; exact Finset.mem_singleton_self _
  | .sname, _, h => by cases h; exact Finset.mem_singleton_self _
  | .term, _, h => by cases h
  | .formula, _, h => by cases h
  | .unit, _, h => by cases h

/-- A value of kind `k` fresh for finitely many values. -/
theorem exists_fresh [Infinite N] (k : Kind) (W : List (Σ k' : Kind, k'.Carrier 𝒮 N)) :
    ∃ a : k.Carrier 𝒮 N, ∀ w ∈ W, Fresh k w.1 a w.2 := by
  classical
  let F : Finset (N ⊕ N) := W.foldr (fun w F => support w.1 w.2 ∪ F) ∅
  have hF : ∀ w ∈ W, support w.1 w.2 ⊆ F := by
    intro w hw
    induction W with
    | nil => simp at hw
    | cons w' W ih =>
      rcases List.mem_cons.1 hw with rfl | hw
      · exact Finset.subset_union_left
      · exact (ih hw).trans Finset.subset_union_right
  have name : ∀ n : N ⊕ N, n ∉ F → ∀ w ∈ W, (∀ m ∈ w.1.nameOf w.2, n ≠ m) ∧ w.1.Ignores w.2 n :=
    fun n hn w hw => ⟨fun m hm e => hn (hF w hw (e ▸ mem_support_of_nameOf w.2 hm)),
      ignores_of_notMem_support w.2 fun h => hn (hF w hw h)⟩
  cases k with
  | nname =>
    obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (F.preimage Sum.inl Sum.inl_injective.injOn)
    refine ⟨x, fun w hw => ⟨?_, ?_, fun _ _ => trivial⟩⟩
    · rintro _ ⟨⟩ m hm
      exact (name _ (by simpa using hx) w hw).1 m hm
    · rintro _ ⟨⟩
      exact (name _ (by simpa using hx) w hw).2
  | sname =>
    obtain ⟨X, hX⟩ := Infinite.exists_notMem_finset (F.preimage Sum.inr Sum.inr_injective.injOn)
    refine ⟨X, fun w hw => ⟨?_, ?_, fun _ _ => trivial⟩⟩
    · rintro _ ⟨⟩ m hm
      exact (name _ (by simpa using hX) w hw).1 m hm
    · rintro _ ⟨⟩
      exact (name _ (by simpa using hX) w hw).2
  | term =>
    refine ⟨⟨zero, .zero⟩, fun w _ => fresh_symm (fresh_of_ignores rfl fun _ _ _ _ => rfl)⟩
  | formula =>
    refine ⟨⟨eq zero zero, .eq .zero .zero⟩,
      fun w _ => fresh_symm (fresh_of_ignores rfl fun _ _ _ _ => rfl)⟩
  | unit => exact ⟨PUnit.unit, fun w _ => fresh_symm (fresh_of_ignores rfl fun _ _ => trivial)⟩

end Kind

/-! ## Freshness of the operations -/

namespace Sem

variable {𝒮 : Set (Set ℕ)} {N : Type} [DecidableEq N]

theorem ignores_var {x : N} {n : N ⊕ N} (h : n ≠ .inl x) : Ignores (var (𝒮 := 𝒮) x) n :=
  fun _ _ => update_of_ne (Ne.symm h) _ _

theorem ignores_const {T : Sort*} (t : T) (n : N ⊕ N) :
    Ignores (𝒮 := 𝒮) (fun _ => t) n := fun _ _ => rfl

theorem ignores_comp {T T' : Sort*} {f : Env 𝒮 N → T} {n : N ⊕ N} (h : Ignores f n)
    (g : T → T') : Ignores (fun ρ => g (f ρ)) n :=
  fun ρ a => congrArg g (h ρ a)

theorem ignores_comp₂ {T T' T'' : Sort*} {f : Env 𝒮 N → T} {f' : Env 𝒮 N → T'} {n : N ⊕ N}
    (h : Ignores f n) (h' : Ignores f' n) (g : T → T' → T'') :
    Ignores (fun ρ => g (f ρ) (f' ρ)) n :=
  fun ρ a => congrArg₂ g (h ρ a) (h' ρ a)

/-- Binding a name preserves ignoring any name. -/
theorem ignores_bind {T T' : Sort*} {f : Env 𝒮 N → T} {n : N ⊕ N} (h : Ignores f n)
    (m : N ⊕ N) (g : (Val 𝒮 N m → T) → T') :
    Ignores (fun ρ => g fun a => f (update ρ m a)) n := by
  intro ρ a
  by_cases hnm : n = m
  · subst hnm
    simp only [update_idem]
  · refine congrArg g (funext fun b => ?_)
    rw [update_comm hnm, h]

theorem ignores_mem {a : Env 𝒮 N → ℕ} {X : N} {n : N ⊕ N} (h : Ignores a n)
    (hX : n ≠ .inr X) : Ignores (mem a X) n := fun ρ b => by
  simp only [mem, h ρ b, update_of_ne (Ne.symm hX)]

theorem ignores_seq {X Y : N} {n : N ⊕ N} (hX : n ≠ .inr X) (hY : n ≠ .inr Y) :
    Ignores (seq (𝒮 := 𝒮) X Y) n := fun ρ b => by
  simp only [seq, update_of_ne (Ne.symm hX), update_of_ne (Ne.symm hY)]

end Sem

/-! ## The model -/

variable (𝒮 : Set (Set ℕ)) (N : Type) [DecidableEq N] [Infinite N]

/-- The ω-model with second-order part `𝒮`, over the names `N`. -/
def model : Model grammar where
  Carrier s := (kind s).Carrier 𝒮 N
  op {s} o a := match s, o, a with
    | _, ⟨.tvar, rfl⟩, a => ⟨var (a ⟨0, by decide⟩), .var _⟩
    | _, ⟨.t0, rfl⟩, _ => ⟨zero, .zero⟩
    | _, ⟨.tS, rfl⟩, a => ⟨succ (a ⟨0, by decide⟩).1, .succ (a ⟨0, by decide⟩).2⟩
    | _, ⟨.tpl, rfl⟩, a => ⟨add (a ⟨0, by decide⟩).1 (a ⟨1, by decide⟩).1,
        .add (a ⟨0, by decide⟩).2 (a ⟨1, by decide⟩).2⟩
    | _, ⟨.tmu, rfl⟩, a => ⟨mul (a ⟨0, by decide⟩).1 (a ⟨1, by decide⟩).1,
        .mul (a ⟨0, by decide⟩).2 (a ⟨1, by decide⟩).2⟩
    | _, ⟨.wn, rfl⟩, a => ⟨not (a ⟨0, by decide⟩).1, .not (a ⟨0, by decide⟩).2⟩
    | _, ⟨.wi, rfl⟩, a => ⟨imp (a ⟨0, by decide⟩).1 (a ⟨1, by decide⟩).1,
        .imp (a ⟨0, by decide⟩).2 (a ⟨1, by decide⟩).2⟩
    | _, ⟨.wb, rfl⟩, a => ⟨iff (a ⟨0, by decide⟩).1 (a ⟨1, by decide⟩).1,
        .iff (a ⟨0, by decide⟩).2 (a ⟨1, by decide⟩).2⟩
    | _, ⟨.wa, rfl⟩, a => ⟨and (a ⟨0, by decide⟩).1 (a ⟨1, by decide⟩).1,
        .and (a ⟨0, by decide⟩).2 (a ⟨1, by decide⟩).2⟩
    | _, ⟨.wal, rfl⟩, a => ⟨all (a ⟨1, by decide⟩) (a ⟨0, by decide⟩).1,
        .all _ (a ⟨0, by decide⟩).2⟩
    | _, ⟨.wex, rfl⟩, a => ⟨ex (a ⟨1, by decide⟩) (a ⟨0, by decide⟩).1,
        .ex _ (a ⟨0, by decide⟩).2⟩
    | _, ⟨.wsal, rfl⟩, a => ⟨sall (a ⟨1, by decide⟩) (a ⟨0, by decide⟩).1,
        .sall _ (a ⟨0, by decide⟩).2⟩
    | _, ⟨.wsex, rfl⟩, a => ⟨sex (a ⟨1, by decide⟩) (a ⟨0, by decide⟩).1,
        .sex _ (a ⟨0, by decide⟩).2⟩
    | _, ⟨.weq, rfl⟩, a => ⟨eq (a ⟨0, by decide⟩).1 (a ⟨1, by decide⟩).1,
        .eq (a ⟨0, by decide⟩).2 (a ⟨1, by decide⟩).2⟩
    | _, ⟨.wlt, rfl⟩, a => ⟨lt (a ⟨0, by decide⟩).1 (a ⟨1, by decide⟩).1,
        .lt (a ⟨0, by decide⟩).2 (a ⟨1, by decide⟩).2⟩
    | _, ⟨.wel, rfl⟩, a => ⟨mem (a ⟨1, by decide⟩).1 (a ⟨0, by decide⟩),
        .mem _ (a ⟨1, by decide⟩).2⟩
    | _, ⟨.wseq, rfl⟩, a => ⟨seq (a ⟨0, by decide⟩) (a ⟨1, by decide⟩), .seq _ _⟩
  Fresh {s t} a b := Kind.Fresh (kind s) (kind t) a b
  fresh_symm := Kind.fresh_symm
  fresh_op {s t} a o args h := by
    obtain ⟨l, rfl⟩ := o
    refine Kind.fresh_of_ignores (by cases l <;> rfl) fun n hn => ?_
    have hj := fun j => h j
    have h0 := fun hlt => (hj ⟨0, hlt⟩).2.1 n hn
    have h1 := fun hlt => (hj ⟨1, hlt⟩).2.1 n hn
    cases l with
    | tvar => exact ignores_var ((hj ⟨0, by decide⟩).1 n hn _ rfl)
    | t0 => exact ignores_const 0 n
    | tS => exact ignores_comp (h0 (by decide)) (· + 1)
    | tpl => exact ignores_comp₂ (h0 (by decide)) (h1 (by decide)) (· + ·)
    | tmu => exact ignores_comp₂ (h0 (by decide)) (h1 (by decide)) (· * ·)
    | wn => exact ignores_comp (h0 (by decide)) Not
    | wi => exact ignores_comp₂ (h0 (by decide)) (h1 (by decide)) (· → ·)
    | wb => exact ignores_comp₂ (h0 (by decide)) (h1 (by decide)) Iff
    | wa => exact ignores_comp₂ (h0 (by decide)) (h1 (by decide)) And
    | wal => exact ignores_bind (h0 (by decide)) (.inl _) fun P => ∀ k, P k
    | wex => exact ignores_bind (h0 (by decide)) (.inl _) fun P => ∃ k, P k
    | wsal => exact ignores_bind (h0 (by decide)) (.inr _) fun P => ∀ k, P k
    | wsex => exact ignores_bind (h0 (by decide)) (.inr _) fun P => ∃ k, P k
    | weq => exact ignores_comp₂ (h0 (by decide)) (h1 (by decide)) (· = ·)
    | wlt => exact ignores_comp₂ (h0 (by decide)) (h1 (by decide)) (· < ·)
    | wel => exact ignores_mem (h1 (by decide)) ((hj ⟨0, by decide⟩).1 n hn _ rfl)
    | wseq =>
      exact ignores_seq ((hj ⟨0, by decide⟩).1 n hn _ rfl) ((hj ⟨1, by decide⟩).1 n hn _ rfl)
  exists_fresh s _ W := (Kind.exists_fresh (kind s) (W.map fun w => ⟨kind w.1, w.2⟩)).imp
    fun _ h _ hw => h _ (List.mem_map_of_mem hw)
  IsTrue {c s} _ a := match c, s, a with
    | .turnstile, .wff, φ => Valid φ.1
    | .bnd, .wff, φ => IsBnd φ.1
    | .sig1, .wff, φ => IsSig1 φ.1
    | .pi1, .wff, φ => IsPi1 φ.1
    | .arith, .wff, φ => IsArith φ.1
    | _, _, _ => False

/-- The full model: `𝒮` is every set of numbers. -/
abbrev fullModel : Model grammar := model Set.univ N

/-! ## Values of trees -/

section Values

variable {𝒮 N} {ctx : V → C → Prop}

/-- Sorting in the context `ctx`. -/
local notation "HS" t:max s:max => grammar.HasSort ctx t s


theorem tvar_0 {a : Tree L V} (h : HS (.node .tvar [a]) .term) : HS a .nvar :=
  h.child ⟨0, by decide⟩

theorem tS_0 {a : Tree L V} (h : HS (.node .tS [a]) .term) : HS a .term :=
  h.child ⟨0, by decide⟩

theorem tpl_0 {a b : Tree L V} (h : HS (.node .tpl [a, b]) .term) : HS a .term :=
  h.child ⟨0, by decide⟩

theorem tpl_1 {a b : Tree L V} (h : HS (.node .tpl [a, b]) .term) : HS b .term :=
  h.child ⟨1, by decide⟩

theorem tmu_0 {a b : Tree L V} (h : HS (.node .tmu [a, b]) .term) : HS a .term :=
  h.child ⟨0, by decide⟩

theorem tmu_1 {a b : Tree L V} (h : HS (.node .tmu [a, b]) .term) : HS b .term :=
  h.child ⟨1, by decide⟩

theorem wn_0 {a : Tree L V} (h : HS (.node .wn [a]) .wff) : HS a .wff :=
  h.child ⟨0, by decide⟩

theorem wi_0 {a b : Tree L V} (h : HS (.node .wi [a, b]) .wff) : HS a .wff :=
  h.child ⟨0, by decide⟩

theorem wi_1 {a b : Tree L V} (h : HS (.node .wi [a, b]) .wff) : HS b .wff :=
  h.child ⟨1, by decide⟩

theorem wb_0 {a b : Tree L V} (h : HS (.node .wb [a, b]) .wff) : HS a .wff :=
  h.child ⟨0, by decide⟩

theorem wb_1 {a b : Tree L V} (h : HS (.node .wb [a, b]) .wff) : HS b .wff :=
  h.child ⟨1, by decide⟩

theorem wa_0 {a b : Tree L V} (h : HS (.node .wa [a, b]) .wff) : HS a .wff :=
  h.child ⟨0, by decide⟩

theorem wa_1 {a b : Tree L V} (h : HS (.node .wa [a, b]) .wff) : HS b .wff :=
  h.child ⟨1, by decide⟩

theorem wal_0 {a b : Tree L V} (h : HS (.node .wal [a, b]) .wff) : HS a .wff :=
  h.child ⟨0, by decide⟩

theorem wal_1 {a b : Tree L V} (h : HS (.node .wal [a, b]) .wff) : HS b .nvar :=
  h.child ⟨1, by decide⟩

theorem wex_0 {a b : Tree L V} (h : HS (.node .wex [a, b]) .wff) : HS a .wff :=
  h.child ⟨0, by decide⟩

theorem wex_1 {a b : Tree L V} (h : HS (.node .wex [a, b]) .wff) : HS b .nvar :=
  h.child ⟨1, by decide⟩

theorem wsal_0 {a b : Tree L V} (h : HS (.node .wsal [a, b]) .wff) : HS a .wff :=
  h.child ⟨0, by decide⟩

theorem wsal_1 {a b : Tree L V} (h : HS (.node .wsal [a, b]) .wff) : HS b .svar :=
  h.child ⟨1, by decide⟩

theorem wsex_0 {a b : Tree L V} (h : HS (.node .wsex [a, b]) .wff) : HS a .wff :=
  h.child ⟨0, by decide⟩

theorem wsex_1 {a b : Tree L V} (h : HS (.node .wsex [a, b]) .wff) : HS b .svar :=
  h.child ⟨1, by decide⟩

theorem weq_0 {a b : Tree L V} (h : HS (.node .weq [a, b]) .wff) : HS a .term :=
  h.child ⟨0, by decide⟩

theorem weq_1 {a b : Tree L V} (h : HS (.node .weq [a, b]) .wff) : HS b .term :=
  h.child ⟨1, by decide⟩

theorem wlt_0 {a b : Tree L V} (h : HS (.node .wlt [a, b]) .wff) : HS a .term :=
  h.child ⟨0, by decide⟩

theorem wlt_1 {a b : Tree L V} (h : HS (.node .wlt [a, b]) .wff) : HS b .term :=
  h.child ⟨1, by decide⟩

theorem wel_0 {a b : Tree L V} (h : HS (.node .wel [a, b]) .wff) : HS a .svar :=
  h.child ⟨0, by decide⟩

theorem wel_1 {a b : Tree L V} (h : HS (.node .wel [a, b]) .wff) : HS b .term :=
  h.child ⟨1, by decide⟩

theorem wseq_0 {a b : Tree L V} (h : HS (.node .wseq [a, b]) .wff) : HS a .svar :=
  h.child ⟨0, by decide⟩

theorem wseq_1 {a b : Tree L V} (h : HS (.node .wseq [a, b]) .wff) : HS b .svar :=
  h.child ⟨1, by decide⟩

variable (ρ : ∀ q s, ctx q s → (model 𝒮 N).Carrier s)


theorem val_tvar {a : Tree L V} (h : HS (.node .tvar [a]) .term) :
    ((model 𝒮 N).value ρ _ h).1 =
      var (𝒮 := 𝒮) (N := N) ((model 𝒮 N).value ρ a (tvar_0 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem val_t0 (h : HS (.node .t0 []) .term) :
    ((model 𝒮 N).value ρ _ h).1 =
      zero := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem val_tS {a : Tree L V} (h : HS (.node .tS [a]) .term) :
    ((model 𝒮 N).value ρ _ h).1 =
      succ ((model 𝒮 N).value ρ a (tS_0 h)).1 := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem val_tpl {a b : Tree L V} (h : HS (.node .tpl [a, b]) .term) :
    ((model 𝒮 N).value ρ _ h).1 =
      add ((model 𝒮 N).value ρ a (tpl_0 h)).1 ((model 𝒮 N).value ρ b (tpl_1 h)).1 := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem val_tmu {a b : Tree L V} (h : HS (.node .tmu [a, b]) .term) :
    ((model 𝒮 N).value ρ _ h).1 =
      mul ((model 𝒮 N).value ρ a (tmu_0 h)).1 ((model 𝒮 N).value ρ b (tmu_1 h)).1 := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem val_wn {a : Tree L V} (h : HS (.node .wn [a]) .wff) :
    ((model 𝒮 N).value ρ _ h).1 =
      Sem.not ((model 𝒮 N).value ρ a (wn_0 h)).1 := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem val_wi {a b : Tree L V} (h : HS (.node .wi [a, b]) .wff) :
    ((model 𝒮 N).value ρ _ h).1 =
      imp ((model 𝒮 N).value ρ a (wi_0 h)).1 ((model 𝒮 N).value ρ b (wi_1 h)).1 := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem val_wb {a b : Tree L V} (h : HS (.node .wb [a, b]) .wff) :
    ((model 𝒮 N).value ρ _ h).1 =
      iff ((model 𝒮 N).value ρ a (wb_0 h)).1 ((model 𝒮 N).value ρ b (wb_1 h)).1 := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem val_wa {a b : Tree L V} (h : HS (.node .wa [a, b]) .wff) :
    ((model 𝒮 N).value ρ _ h).1 =
      Sem.and ((model 𝒮 N).value ρ a (wa_0 h)).1 ((model 𝒮 N).value ρ b (wa_1 h)).1 := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem val_wal {a b : Tree L V} (h : HS (.node .wal [a, b]) .wff) :
    ((model 𝒮 N).value ρ _ h).1 =
      all (N := N) ((model 𝒮 N).value ρ b (wal_1 h)) ((model 𝒮 N).value ρ a (wal_0 h)).1 := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem val_wex {a b : Tree L V} (h : HS (.node .wex [a, b]) .wff) :
    ((model 𝒮 N).value ρ _ h).1 =
      ex (N := N) ((model 𝒮 N).value ρ b (wex_1 h)) ((model 𝒮 N).value ρ a (wex_0 h)).1 := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem val_wsal {a b : Tree L V} (h : HS (.node .wsal [a, b]) .wff) :
    ((model 𝒮 N).value ρ _ h).1 =
      sall (N := N) ((model 𝒮 N).value ρ b (wsal_1 h)) ((model 𝒮 N).value ρ a (wsal_0 h)).1 := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem val_wsex {a b : Tree L V} (h : HS (.node .wsex [a, b]) .wff) :
    ((model 𝒮 N).value ρ _ h).1 =
      sex (N := N) ((model 𝒮 N).value ρ b (wsex_1 h)) ((model 𝒮 N).value ρ a (wsex_0 h)).1 := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem val_weq {a b : Tree L V} (h : HS (.node .weq [a, b]) .wff) :
    ((model 𝒮 N).value ρ _ h).1 =
      eq ((model 𝒮 N).value ρ a (weq_0 h)).1 ((model 𝒮 N).value ρ b (weq_1 h)).1 := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem val_wlt {a b : Tree L V} (h : HS (.node .wlt [a, b]) .wff) :
    ((model 𝒮 N).value ρ _ h).1 =
      lt ((model 𝒮 N).value ρ a (wlt_0 h)).1 ((model 𝒮 N).value ρ b (wlt_1 h)).1 := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem val_wel {a b : Tree L V} (h : HS (.node .wel [a, b]) .wff) :
    ((model 𝒮 N).value ρ _ h).1 =
      mem (N := N) ((model 𝒮 N).value ρ b (wel_1 h)).1 ((model 𝒮 N).value ρ a (wel_0 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem val_wseq {a b : Tree L V} (h : HS (.node .wseq [a, b]) .wff) :
    ((model 𝒮 N).value ρ _ h).1 =
      seq (𝒮 := 𝒮) (N := N) ((model 𝒮 N).value ρ a (wseq_0 h))
        ((model 𝒮 N).value ρ b (wseq_1 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem val_var {q : V} {s : C} (h : HS (.var q) s) :
    (model 𝒮 N).value ρ (.var q) h = ρ q s (HasSort.var_iff.1 h) :=
  Model.value_var _ ρ h

end Values

end Silmaril.Logic.Metamath.SecondOrder
