module

public import Silmaril.Wasm.Binaryen.Equiv
public import Silmaril.Wasm.Binaryen.Profile
public import Silmaril.Wasm.Binaryen.RenTyping
public import Silmaril.Wasm.Binaryen.Pass.RUMESim.Init
public import Silmaril.Wasm.Binaryen.Pass.RUMESim.Ren

@[expose] public section

/-! # P4: RemoveUnusedModuleElements (functions and globals)

Binaryen's `RemoveUnusedModuleElements` (`src/passes/RemoveUnusedModuleElements.cpp`,
version_133) computes the elements reachable from the roots (exports, start,
segments) and removes the rest. Here: defined functions and defined globals,
reached through direct calls, `ref.func`, `global.get`/`global.set`, and global
initialisers. Imports are kept. The "referenced but not used" tier (a function
only referenced from a table keeps a body of `unreachable`) waits for tables.

`rume` filters and re-indexes (`rumeCore`); modules outside the base profile or
with imported globals are left unchanged, since the simulation below assumes that global addresses are all allocated
by the module itself. Its soundness is `ExportEquiv Eq`: exports are
observed by name, so re-indexing is invisible. The proof route is an
address-injection store relation reusing `Link/GlobalRename*` and
`Link/GlobalPermutation` (which already relate stores under global
renumbering) and the `Reachable`/`StepClosed` pattern of a separate reachable-store refinement development (not included in this package):
from reachable code, only reachable functions and globals are ever touched.

Inlining's callee deletion is this pass: `rume_deletes` says a function with no
references that is neither exported nor the start function is removed.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics

/-- Live functions and globals (absolute indices). -/
structure Live where
  funcs : List Nat
  globals : List Nat
  deriving Repr

namespace BModule

/-- Total function and global counts (imports included). -/
def numFuncs (m : BModule) : Nat := m.numImportedFuncs + m.funcs.length
def numGlobals (m : BModule) : Nat := m.numImportedGlobals + m.base.globals.length

/-- Functions and globals referenced by function `f`'s body. -/
def funcEdges (m : BModule) (f : Nat) : List Nat × List Nat :=
  match m.defFunc? f with
  | some fn =>
      let code := BExpr.lowerList fn.body
      (Validation.Expr.freeFuncs code, instrsGlobals code)
  | none => ([], [])

/-- Functions and globals referenced by global `g`'s initialiser. -/
def globalEdges (m : BModule) (g : Nat) : List Nat × List Nat :=
  if g < m.numImportedGlobals then ([], [])
  else match m.base.globals[g - m.numImportedGlobals]? with
    | some gl => (Validation.Expr.freeFuncs gl.init, instrsGlobals gl.init)
    | none => ([], [])

/-- Roots: exports and the start function. -/
def roots (m : BModule) : Live where
  funcs := m.base.exports.filterMap (fun e => match e.index with
    | .func f => some f.toNat | _ => none) ++ (m.base.start.map Idx.toNat).toList
  globals := m.base.exports.filterMap fun e => match e.index with
    | .global g => some g.toNat | _ => none

/-- One closure step. -/
def reachStep (m : BModule) (l : Live) : Live where
  funcs := (l.funcs ++ (l.funcs.map m.funcEdges).flatMap Prod.fst ++
    (l.globals.map m.globalEdges).flatMap Prod.fst).eraseDups
  globals := (l.globals ++ (l.funcs.map m.funcEdges).flatMap Prod.snd ++
    (l.globals.map m.globalEdges).flatMap Prod.snd).eraseDups

/-- **The reachable set**: the least set containing the roots and closed under
references, computed by iterating `reachStep` (it stabilises within the number
of elements). -/
def reach (m : BModule) : Live := Nat.iterate m.reachStep (m.numFuncs + m.numGlobals + 1) m.roots

/-- Re-indexing: an index keeps its rank among the kept ones. -/
def rank (keep : Nat → Bool) (n : Nat) : Nat := ((List.range n).filter keep).length

end BModule

/-- Keep the elements whose (offset) index satisfies `p`. -/
def filterIdxFrom {α : Type} (p : Nat → Bool) : Nat → List α → List α
  | _, [] => []
  | n, a :: as => if p n then a :: filterIdxFrom p (n + 1) as else filterIdxFrom p (n + 1) as

/-- RemoveUnusedModuleElements for functions and globals, on any module. -/
def rumeCore (m : BModule) : BModule :=
  let live := m.reach
  let keepF : Nat → Bool := fun f => f < m.numImportedFuncs || live.funcs.contains f
  let keepG : Nat → Bool := fun g => g < m.numImportedGlobals || live.globals.contains g
  let ρ : Ren := ⟨BModule.rank keepF, BModule.rank keepG⟩
  let funcs := (filterIdxFrom keepF m.numImportedFuncs m.funcs).map
    fun f => { f with body := ρ.bexprs f.body }
  let globals := (filterIdxFrom keepG m.numImportedGlobals m.base.globals).map
    fun g => { g with init := ρ.instrs g.init }
  let exports := m.base.exports.map fun e => match e.index with
    | .func f => { e with index := .func (ρ.funcIdx f) }
    | .global g => { e with index := .global (ρ.globalIdx g) }
    | _ => e
  ⟨{ m.base with globals := globals, exports := exports, start := m.base.start.map ρ.funcIdx },
    funcs⟩


/-! ## The closure argument for `reach` -/

namespace BModule

/-- `l` is closed under the reference edges of `m`. -/
def LiveClosed (m : BModule) (l : Live) : Prop :=
  (∀ f ∈ l.funcs, (m.funcEdges f).1 ⊆ l.funcs ∧ (m.funcEdges f).2 ⊆ l.globals) ∧
  (∀ g ∈ l.globals, (m.globalEdges g).1 ⊆ l.funcs ∧ (m.globalEdges g).2 ⊆ l.globals)

theorem mem_reachStep_funcs (m : BModule) (l : Live) (x : Nat) :
    x ∈ (m.reachStep l).funcs ↔ x ∈ l.funcs ∨ (∃ f ∈ l.funcs, x ∈ (m.funcEdges f).1) ∨
      ∃ g ∈ l.globals, x ∈ (m.globalEdges g).1 := by
  simp only [reachStep, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ((h | ⟨_, ⟨f, hf, rfl⟩, hx⟩) | ⟨_, ⟨g, hg, rfl⟩, hx⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨f, hf, hx⟩)
    · exact Or.inr (Or.inr ⟨g, hg, hx⟩)
  · rintro (h | ⟨f, hf, hx⟩ | ⟨g, hg, hx⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨_, ⟨f, hf, rfl⟩, hx⟩)
    · exact Or.inr ⟨_, ⟨g, hg, rfl⟩, hx⟩

theorem mem_reachStep_globals (m : BModule) (l : Live) (x : Nat) :
    x ∈ (m.reachStep l).globals ↔ x ∈ l.globals ∨ (∃ f ∈ l.funcs, x ∈ (m.funcEdges f).2) ∨
      ∃ g ∈ l.globals, x ∈ (m.globalEdges g).2 := by
  simp only [reachStep, List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ((h | ⟨_, ⟨f, hf, rfl⟩, hx⟩) | ⟨_, ⟨g, hg, rfl⟩, hx⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨f, hf, hx⟩)
    · exact Or.inr (Or.inr ⟨g, hg, hx⟩)
  · rintro (h | ⟨f, hf, hx⟩ | ⟨g, hg, hx⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨_, ⟨f, hf, rfl⟩, hx⟩)
    · exact Or.inr ⟨_, ⟨g, hg, rfl⟩, hx⟩

theorem funcEdges_of_ge {m : BModule} {f : Nat} (h : m.numFuncs ≤ f) :
    m.funcEdges f = ([], []) := by
  have hd : m.defFunc? f = none := by
    unfold defFunc?
    split
    · rfl
    · simp only [numFuncs] at h
      exact List.getElem?_eq_none (by omega)
  simp [funcEdges, hd]

theorem globalEdges_of_ge {m : BModule} {g : Nat} (h : m.numGlobals ≤ g) :
    m.globalEdges g = ([], []) := by
  unfold globalEdges
  split
  · rfl
  · simp only [numGlobals] at h
    rw [List.getElem?_eq_none (by omega)]

/-- If a step adds nothing new in range, its result is closed. -/
theorem liveClosed_of_stable (m : BModule) (l : Live)
    (hf : ∀ x < m.numFuncs, x ∈ (m.reachStep l).funcs → x ∈ l.funcs)
    (hg : ∀ x < m.numGlobals, x ∈ (m.reachStep l).globals → x ∈ l.globals) :
    m.LiveClosed (m.reachStep l) := by
  refine ⟨fun f hfm => ?_, fun g hgm => ?_⟩
  · by_cases hlt : f < m.numFuncs
    · have hl := hf f hlt hfm
      exact ⟨fun x hx => (mem_reachStep_funcs m l x).2 (Or.inr (Or.inl ⟨f, hl, hx⟩)),
        fun x hx => (mem_reachStep_globals m l x).2 (Or.inr (Or.inl ⟨f, hl, hx⟩))⟩
    · rw [funcEdges_of_ge (by omega)]
      exact ⟨List.nil_subset _, List.nil_subset _⟩
  · by_cases hlt : g < m.numGlobals
    · have hl := hg g hlt hgm
      exact ⟨fun x hx => (mem_reachStep_funcs m l x).2 (Or.inr (Or.inr ⟨g, hl, hx⟩)),
        fun x hx => (mem_reachStep_globals m l x).2 (Or.inr (Or.inr ⟨g, hl, hx⟩))⟩
    · rw [globalEdges_of_ge (by omega)]
      exact ⟨List.nil_subset _, List.nil_subset _⟩

/-- A closed set stays closed under `reachStep` (it is a fixpoint up to membership). -/
theorem liveClosed_reachStep {m : BModule} {l : Live} (h : m.LiveClosed l) :
    m.LiveClosed (m.reachStep l) := by
  apply liveClosed_of_stable
  · intro x _ hx
    rcases (mem_reachStep_funcs m l x).1 hx with hx | ⟨f, hf, hx⟩ | ⟨g, hg, hx⟩
    · exact hx
    · exact (h.1 f hf).1 hx
    · exact (h.2 g hg).1 hx
  · intro x _ hx
    rcases (mem_reachStep_globals m l x).1 hx with hx | ⟨f, hf, hx⟩ | ⟨g, hg, hx⟩
    · exact hx
    · exact (h.1 f hf).2 hx
    · exact (h.2 g hg).2 hx

private theorem filter_length_le {p q : Nat → Bool} :
    ∀ (xs : List Nat), (∀ x ∈ xs, p x = true → q x = true) →
      (xs.filter p).length ≤ (xs.filter q).length
  | [], _ => Nat.le_refl _
  | a :: xs, h => by
    have ih := filter_length_le xs (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha := h a List.mem_cons_self
    simp only [List.filter_cons]
    cases hp : p a <;> cases hq : q a <;> (simp_all; try omega)

private theorem filter_length_lt {p q : Nat → Bool} :
    ∀ (xs : List Nat), (∀ x ∈ xs, p x = true → q x = true) →
      (∃ x ∈ xs, q x = true ∧ p x = false) → (xs.filter p).length < (xs.filter q).length
  | [], _, ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | a :: xs, h, ⟨x, hx, hqx, hpx⟩ => by
    have hle := filter_length_le xs (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha := h a List.mem_cons_self
    simp only [List.filter_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · simp [hqx, hpx]; omega
    · have ih := filter_length_lt xs (fun x hx => h x (List.mem_cons_of_mem a hx))
        ⟨x, hx, hqx, hpx⟩
      cases hp : p a <;> cases hq : q a <;> (simp_all; try omega)

/-- The number of in-range live elements. -/
def liveCount (m : BModule) (l : Live) : Nat :=
  ((List.range m.numFuncs).filter (fun x => decide (x ∈ l.funcs))).length +
  ((List.range m.numGlobals).filter (fun x => decide (x ∈ l.globals))).length

theorem liveCount_le (m : BModule) (l : Live) : m.liveCount l ≤ m.numFuncs + m.numGlobals := by
  have h₁ := List.length_filter_le (fun x => decide (x ∈ l.funcs)) (List.range m.numFuncs)
  have h₂ := List.length_filter_le (fun x => decide (x ∈ l.globals)) (List.range m.numGlobals)
  simp only [List.length_range] at h₁ h₂
  unfold liveCount; omega

/-- A step that does not close the set strictly increases the count. -/
theorem liveCount_lt {m : BModule} {l : Live} (h : ¬ m.LiveClosed (m.reachStep l)) :
    m.liveCount l < m.liveCount (m.reachStep l) := by
  have subF : ∀ x ∈ List.range m.numFuncs, decide (x ∈ l.funcs) = true →
      decide (x ∈ (m.reachStep l).funcs) = true := by
    intro x _ hx
    simp only [decide_eq_true_eq] at hx ⊢
    exact (mem_reachStep_funcs m l x).2 (Or.inl hx)
  have subG : ∀ x ∈ List.range m.numGlobals, decide (x ∈ l.globals) = true →
      decide (x ∈ (m.reachStep l).globals) = true := by
    intro x _ hx
    simp only [decide_eq_true_eq] at hx ⊢
    exact (mem_reachStep_globals m l x).2 (Or.inl hx)
  have hF := filter_length_le _ subF
  have hG := filter_length_le _ subG
  unfold liveCount
  by_cases hf : ∀ x < m.numFuncs, x ∈ (m.reachStep l).funcs → x ∈ l.funcs
  · by_cases hg : ∀ x < m.numGlobals, x ∈ (m.reachStep l).globals → x ∈ l.globals
    · exact absurd (liveClosed_of_stable m l hf hg) h
    · have : ∃ x ∈ List.range m.numGlobals, decide (x ∈ (m.reachStep l).globals) = true ∧
          decide (x ∈ l.globals) = false := by
        simp only [not_forall] at hg
        obtain ⟨x, hx, hm, hn⟩ := hg
        exact ⟨x, List.mem_range.2 hx, by simpa using hm, by simpa using hn⟩
      have := filter_length_lt _ subG this
      omega
  · have : ∃ x ∈ List.range m.numFuncs, decide (x ∈ (m.reachStep l).funcs) = true ∧
        decide (x ∈ l.funcs) = false := by
      simp only [not_forall] at hf
      obtain ⟨x, hx, hm, hn⟩ := hf
      exact ⟨x, List.mem_range.2 hx, by simpa using hm, by simpa using hn⟩
    have := filter_length_lt _ subF this
    omega

theorem iterate_succ_apply (m : BModule) (k : Nat) (l : Live) :
    Nat.iterate m.reachStep (k + 1) l = m.reachStep (Nat.iterate m.reachStep k l) := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih => exact ih (m.reachStep l)

theorem iterate_closed_or (m : BModule) (l : Live) : ∀ k,
    m.LiveClosed (Nat.iterate m.reachStep k l) ∨ k ≤ m.liveCount (Nat.iterate m.reachStep k l)
  | 0 => Or.inr (Nat.zero_le _)
  | k + 1 => by
    rw [iterate_succ_apply]
    by_cases hc : m.LiveClosed (m.reachStep (Nat.iterate m.reachStep k l))
    · exact Or.inl hc
    · right
      have hlt := liveCount_lt hc
      rcases iterate_closed_or m l k with h | h
      · exact absurd (liveClosed_reachStep h) hc
      · omega

/-- **`reach` is closed** under function and global edges. -/
theorem reach_liveClosed (m : BModule) : m.LiveClosed m.reach := by
  rcases iterate_closed_or m m.roots (m.numFuncs + m.numGlobals + 1) with h | h
  · exact h
  · have := liveCount_le m (Nat.iterate m.reachStep (m.numFuncs + m.numGlobals + 1) m.roots)
    unfold reach at *
    omega

/-- Every live function is a root or referenced from a function body or a global
initialiser. -/
theorem iterate_funcs_sub (m : BModule) : ∀ k, ∀ x ∈ (Nat.iterate m.reachStep k m.roots).funcs,
    x ∈ m.roots.funcs ∨
      x ∈ (m.funcs.flatMap fun fn => Validation.Expr.freeFuncs (BExpr.lowerList fn.body)) ∨
      x ∈ (m.base.globals.flatMap fun g => Validation.Expr.freeFuncs g.init)
  | 0, x, hx => Or.inl hx
  | k + 1, x, hx => by
    rw [iterate_succ_apply] at hx
    rcases (mem_reachStep_funcs m _ x).1 hx with hx | ⟨f, _, hx⟩ | ⟨g, _, hx⟩
    · exact iterate_funcs_sub m k x hx
    · right; left
      unfold funcEdges at hx
      split at hx
      · rename_i fn hfn
        unfold defFunc? at hfn
        split at hfn
        · cases hfn
        · exact List.mem_flatMap.2 ⟨fn, List.mem_of_getElem? hfn, hx⟩
      · simp at hx
    · right; right
      unfold globalEdges at hx
      split at hx
      · simp at hx
      · split at hx
        · rename_i gl hgl
          exact List.mem_flatMap.2 ⟨gl, List.mem_of_getElem? hgl, hx⟩
        · simp at hx

end BModule

/-- The reachable set is closed under references. -/
theorem reach_closed (m : BModule) : ∀ f ∈ m.reach.funcs,
    (m.funcEdges f).1 ⊆ m.reach.funcs ∧ (m.funcEdges f).2 ⊆ m.reach.globals :=
  (BModule.reach_liveClosed m).1

/-! ## Filtering and re-indexing -/

/-- Number of kept indices among `n, …, n + x - 1`. -/
def cntFrom (p : Nat → Bool) (n x : Nat) : Nat := ((List.range x).filter fun i => p (n + i)).length

theorem filterIdxFrom_append {α : Type} (p : Nat → Bool) : ∀ (n : Nat) (A B : List α),
    filterIdxFrom p n (A ++ B) = filterIdxFrom p n A ++ filterIdxFrom p (n + A.length) B
  | n, [], B => by simp [filterIdxFrom]
  | n, a :: A, B => by
    have ih := filterIdxFrom_append p (n + 1) A B
    rw [show n + 1 + A.length = n + (a :: A).length by simp only [List.length_cons]; omega] at ih
    cases h : p n <;> simp [filterIdxFrom, h, ih]

theorem filterIdxFrom_all {α : Type} (p : Nat → Bool) : ∀ (n : Nat) (A : List α),
    (∀ j < A.length, p (n + j) = true) → filterIdxFrom p n A = A
  | _, [], _ => rfl
  | n, a :: A, h => by
    have h0 : p n = true := by simpa using h 0 (by simp)
    have ih := filterIdxFrom_all p (n + 1) A (fun j hj => by
      have := h (j + 1) (by simp only [List.length_cons]; omega)
      rwa [show n + (j + 1) = n + 1 + j by omega] at this)
    simp [filterIdxFrom, h0, ih]

theorem cntFrom_succ (p : Nat → Bool) (n x : Nat) :
    cntFrom p n (x + 1) = cntFrom p (n + 1) x + (if p n then 1 else 0) := by
  unfold cntFrom
  rw [List.range_succ_eq_map, List.filter_cons, List.filter_map]
  have e : ((fun i => p (n + i)) ∘ Nat.succ) = fun i => p (n + 1 + i) := by
    funext i
    simp only [Function.comp]
    congr 1
    omega
  rw [e]
  cases p n <;> simp

theorem filterIdxFrom_getElem? {α : Type} (p : Nat → Bool) : ∀ (n : Nat) (L : List α) (x : Nat),
    p (n + x) = true → x < L.length → (filterIdxFrom p n L)[cntFrom p n x]? = L[x]?
  | _, [], _, _, hx => by simp at hx
  | n, a :: L, 0, hp, _ => by
    simp only [Nat.add_zero] at hp
    simp [filterIdxFrom, hp, cntFrom]
  | n, a :: L, x + 1, hp, hx => by
    rw [cntFrom_succ]
    have ih := filterIdxFrom_getElem? p (n + 1) L x
      (by rwa [show n + 1 + x = n + (x + 1) by omega]) (by simp at hx; omega)
    cases h : p n
    · simp only [filterIdxFrom, h, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
        List.getElem?_cons_succ]
      exact ih
    · simp only [filterIdxFrom, h, ↓reduceIte, List.getElem?_cons_succ]
      exact ih

theorem rank_eq_cntFrom (p : Nat → Bool) (x : Nat) : BModule.rank p x = cntFrom p 0 x := by
  simp [BModule.rank, cntFrom]

theorem BModule.rank_le (p : Nat → Bool) (n : Nat) : BModule.rank p n ≤ n := by
  have := List.length_filter_le p (List.range n)
  simpa [BModule.rank] using this

/-- Looking up a kept index after filtering, with an always-kept prefix. -/
theorem lookup_kept {α : Type} (p : Nat → Bool) (A B : List α)
    (hA : ∀ j < A.length, p j = true) {x : Nat} (hx : p x = true) {a : α}
    (h : (A ++ B)[x]? = some a) : (A ++ filterIdxFrom p A.length B)[BModule.rank p x]? = some a := by
  have e : A ++ filterIdxFrom p A.length B = filterIdxFrom p 0 (A ++ B) := by
    rw [filterIdxFrom_append, filterIdxFrom_all p 0 A (fun j hj => by simpa using hA j hj),
      Nat.zero_add]
  rw [e, rank_eq_cntFrom, filterIdxFrom_getElem? p 0 (A ++ B) x (by simpa using hx)
    (List.getElem?_eq_some_iff.1 h).1, h]

theorem forall₂_filterIdxFrom {α β γ : Type} {R : α → β → Prop} {S : γ → β → Prop}
    (p : Nat → Bool) (g : α → γ) : ∀ (n : Nat) (l₁ : List α) (l₂ : List β),
    List.Forall₂ R l₁ l₂ →
    (∀ j a b, l₁[j]? = some a → p (n + j) = true → R a b → S (g a) b) →
    List.Forall₂ S ((filterIdxFrom p n l₁).map g) (filterIdxFrom p n l₂)
  | _, [], [], .nil, _ => .nil
  | n, a :: l₁, b :: l₂, .cons hab h, hS => by
    have ih := forall₂_filterIdxFrom p g (n + 1) l₁ l₂ h (fun j a' b' hj hp hr =>
      hS (j + 1) a' b' (by simpa using hj) (by rwa [show n + (j + 1) = n + 1 + j by omega]) hr)
    cases hp : p n
    · simpa [filterIdxFrom, hp] using ih
    · simp only [filterIdxFrom, hp, ↓reduceIte, List.map_cons]
      exact .cons (hS 0 a b rfl (by simpa using hp) hab) ih

theorem forall₂_imp_mem {α β : Type} {R S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → (∀ a ∈ l₁, ∀ b, R a b → S a b) →
      List.Forall₂ S l₁ l₂
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, hS => .cons (hS _ List.mem_cons_self _ h)
      (forall₂_imp_mem t fun a ha b hab => hS a (List.mem_cons_of_mem _ ha) b hab)

theorem forall₂_map_left {α β γ : Type} {R : γ → β → Prop} (f : α → γ) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ (fun a b => R (f a) b) l₁ l₂ →
      List.Forall₂ R (l₁.map f) l₂
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons h (forall₂_map_left f t)

theorem forall₂_of_map_left {α β γ : Type} {R : γ → β → Prop} (f : α → γ) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R (l₁.map f) l₂ →
      List.Forall₂ (fun a b => R (f a) b) l₁ l₂
  | [], [], _ => .nil
  | _ :: _, _ :: _, .cons h t => .cons h (forall₂_of_map_left f t)

theorem map_name_eq (l : List Export) (F : Export → Export) (hF : ∀ e, (F e).name = e.name) :
    (l.map F).map Export.name = l.map Export.name := by
  rw [List.map_map]
  exact List.map_congr_left (fun e _ => hF e)

/-! ## What RUME keeps -/

namespace BModule

/-- RUME's kept functions (absolute indices). -/
def keepF (m : BModule) : Nat → Bool := fun f => f < m.numImportedFuncs || m.reach.funcs.contains f

/-- RUME's kept globals (absolute indices). -/
def keepG (m : BModule) : Nat → Bool :=
  fun g => g < m.numImportedGlobals || m.reach.globals.contains g

/-- RUME's renaming. -/
def rumeRen (m : BModule) : Ren := ⟨rank m.keepF, rank m.keepG⟩

theorem roots_sub_iterate (m : BModule) : ∀ k,
    (∀ x ∈ m.roots.funcs, x ∈ (Nat.iterate m.reachStep k m.roots).funcs) ∧
    (∀ x ∈ m.roots.globals, x ∈ (Nat.iterate m.reachStep k m.roots).globals)
  | 0 => ⟨fun _ hx => hx, fun _ hx => hx⟩
  | k + 1 => by
    rw [iterate_succ_apply]
    exact ⟨fun x hx => (mem_reachStep_funcs m _ x).2 (Or.inl ((roots_sub_iterate m k).1 x hx)),
      fun x hx => (mem_reachStep_globals m _ x).2 (Or.inl ((roots_sub_iterate m k).2 x hx))⟩

theorem keepF_of_mem {m : BModule} {x : Nat} (h : x ∈ m.reach.funcs) : m.keepF x = true := by
  simp [keepF, h]

theorem keepG_of_mem {m : BModule} {x : Nat} (h : x ∈ m.reach.globals) : m.keepG x = true := by
  simp [keepG, h]

theorem keepF_of_root {m : BModule} {x : Nat} (h : x ∈ m.roots.funcs) : m.keepF x = true :=
  keepF_of_mem ((roots_sub_iterate m _).1 x h)

theorem keepG_of_root {m : BModule} {x : Nat} (h : x ∈ m.roots.globals) : m.keepG x = true :=
  keepG_of_mem ((roots_sub_iterate m _).2 x h)

theorem mem_of_keepF {m : BModule} {x : Nat} (h : m.keepF x = true)
    (hx : m.numImportedFuncs ≤ x) : x ∈ m.reach.funcs := by
  simp only [keepF, Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
  rcases h with h | h
  · omega
  · exact h

theorem mem_of_keepG {m : BModule} {x : Nat} (h : m.keepG x = true)
    (hx : m.numImportedGlobals ≤ x) : x ∈ m.reach.globals := by
  simp only [keepG, Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
  rcases h with h | h
  · omega
  · exact h

/-- The references of a kept function body are kept. -/
theorem funcEdges_kept {m : BModule} {f : Nat} {fn : BFunc} (hk : m.keepF f = true)
    (hf : m.numImportedFuncs ≤ f) (hfn : m.funcs[f - m.numImportedFuncs]? = some fn) :
    (∀ x ∈ Validation.Expr.freeFuncs (BExpr.lowerList fn.body), m.keepF x = true) ∧
    (∀ x ∈ instrsGlobals (BExpr.lowerList fn.body), m.keepG x = true) := by
  have hmem := mem_of_keepF hk hf
  have hd : m.defFunc? f = some fn := by
    have hlt : ¬ f < m.numImportedFuncs := by omega
    unfold defFunc?
    simp only [hlt, ↓reduceIte]
    exact hfn
  have hc := (reach_liveClosed m).1 f hmem
  simp only [funcEdges, hd] at hc
  exact ⟨fun x hx => keepF_of_mem (hc.1 hx), fun x hx => keepG_of_mem (hc.2 hx)⟩

/-- The references of a kept global initialiser are kept. -/
theorem globalEdges_kept {m : BModule} {g : Nat} {gl : Global} (hk : m.keepG g = true)
    (hg : m.numImportedGlobals ≤ g) (hgl : m.base.globals[g - m.numImportedGlobals]? = some gl) :
    (∀ x ∈ Validation.Expr.freeFuncs gl.init, m.keepF x = true) ∧
    (∀ x ∈ instrsGlobals gl.init, m.keepG x = true) := by
  have hmem := mem_of_keepG hk hg
  have he : m.globalEdges g = (Validation.Expr.freeFuncs gl.init, instrsGlobals gl.init) := by
    have hlt : ¬ g < m.numImportedGlobals := by omega
    unfold globalEdges
    simp only [hlt, ↓reduceIte, hgl]
  have hc := (reach_liveClosed m).2 g hmem
  rw [he] at hc
  exact ⟨fun x hx => keepF_of_mem (hc.1 hx), fun x hx => keepG_of_mem (hc.2 hx)⟩

theorem rumeRen_funcIdx (m : BModule) (x : FuncIdx) :
    (m.rumeRen.funcIdx x).toNat = rank m.keepF x.toNat := by
  have hlt : rank m.keepF x.toNat < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (rank_le _ _) x.value.isLt
  show ((Idx.ofNat? (rank m.keepF x.toNat)).getD x).toNat = _
  simp only [Idx.ofNat?, hlt, ↓reduceDIte, Option.getD_some]
  rfl

theorem rumeRen_globalIdx (m : BModule) (x : GlobalIdx) :
    (m.rumeRen.globalIdx x).toNat = rank m.keepG x.toNat := by
  have hlt : rank m.keepG x.toNat < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (rank_le _ _) x.value.isLt
  show ((Idx.ofNat? (rank m.keepG x.toNat)).getD x).toNat = _
  simp only [Idx.ofNat?, hlt, ↓reduceDIte, Option.getD_some]
  rfl

end BModule

theorem rume_lower_funcs (m : BModule) : (rumeCore m).lower.funcs =
    ((filterIdxFrom m.keepF m.numImportedFuncs m.funcs).map fun f =>
      ({ f with body := m.rumeRen.bexprs f.body } : BFunc)).map
        (Declaration.Func.mapBody BExpr.lowerList) := rfl

theorem rume_lower_globals (m : BModule) : (rumeCore m).lower.globals =
    (filterIdxFrom m.keepG m.numImportedGlobals m.base.globals).map
      fun g => { g with init := m.rumeRen.instrs g.init } := rfl

theorem rume_lower_exports (m : BModule) : (rumeCore m).lower.exports =
    m.base.exports.map fun e => match e.index with
      | .func f => { e with index := .func (m.rumeRen.funcIdx f) }
      | .global g => { e with index := .global (m.rumeRen.globalIdx g) }
      | _ => e := rfl

theorem rume_lower_start (m : BModule) :
    (rumeCore m).lower.start = m.base.start.map m.rumeRen.funcIdx := rfl

/-! ## Typing the output -/

theorem imports_ok_funcs {C : Context} : ∀ {ims : List Import} {xts : List CExternType},
    List.Forall₂ (ImportOk C) ims xts → (∀ i ∈ ims, FuncOrMemImport i) →
    CExternType.globals xts = [] ∧
      (CExternType.funcs xts).length = (ims.filterMap fun e => match e.type with
        | .func t => some t | _ => none).length
  | [], [], .nil, _ => ⟨rfl, rfl⟩
  | im :: ims, xt :: xts, .cons hi hs, hf => by
    obtain ⟨ih₁, ih₂⟩ := imports_ok_funcs hs (fun i hi => hf i (List.mem_cons_of_mem _ hi))
    rcases hf im List.mem_cons_self with ⟨t, ht⟩ | ⟨mt, ht⟩
    · have hx : ∃ d, xt = .func d := by
        have := hi.1
        rw [ht] at this
        simp only [Context.closeExtern?, Option.map_eq_some_iff] at this
        obtain ⟨d, -, rfl⟩ := this
        exact ⟨d, rfl⟩
      obtain ⟨d, rfl⟩ := hx
      refine ⟨ih₁, ?_⟩
      simp [CExternType.funcs, ht, ih₂]
    · have hx : ∃ mt', xt = .mem mt' := by
        have := hi.1
        rw [ht] at this
        simp only [Context.closeExtern?, Option.some.injEq] at this
        exact ⟨_, this.symm⟩
      obtain ⟨mt', rfl⟩ := hx
      exact ⟨by simpa [CExternType.globals] using ih₁, by simpa [CExternType.funcs, ht] using ih₂⟩

theorem numImportedGlobals_eq_zero {m : BModule}
    (h : ∀ i ∈ m.base.imports, FuncOrMemImport i) : m.numImportedGlobals = 0 := by
  unfold BModule.numImportedGlobals
  rw [List.filter_eq_nil_iff.2]
  · rfl
  · intro i hi
    rcases h i hi with ⟨t, ht⟩ | ⟨mt, ht⟩ <;> simp [ht]

/-- Validity of the kept globals. -/
theorem globalsOk_ren {C : Context} {FT : List DefType} {RT : List Nat} (p kf : Nat → Bool)
    (ρ : Ren)
    (hρf : ∀ x : FuncIdx, kf x.toNat = true → ∀ d, C.funcs[x.toNat]? = some d →
      FT[(ρ.funcIdx x).toNat]? = some d)
    (hρg : ∀ x : GlobalIdx, p x.toNat = true → (ρ.globalIdx x).toNat = BModule.rank p x.toNat) :
    ∀ (P : List CGlobalType) (gs : List Global) (gts : List CGlobalType),
    GlobalsOk { C with globals := P } gs gts →
    (∀ j g, gs[j]? = some g → p (P.length + j) = true →
      (∀ x ∈ Validation.Expr.freeFuncs g.init, kf x = true) ∧
      (∀ x ∈ instrsGlobals g.init, p x = true) ∧ ∀ i ∈ g.init, instrInProfile i) →
    GlobalsOk { C with funcs := FT, globals := filterIdxFrom p 0 P, refs := RT }
      ((filterIdxFrom p P.length gs).map fun g => { g with init := ρ.instrs g.init })
      (filterIdxFrom p P.length gts)
  | _, [], [], .nil, _ => .nil
  | P, g :: gs, gt :: gts, .cons hg hs, hk => by
    change GlobalsOk { C with globals := P ++ [gt] } gs gts at hs
    have ih := globalsOk_ren (RT := RT) p kf ρ hρf hρg (P ++ [gt]) gs gts hs (fun j g' hj hp =>
      hk (j + 1) g' (by simpa using hj) (by rwa [show P.length + (j + 1) =
        (P ++ [gt]).length + j by simp only [List.length_append, List.length_singleton]; omega]))
    have hlen : (P ++ [gt]).length = P.length + 1 := by simp
    rw [hlen, filterIdxFrom_append] at ih
    cases hpk : p P.length
    · simp only [filterIdxFrom, hpk, Bool.false_eq_true, ↓reduceIte, List.append_nil,
        Nat.zero_add] at ih ⊢
      exact ih
    · simp only [filterIdxFrom, hpk, ↓reduceIte, List.map_cons, Nat.zero_add] at ih ⊢
      obtain ⟨hkf, hkg, hkp⟩ := hk 0 g rfl (by simpa using hpk)
      have hρ : RenOk ρ (fun x => kf x = true) (fun x => p x = true) { C with globals := P } FT
          (filterIdxFrom p 0 P) := by
        refine ⟨fun x hx d hd => hρf x hx d hd, fun x hx g' hg' => ?_⟩
        rw [hρg x hx, rank_eq_cntFrom]
        rw [filterIdxFrom_getElem? p 0 P x.toNat (by simpa using hx)
          (List.getElem?_eq_some_iff.1 hg').1]
        exact hg'
      refine .cons (And.intro hg.1 (And.intro hg.2.1 (ExprOkConst.mk ?_ ?_))) ih
      · exact RenTyping.instrsOk_ren hg.2.2.typed RT hρ hkf hkg hkp
      · intro i hi
        obtain ⟨i₀, hi₀, rfl⟩ := List.mem_map.1 hi
        exact RenTyping.instrConst_ren (C := { C with globals := P }) (hg.2.2.const i₀ hi₀)
          hρ
          (fun x hx => hkg x (List.mem_flatMap.2 ⟨i₀, hi₀, hx⟩))

/-- Validity of a kept function. -/
theorem funcOk_ren {C : Context} {fn : BFunc} {d : DefType}
    (h : FuncOk C (Declaration.Func.mapBody BExpr.lowerList fn) d)
    {FT : List DefType} {GT : List CGlobalType} {RT : List Nat}
    {ρ : Ren} {kf kg : Nat → Prop} (hρ : RenOk ρ kf kg C FT GT)
    (hf : ∀ x ∈ Validation.Expr.freeFuncs (BExpr.lowerList fn.body), kf x)
    (hg : ∀ x ∈ instrsGlobals (BExpr.lowerList fn.body), kg x)
    (hp : ∀ i ∈ BExpr.lowerList fn.body, instrInProfile i) :
    FuncOk { C with funcs := FT, globals := GT, refs := RT }
      (Declaration.Func.mapBody BExpr.lowerList ({ fn with body := ρ.bexprs fn.body } : BFunc))
      d := by
  cases h with
  | mk hd he hl hb =>
    refine .mk hd he (hl.imp fun _ _ h => ?_) ?_
    · cases h <;> constructor <;> assumption
    · have := RenTyping.instrsOk_ren hb RT ⟨hρ.funcs, hρ.globals⟩ hf hg hp
      change InstrsOk _ (BExpr.lowerList (ρ.bexprs fn.body)) _
      rw [Ren.lowerList_bexprs]
      exact this

/-- RUME preserves validity. -/
theorem rumeCore_valid {m : BModule} (hp : m.inProfileBase = true) (hng : m.numImportedGlobals = 0)
    (h : m.Ok) : (rumeCore m).Ok := by
  have hpr := BModule.inProfileBase_sound hp
  obtain ⟨mt, hM⟩ := h
  cases hM with
  | @mk dts xtI jts gts tts fdts rts xtE C' C htypes himports hC' hC htags hglobals hmems htables
      hfuncs hdata helems hstart hexports hdisjoint =>
  subst hC' hC
  have himp : ∀ i ∈ m.base.imports, FuncOrMemImport i := hpr.funcOrMemImports hng
  obtain ⟨hxg, hxf⟩ := imports_ok_funcs himports himp
  have hnIG := numImportedGlobals_eq_zero himp
  have hnIF : (CExternType.funcs xtI).length = m.numImportedFuncs := hxf
  have hj : jts = [] := by
    rw [show m.lower.tags = [] from hpr.tags] at htags
    cases htags
    rfl
  have ht : tts = [] := by
    rw [show m.lower.tables = [] from hpr.tables] at htables
    cases htables
    rfl
  have hr : rts = [] := by
    rw [show m.lower.elems = [] from hpr.elems] at helems
    cases helems
    rfl
  subst hj ht hr
  -- the function and global index facts
  have hkA : ∀ j < (CExternType.funcs xtI).length, m.keepF j = true := by
    intro j hj
    rw [hnIF] at hj
    simp [BModule.keepF, hj]
  have hFT : ∀ x : FuncIdx, m.keepF x.toNat = true → ∀ d,
      (CExternType.funcs xtI ++ fdts)[x.toNat]? = some d →
      (CExternType.funcs xtI ++ filterIdxFrom m.keepF m.numImportedFuncs fdts)[
        (m.rumeRen.funcIdx x).toNat]? = some d := by
    intro x hx d hd
    rw [BModule.rumeRen_funcIdx, ← hnIF]
    exact lookup_kept m.keepF _ fdts hkA hx hd
  have hGT : ∀ x : GlobalIdx, m.keepG x.toNat = true → ∀ g,
      (CExternType.globals xtI ++ gts)[x.toNat]? = some g →
      (CExternType.globals xtI ++ filterIdxFrom m.keepG 0 gts)[
        (m.rumeRen.globalIdx x).toNat]? = some g := by
    intro x hx g hg
    rw [BModule.rumeRen_globalIdx, hxg]
    rw [hxg] at hg
    exact lookup_kept m.keepG [] gts (fun j hj => absurd hj (by simp)) hx hg
  refine ⟨⟨xtI, xtE⟩, ModuleOk.mk (dts := dts) (jts := []) (tts := []) (rts := [])
    (gts := filterIdxFrom m.keepG 0 gts)
    (fdts := filterIdxFrom m.keepF m.numImportedFuncs fdts)
    htypes himports rfl rfl ?_ ?_ hmems ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · -- tags
    show List.Forall₂ _ m.lower.tags []
    rw [hpr.tags]
    exact .nil
  · -- globals
    rw [hxg] at hglobals ⊢
    rw [rume_lower_globals, hnIG]
    exact globalsOk_ren
      (C := { types := dts, globals := [], funcs := CExternType.funcs xtI ++ fdts,
              refs := funcIdxNonFuncs m.lower })
      m.keepG m.keepF m.rumeRen
      (fun x hx d hd => hFT x hx d hd)
      (fun x _ => BModule.rumeRen_globalIdx m x) [] m.base.globals gts hglobals
      (fun j g hj hk => by
        have hj' : m.base.globals[j - m.numImportedGlobals]? = some g := by
          rw [hnIG]; exact hj
        obtain ⟨h₁, h₂⟩ := BModule.globalEdges_kept (by simpa using hk) (by omega) hj'
        refine ⟨h₁, h₂, (hpr.globals g (List.mem_of_getElem? hj)).2⟩)
  · -- tables
    show List.Forall₂ _ m.lower.tables []
    rw [hpr.tables]
    exact .nil
  · -- functions
    rw [rume_lower_funcs, List.map_map]
    have hR : List.Forall₂ (fun fn d => FuncOk _ (Declaration.Func.mapBody BExpr.lowerList fn) d)
        m.funcs fdts := forall₂_of_map_left _ hfuncs
    refine forall₂_filterIdxFrom m.keepF _ m.numImportedFuncs m.funcs fdts hR ?_
    intro j fn d hj hk hfn
    have hj' : m.funcs[m.numImportedFuncs + j - m.numImportedFuncs]? = some fn := by
      rw [Nat.add_sub_cancel_left]; exact hj
    obtain ⟨h₁, h₂⟩ := BModule.funcEdges_kept hk (by omega) hj'
    exact funcOk_ren hfn (ρ := m.rumeRen) (kf := fun x => m.keepF x = true)
      (kg := fun x => m.keepG x = true)
      ⟨fun x hx d hd => hFT x hx d hd, fun x hx g hg => hGT x hx g hg⟩ h₁ h₂
      (hpr.code _ (List.mem_map_of_mem (List.mem_of_getElem? hj)))
  · -- data: constant offsets mention no function or global
    intro d hd
    obtain ⟨-, hoff⟩ := hpr.data d hd
    have hok := hdata d hd
    obtain ⟨bytes, mode⟩ := d
    unfold DataOk at hok ⊢
    cases hok with
    | passive => exact .passive
    | active hx ho =>
      obtain ⟨c, rfl⟩ := hoff _ _ rfl
      have ht := RenTyping.instrsOk_ren ho.typed (funcIdxNonFuncs (rumeCore m).lower)
        (F := CExternType.funcs xtI ++ filterIdxFrom m.keepF m.numImportedFuncs fdts)
        (G := CExternType.globals xtI ++ filterIdxFrom m.keepG 0 gts) (ρ := m.rumeRen)
        (kf := fun x => m.keepF x = true) (kg := fun x => m.keepG x = true)
        ⟨fun x hx d hd => hFT x hx d hd, fun x hx g hg => hGT x hx g hg⟩
        (by simp [Validation.Expr.freeFuncs, Instr.freeFuncs])
        (by simp [instrsGlobals, instrGlobals])
        (fun i hi => by
          simp only [List.mem_singleton] at hi
          subst hi
          exact instrInProfile_of_flat (by rfl))
      have hc := RenTyping.instrConst_ren (ho.const _ List.mem_cons_self)
        (R := funcIdxNonFuncs (rumeCore m).lower) (ρ := m.rumeRen)
        (kf := fun x => m.keepF x = true) (kg := fun x => m.keepG x = true)
        (F := CExternType.funcs xtI ++ filterIdxFrom m.keepF m.numImportedFuncs fdts)
        (G := CExternType.globals xtI ++ filterIdxFrom m.keepG 0 gts)
        ⟨fun x hx d hd => hFT x hx d hd, fun x hx g hg => hGT x hx g hg⟩ (by simp [instrGlobals])
      have hfix : m.rumeRen.instr (.intConst .i32 c) = .intConst .i32 c :=
        RenTyping.ren_fixed _ rfl (by simp [Instr.freeFuncs]) (by simp [instrGlobals])
      simp only [Ren.instrs, List.map_cons, List.map_nil, hfix] at ht
      rw [hfix] at hc
      refine .active hx ⟨ht, fun i hi => ?_⟩
      simp only [List.mem_singleton] at hi
      subst hi
      exact hc
  · -- elems
    show List.Forall₂ _ m.lower.elems []
    rw [hpr.elems]
    exact .nil
  · -- start
    intro x hx
    rw [rume_lower_start] at hx
    obtain ⟨x₀, hs, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨d, hd, he⟩ := hstart x₀ hs
    refine ⟨d, hFT x₀ (BModule.keepF_of_root ?_) d hd, he⟩
    simp [BModule.roots, hs]
  · -- exports
    rw [rume_lower_exports]
    refine forall₂_map_left _ (forall₂_imp_mem hexports ?_)
    rintro ⟨name, idx⟩ he xt hxt
    change ExternIdxOk _ idx xt at hxt
    cases idx with
    | func x =>
      cases hxt with
      | func hd =>
        show ExternIdxOk _ (.func (m.rumeRen.funcIdx x)) _
        refine .func (hFT x (BModule.keepF_of_root ?_) _ hd)
        simp only [BModule.roots, List.mem_append, List.mem_filterMap]
        exact Or.inl ⟨_, he, rfl⟩
    | global x =>
      cases hxt with
      | global hg =>
        show ExternIdxOk _ (.global (m.rumeRen.globalIdx x)) _
        refine .global (hGT x (BModule.keepG_of_root ?_) _ hg)
        simp only [BModule.roots, List.mem_filterMap]
        exact ⟨_, he, rfl⟩
    | tag x =>
      cases hxt
      rename_i hd
      show ExternIdxOk _ (.tag x) _
      exact ExternIdxOk.tag hd
    | memory x =>
      cases hxt
      rename_i hd
      show ExternIdxOk _ (.memory x) _
      exact ExternIdxOk.mem hd
    | table x =>
      cases hxt
      rename_i hd
      show ExternIdxOk _ (.table x) _
      exact ExternIdxOk.table hd
  · -- distinct export names
    rw [show (rumeCore m).lower.exports.map Export.name = m.base.exports.map Export.name from
      map_name_eq _ _ (fun e => by rcases e with ⟨name, idx⟩; cases idx <;> rfl)]
    exact hdisjoint

/-! ## Soundness: the instances of `m` and `rumeCore m` execute in lockstep

The simulation of `RUMESim` relates the source and target instances: foreign
functions and globals keep their addresses, kept functions and globals are
related through the two module instances, and their code through the renaming.
-/

section Soundness

open RUMESim

/-! ### Counting kept indices -/

theorem length_filterIdxFrom {α : Type} (p : Nat → Bool) : ∀ (n : Nat) (l : List α),
    (filterIdxFrom p n l).length = cntFrom p n l.length
  | n, [] => by simp [filterIdxFrom, cntFrom]
  | n, a :: l => by
    rw [List.length_cons, cntFrom_succ]
    have ih := length_filterIdxFrom p (n + 1) l
    cases h : p n <;> simp [filterIdxFrom, h, ih]

theorem cntFrom_add (p : Nat → Bool) (n a b : Nat) :
    cntFrom p n (a + b) = cntFrom p n a + cntFrom p (n + a) b := by
  induction a generalizing n with
  | zero => simp [cntFrom]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, cntFrom_succ, cntFrom_succ, ih (n + 1),
      show n + 1 + a = n + (a + 1) by omega]
    omega

theorem cntFrom_mono (p : Nat → Bool) (n : Nat) {x y : Nat} (h : x ≤ y) :
    cntFrom p n x ≤ cntFrom p n y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [cntFrom_add]
  omega

theorem cntFrom_lt (p : Nat → Bool) (n : Nat) {x y : Nat} (hp : p (n + x) = true) (h : x < y) :
    cntFrom p n x < cntFrom p n y := by
  have h1 : cntFrom p n (x + 1) ≤ cntFrom p n y := cntFrom_mono p n h
  have h2 : cntFrom p n (x + 1) = cntFrom p n x + 1 := by
    rw [cntFrom_add]
    simp [cntFrom, hp]
  omega

theorem cntFrom_le (p : Nat → Bool) (n x : Nat) : cntFrom p n x ≤ x := by
  have := List.length_filter_le (fun i => p (n + i)) (List.range x)
  simpa [cntFrom] using this

theorem cntFrom_all (p : Nat → Bool) (n x : Nat) (h : ∀ j < x, p (n + j) = true) :
    cntFrom p n x = x := by
  unfold cntFrom
  rw [List.filter_eq_self.2 (fun a ha => h a (List.mem_range.1 ha))]
  simp

theorem rank_inj {p : Nat → Bool} {x y : Nat} (hx : p x = true) (hy : p y = true)
    (h : BModule.rank p x = BModule.rank p y) : x = y := by
  rw [rank_eq_cntFrom, rank_eq_cntFrom] at h
  rcases Nat.lt_trichotomy x y with hxy | rfl | hxy
  · exact absurd h (Nat.ne_of_lt (cntFrom_lt p 0 (by simpa using hx) hxy))
  · rfl
  · exact absurd h.symm (Nat.ne_of_lt (cntFrom_lt p 0 (by simpa using hy) hxy))

/-- The rank of an index past an always-kept prefix. -/
theorem rank_split {p : Nat → Bool} {k x : Nat} (hk : ∀ j < k, p j = true) (hx : k ≤ x) :
    BModule.rank p x = k + cntFrom p k (x - k) := by
  rw [rank_eq_cntFrom, show x = k + (x - k) by omega, cntFrom_add,
    cntFrom_all p 0 k (fun j hj => by simpa using hk j hj)]
  simp

theorem filterIdxFrom_map {α β : Type} (p : Nat → Bool) (f : α → β) : ∀ (n : Nat) (l : List α),
    (filterIdxFrom p n l).map f = filterIdxFrom p n (l.map f)
  | _, [] => rfl
  | n, a :: l => by
    cases h : p n <;> simp [filterIdxFrom, h, filterIdxFrom_map p f (n + 1) l]

theorem mapM_filterIdxFrom {α β : Type} (p : Nat → Bool) (g : α → Option β) :
    ∀ (n : Nat) {l : List α} {r : List β}, l.mapM g = some r →
      (filterIdxFrom p n l).mapM g = some (filterIdxFrom p n r)
  | _, [], r, h => by simp at h; subst h; rfl
  | n, a :: l, r, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, r', hr', rfl⟩ := h
    have ih := mapM_filterIdxFrom p g (n + 1) hr'
    cases hp : p n <;> simp [filterIdxFrom, hp, hb, ih]

theorem filterIdxFrom_getElem?_kept {α : Type} {p : Nat → Bool} {l : List α} {x : Nat}
    (hx : p x = true) : (filterIdxFrom p 0 l)[BModule.rank p x]? = l[x]? := by
  by_cases hl : x < l.length
  · rw [rank_eq_cntFrom, filterIdxFrom_getElem? p 0 l x (by simpa using hx) hl]
  · have h1 : l[x]? = none := List.getElem?_eq_none (by omega)
    have h2 : (filterIdxFrom p 0 l)[BModule.rank p x]? = none := by
      apply List.getElem?_eq_none
      rw [length_filterIdxFrom, rank_eq_cntFrom]
      exact cntFrom_mono p 0 (by omega)
    rw [h1, h2]

/-! ### Global initialisers -/

theorem pcI_fixed (ρ : Ren) {i : Instr} (hp : pcI i) (hg : ∀ x, i ≠ .globalGet x) :
    ρ.instr i = i := by
  cases i with
  | intConst t c => exact RenTyping.ren_fixed ρ rfl (by simp [Instr.freeFuncs]) (by simp [instrGlobals])
  | floatConst t c => exact RenTyping.ren_fixed ρ rfl (by simp [Instr.freeFuncs]) (by simp [instrGlobals])
  | intBinOp t op => exact RenTyping.ren_fixed ρ rfl (by simp [Instr.freeFuncs]) (by simp [instrGlobals])
  | globalGet x => exact absurd rfl (hg x)
  | _ => exact absurd hp (by simp [pcI])

/-- A kept initialiser reads the same values from the kept globals. -/
theorem crel_ren_env (ρ : Ren) (kg : Nat → Bool)
    (hρ : ∀ x : GlobalIdx, kg x.toNat = true → (ρ.globalIdx x).toNat = BModule.rank kg x.toNat)
    (accA : List Val) : ∀ (e : List Instr), (∀ i ∈ e, pcI i) → (∀ x ∈ instrsGlobals e, kg x = true) →
    List.Forall₂ (CRel (envStore (H := Empty) accA) (envFrame accA)
      (envStore (H := Empty) (filterIdxFrom kg 0 accA)) (envFrame (filterIdxFrom kg 0 accA)))
      e (ρ.instrs e)
  | [], _, _ => .nil
  | i :: e, hp, hg => by
    have hgi : ∀ x ∈ instrGlobals i, kg x = true := fun x hx =>
      hg x (by simp only [instrsGlobals, List.flatMap_cons, List.mem_append]; exact .inl hx)
    have hge : ∀ x ∈ instrsGlobals e, kg x = true := fun x hx =>
      hg x (by simp only [instrsGlobals, List.flatMap_cons, List.mem_append] at hx ⊢; exact .inr hx)
    refine .cons ?_ (crel_ren_env ρ kg hρ accA e (fun j hj => hp j (by simp [hj])) hge)
    by_cases hi : ∃ x, i = .globalGet x
    · obtain ⟨x, rfl⟩ := hi
      rw [RenTyping.ren_globalGet]
      refine .inr ⟨x, ρ.globalIdx x, rfl, rfl, ?_⟩
      rw [gval_env, gval_env]
      have hk : kg x.toNat = true := hgi x.toNat (by simp [instrGlobals])
      rw [hρ x hk, filterIdxFrom_getElem?_kept hk]
    · refine .inl ⟨(pcI_fixed ρ (hp i (by simp)) fun x hx => hi ⟨x, hx⟩).symm, hp i (by simp),
        fun x hx => hi ⟨x, hx⟩⟩

/-- **Kept global values**: the target's initialisers compute the kept source values. -/
theorem gv_keep (ρ : Ren) (kg : Nat → Bool)
    (hρ : ∀ x : GlobalIdx, kg x.toNat = true → (ρ.globalIdx x).toNat = BModule.rank kg x.toNat) :
    ∀ (es : List Expr) (accA vals : List Val), (∀ e ∈ es, ∀ i ∈ e, pcI i) →
    (∀ (j : Nat) (e : Expr), es[j]? = some e → kg (accA.length + j) = true →
      ∀ x ∈ instrsGlobals e, kg x = true) →
    gv accA es = some vals →
    gv (filterIdxFrom kg 0 accA) (filterIdxFrom kg accA.length (es.map ρ.instrs)) =
      some (filterIdxFrom kg 0 vals)
  | [], accA, vals, _, _, h => by
    simp only [gv, Option.some.injEq] at h
    subst h
    rfl
  | e :: es, accA, vals, hpc, hkg, h => by
    simp only [gv] at h
    split at h
    · rename_i v hv
      have ih := gv_keep ρ kg hρ es (accA ++ [v]) vals (fun e' h' => hpc e' (by simp [h']))
        (fun j e' hj hk => hkg (j + 1) e' (by simpa using hj)
          (by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hk)) h
      rw [filterIdxFrom_append] at ih
      simp only [List.length_append, List.length_singleton] at ih
      simp only [List.map_cons, filterIdxFrom]
      cases hk : kg accA.length
      · simpa [filterIdxFrom, hk] using ih
      · have hpe : pureEval (filterIdxFrom kg 0 accA) (ρ.instrs e) = some v := by
          unfold pureEval at hv ⊢
          obtain ⟨⟨s', v'⟩, he1, hvv⟩ := Option.map_eq_some_iff.1 hv
          simp only at hvv
          subst hvv
          have hpe0 : ∀ i ∈ e, pcI i := hpc e (by simp)
          have := (evalConst?_rel hpe0 (crel_ren_env ρ kg hρ accA e hpe0
            (hkg 0 e rfl (by simpa using hk))) he1).1
          rw [this]
          rfl
        simp only [ite_true, gv, hpe]
        simpa [filterIdxFrom, hk] using ih
    · cases h


/-! ### Address lists of the two instances -/

theorem funcs_lookup {L : List Nat} {n0 NF : Nat} {p : Nat → Bool}
    (hp : ∀ j < L.length, p j = true) {x : Nat} (hx : p x = true) :
    ((L ++ (List.range NF).map (n0 + ·))[x]? =
      if x < L.length then L[x]? else if x - L.length < NF then some (n0 + (x - L.length))
      else none) ∧
    ((L ++ (List.range (cntFrom p L.length NF)).map (n0 + ·))[BModule.rank p x]? =
      if x < L.length then L[x]? else if x - L.length < NF
        then some (n0 + cntFrom p L.length (x - L.length)) else none) := by
  by_cases hl : x < L.length
  · have hr : BModule.rank p x = x := by
      rw [rank_eq_cntFrom]
      exact cntFrom_all p 0 x (fun j hj => by simpa using hp j (by omega))
    simp [hl, hr, List.getElem?_append_left hl]
  · have hr := rank_split hp (Nat.le_of_not_lt hl)
    refine ⟨?_, ?_⟩
    · rw [List.getElem?_append_right (by omega)]
      simp only [hl, ite_false, List.getElem?_map]
      split <;> simp_all
    · rw [hr, List.getElem?_append_right (by omega)]
      simp only [hl, ite_false, Nat.add_sub_cancel_left, List.getElem?_map]
      by_cases hj : x - L.length < NF
      · have := cntFrom_lt p L.length (x := x - L.length) (y := NF)
          (by rw [Nat.add_sub_cancel' (Nat.le_of_not_lt hl)]; exact hx) hj
        simp [hj, this]
      · have := cntFrom_mono p L.length (x := NF) (y := x - L.length) (by omega)
        simp [hj, show ¬ cntFrom p L.length (x - L.length) < cntFrom p L.length NF by omega]

theorem globals_lookup {g NG : Nat} {p : Nat → Bool} {x : Nat} (hx : p x = true) :
    (List.range' (g + NG) NG)[x]? = (if x < NG then some (g + NG + x) else none) ∧
    (List.range' (g + cntFrom p 0 NG) (cntFrom p 0 NG))[BModule.rank p x]? =
      (if x < NG then some (g + cntFrom p 0 NG + BModule.rank p x) else none) := by
  refine ⟨?_, ?_⟩
  · by_cases hj : x < NG
    · rw [List.getElem?_range' hj]
      simp [hj]
    · rw [List.getElem?_eq_none (by simp only [List.length_range']; omega)]
      simp [hj]
  · rw [rank_eq_cntFrom]
    by_cases hj : x < NG
    · have := cntFrom_lt p 0 (x := x) (y := NG) (by simpa using hx) hj
      rw [List.getElem?_range' this]
      simp [hj]
    · have := cntFrom_mono p 0 (x := NG) (y := x) (by omega)
      rw [List.getElem?_eq_none (by simp only [List.length_range']; omega)]
      simp [hj]

/-! ### Lists of the two modules -/

theorem mem_filterIdxFrom {α : Type} {p : Nat → Bool} : ∀ {n : Nat} {l : List α} {a : α},
    a ∈ filterIdxFrom p n l → a ∈ l
  | _, [], _, h => by simp [filterIdxFrom] at h
  | n, b :: l, a, h => by
    unfold filterIdxFrom at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_filterIdxFrom h)
    · exact List.mem_cons_of_mem _ (mem_filterIdxFrom h)

theorem zip_filterIdxFrom {α β : Type} (p : Nat → Bool) : ∀ (n : Nat) {l₁ : List α} {l₂ : List β},
    l₁.length = l₂.length →
    (filterIdxFrom p n l₁).zip (filterIdxFrom p n l₂) = filterIdxFrom p n (l₁.zip l₂)
  | _, [], [], _ => rfl
  | n, a :: l₁, b :: l₂, h => by
    have ih := zip_filterIdxFrom p (n + 1) (l₁ := l₁) (l₂ := l₂) (by simpa using h)
    cases hp : p n <;> simp [filterIdxFrom, hp, ih]

theorem mapM_getElem? {α β : Type} {g : α → Option β} : ∀ {l : List α} {r : List β},
    l.mapM g = some r → ∀ j : Nat, r[j]? = l[j]?.bind g
  | [], r, h, j => by simp at h; subst h; simp
  | a :: l, r, h, j => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, r', hr', rfl⟩ := h
    cases j with
    | zero => simp [hb]
    | succ j => simpa using mapM_getElem? hr' j

theorem forall₂_getElem?_l {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {n : Nat} {a : α}, l₁[n]? = some a →
      ∃ b, l₂[n]? = some b ∧ R a b
  | _, _, .nil, n, a, h => by simp at h
  | _ :: _, b :: _, .cons hr t, 0, a, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨b, rfl, hr⟩
  | _ :: _, _ :: _, .cons _ t, n + 1, a, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact forall₂_getElem?_l t h

theorem mapM_congr_map {α β γ : Type} (g : α → Option β) (k : γ → Option β) :
    ∀ {l₁ : List α} {l₂ : List γ}, l₁.map g = l₂.map k → l₁.mapM g = l₂.mapM k
  | [], [], _ => rfl
  | a :: l₁, c :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.mapM_cons, h.1, mapM_congr_map g k h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem mapM_length {α β : Type} {g : α → Option β} : ∀ {l : List α} {r : List β},
    l.mapM g = some r → r.length = l.length
  | [], r, h => by simp at h; subst h; rfl
  | a :: l, r, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, r', hr', rfl⟩ := h
    simp [mapM_length hr']

theorem xrel_mono {F₁ F₂ : Nat → Nat → Prop} (hF : ∀ a b, F₁ a b → F₂ a b) :
    ∀ {la lb : List ExportInst}, List.Forall₂ (XRel F₁) la lb → List.Forall₂ (XRel F₂) la lb
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons ⟨hn, hk⟩ t => by
    refine .cons ⟨hn, ?_⟩ (xrel_mono hF t)
    rcases hk with ⟨x, y, hx, hy, hxy⟩ | h
    · exact .inl ⟨x, y, hx, hy, hF _ _ hxy⟩
    · exact .inr h

theorem gv_length : ∀ {acc : List Val} {es : List Expr} {vals : List Val},
    gv acc es = some vals → vals.length = acc.length + es.length
  | acc, [], vals, h => by
    simp only [gv, Option.some.injEq] at h
    subst h; simp
  | acc, e :: es, vals, h => by
    simp only [gv] at h
    split at h
    · have := gv_length h
      simp only [List.length_append, List.length_singleton] at this
      simp only [List.length_cons]
      omega
    · cases h

theorem globalsOk_const {C : Context} {gs : List Global} {gts : List CGlobalType}
    (h : GlobalsOk C gs gts) : ∀ g ∈ gs, ∀ i ∈ g.init, ∃ C', InstrConst C' i := by
  induction h with
  | nil => simp
  | cons hg _ ih =>
    intro g hm i hi
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨_, hg.2.2.const i hi⟩
    · exact ih g hm i hi

theorem pcI_ren (ρ : Ren) {i : Instr} (h : pcI i) : pcI (ρ.instr i) := by
  by_cases hg : ∃ x, i = .globalGet x
  · obtain ⟨x, rfl⟩ := hg
    rw [RenTyping.ren_globalGet]
    trivial
  · rw [pcI_fixed ρ h fun x hx => hg ⟨x, hx⟩]
    exact h

theorem rume_globals_init (m : BModule) (hnIG : m.numImportedGlobals = 0) :
    (rumeCore m).lower.globals.map Global.init =
      filterIdxFrom m.keepG 0 ((m.lower.globals.map Global.init).map m.rumeRen.instrs) := by
  rw [rume_lower_globals, hnIG, List.map_map, filterIdxFrom_map, List.map_map]
  rfl

theorem rume_gtys (m : BModule) (hnIG : m.numImportedGlobals = 0) :
    gtys (rumeCore m).lower = filterIdxFrom m.keepG 0 (gtys m.lower) := by
  unfold gtys
  rw [rume_lower_globals, hnIG, List.map_map, filterIdxFrom_map]
  rfl

theorem rume_funcs_mapM (m : BModule) :
    (rumeCore m).lower.funcs.mapM (fun fn => (allocTypes (rumeCore m).lower.types)[fn.type.toNat]?) =
      (filterIdxFrom m.keepF m.numImportedFuncs m.lower.funcs).mapM
        (fun fn => (allocTypes m.lower.types)[fn.type.toNat]?) := by
  apply mapM_congr_map
  rw [rume_lower_funcs]
  simp only [BModule.lower, List.map_map]
  rw [← filterIdxFrom_map, List.map_map]
  rfl

theorem rume_funcs_getElem? (m : BModule) {j : Nat} (hk : m.keepF (m.numImportedFuncs + j) = true)
    (hj : j < m.funcs.length) :
    (rumeCore m).lower.funcs[cntFrom m.keepF m.numImportedFuncs j]? =
      (m.funcs[j]?).map fun fn => Declaration.Func.mapBody BExpr.lowerList
        ({ fn with body := m.rumeRen.bexprs fn.body } : BFunc) := by
  rw [rume_lower_funcs, List.map_map, List.getElem?_map,
    filterIdxFrom_getElem? m.keepF m.numImportedFuncs m.funcs j hk hj]
  rfl

/-! ### The relation of the two instances -/

section Rel

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem MIrec_funcs (s : Store H) (N : Module) (xas : List ExternAddr) (vals : List Val)
    (xi : List ExportInst) : (MIrec s N xas vals xi).funcs =
      ExternAddr.funcs xas ++ (List.range N.funcs.length).map (s.funcs.length + ·) := rfl

theorem MIrec_globals (s : Store H) (N : Module) (xas : List ExternAddr) (vals : List Val)
    (xi : List ExportInst) (hxg : ExternAddr.globals xas = [])
    (hl : vals.length = N.globals.length) : (MIrec s N xas vals xi).globals =
      List.range' (s.globals.length + N.globals.length) N.globals.length := by
  simp [MIrec, tmpStore, hxg, gtys, hl]

theorem STrec_funcs (s : Store H) (N : Module) (vals : List Val) (ft : List DefType)
    (mi : ModuleInst) : (STrec s N vals ft mi).funcs =
      s.funcs ++ (ft.zip N.funcs).map fun p => ⟨p.1, mi, .wasm p.2⟩ := rfl

theorem STrec_globals (s : Store H) (N : Module) (vals : List Val) (ft : List DefType)
    (mi : ModuleInst) : (STrec s N vals ft mi).globals =
      s.globals ++ ((gtys N).zip vals).map (fun p => (⟨p.1, p.2⟩ : GlobalInst)) ++
        ((gtys N).zip vals).map (fun p => (⟨p.1, p.2⟩ : GlobalInst)) := rfl

theorem STrec_lo_funcs {s : Store H} {N : Module} {vals : List Val} {ft : List DefType}
    {mi : ModuleInst} {a : Nat} (ha : a < s.funcs.length) :
    (STrec s N vals ft mi).funcs[a]? = s.funcs[a]? := by
  rw [STrec_funcs, List.getElem?_append_left ha]

theorem STrec_lo_globals {s : Store H} {N : Module} {vals : List Val} {ft : List DefType}
    {mi : ModuleInst} {a : Nat} (ha : a < s.globals.length) :
    (STrec s N vals ft mi).globals[a]? = s.globals[a]? := by
  rw [STrec_globals, List.append_assoc, List.getElem?_append_left ha]

/-- The functions an instance allocates. -/
theorem STrec_hi_funcs {s : Store H} {N : Module} {vals : List Val} {ft : List DefType}
    {mi : ModuleInst} {j : Nat} {d : DefType} {fn : Func} (hd : ft[j]? = some d)
    (hfn : N.funcs[j]? = some fn) :
    (STrec s N vals ft mi).funcs[s.funcs.length + j]? = some ⟨d, mi, .wasm fn⟩ := by
  rw [STrec_funcs, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_map]
  have : (ft.zip N.funcs)[j]? = some (d, fn) := List.getElem?_zip_eq_some.2 ⟨hd, hfn⟩
  rw [this]
  rfl

/-- The globals an instance allocates. -/
theorem STrec_hi_globals {s : Store H} {N : Module} {vals : List Val} {ft : List DefType}
    {mi : ModuleInst} (hl : vals.length = N.globals.length) {x : Nat} :
    (STrec s N vals ft mi).globals[s.globals.length + N.globals.length + x]? =
      (((gtys N).zip vals).map (fun p => (⟨p.1, p.2⟩ : GlobalInst)))[x]? := by
  have hz : (((gtys N).zip vals).map (fun p => (⟨p.1, p.2⟩ : GlobalInst))).length =
      N.globals.length := by simp [gtys, hl]
  rw [STrec_globals, List.getElem?_append_right (by simp [hz])]
  congr 1
  simp [hz]

/-- The store an instance allocates is foreign to its functions. -/
theorem STrec_storeF {s : Store H} (hs : StoreOk s) {N : Module} (hN : Profiled N)
    {vals : List Val} {ft : List DefType} {mi : ModuleInst}
    (hv : ∀ v ∈ vals, ∃ n, v = .num n) :
    StoreF s.funcs.length s.globals.length (STrec s N vals ft mi) := by
  have hsF := storeF_of_storeOk hs
  refine ⟨?_, ?_, hsF.structs, hsF.arrays, hsF.exns, ?_, ?_⟩
  · intro ti hti r hr
    simp [STrec, tmpStore, hN.tables] at hti
    exact hsF.tables ti hti r hr
  · intro ei hei r hr
    simp [STrec, tmpStore, hN.elems] at hei
    exact hsF.elems ei hei r hr
  · intro g hg
    rw [STrec_globals] at hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with (hg | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩
    · exact hsF.globals g hg
    · obtain ⟨n, hn⟩ := hv _ (List.of_mem_zip hp).2
      simp [hn]
    · obtain ⟨n, hn⟩ := hv _ (List.of_mem_zip hp).2
      simp [hn]
  · intro a ha fi hfi c hc
    rw [STrec_lo_funcs ha] at hfi
    exact hsF.funcs a ha fi hfi c hc

end Rel

/-! ### The instances of `m` and `rumeCore m` -/

section Main

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The configuration an instantiation of a profile module starts from. -/
abbrev instConf (s : Store H) (N : Module) (xas : List ExternAddr) (vals : List Val)
    (ft : List DefType) (xi : List ExportInst) : Config H :=
  ⟨STrec s N vals ft (MIrec s N xas vals xi), { module := MIrec s N xas vals xi }, startCode N⟩

theorem profiled_lower {m : BModule} (hp : m.inProfileBase = true) {mt : CModuleType}
    (hmod : ModuleOk m.lower mt) : Profiled m.lower := by
  have hpr := BModule.inProfileBase_sound hp
  refine ⟨hpr.tags, hpr.tables, hpr.elems, hpr.data, hpr.dataLen, ?_⟩
  intro g hg i hi
  cases hmod with
  | mk _ _ _ _ _ hglobals =>
    obtain ⟨C₀, hc⟩ := globalsOk_const hglobals g hg i hi
    exact pcI_of ((hpr.globals g hg).2 i hi) hc

theorem profiled_rume {m : BModule} (hm : Profiled m.lower) : Profiled (rumeCore m).lower := by
  refine ⟨hm.tags, hm.tables, hm.elems, hm.data, hm.dataLen, ?_⟩
  intro g hg i hi
  rw [rume_lower_globals] at hg
  obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 hg
  obtain ⟨i₀, hi₀, rfl⟩ := List.mem_map.1 hi
  exact pcI_ren _ (hm.pc g₀ (mem_filterIdxFrom hg₀) i₀ hi₀)

/-- The function types of a module's type section have numeric parameters. -/
theorem numParams_types {m : BModule}
    (hty : ∀ st ∈ m.base.typeDefinitions, ∀ ft : FuncType, st.body = .func ft →
      ∀ t ∈ ft.params ++ ft.results, profileValType t = true) :
    ∀ d ∈ allocTypes m.lower.types, NumParams d :=
  numParams_allocTypes fun rt hrt => groupNumP_liftRec fun st hst ft hb t ht =>
    hty st (by
      simp only [Module.typeDefinitions, List.mem_flatMap]
      exact ⟨rt, hrt, hst⟩) ft hb t ht

/-- Profile globals have numeric types. -/
theorem globalsOk_num {C : Context} {gs : List Global} {gts : List CGlobalType}
    (h : GlobalsOk C gs gts) (hp : ∀ g ∈ gs, profileValType g.type.value = true) :
    ∀ gt ∈ gts, ∃ t, gt.type = .num t := by
  induction h with
  | nil => simp
  | @cons C g gs gt gts hg hs ih =>
    intro gt' hgt
    rcases List.mem_cons.1 hgt with rfl | hgt
    · obtain ⟨h1, -, -⟩ := hg
      subst h1
      have hv := hp g List.mem_cons_self
      cases hgv : g.type.value with
      | num t =>
        cases t with
        | int it => exact ⟨.int it, by simp [Context.closeGlobalType, Context.closeVal, hgv, liftVal]; rfl⟩
        | float ft => exact ⟨.float ft, by simp [Context.closeGlobalType, Context.closeVal, hgv, liftVal]; rfl⟩
      | vec _ => rw [hgv] at hv; simp [profileValType] at hv
      | ref _ => rw [hgv] at hv; simp [profileValType] at hv
    · exact ih (fun g' hg' => hp g' (List.mem_cons_of_mem _ hg')) gt' hgt

/-- **The instances of `m` and `rumeCore m` are related**, in both directions. -/
theorem rume_rel {m : BModule} (hp : m.inProfileBase = true) (hng : m.numImportedGlobals = 0)
    (hty : ∀ st ∈ m.base.typeDefinitions, ∀ ft : FuncType, st.body = .func ft →
      ∀ t ∈ ft.params ++ ft.results, profileValType t = true)
    {s : Store H} (hs : StoreOk s) {xas : List ExternAddr} {xtI xtE : List CExternType}
    (hmod : ModuleOk m.lower ⟨xtI, xtE⟩) (hxas : List.Forall₂ (ExternAddrOk s) xas xtI)
    {valsA : List Val} {ftA : List DefType} {xiA : List ExportInst}
    (hvals : gv [] (m.lower.globals.map Global.init) = some valsA)
    (hft : m.lower.funcs.mapM (fun fn => (allocTypes m.lower.types)[fn.type.toNat]?) = some ftA)
    (hxi : m.lower.exports.mapM (allocExport? (EIrec s m.lower xas valsA)) = some xiA) :
    ∃ xiB, gv [] ((rumeCore m).lower.globals.map Global.init) = some (filterIdxFrom m.keepG 0 valsA) ∧
      (rumeCore m).lower.funcs.mapM (fun fn => (allocTypes (rumeCore m).lower.types)[fn.type.toNat]?) =
        some (filterIdxFrom m.keepF m.numImportedFuncs ftA) ∧
      (rumeCore m).lower.exports.mapM
        (allocExport? (EIrec s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA))) = some xiB ∧
      (∃ X : SimCtx, X.WF ∧ ExportsRel X ∧
        ConfRel X .ours (instConf s m.lower xas valsA ftA xiA)
          (instConf s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA)
            (filterIdxFrom m.keepF m.numImportedFuncs ftA) xiB) ∧
        (instConf (H := H) s m.lower xas valsA ftA xiA).frame.module = X.MA ∧
        (instConf (H := H) s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA)
            (filterIdxFrom m.keepF m.numImportedFuncs ftA) xiB).frame.module = X.MB) ∧
      (∃ X : SimCtx, X.WF ∧ ExportsRel X ∧
        ConfRel X .ours (instConf s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA)
            (filterIdxFrom m.keepF m.numImportedFuncs ftA) xiB)
          (instConf s m.lower xas valsA ftA xiA) ∧
        (instConf (H := H) s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA)
            (filterIdxFrom m.keepF m.numImportedFuncs ftA) xiB).frame.module = X.MA ∧
        (instConf (H := H) s m.lower xas valsA ftA xiA).frame.module = X.MB) := by
  have hpr := BModule.inProfileBase_sound hp
  have hPA := profiled_lower hp hmod
  have hPB := profiled_rume hPA
  have himp : ∀ i ∈ m.base.imports, FuncOrMemImport i := hpr.funcOrMemImports hng
  have hnIG := numImportedGlobals_eq_zero himp
  have hexpk : ∀ e ∈ m.base.exports,
      (match e.index with | .func _ | .global _ | .memory _ => true | _ => false) = true := by
    have h := hp
    simp only [BModule.inProfileBase, Bool.and_eq_true, List.all_eq_true] at h
    exact h.2
  have hIP := numParams_types hty
  have hsF := storeF_of_storeOk hs
  cases hmod with
  | @mk dts _ jts gts tts fdts rts _ C' C htypes himports hC' hC htags hglobals hmems htables
      hfuncs hdata helems hstart hexports hdisjoint =>
  subst hC' hC
  obtain ⟨hxtg, hxtf⟩ := imports_ok_funcs himports himp
  have hnIF : (CExternType.funcs xtI).length = m.numImportedFuncs := hxtf
  have hxf := ExternAddrOk.forall₂_funcs hxas
  have hxg : ExternAddr.globals xas = [] := by
    have h := ExternAddrOk.forall₂_globals hxas
    rw [hxtg] at h
    exact List.forall₂_nil_right_iff.1 h
  have hxfl : (ExternAddr.funcs xas).length = m.numImportedFuncs := by
    rw [hxf.length_eq, hnIF]
  have hdts : allocTypes m.lower.types = dts := allocTypes_eq htypes
  -- lengths
  have hNG : valsA.length = m.base.globals.length := by
    have := gv_length hvals
    simpa [BModule.lower] using this
  have hNF : ftA.length = m.funcs.length := by
    have := mapM_length hft
    simpa [BModule.lower] using this
  have hKG : (filterIdxFrom m.keepG 0 valsA).length = cntFrom m.keepG 0 m.base.globals.length := by
    rw [length_filterIdxFrom, hNG]
  have hGB : (rumeCore m).lower.globals.length = cntFrom m.keepG 0 m.base.globals.length := by
    rw [rume_lower_globals, List.length_map, length_filterIdxFrom, hnIG]
  have hFB : (rumeCore m).lower.funcs.length =
      cntFrom m.keepF m.numImportedFuncs m.funcs.length := by
    rw [rume_lower_funcs, List.length_map, List.length_map, length_filterIdxFrom]
  have hkA : ∀ j < (ExternAddr.funcs xas).length, m.keepF j = true := by
    intro j hj
    rw [hxfl] at hj
    simp [BModule.keepF, hj]
  -- the target's global values and function types
  have hpcA : ∀ e ∈ m.lower.globals.map Global.init, ∀ i ∈ e, pcI i := by
    intro e he i hi
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 he
    exact hPA.pc g hg i hi
  have hkgA : ∀ (j : Nat) (e : Expr), (m.lower.globals.map Global.init)[j]? = some e →
      m.keepG (([] : List Val).length + j) = true → ∀ x ∈ instrsGlobals e, m.keepG x = true := by
    intro j e hj hk x hx
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hj
    obtain ⟨gl, hgl, rfl⟩ := hj
    have hgl' : m.base.globals[j - m.numImportedGlobals]? = some gl := by rw [hnIG]; exact hgl
    exact (BModule.globalEdges_kept (by simpa using hk) (by omega) hgl').2 x hx
  have hvB : gv [] ((rumeCore m).lower.globals.map Global.init) =
      some (filterIdxFrom m.keepG 0 valsA) := by
    rw [rume_globals_init m hnIG]
    exact gv_keep m.rumeRen m.keepG (fun x _ => BModule.rumeRen_globalIdx m x) _ [] valsA hpcA
      hkgA hvals
  have hftB : (rumeCore m).lower.funcs.mapM
      (fun fn => (allocTypes (rumeCore m).lower.types)[fn.type.toNat]?) =
        some (filterIdxFrom m.keepF m.numImportedFuncs ftA) := by
    rw [rume_funcs_mapM]
    exact mapM_filterIdxFrom m.keepF _ m.numImportedFuncs hft
  -- the global values are integers
  have hfdts : ∀ d ∈ fdts, d ∈ dts := by
    intro d hd
    obtain ⟨fn, -, hfn⟩ := forall₂_mem_right' hfuncs d hd
    cases hfn with
    | mk hd' _ _ _ => exact List.mem_of_getElem? hd'
  have hvA : ∀ v ∈ valsA, ∃ n, v = .num n := by
    have hdts' : ∀ d ∈ dts, TyOk {} d := TypesOk.tyOk_empty htypes
    have hcl : ∀ d ∈ dts, d.Closed := TypesOk.closed (by simp) htypes
    have hC'ok : ConstCtxOk
        { types := dts, globals := CExternType.globals xtI,
          funcs := CExternType.funcs xtI ++ fdts, refs := funcIdxNonFuncs m.lower } := by
      refine ConstCtxOk.of hdts' hcl rfl (by simp) (imports_globals_ty himports rfl) (by simp)
        (fun d hd => TyOk.of_empty _ (hdts' d ?_)) rfl rfl rfl (by simp)
      rcases List.mem_append.1 hd with hd | hd
      · exact imports_funcs_mem himports d hd
      · exact hfdts d hd
    obtain ⟨vals, hv, hvt⟩ := gv_progress hC'ok hglobals (fun g hg => hPA.pc g hg)
      (globalsOk_num hglobals fun g hg => (hpr.globals g hg).1) [] (by simp [hxtg])
    rw [hvals] at hv
    cases hv
    intro v hv'
    obtain ⟨t, hvt'⟩ := forall₂_mem_left'' hvt v hv'
    obtain ⟨it, c, -, rfl⟩ := hvt'
    exact ⟨_, rfl⟩
  have hvB' : ∀ v ∈ filterIdxFrom m.keepG 0 valsA, ∃ n, v = .num n :=
    fun v hv => hvA v (mem_filterIdxFrom hv)
  -- address lists of the two instances
  have hmiAf : ∀ xi, (MIrec s m.lower xas valsA xi).funcs =
      ExternAddr.funcs xas ++ (List.range m.funcs.length).map (s.funcs.length + ·) := by
    intro xi
    rw [MIrec_funcs]
    simp [BModule.lower]
  have hmiBf : ∀ xi, (MIrec s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA) xi).funcs =
      ExternAddr.funcs xas ++ (List.range (cntFrom m.keepF m.numImportedFuncs
        m.funcs.length)).map (s.funcs.length + ·) := by
    intro xi
    rw [MIrec_funcs, hFB]
  have hmiAg : ∀ xi, (MIrec s m.lower xas valsA xi).globals =
      List.range' (s.globals.length + m.base.globals.length) m.base.globals.length := by
    intro xi
    exact MIrec_globals s _ xas valsA xi hxg hNG
  have hmiBg : ∀ xi, (MIrec s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA) xi).globals =
      List.range' (s.globals.length + cntFrom m.keepG 0 m.base.globals.length)
        (cntFrom m.keepG 0 m.base.globals.length) := by
    intro xi
    rw [MIrec_globals s _ xas _ xi hxg (by rw [hKG, hGB]), hGB]
  have hfl : ∀ xi xi' x, m.keepF x = true →
      (MIrec s m.lower xas valsA xi).funcs[x]? =
        (if x < m.numImportedFuncs then (ExternAddr.funcs xas)[x]?
          else if x - m.numImportedFuncs < m.funcs.length
            then some (s.funcs.length + (x - m.numImportedFuncs)) else none) ∧
      (MIrec s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA) xi').funcs[
          BModule.rank m.keepF x]? =
        (if x < m.numImportedFuncs then (ExternAddr.funcs xas)[x]?
          else if x - m.numImportedFuncs < m.funcs.length
            then some (s.funcs.length + cntFrom m.keepF m.numImportedFuncs (x - m.numImportedFuncs))
            else none) := by
    intro xi xi' x hx
    rw [hmiAf, hmiBf, ← hxfl]
    exact funcs_lookup (n0 := s.funcs.length) (NF := m.funcs.length) hkA hx
  have hgl : ∀ xi xi' x, m.keepG x = true →
      (MIrec s m.lower xas valsA xi).globals[x]? =
        (if x < m.base.globals.length
          then some (s.globals.length + m.base.globals.length + x) else none) ∧
      (MIrec s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA) xi').globals[
          BModule.rank m.keepG x]? =
        (if x < m.base.globals.length then some (s.globals.length +
          cntFrom m.keepG 0 m.base.globals.length + BModule.rank m.keepG x) else none) := by
    intro xi xi' x hx
    rw [hmiAg, hmiBg]
    exact globals_lookup hx
  -- related addresses
  have hfex : ∀ xi xi' x a, m.keepF x = true → (MIrec s m.lower xas valsA xi).funcs[x]? = some a →
      ∃ b, (MIrec s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA) xi').funcs[
          BModule.rank m.keepF x]? = some b ∧
        ((x < m.numImportedFuncs ∧ b = a ∧ (ExternAddr.funcs xas)[x]? = some a) ∨
         (m.numImportedFuncs ≤ x ∧ x - m.numImportedFuncs < m.funcs.length ∧
           a = s.funcs.length + (x - m.numImportedFuncs) ∧
           b = s.funcs.length + cntFrom m.keepF m.numImportedFuncs (x - m.numImportedFuncs))) := by
    intro xi xi' x a hx ha
    obtain ⟨h1, h2⟩ := hfl xi xi' x hx
    rw [h1] at ha
    by_cases hlt : x < m.numImportedFuncs
    · rw [ite_eq_left hlt] at ha h2
      exact ⟨a, h2.trans ha, .inl ⟨hlt, rfl, ha⟩⟩
    · rw [ite_eq_right hlt] at ha h2
      by_cases hj : x - m.numImportedFuncs < m.funcs.length
      · rw [ite_eq_left hj] at ha h2
        exact ⟨_, h2, .inr ⟨by omega, hj, (Option.some.inj ha).symm, rfl⟩⟩
      · rw [ite_eq_right hj] at ha
        cases ha
  have hfex' : ∀ xi xi' x b, m.keepF x = true →
      (MIrec s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA) xi').funcs[
          BModule.rank m.keepF x]? = some b →
      ∃ a, (MIrec s m.lower xas valsA xi).funcs[x]? = some a := by
    intro xi xi' x b hx hb
    obtain ⟨h1, h2⟩ := hfl xi xi' x hx
    rw [h2] at hb
    by_cases hlt : x < m.numImportedFuncs
    · rw [ite_eq_left hlt] at hb h1
      exact ⟨b, h1.trans hb⟩
    · rw [ite_eq_right hlt] at hb h1
      by_cases hj : x - m.numImportedFuncs < m.funcs.length
      · rw [ite_eq_left hj] at hb h1
        exact ⟨_, h1⟩
      · rw [ite_eq_right hj] at hb
        cases hb
  have hgex : ∀ xi xi' x a, m.keepG x = true → (MIrec s m.lower xas valsA xi).globals[x]? = some a →
      x < m.base.globals.length ∧ a = s.globals.length + m.base.globals.length + x ∧
      (MIrec s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA) xi').globals[
          BModule.rank m.keepG x]? = some (s.globals.length +
            cntFrom m.keepG 0 m.base.globals.length + BModule.rank m.keepG x) := by
    intro xi xi' x a hx ha
    obtain ⟨h1, h2⟩ := hgl xi xi' x hx
    rw [h1] at ha
    by_cases hlt : x < m.base.globals.length
    · rw [ite_eq_left hlt] at ha h2
      exact ⟨hlt, (Option.some.inj ha).symm, h2⟩
    · rw [ite_eq_right hlt] at ha
      cases ha
  have hgex' : ∀ xi xi' x b, m.keepG x = true →
      (MIrec s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA) xi').globals[
          BModule.rank m.keepG x]? = some b →
      ∃ a, (MIrec s m.lower xas valsA xi).globals[x]? = some a := by
    intro xi xi' x b hx hb
    obtain ⟨h1, h2⟩ := hgl xi xi' x hx
    rw [h2] at hb
    by_cases hlt : x < m.base.globals.length
    · rw [ite_eq_left hlt] at hb h1
      exact ⟨_, h1⟩
    · rw [ite_eq_right hlt] at hb
      cases hb
  -- the exports
  have hfE : ∀ x : FuncIdx, m.keepF x.toNat = true → ∀ a,
      (EIrec s m.lower xas valsA).funcs[x.toNat]? = some a →
      ∃ b, (EIrec s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA)).funcs[
          (m.rumeRen.funcIdx x).toNat]? = some b ∧
        (∃ x y, (m.keepF x = true ∧ y = BModule.rank m.keepF x) ∧
          (EIrec s m.lower xas valsA).funcs[x]? = some a ∧
          (EIrec s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA)).funcs[y]? = some b) := by
    intro x hx a ha
    rw [BModule.rumeRen_funcIdx]
    obtain ⟨b, hb, -⟩ := hfex [] [] x.toNat a hx ha
    exact ⟨b, hb, x.toNat, _, ⟨hx, rfl⟩, ha, hb⟩
  have hgE : ∀ x : GlobalIdx, m.keepG x.toNat = true → ∀ a,
      (EIrec s m.lower xas valsA).globals[x.toNat]? = some a →
      ∃ b, (EIrec s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA)).globals[
          (m.rumeRen.globalIdx x).toNat]? = some b := by
    intro x hx a ha
    rw [BModule.rumeRen_globalIdx]
    obtain ⟨-, -, hb⟩ := hgex [] [] x.toNat a hx ha
    exact ⟨_, hb⟩
  have heE : ∀ e ∈ m.lower.exports, (∃ x, e.index = .func x ∧ m.keepF x.toNat = true) ∨
      (∃ x, e.index = .global x ∧ m.keepG x.toNat = true) ∨
      (∃ x, e.index = .memory x) := by
    intro e he
    have hk := hexpk e he
    obtain ⟨name, idx⟩ := e
    cases idx with
    | func x =>
      refine .inl ⟨x, rfl, BModule.keepF_of_root ?_⟩
      simp only [BModule.roots, List.mem_append, List.mem_filterMap]
      exact .inl ⟨_, he, rfl⟩
    | global x =>
      refine .inr (.inl ⟨x, rfl, BModule.keepG_of_root ?_⟩)
      simp only [BModule.roots, List.mem_filterMap]
      exact ⟨_, he, rfl⟩
    | memory x => exact .inr (.inr ⟨x, rfl⟩)
    | _ => simp at hk
  obtain ⟨xiB, hxiB, hR⟩ := mapM_allocExport_rel
    (EA := EIrec s m.lower xas valsA)
    (EB := EIrec s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA))
    m.rumeRen m.keepF m.keepG rfl hfE hgE
    m.lower.exports heE hxi
  -- the functions of the two instances
  have hours : ∀ xi xi' x, m.keepF x = true → m.numImportedFuncs ≤ x →
      x - m.numImportedFuncs < m.funcs.length →
      ∃ fn dA, m.funcs[x - m.numImportedFuncs]? = some fn ∧ dA ∈ allocTypes m.lower.types ∧
        (STrec s m.lower valsA ftA (MIrec s m.lower xas valsA xi)).funcs[
            s.funcs.length + (x - m.numImportedFuncs)]? =
          some ⟨dA, MIrec s m.lower xas valsA xi,
            .wasm (Declaration.Func.mapBody BExpr.lowerList fn)⟩ ∧
        (STrec s (rumeCore m).lower (filterIdxFrom m.keepG 0 valsA)
            (filterIdxFrom m.keepF m.numImportedFuncs ftA)
            (MIrec s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA) xi')).funcs[
            s.funcs.length + cntFrom m.keepF m.numImportedFuncs (x - m.numImportedFuncs)]? =
          some ⟨dA, MIrec s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA) xi',
            .wasm (Declaration.Func.mapBody BExpr.lowerList
              ({ fn with body := m.rumeRen.bexprs fn.body } : BFunc))⟩ := by
    intro xi xi' x hx hle hj
    obtain ⟨fn, hfn⟩ : ∃ fn, m.funcs[x - m.numImportedFuncs]? = some fn :=
      ⟨_, List.getElem?_eq_getElem hj⟩
    have hjA : x - m.numImportedFuncs < ftA.length := by rw [hNF]; exact hj
    obtain ⟨dA, hdA⟩ : ∃ dA, ftA[x - m.numImportedFuncs]? = some dA :=
      ⟨_, List.getElem?_eq_getElem hjA⟩
    have hdA' := mapM_getElem? hft (x - m.numImportedFuncs)
    rw [hdA] at hdA'
    have hfnL : m.lower.funcs[x - m.numImportedFuncs]? =
        some (Declaration.Func.mapBody BExpr.lowerList fn) := by
      simp [BModule.lower, hfn]
    rw [hfnL, Option.bind_some] at hdA'
    have hk' : m.keepF (m.numImportedFuncs + (x - m.numImportedFuncs)) = true := by
      rw [Nat.add_sub_cancel' hle]; exact hx
    refine ⟨fn, dA, hfn, List.mem_of_getElem? hdA'.symm, STrec_hi_funcs hdA hfnL, ?_⟩
    refine STrec_hi_funcs ?_ ?_
    · rw [filterIdxFrom_getElem? m.keepF m.numImportedFuncs ftA _ hk' hjA]
      exact hdA
    · rw [rume_funcs_getElem? m hk' hj, hfn]
      rfl
  have hbody : ∀ x fn, m.keepF x = true → m.numImportedFuncs ≤ x →
      m.funcs[x - m.numImportedFuncs]? = some fn →
      (∀ i ∈ BExpr.lowerList fn.body, instrInProfile i) ∧
      (∀ y ∈ Validation.Expr.freeFuncs (BExpr.lowerList fn.body), m.keepF y = true) ∧
      (∀ y ∈ instrsGlobals (BExpr.lowerList fn.body), m.keepG y = true) := by
    intro x fn hx hle hfn
    obtain ⟨h1, h2⟩ := BModule.funcEdges_kept hx hle hfn
    refine ⟨fun i hi => hpr.code (Declaration.Func.mapBody BExpr.lowerList fn) ?_ i hi, h1, h2⟩
    exact List.mem_map_of_mem (List.mem_of_getElem? hfn)
  have hTB : ((gtys (rumeCore m).lower).zip (filterIdxFrom m.keepG 0 valsA)).map
      (fun p => (⟨p.1, p.2⟩ : GlobalInst)) =
      filterIdxFrom m.keepG 0 (((gtys m.lower).zip valsA).map
        (fun p => (⟨p.1, p.2⟩ : GlobalInst))) := by
    rw [rume_gtys m hnIG, zip_filterIdxFrom _ _ (by simp [gtys, hNG, BModule.lower]),
      filterIdxFrom_map]
  have hTA : ∀ x, x < m.base.globals.length → ∃ g,
      (((gtys m.lower).zip valsA).map (fun p => (⟨p.1, p.2⟩ : GlobalInst)))[x]? = some g := by
    intro x hx
    have hl : (((gtys m.lower).zip valsA).map (fun p => (⟨p.1, p.2⟩ : GlobalInst))).length =
        m.base.globals.length := by simp [gtys, hNG, BModule.lower]
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hglA : ∀ xi x, x < m.base.globals.length →
      (STrec s m.lower valsA ftA (MIrec s m.lower xas valsA xi)).globals[
          s.globals.length + m.base.globals.length + x]? =
        (((gtys m.lower).zip valsA).map (fun p => (⟨p.1, p.2⟩ : GlobalInst)))[x]? := by
    intro xi x _
    exact STrec_hi_globals (N := m.lower) hNG
  have hglB : ∀ xi x, m.keepG x = true →
      (STrec s (rumeCore m).lower (filterIdxFrom m.keepG 0 valsA)
          (filterIdxFrom m.keepF m.numImportedFuncs ftA)
          (MIrec s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA) xi)).globals[
          s.globals.length + cntFrom m.keepG 0 m.base.globals.length + BModule.rank m.keepG x]? =
        (((gtys m.lower).zip valsA).map (fun p => (⟨p.1, p.2⟩ : GlobalInst)))[x]? := by
    intro xi x hx
    rw [← hGB, STrec_hi_globals (N := (rumeCore m).lower) (by rw [hKG, hGB]), hTB,
      filterIdxFrom_getElem?_kept hx]
  have himpF : ∀ (x a : Nat), (ExternAddr.funcs xas)[x]? = some a →
      a < s.funcs.length ∧ NumParamsAt s.funcs a := by
    intro x a hxa
    obtain ⟨d, hd, hext⟩ := forall₂_getElem?_l hxf hxa
    refine ⟨externAddr_func_lt hext, numParams_externAddr hs hext (hIP d ?_)⟩
    rw [hdts]
    exact imports_funcs_mem himports d (List.mem_of_getElem? hd)
  -- the start call
  have hst0 : m.lower.start = m.base.start := rfl
  have hstartF : ∀ (X : SimCtx), (∀ x : FuncIdx, m.keepF x.toNat = true →
      X.KF x.toNat (m.rumeRen.funcIdx x).toNat) →
      CodeR X .ours (startCode m.lower) (startCode (rumeCore m).lower) := by
    intro X hX
    refine CodeR.append (dataCode_rel fun d hd => (hPA.data d hd).2) ?_
    simp only [hst0, rume_lower_start]
    cases h : m.base.start with
    | none => exact .nil
    | some x =>
      refine .cons (.plainO (.call (hX x (BModule.keepF_of_root ?_)))) .nil
      simp [BModule.roots, h]
  have hstartB : ∀ (X : SimCtx), (∀ x : FuncIdx, m.keepF x.toNat = true →
      X.KF (m.rumeRen.funcIdx x).toNat x.toNat) →
      CodeR X .ours (startCode (rumeCore m).lower) (startCode m.lower) := by
    intro X hX
    refine CodeR.append (dataCode_rel fun d hd => (hPA.data d hd).2) ?_
    simp only [hst0, rume_lower_start]
    cases h : m.base.start with
    | none => exact .nil
    | some x =>
      refine .cons (.plainO (.call (hX x (BModule.keepF_of_root ?_)))) .nil
      simp [BModule.roots, h]
  refine ⟨xiB, hvB, hftB, hxiB, ?_, ?_⟩
  · -- source to target
    refine ⟨mkCtx s.funcs.length s.globals.length
      (fun x y => m.keepF x = true ∧ y = BModule.rank m.keepF x)
      (fun x y => m.keepG x = true ∧ y = BModule.rank m.keepG x)
      (MIrec s m.lower xas valsA xiA)
      (MIrec s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA) xiB), ?_, ?_, ?_, rfl, rfl⟩
    · refine mkCtx_wf rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
      · rintro x y a ⟨hx, rfl⟩ ha
        obtain ⟨b, hb, -⟩ := hfex xiA xiB x a hx ha
        exact ⟨b, hb⟩
      · rintro x y a ⟨hx, rfl⟩ ha
        obtain ⟨-, -, hb⟩ := hgex xiA xiB x a hx ha
        exact ⟨_, hb⟩
      · rintro x y y' ⟨-, rfl⟩ ⟨-, rfl⟩
        rfl
      · rintro x x' y ⟨hx, rfl⟩ ⟨hx', h⟩
        exact rank_inj hx hx' h
      · rw [hmiAg]; exact List.nodup_range'
      · rw [hmiBg]; exact List.nodup_range'
    · exact exportsRel_of hR
    · refine ⟨?_, ⟨rfl, rfl, rfl, fun o ho => by simp at ho⟩,
        hstartF _ fun x hx => ⟨hx, BModule.rumeRen_funcIdx m x⟩⟩
      refine ⟨rfl, fun a ha => ?_, fun a ha => ?_, ?_, ?_, STrec_storeF hs hPA hvA, ?_⟩
      · rw [STrec_lo_funcs ha, STrec_lo_funcs ha]
      · rw [STrec_lo_globals ha, STrec_lo_globals ha]
      · rintro a b ⟨x, y, ⟨hx, rfl⟩, ha, hb⟩
        obtain ⟨b', hb', hcase⟩ := hfex xiA xiB x a hx ha
        rw [hb] at hb'
        cases hb'
        rcases hcase with ⟨-, rfl, hxa⟩ | ⟨hle, hj, rfl, rfl⟩
        · exact .inl ⟨(himpF x _ hxa).1, rfl⟩
        · obtain ⟨fn, dA, hfn, -, hA, hB⟩ := hours xiA xiB x hx hle hj
          obtain ⟨hprof, hfree, hglob⟩ := hbody x fn hx hle hfn
          refine .inr ⟨by change s.funcs.length ≤ _; omega, by change s.funcs.length ≤ _; omega,
            _, _, _, _, hA, hB, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
          show IRels _ (BExpr.lowerList fn.body) (BExpr.lowerList (m.rumeRen.bexprs fn.body))
          rw [Ren.lowerList_bexprs]
          refine irels_ren_fwd _ m.rumeRen (fun x => m.keepF x = true) (fun x => m.keepG x = true)
            ?_ ?_ _ hprof hfree hglob
          · intro x hx; exact ⟨hx, BModule.rumeRen_funcIdx m x⟩
          · intro x hx; exact ⟨hx, BModule.rumeRen_globalIdx m x⟩
      · rintro a b ⟨x, y, ⟨hx, rfl⟩, ha, hb⟩
        obtain ⟨hlt, rfl, hb'⟩ := hgex xiA xiB x a hx ha
        rw [hb] at hb'
        cases hb'
        obtain ⟨g, hg⟩ := hTA x hlt
        refine ⟨by change s.globals.length ≤ _; omega, by change s.globals.length ≤ _; omega,
          g, ?_, ?_⟩
        · rw [hglA xiA x hlt, hg]
        · rw [hglB xiB x hx, hg]
      · rintro a b ⟨x, y, ⟨hx, rfl⟩, ha, hb⟩
        obtain ⟨b', hb', hcase⟩ := hfex xiA xiB x a hx ha
        rcases hcase with ⟨-, -, hxa⟩ | ⟨hle, hj, rfl, -⟩
        · obtain ⟨hlt, hip⟩ := himpF x a hxa
          intro fi hfi
          rw [STrec_lo_funcs hlt] at hfi
          exact hip fi hfi
        · obtain ⟨fn, dA, -, hdA, hA, -⟩ := hours xiA xiB x hx hle hj
          intro fi hfi
          rw [hA] at hfi
          cases hfi
          exact hIP dA hdA
  · -- target to source
    refine ⟨mkCtx s.funcs.length s.globals.length
      (fun y x => m.keepF x = true ∧ y = BModule.rank m.keepF x)
      (fun y x => m.keepG x = true ∧ y = BModule.rank m.keepG x)
      (MIrec s (rumeCore m).lower xas (filterIdxFrom m.keepG 0 valsA) xiB)
      (MIrec s m.lower xas valsA xiA), ?_, ?_, ?_, rfl, rfl⟩
    · refine mkCtx_wf rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
      · rintro y x b ⟨hx, rfl⟩ hb
        exact hfex' xiA xiB x b hx hb
      · rintro y x b ⟨hx, rfl⟩ hb
        exact hgex' xiA xiB x b hx hb
      · rintro y x x' ⟨hx, h1⟩ ⟨hx', h2⟩
        exact rank_inj hx hx' (h1.symm.trans h2)
      · rintro y y' x ⟨-, rfl⟩ ⟨-, rfl⟩
        rfl
      · rw [hmiBg]; exact List.nodup_range'
      · rw [hmiAg]; exact List.nodup_range'
    · refine exportsRel_of (xrel_mono ?_ (xrel_flip hR))
      rintro b a ⟨x, y, ⟨hx, rfl⟩, ha, hb⟩
      exact ⟨_, x, ⟨hx, rfl⟩, hb, ha⟩
    · refine ⟨?_, ⟨rfl, rfl, rfl, fun o ho => by simp at ho⟩,
        hstartB _ fun x hx => ⟨hx, BModule.rumeRen_funcIdx m x⟩⟩
      refine ⟨rfl, fun a ha => ?_, fun a ha => ?_, ?_, ?_, STrec_storeF hs hPB hvB',
        ?_⟩
      · rw [STrec_lo_funcs ha, STrec_lo_funcs ha]
      · rw [STrec_lo_globals ha, STrec_lo_globals ha]
      · rintro b a ⟨y, x, ⟨hx, rfl⟩, hb, ha⟩
        obtain ⟨b', hb', hcase⟩ := hfex xiA xiB x a hx ha
        rw [hb] at hb'
        cases hb'
        rcases hcase with ⟨-, rfl, hxa⟩ | ⟨hle, hj, rfl, rfl⟩
        · exact .inl ⟨(himpF x _ hxa).1, rfl⟩
        · obtain ⟨fn, dA, hfn, -, hA, hB⟩ := hours xiA xiB x hx hle hj
          obtain ⟨hprof, hfree, hglob⟩ := hbody x fn hx hle hfn
          refine .inr ⟨by change s.funcs.length ≤ _; omega, by change s.funcs.length ≤ _; omega,
            _, _, _, _, hB, hA, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
          show IRels _ (BExpr.lowerList (m.rumeRen.bexprs fn.body)) (BExpr.lowerList fn.body)
          rw [Ren.lowerList_bexprs]
          refine irels_ren_bwd _ m.rumeRen (fun x => m.keepF x = true) (fun x => m.keepG x = true)
            ?_ ?_ _ hprof hfree hglob
          · intro x hx; exact ⟨hx, BModule.rumeRen_funcIdx m x⟩
          · intro x hx; exact ⟨hx, BModule.rumeRen_globalIdx m x⟩
      · rintro b a ⟨y, x, ⟨hx, rfl⟩, hb, ha⟩
        obtain ⟨hlt, rfl, hb'⟩ := hgex xiA xiB x a hx ha
        rw [hb] at hb'
        cases hb'
        obtain ⟨g, hg⟩ := hTA x hlt
        refine ⟨by change s.globals.length ≤ _; omega, by change s.globals.length ≤ _; omega,
          g, ?_, ?_⟩
        · rw [hglB xiB x hx, hg]
        · rw [hglA xiA x hlt, hg]
      · rintro b a ⟨y, x, ⟨hx, rfl⟩, hb, ha⟩
        obtain ⟨b', hb', hcase⟩ := hfex xiA xiB x a hx ha
        rw [hb] at hb'
        cases hb'
        rcases hcase with ⟨-, rfl, hxa⟩ | ⟨hle, hj, rfl, rfl⟩
        · obtain ⟨hlt, hip⟩ := himpF x _ hxa
          intro fi hfi
          rw [STrec_lo_funcs hlt] at hfi
          exact hip fi hfi
        · obtain ⟨fn, dA, -, hdA, -, hB⟩ := hours xiA xiB x hx hle hj
          intro fi hfi
          rw [hB] at hfi
          cases hfi
          exact hIP dA hdA

theorem mapM_of_forall₂ {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {r : List β}, List.Forall₂ (fun a b => g a = some b) l r → l.mapM g = some r
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h t => by simp [List.mapM_cons, h, mapM_of_forall₂ t]

theorem xas_globals_nil {m : BModule} (hp : m.inProfileBase = true) (hng : m.numImportedGlobals = 0)
    {s : Store H}
    {xas : List ExternAddr} {xtI xtE : List CExternType} (hmod : ModuleOk m.lower ⟨xtI, xtE⟩)
    (hxas : List.Forall₂ (ExternAddrOk s) xas xtI) : ExternAddr.globals xas = [] := by
  have hpr := BModule.inProfileBase_sound hp
  cases hmod with
  | mk htypes himports =>
    obtain ⟨hxtg, -⟩ := imports_ok_funcs himports (hpr.funcOrMemImports hng)
    have h := ExternAddrOk.forall₂_globals hxas
    rw [hxtg] at h
    exact List.forall₂_nil_right_iff.1 h

/-- **A valid profile module instantiates** (its closed-form data exist). -/
theorem src_data {m : BModule} (hp : m.inProfileBase = true) (hng : m.numImportedGlobals = 0)
    {s : Store H}
    {xas : List ExternAddr} {xtI xtE : List CExternType} (hmod : ModuleOk m.lower ⟨xtI, xtE⟩)
    (hxas : List.Forall₂ (ExternAddrOk s) xas xtI) :
    ∃ vals ft xi, gv [] (m.lower.globals.map Global.init) = some vals ∧
      m.lower.funcs.mapM (fun fn => (allocTypes m.lower.types)[fn.type.toNat]?) = some ft ∧
      m.lower.exports.mapM (allocExport? (EIrec s m.lower xas vals)) = some xi := by
  have hpr := BModule.inProfileBase_sound hp
  have hPA := profiled_lower hp hmod
  have himp : ∀ i ∈ m.base.imports, FuncOrMemImport i := hpr.funcOrMemImports hng
  have hxg := xas_globals_nil hp hng hmod hxas
  cases hmod with
  | @mk dts _ jts gts tts fdts rts _ C' C htypes himports hC' hC htags hglobals hmems htables
      hfuncs hdata helems hstart hexports hdisjoint =>
  subst hC' hC
  obtain ⟨hxtg, hxtf⟩ := imports_ok_funcs himports himp
  have hxf := ExternAddrOk.forall₂_funcs hxas
  have hdts : allocTypes m.lower.types = dts := allocTypes_eq htypes
  have hfdts : ∀ d ∈ fdts, d ∈ dts := by
    intro d hd
    obtain ⟨fn, -, hfn⟩ := forall₂_mem_right' hfuncs d hd
    cases hfn with
    | mk hd' _ _ _ => exact List.mem_of_getElem? hd'
  have hdts' : ∀ d ∈ dts, TyOk {} d := TypesOk.tyOk_empty htypes
  have hcl : ∀ d ∈ dts, d.Closed := TypesOk.closed (by simp) htypes
  have hC'ok : ConstCtxOk
      { types := dts, globals := CExternType.globals xtI,
        funcs := CExternType.funcs xtI ++ fdts, refs := funcIdxNonFuncs m.lower } := by
    refine ConstCtxOk.of hdts' hcl rfl (by simp) (imports_globals_ty himports rfl) (by simp)
      (fun d hd => TyOk.of_empty _ (hdts' d ?_)) rfl rfl rfl (by simp)
    rcases List.mem_append.1 hd with hd | hd
    · exact imports_funcs_mem himports d hd
    · exact hfdts d hd
  obtain ⟨vals, hv, hvt⟩ := gv_progress hC'ok hglobals (fun g hg => hPA.pc g hg)
    (globalsOk_num hglobals fun g hg => (hpr.globals g hg).1) [] (by simp [hxtg])
  have hNG : vals.length = m.lower.globals.length := by
    have := gv_length hv
    simpa using this
  have hB : m.lower.funcs.mapM (fun fn => (allocTypes m.lower.types)[fn.type.toNat]?) =
      some fdts := by
    rw [hdts]
    refine mapM_of_forall₂ (List.Forall₂.imp ?_ hfuncs)
    intro fn d hfn
    cases hfn with
    | mk hd' _ _ _ => exact hd'
  suffices hE : ∃ xi, m.lower.exports.mapM (allocExport? (EIrec s m.lower xas vals)) = some xi by
    obtain ⟨xi, hxi⟩ := hE
    exact ⟨vals, fdts, xi, hv, hB, hxi⟩
  · -- the exports resolve
    have hlen : (CExternType.funcs xtI).length = (ExternAddr.funcs xas).length :=
      hxf.length_eq.symm
    have hgl : gts.length = m.lower.globals.length := (GlobalsOk.length_eq hglobals).symm
    have hfl : fdts.length = m.lower.funcs.length := hfuncs.length_eq.symm
    have hexpk : ∀ e ∈ m.base.exports,
        (match e.index with | .func _ | .global _ | .memory _ => true | _ => false) = true := by
      have h := hp
      simp only [BModule.inProfileBase, Bool.and_eq_true, List.all_eq_true] at h
      exact h.2
    have hkind : ∀ e ∈ m.lower.exports, (∃ x, e.index = .func x) ∨ (∃ x, e.index = .global x) ∨ (∃ x, e.index = .memory x) := by
      intro e he
      have hk := hexpk e he
      obtain ⟨name, idx⟩ := e
      cases idx with
      | func x => exact .inl ⟨x, rfl⟩
      | global x => exact .inr (.inl ⟨x, rfl⟩)
      | memory x => exact .inr (.inr ⟨x, rfl⟩)
      | _ => simp at hk
    have hxm := (ExternAddrOk.forall₂_mems hxas).length_eq
    suffices key : ∀ (Cx : Context), Cx.funcs = CExternType.funcs xtI ++ fdts →
        Cx.globals = CExternType.globals xtI ++ gts →
        Cx.mems = CExternType.mems xtI ++ m.lower.memories → ∀ (es : List Export) (xts : List CExternType),
        (∀ e ∈ es, (∃ x, e.index = .func x) ∨ (∃ x, e.index = .global x) ∨ (∃ x, e.index = .memory x)) →
        List.Forall₂ (ExportOk Cx) es xts →
        ∃ xi, es.mapM (allocExport? (EIrec s m.lower xas vals)) = some xi from
      key _ rfl rfl rfl _ _ hkind hexports
    intro Cx hCf hCg hCm es xts hk hes
    induction hes with
    | nil => exact ⟨[], rfl⟩
    | @cons e xt es xts he _ ih =>
      obtain ⟨xi, hxi⟩ := ih (fun e' h' => hk e' (by simp [h']))
      obtain ⟨name, idx⟩ := e
      have hk0 := hk ⟨name, idx⟩ (by simp)
      have hone : ∃ x, allocExport? (EIrec s m.lower xas vals) ⟨name, idx⟩ = some x := by
        change ExternIdxOk _ idx xt at he
        cases he with
        | func hd =>
          have hlt := (List.getElem?_eq_some_iff.1 hd).1
          rw [hCf] at hlt
          simp only [List.length_append] at hlt
          simp only [allocExport?, EIrec, Option.map_map]
          rw [List.getElem?_eq_getElem (by simp [BModule.lower] at hfl ⊢; omega)]
          exact ⟨_, rfl⟩
        | global hg =>
          have hlt := (List.getElem?_eq_some_iff.1 hg).1
          rw [hCg] at hlt
          simp only [List.length_append, hxtg, List.length_nil, Nat.zero_add] at hlt
          simp only [allocExport?, EIrec, Option.map_map]
          rw [List.getElem?_eq_getElem (by simp [hxg, tmpStore, gtys, hNG]; omega)]
          exact ⟨_, rfl⟩
        | mem hm =>
          have hlt := (List.getElem?_eq_some_iff.1 hm).1
          rw [hCm] at hlt
          simp only [List.length_append] at hlt
          simp only [allocExport?, Option.map_map]
          rw [List.getElem?_eq_getElem (by
            simp only [EIrec, List.length_append, List.length_range']
            omega)]
          exact ⟨_, rfl⟩
        | _ => rcases hk0 with ⟨x, hx⟩ | ⟨x, hx⟩ | ⟨x, hx⟩ <;> cases hx
      obtain ⟨x, hx⟩ := hone
      exact ⟨x :: xi, by simp [List.mapM_cons, hx, hxi]⟩

end Main

end Soundness

/-- **RUME is an equivalence** (exports are observed by name; the closed host is
the first instance, a host respecting address injections the general one).

`hty` restricts the function types of the type section to profile value types.
Without it the statement is false (`RUMECounter.rume_sound_original_false`): an
exported `funcref` parameter lets the script pass the address of a function that
exists only in the source store, so the source invocation runs while the target
invocation is ill-typed. -/
theorem rumeCore_sound {m : BModule} (hp : m.inProfileBase = true) (hng : m.numImportedGlobals = 0)
    (h : m.Ok) (hty : ∀ st ∈ m.base.typeDefinitions, ∀ ft : FuncType, st.body = .func ft →
      ∀ t ∈ ft.params ++ ft.results, profileValType t = true)
    (P : Profile) {H : Type} :
    ExportEquiv (· = ·) P (closedHost (H := H)) (rumeCore m).lower m.lower := by
  -- validity of the target with the source's import types
  have hval : ∀ {xtI xtE : List CExternType}, ModuleOk m.lower ⟨xtI, xtE⟩ →
      ∃ xtE', ModuleOk (rumeCore m).lower ⟨xtI, xtE'⟩ := by
    intro xtI xtE hmod
    obtain ⟨⟨xtI', xtE'⟩, hmod'⟩ := rumeCore_valid hp hng h
    have e := RUMESim.moduleOk_xtI (N := m.lower) (N' := (rumeCore m).lower) rfl rfl hmod hmod'
    subst e
    exact ⟨xtE', hmod'⟩
  -- a source instantiation has a related target instantiation
  have fwd : ∀ (s : Store H) (xas : List ExternAddr) (cA : Config H), StoreOk s →
      Instantiate P closedHost s m.lower xas cA →
      ∃ cB, Instantiate P closedHost s (rumeCore m).lower xas cB ∧
        (∃ X : RUMESim.SimCtx, X.WF ∧ RUMESim.ExportsRel X ∧ RUMESim.ConfRel X .ours cA cB ∧
          cA.frame.module = X.MA ∧ cB.frame.module = X.MB) ∧
        (∃ X : RUMESim.SimCtx, X.WF ∧ RUMESim.ExportsRel X ∧ RUMESim.ConfRel X .ours cB cA ∧
          cB.frame.module = X.MA ∧ cA.frame.module = X.MB) := by
    intro s xas cA hs hA
    obtain ⟨xtE, xtI, hmod, hxas⟩ := hA.valid
    have hPA := profiled_lower hp hmod
    have hxg := xas_globals_nil hp hng hmod hxas
    obtain ⟨vals, ft, xi, hvals, hft, hxi, rfl⟩ := RUMESim.inst_closed hPA hxg hA
    obtain ⟨xiB, hvB, hftB, hxiB, h1, h2⟩ := rume_rel hp hng hty hs hmod hxas hvals hft hxi
    obtain ⟨xtE', hmod'⟩ := hval hmod
    exact ⟨_, RUMESim.inst_of_closed (profiled_rume hPA) hxg ⟨xtE', xtI, hmod', hxas⟩ hvB hftB hxiB,
      h1, h2⟩
  -- a target instantiation has a related source instantiation
  have bwd : ∀ (s : Store H) (xas : List ExternAddr) (cB : Config H), StoreOk s →
      Instantiate P closedHost s (rumeCore m).lower xas cB →
      ∃ cA, Instantiate P closedHost s m.lower xas cA ∧
        (∃ X : RUMESim.SimCtx, X.WF ∧ RUMESim.ExportsRel X ∧ RUMESim.ConfRel X .ours cB cA ∧
          cB.frame.module = X.MA ∧ cA.frame.module = X.MB) := by
    intro s xas cB hs hB
    obtain ⟨xtE', xtI, hmod', hxas⟩ := hB.valid
    obtain ⟨⟨xtI₀, xtE⟩, hmod⟩ := h
    have e := RUMESim.moduleOk_xtI (N := m.lower) (N' := (rumeCore m).lower) rfl rfl hmod hmod'
    subst e
    have hPA := profiled_lower hp hmod
    have hxg := xas_globals_nil hp hng hmod hxas
    obtain ⟨vals, ft, xi, hvals, hft, hxi⟩ := src_data hp hng hmod hxas
    have hA := RUMESim.inst_of_closed (P := P) (host := closedHost) hPA hxg ⟨xtE, xtI₀, hmod, hxas⟩
      hvals hft hxi
    obtain ⟨cB', hB', -, h2⟩ := fwd s xas _ hs hA
    have e := RUMESim.inst_det hB hB'
    subst e
    exact ⟨_, hA, h2⟩
  refine ⟨⟨fun s xas c' hs hi => ?_, fun s xas script hs bs hbs => ?_⟩,
    ⟨fun s xas c' hs hi => ?_, fun s xas script hs bs hbs => ?_⟩⟩
  · obtain ⟨cB, hB, -⟩ := fwd s xas c' hs hi
    exact ⟨cB, hB⟩
  · refine ⟨bs, RUMESim.obs_sim (fun c hc => ?_) bs hbs,
      by apply SessionRel.refl; intro _; rfl⟩
    obtain ⟨cA, hA, X, hX, hE, hrel, h1, h2⟩ := bwd s xas c hs hc
    exact ⟨X, cA, hX, hE, hA, hrel, h1, h2⟩
  · obtain ⟨cA, hA, -⟩ := bwd s xas c' hs hi
    exact ⟨cA, hA⟩
  · refine ⟨bs, RUMESim.obs_sim (fun c hc => ?_) bs hbs,
      by apply SessionRel.refl; intro _; rfl⟩
    obtain ⟨cB, hB, ⟨X, hX, hE, hrel, h1, h2⟩, -⟩ := fwd s xas c hs hc
    exact ⟨X, cB, hX, hE, hB, hrel, h1, h2⟩

/-- Number of references to function `f` in bodies, global initialisers and the
start function. -/
def BModule.refs (m : BModule) (f : Nat) : Nat :=
  (m.funcs.flatMap fun fn => Validation.Expr.freeFuncs (BExpr.lowerList fn.body)).count f +
  (m.base.globals.flatMap fun g => Validation.Expr.freeFuncs g.init).count f

/-- Exported or the start function (Binaryen's "used globally"). -/
def BModule.usedGlobally (m : BModule) (f : Nat) : Bool :=
  (m.base.exports.any fun e => match e.index with | .func g => g.toNat == f | _ => false) ||
  m.base.start.any (·.toNat == f)

/-- **Callee deletion is RUME**: an unreferenced defined function that is neither
exported nor the start function is not reachable, hence removed. -/
theorem rume_deletes {m : BModule} {f : Nat} (hdef : m.numImportedFuncs ≤ f)
    (href : m.refs f = 0) (hg : m.usedGlobally f = false) : f ∉ m.reach.funcs := by
  have _ := hdef
  intro hf
  have href': _ ∧ _ := Nat.add_eq_zero_iff.1 href
  rw [List.count_eq_zero, List.count_eq_zero] at href'
  rcases BModule.iterate_funcs_sub m _ f hf with h | h | h
  · simp only [BModule.usedGlobally, Bool.or_eq_false_iff, List.any_eq_false] at hg
    simp only [BModule.roots, List.mem_append, List.mem_filterMap, Option.mem_toList,
      Option.map_eq_some_iff] at h
    rcases h with ⟨e, he, hfe⟩ | ⟨x, hx, rfl⟩
    · have := hg.1 e he
      split at hfe
      · rename_i g hg'
        cases hfe
        simp [hg'] at this
      · cases hfe
    · have := hg.2
      rw [hx] at this
      simp at this
  · exact href'.1 h
  · exact href'.2 h

/-! ## The pipeline's RUME: the identity outside the base profile

`rumeCore` renumbers functions, and a table element holding a function index cannot be
related across that renumbering by the store relation (`StoreRel.rest` requires equal
element contents). So the pipeline's RUME runs `rumeCore` only on modules of the base
profile (no tables, element segments or `call_indirect`) without imported globals
whose function types have numeric parameters and results (`numSigs`: with a `funcref`
parameter `rumeCore_sound` is false, `RUMECounter.rume_sound_original_false`), and
leaves every other module unchanged; its contract needs no table relation. -/

/-- Every function type of the type section has numeric (`profileValType`) parameters
and results. -/
def numSigs (m : BModule) : Bool :=
  m.base.typeDefinitions.all fun st => match st.body with
    | .func ft => (ft.params ++ ft.results).all profileValType
    | _ => true

theorem numSigs_sound {m : BModule} (h : numSigs m = true) :
    ∀ st ∈ m.base.typeDefinitions, ∀ ft : FuncType, st.body = .func ft →
      ∀ t ∈ ft.params ++ ft.results, profileValType t = true := by
  intro st hst ft hft t ht
  have := List.all_eq_true.mp h st hst
  rw [hft] at this
  exact List.all_eq_true.mp this t ht

/-- **RemoveUnusedModuleElements**, as the pipeline runs it: `rumeCore` on the base
profile without imported globals and with numeric function types, the identity
elsewhere. -/
def rume (m : BModule) : BModule :=
  if m.inProfileBase && m.numImportedGlobals == 0 && numSigs m then rumeCore m else m

theorem rume_valid {m : BModule} (h : m.Ok) : (rume m).Ok := by
  unfold rume
  split
  · next hp =>
    have hh : m.inProfileBase = true ∧ (m.numImportedGlobals == 0) = true ∧
        numSigs m = true := by
      simpa only [Bool.and_eq_true, and_assoc] using hp
    exact rumeCore_valid hh.1 (by simpa using hh.2.1) h
  · exact h

/-- **The pipeline's RUME is an equivalence** (closed host). -/
theorem rume_sound {m : BModule} (h : m.Ok) (P : Profile) {H : Type} :
    ExportEquiv (· = ·) P (closedHost (H := H)) (rume m).lower m.lower := by
  unfold rume
  split
  · next hp =>
    have hh : m.inProfileBase = true ∧ (m.numImportedGlobals == 0) = true ∧
        numSigs m = true := by
      simpa only [Bool.and_eq_true, and_assoc] using hp
    exact rumeCore_sound hh.1 (by simpa using hh.2.1) h (numSigs_sound hh.2.2) P
  · exact ⟨ExportRefines.refl (R := fun b b' => b = b') (fun _ => rfl) _,
      ExportRefines.refl (R := fun b b' => b' = b) (fun _ => rfl) _⟩

end Silmaril.Wasm.Binaryen
