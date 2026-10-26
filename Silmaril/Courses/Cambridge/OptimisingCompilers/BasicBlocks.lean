module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.Liveness
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Rotate

/-! # §1 Flowgraphs and basic blocks (notes pp. 4–6; slides pp. 42–46)

"A basic block is a maximal sequence of instructions `n₁, …, nₖ` which have
exactly one predecessor (except possibly for `n₁`) [and] exactly one successor
(except possibly for `nₖ`)" (notes p. 6). Liveness can be stored once per block
and recomputed inside it; the block form of the equations (notes p. 9) applies
the instruction transfer functions from the last instruction back to the first.

A flowgraph is in *normal form* when every temporary is assigned at most once
(notes p. 6: "uses a new temporary variable on each occasion that one is
required").
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers

/-! ### Chains under a relation that is functional in both directions

The rotation theorem for basic blocks is proved for an abstract relation `R`
(instantiated with the flowgraph edge relation `Flowgraph.Chain`) that is
forward-functional (`R a b → R a c → b = c`) and backward-functional
(`R a c → R b c → a = b`). -/

namespace BlockChain

variable {α : Type*} {R : α → α → Prop}

/-- A non-empty duplicate-free `R`-chain. -/
def Seg (R : α → α → Prop) (l : List α) : Prop := l ≠ [] ∧ l.IsChain R ∧ l.Nodup

/-- A maximal (under `<:+:`) `R`-segment. -/
def MaxSeg (R : α → α → Prop) (l : List α) : Prop := Seg R l ∧ ∀ m, Seg R m → l <:+: m → m = l

theorem getLast?_append_of_cons (l : List α) (n : α) (Y : List α) :
    (l ++ n :: Y).getLast? = (n :: Y).getLast? := by
  cases h : (n :: Y).getLast? with
  | none => simp at h
  | some x => rw [List.getLast?_append, h]; rfl

/-- Forward determinism: two chains from the same node agree as far as both go. -/
theorem prefix_or_prefix (hf : ∀ ⦃a b c⦄, R a b → R a c → b = c) :
    ∀ {a : α} {l₁ l₂ : List α}, (a :: l₁).IsChain R → (a :: l₂).IsChain R →
      l₁ <+: l₂ ∨ l₂ <+: l₁
  | _, [], _, _, _ => .inl (List.nil_prefix)
  | _, _ :: _, [], _, _ => .inr (List.nil_prefix)
  | _, b :: l₁, c :: l₂, h₁, h₂ => by
    rw [List.isChain_cons_cons] at h₁ h₂
    obtain rfl := hf h₁.1 h₂.1
    rcases prefix_or_prefix hf h₁.2 h₂.2 with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact .inl ⟨t, rfl⟩
    · exact .inr ⟨t, rfl⟩

theorem seg_reverse {l : List α} (h : Seg R l) : Seg (fun a b => R b a) l.reverse :=
  ⟨by simpa using h.1, List.isChain_reverse.2 h.2.1, List.nodup_reverse.2 h.2.2⟩

theorem max_reverse {l : List α} (h : MaxSeg R l) : MaxSeg (fun a b => R b a) l.reverse := by
  refine ⟨seg_reverse h.1, fun m hm hinf => ?_⟩
  have hm' : Seg R m.reverse := by
    simpa using (seg_reverse hm : Seg (fun a b => R a b) m.reverse)
  have := h.2 m.reverse hm' (by simpa using (List.reverse_infix.2 hinf))
  rw [← this, List.reverse_reverse]

/-- A maximal segment whose last node has an `R`-successor is closed: its last
node steps to its head. -/
theorem closed_of_succ (hb : ∀ ⦃a b c⦄, R a c → R b c → a = b) {l : List α}
    (hl : MaxSeg R l) {x y : α} (hx : x ∈ l.getLast?) (hxy : R x y) : ∀ z ∈ l.head?, R x z := by
  by_cases hy : y ∈ l
  · obtain ⟨P, Q, rfl⟩ := List.append_of_mem hy
    rcases P.eq_nil_or_concat with rfl | ⟨P', p, rfl⟩
    · intro z hz
      simp only [List.nil_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hz
      exact hz ▸ hxy
    · exfalso
      have hch := (List.isChain_split.1 hl.1.2.1).1
      have hpy : R p y := by
        simp only [List.concat_eq_append, List.append_assoc, List.singleton_append] at hch
        exact (List.isChain_append_cons_cons.1 hch).2.1
      have hxQ : x ∈ y :: Q := by
        rw [getLast?_append_of_cons] at hx
        exact List.mem_of_getLast? hx
      have hnd := hl.1.2.2
      simp only [List.concat_eq_append] at hnd
      rw [List.nodup_append] at hnd
      exact hnd.2.2 p (by simp) x hxQ (hb hpy hxy)
  · exfalso
    have hseg : Seg R (l ++ [y]) := by
      refine ⟨by simp, hl.1.2.1.append (.singleton y) ?_, ?_⟩
      · intro a ha b hb'
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb'
        rw [Option.mem_unique ha hx, ← hb']
        exact hxy
      · rw [List.nodup_append_comm]
        exact List.nodup_cons.2 ⟨hy, hl.1.2.2⟩
    have := congrArg List.length (hl.2 _ hseg ⟨[], [y], by simp⟩)
    simp at this

/-- Dually, a maximal segment whose head has an `R`-predecessor is closed. -/
theorem closed_of_pred (hf : ∀ ⦃a b c⦄, R a b → R a c → b = c) {l : List α}
    (hl : MaxSeg R l) {y z : α} (hz : z ∈ l.head?) (hyz : R y z) : ∀ x ∈ l.getLast?, R x z := by
  intro x hx
  exact closed_of_succ (R := fun a b => R b a) (fun _ _ _ h₁ h₂ => hf h₁ h₂) (max_reverse hl)
    (by simpa using hz) hyz x (by simpa using hx)

/-- Rotating a closed chain at `n` gives a chain from `n` that steps back to `n`. -/
theorem rotate_closed {X Y : List α} {n : α} (h : (X ++ n :: Y).IsChain R)
    (hc : ∀ x ∈ (X ++ n :: Y).getLast?, ∀ z ∈ (X ++ n :: Y).head?, R x z) :
    (n :: (Y ++ X)).IsChain R ∧ ∀ x ∈ (n :: (Y ++ X)).getLast?, R x n := by
  have hnY := (List.isChain_split.1 h).2
  rcases X with _ | ⟨a, X'⟩
  · simp only [List.nil_append, List.append_nil] at h hc ⊢
    exact ⟨h, fun x hx => hc x hx n rfl⟩
  · have hX := (List.isChain_split.1 h).1
    refine ⟨?_, ?_⟩
    · show ((n :: Y) ++ (a :: X')).IsChain R
      refine List.IsChain.append hnY (List.isChain_append.1 hX).1 fun x hx z hz => ?_
      refine hc x ?_ z hz
      rw [getLast?_append_of_cons]
      exact hx
    · intro x hx
      refine (List.isChain_append.1 hX).2.2 x ?_ n rfl
      have : (n :: (Y ++ a :: X')).getLast? = (a :: X').getLast? := by
        rw [← List.cons_append, getLast?_append_of_cons]
      rwa [this] at hx

/-- Two closed duplicate-free chains from the same node coincide. -/
theorem closed_eq_of_prefix (hf : ∀ ⦃a b c⦄, R a b → R a c → b = c) {n : α} {l₁ l₂ : List α}
    (h₂ : (n :: l₂).IsChain R) (c₁ : ∀ x ∈ (n :: l₁).getLast?, R x n)
    (nd₂ : (n :: l₂).Nodup) (hp : l₁ <+: l₂) : l₁ = l₂ := by
  obtain ⟨t, rfl⟩ := hp
  rcases t with _ | ⟨q, t⟩
  · simp
  · exfalso
    have hch : ((n :: l₁) ++ (q :: t)).IsChain R := h₂
    cases hx : (n :: l₁).getLast? with
    | none => simp at hx
    | some x =>
      have hq := hf ((List.isChain_append.1 hch).2.2 x hx q rfl) (c₁ x hx)
      subst hq
      exact (List.nodup_cons.1 nd₂).1 (by simp)

theorem closed_eq (hf : ∀ ⦃a b c⦄, R a b → R a c → b = c) {n : α} {l₁ l₂ : List α}
    (h₁ : (n :: l₁).IsChain R) (h₂ : (n :: l₂).IsChain R)
    (c₁ : ∀ x ∈ (n :: l₁).getLast?, R x n) (c₂ : ∀ x ∈ (n :: l₂).getLast?, R x n)
    (nd₁ : (n :: l₁).Nodup) (nd₂ : (n :: l₂).Nodup) : l₁ = l₂ := by
  rcases prefix_or_prefix hf h₁ h₂ with hp | hp
  · exact closed_eq_of_prefix hf h₂ c₁ nd₂ hp
  · exact (closed_eq_of_prefix hf h₁ c₂ nd₁ hp).symm

/-- The nested/crossed case analysis, assuming the forward part of `ns` is a
prefix of that of `ms`. -/
theorem isRotated_of_prefix (hf : ∀ ⦃a b c⦄, R a b → R a c → b = c)
    (hb : ∀ ⦃a b c⦄, R a c → R b c → a = b) {A B C D : List α} {n : α}
    (hn : MaxSeg R (A ++ n :: B)) (hm : MaxSeg R (C ++ n :: D)) (hBD : B <+: D) :
    (A ++ n :: B) ~r (C ++ n :: D) := by
  obtain ⟨D0, rfl⟩ := hBD
  have hbA : (n :: A.reverse).IsChain (fun a b => R b a) := by
    simpa using List.isChain_reverse.2 (List.isChain_split.1 hn.1.2.1).1
  have hbC : (n :: C.reverse).IsChain (fun a b => R b a) := by
    simpa using List.isChain_reverse.2 (List.isChain_split.1 hm.1.2.1).1
  have hsub : A <:+ C ∨ C <:+ A := by
    rcases prefix_or_prefix (R := fun a b => R b a) (fun _ _ _ h₁ h₂ => hb h₁ h₂) hbA hbC with h | h
    · exact .inl (List.reverse_prefix.1 h)
    · exact .inr (List.reverse_prefix.1 h)
  rcases hsub with ⟨C0, rfl⟩ | ⟨A0, rfl⟩
  · rw [hn.2 _ hm.1 ⟨C0, D0, by simp⟩]
  rcases A0.eq_nil_or_concat with rfl | ⟨A1, p, rfl⟩
  · rw [hn.2 _ hm.1 ⟨[], D0, by simp⟩]
  rcases D0 with _ | ⟨q, D1⟩
  · rw [hm.2 _ hn.1 ⟨A1.concat p, [], by simp⟩]
  simp only [List.concat_eq_append] at hn ⊢
  -- `ns` is closed: its last node steps to `q`.
  have hcn : ∀ x ∈ (A1 ++ [p] ++ C ++ n :: B).getLast?,
      ∀ z ∈ (A1 ++ [p] ++ C ++ n :: B).head?, R x z := by
    intro x hx
    have hxq : R x q := by
      have hch' : ((C ++ n :: B) ++ (q :: D1)).IsChain R := by simpa using hm.1.2.1
      refine (List.isChain_append.1 hch').2.2 x ?_ q rfl
      rw [getLast?_append_of_cons] at hx ⊢
      exact hx
    exact closed_of_succ hb hn hx hxq
  -- `ms` is closed: `p` steps to its head.
  have hcm : ∀ x ∈ (C ++ n :: (B ++ q :: D1)).getLast?,
      ∀ z ∈ (C ++ n :: (B ++ q :: D1)).head?, R x z := by
    intro x hx z hz
    have hch' : ((A1 ++ [p]) ++ (C ++ n :: B)).IsChain R := by simpa using hn.1.2.1
    have hpz : R p z := by
      refine (List.isChain_append.1 hch').2.2 p (by simp) z ?_
      rcases C with _ | ⟨c, C'⟩ <;> simpa using hz
    exact closed_of_pred hf hm hz hpz x hx
  have r₁ := rotate_closed (X := A1 ++ [p] ++ C) (by simpa using hn.1.2.1) (by simpa using hcn)
  have r₂ := rotate_closed hm.1.2.1 hcm
  have nd₁ : (n :: (B ++ (A1 ++ [p] ++ C))).Nodup := by
    have := List.nodup_append_comm.1 hn.1.2.2
    simpa using this
  have nd₂ : (n :: ((B ++ q :: D1) ++ C)).Nodup := by
    have := List.nodup_append_comm.1 hm.1.2.2
    simpa using this
  have heq := closed_eq hf r₁.1 r₂.1 r₁.2 r₂.2 nd₁ nd₂
  have e₁ : (A1 ++ [p] ++ C ++ n :: B) ~r (n :: (B ++ (A1 ++ [p] ++ C))) := by
    have := List.isRotated_append (l := A1 ++ [p] ++ C) (l' := n :: B)
    simpa using this
  have e₂ : (C ++ n :: (B ++ q :: D1)) ~r (n :: ((B ++ q :: D1) ++ C)) := by
    have := List.isRotated_append (l := C) (l' := n :: (B ++ q :: D1))
    simpa using this
  rw [heq] at e₁
  exact e₁.trans e₂.symm

/-- Maximal segments sharing a node are rotations of each other. -/
theorem isRotated_of_mem (hf : ∀ ⦃a b c⦄, R a b → R a c → b = c)
    (hb : ∀ ⦃a b c⦄, R a c → R b c → a = b) {ns ms : List α} (hn : MaxSeg R ns)
    (hm : MaxSeg R ms) {n : α} (h₁ : n ∈ ns) (h₂ : n ∈ ms) : ns ~r ms := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem h₁
  obtain ⟨C, D, rfl⟩ := List.append_of_mem h₂
  rcases prefix_or_prefix hf (List.isChain_split.1 hn.1.2.1).2
      (List.isChain_split.1 hm.1.2.1).2 with h | h
  · exact isRotated_of_prefix hf hb hn hm h
  · exact (isRotated_of_prefix hf hb hm hn h).symm

end BlockChain

namespace Flowgraph

variable {V ι : Type*} (G : Flowgraph V ι)

/-- `ns` is a path of the flowgraph: each node is followed by a successor. -/
def IsPath : List ι → Prop
  | [] | [_] => True
  | n :: m :: ns => m ∈ G.succ n ∧ IsPath (m :: ns)

/-- The sequence `ns` satisfies the basic-block conditions of notes p. 6: it is a
non-empty path whose interior edges are the only edges out of and into their
endpoints. -/
def IsBlockSegment (ns : List ι) : Prop :=
  ns ≠ [] ∧ G.IsPath ns ∧ ns.Nodup ∧
    ∀ i (h : i + 1 < ns.length),
      G.succ (ns.get ⟨i, by omega⟩) = {ns.get ⟨i + 1, h⟩} ∧
        G.pred (ns.get ⟨i + 1, h⟩) = {ns.get ⟨i, by omega⟩}

/-- A basic block: a block segment that cannot be extended at either end
(notes p. 6, "maximal"). -/
def IsBasicBlock (ns : List ι) : Prop :=
  G.IsBlockSegment ns ∧ ∀ ms, G.IsBlockSegment ms → ns <:+: ms → ms = ns

/-- Every node lies in some basic block. -/
theorem exists_basicBlock_mem [Finite ι] (n : ι) : ∃ ns, G.IsBasicBlock ns ∧ n ∈ ns := by
  classical
  have := Fintype.ofFinite ι
  let P : ℕ → Prop := fun k => ∃ ms, G.IsBlockSegment ms ∧ n ∈ ms ∧ ms.length = k
  have hP1 : P 1 := ⟨[n], ⟨List.cons_ne_nil _ _, trivial, List.nodup_singleton _,
    fun i h => absurd h (by simp only [List.length_singleton]; omega)⟩,
    List.mem_singleton_self _, rfl⟩
  have hle : ∀ k, P k → k ≤ Fintype.card ι := by
    rintro k ⟨ms, hms, -, rfl⟩
    exact hms.2.2.1.length_le_card
  obtain ⟨ms, hms, hn, hlen⟩ := Nat.findGreatest_spec (hle 1 hP1) hP1
  refine ⟨ms, ⟨hms, fun ms' hms' hinf => ?_⟩, hn⟩
  have hP' : P ms'.length := ⟨ms', hms', hinf.subset hn, rfl⟩
  have h1 : ms'.length ≤ ms.length := (Nat.le_findGreatest (hle _ hP') hP').trans hlen.ge
  exact (hinf.eq_of_length (le_antisymm hinf.length_le h1)).symm

/-- A block segment through every node is a basic block. -/
theorem isBasicBlock_of_length [Fintype ι] {ns : List ι} (h : G.IsBlockSegment ns)
    (hlen : ns.length = Fintype.card ι) : G.IsBasicBlock ns :=
  ⟨h, fun _ hms hinf =>
    (hinf.eq_of_length (le_antisymm hinf.length_le (hms.2.2.1.length_le_card.trans hlen.ge))).symm⟩

/-- The edge relation inside a basic block: `a`'s only successor is `b` and
`b`'s only predecessor is `a`. -/
def Chain (a b : ι) : Prop := G.succ a = {b} ∧ G.pred b = {a}

theorem isPath_of_isChain : ∀ {ns : List ι}, ns.IsChain G.Chain → G.IsPath ns
  | [], _ | [_], _ => trivial
  | _ :: _ :: _, h => by
    rw [List.isChain_cons_cons] at h
    exact ⟨by rw [h.1.1]; rfl, isPath_of_isChain h.2⟩

/-- `IsBlockSegment` is a non-empty duplicate-free `Chain`-chain. -/
theorem isBlockSegment_iff {ns : List ι} :
    G.IsBlockSegment ns ↔ BlockChain.Seg G.Chain ns := by
  simp only [IsBlockSegment, BlockChain.Seg, List.isChain_iff_getElem, List.get_eq_getElem]
  constructor
  · rintro ⟨h0, -, h2, h3⟩
    exact ⟨h0, h3, h2⟩
  · rintro ⟨h0, h3, h2⟩
    exact ⟨h0, G.isPath_of_isChain (List.isChain_iff_getElem.2 h3), h2, h3⟩

theorem isBasicBlock_iff {ns : List ι} : G.IsBasicBlock ns ↔ BlockChain.MaxSeg G.Chain ns := by
  simp only [IsBasicBlock, BlockChain.MaxSeg, isBlockSegment_iff]

theorem chain_functional {a b c : ι} (h₁ : G.Chain a b) (h₂ : G.Chain a c) : b = c :=
  Set.singleton_eq_singleton_iff.1 (h₁.1.symm.trans h₂.1)

theorem chain_injective {a b c : ι} (h₁ : G.Chain a c) (h₂ : G.Chain b c) : a = b :=
  Set.singleton_eq_singleton_iff.1 (h₁.2.symm.trans h₂.2)

/-- Basic blocks sharing a node are rotations of each other, so the blocks
partition the nodes. A rotation is all one can say: on a cycle every rotation
is maximal (`exists_basicBlock_rotation_ne`). -/
theorem basicBlock_isRotated {ns ms : List ι} (hn : G.IsBasicBlock ns) (hm : G.IsBasicBlock ms)
    {n : ι} (h₁ : n ∈ ns) (h₂ : n ∈ ms) : ns ~r ms :=
  BlockChain.isRotated_of_mem (R := G.Chain) (fun _ _ _ => G.chain_functional)
    (fun _ _ _ => G.chain_injective) (G.isBasicBlock_iff.1 hn)
    (G.isBasicBlock_iff.1 hm) h₁ h₂

/-- On the two-node cycle `0 → 1 → 0`, both `[0, 1]` and `[1, 0]` are basic
blocks. -/
theorem exists_basicBlock_rotation_ne :
    ∃ (G : Flowgraph Unit (Fin 2)) (ns ms : List (Fin 2)),
      G.IsBasicBlock ns ∧ G.IsBasicBlock ms ∧ 0 ∈ ns ∧ 0 ∈ ms ∧ ns ≠ ms := by
  let G : Flowgraph Unit (Fin 2) := ⟨0, ![.nop 1, .nop 0]⟩
  have hseg : ∀ a b : Fin 2, a ≠ b → G.succ a = {b} → G.pred b = {a} → G.IsBlockSegment [a, b] := by
    intro a b hab hs hp
    refine ⟨List.cons_ne_nil _ _, ⟨by rw [hs]; exact Set.mem_singleton b, trivial⟩, ?_, fun i h => ?_⟩
    · simpa using hab
    · have hi : i = 0 := by simp only [List.length_cons, List.length_nil] at h; omega
      subst hi
      exact ⟨hs, hp⟩
  have h01 : G.succ 0 = {1} := by ext m; simp [G, succ, Instr.succs]
  have h10 : G.succ 1 = {0} := by ext m; simp [G, succ, Instr.succs]
  have p1 : G.pred 1 = {0} := by ext m; fin_cases m <;> simp [G, pred, Instr.succs]
  have p0 : G.pred 0 = {1} := by ext m; fin_cases m <;> simp [G, pred, Instr.succs]
  refine ⟨G, [0, 1], [1, 0], G.isBasicBlock_of_length (hseg 0 1 (by decide) h01 p1) rfl,
    G.isBasicBlock_of_length (hseg 1 0 (by decide) h10 p0) rfl, by simp, by simp, by decide⟩

variable [DecidableEq V]

/-- The block transfer function of notes p. 9:
`((S \ def(iₖ) ∪ ref(iₖ)) ⋯ \ def(i₁)) ∪ ref(i₁)`. -/
def blockTransfer (ns : List ι) (S : Set V) : Set V :=
  ns.foldr (fun n T => G.liveTransfer n T) S

/-- At a node with a single successor `b`, `live(a)` is the transfer of `live(b)`. -/
theorem live_eq_liveTransfer_of_succ {a b : ι} (h : G.succ a = {b}) :
    G.live a = G.liveTransfer a (G.live b) := by
  refine ((Silmaril.Semantics.Dataflow.Equations.isSolution_iff _ _).1
    G.liveEquations.least_isSolution a).trans ?_
  show G.liveTransfer a (⨆ m ∈ G.succ a, G.live m) = _
  rw [h, iSup_singleton]

theorem live_eq_blockTransfer_aux : ∀ (l : List ι) (a m : ι),
    (∀ i (h : i + 1 < (a :: l).length),
      G.succ ((a :: l).get ⟨i, by omega⟩) = {(a :: l).get ⟨i + 1, h⟩}) →
    (a :: l).getLast? = some m → G.live a = G.blockTransfer (a :: l).dropLast (G.live m)
  | [], a, m, _, hm => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hm
    subst hm
    rfl
  | b :: l, a, m, h, hm => by
    have hab : G.succ a = {b} := h 0 (by simp)
    have ih := live_eq_blockTransfer_aux l b m (fun i hi => h (i + 1) (by simp at hi ⊢; omega))
      (by simpa using hm)
    rw [G.live_eq_liveTransfer_of_succ hab, ih]
    rfl

/-- Block-level liveness agrees with node-level liveness: the live set at the
head of a basic block is the transfer, over every node of the block except the
last, of the live-in set `G.live m` of its last node `m` (notes p. 9). -/
theorem live_head_eq_blockTransfer {ns : List ι} (hns : G.IsBasicBlock ns) (n : ι)
    (hn : ns.head? = some n) (m : ι) (hm : ns.getLast? = some m) :
    G.live n = G.blockTransfer ns.dropLast (G.live m) := by
  cases ns with
  | nil => simp at hn
  | cons a l =>
  simp only [List.head?_cons, Option.some.injEq] at hn
  subst hn
  exact G.live_eq_blockTransfer_aux l a m (fun i h => (hns.1.2.2.2 i h).1) hm

/-- Normal form (notes p. 6): each variable in `temps` is defined at most once. -/
def IsNormalForm (temps : Set V) : Prop :=
  ∀ t ∈ temps, ∀ n m, t ∈ (G.code n).defs → t ∈ (G.code m).defs → n = m

end Flowgraph

end Silmaril.Courses.Cambridge.OptimisingCompilers
