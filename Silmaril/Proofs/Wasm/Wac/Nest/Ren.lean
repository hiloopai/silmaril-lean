module

public import Silmaril.Wasm.Wac.NestRun.Defs
public import Silmaril.Proofs.Wasm.Wac.Graph
public import Silmaril.Proofs.Wasm.Wac.Seq

/-!
# Nesting = inlining: the renaming built by inlining

* `src_ren`, `src_inner`: the references of the renamed and of the inlined instances;
* `inlineNode_ne`, `inlineNode_eq`: one step of `Graph.inline`;
* `renOk_nil`, `renOk_step_ne`, `renOk_step_eq`: the renaming sends exports of instances
  of `g₂` to exports of instances of the inlined graph, of the same types (`RenOk`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.NestProof

open Silmaril.Wasm.Component

variable {M : Type}

/-! ## References -/

theorem src_mapArgs (pkg : Nat) (args : List (String × Src)) (f : Src → Src) (x : String) :
    (⟨pkg, args.map fun a => (a.1, f a.2)⟩ : Inst).src x = ((args.lookup x).map f).getD (.imp x) := by
  unfold Inst.src
  rw [lookup_map_snd]

/-- The references of a renamed instance are renamed. -/
theorem src_ren (ren : List (String → Src)) (n : Inst) (x : String) :
    (⟨n.pkg, n.args.map fun a => (a.1, renSrc ren a.2)⟩ : Inst).src x = renSrc ren (n.src x) := by
  rw [src_mapArgs]
  unfold Inst.src
  cases n.args.lookup x <;> rfl

/-- The references of an inlined instance. -/
theorem src_inner (S : Nat → PkgSig) (n' : Inst) (base : Nat) (m : Inst) {x : String}
    (hx : x ∈ names (S m.pkg).imports) :
    (⟨m.pkg, (m.explicate S).args.map fun a => (a.1, innerSrc n' base a.2)⟩ :
      Inst).src x = innerSrc n' base (m.src x) := by
  rw [src_mapArgs]
  have h : (m.explicate S).args.lookup x = some (m.src x) :=
    lookup_map_self (fun y => m.src y) _ x hx
  rw [h]
  rfl

/-! ## The renaming -/

theorem renSrc_append_lt (ren : List (String → Src)) (f : String → Src) {j : Nat}
    (h : j < ren.length) (q : String) : renSrc (ren ++ [f]) (.out j q) = renSrc ren (.out j q) := by
  simp only [renSrc, List.getElem?_append_left h]

theorem renSrc_append_self (ren : List (String → Src)) (f : String → Src) (q : String) :
    renSrc (ren ++ [f]) (.out ren.length q) = f q := by
  simp [renSrc]

/-- The node of a non-`k0` instance. -/
def renInst (ren : List (String → Src)) (n : Inst) : Inst :=
  ⟨n.pkg, n.args.map fun a => (a.1, renSrc ren a.2)⟩

/-- The nodes inlined for an instance of `k0`. -/
def innerNodes (S : Nat → PkgSig) (g₁ : Graph) (n' : Inst) (base : Nat) : List Inst :=
  (g₁.explicate S).nodes.map fun m => ⟨m.pkg, m.args.map fun a => (a.1, innerSrc n' base a.2)⟩

/-- The renaming of the exports of an inlined instance. -/
def innerRen (g₁ : Graph) (n' : Inst) (base : Nat) : String → Src := fun q =>
  match g₁.exports.lookup q with
  | some s => innerSrc n' base s
  | none => .imp q

/-- One step of inlining at a non-`k0` instance. -/
def stepNe (acc : IAcc) (n : Inst) : IAcc where
  nodes := acc.nodes ++ [renInst acc.ren n]
  ren := acc.ren ++ [fun q => .out acc.nodes.length q]

/-- One step of inlining at an instance of `k0`. -/
def stepEq (S : Nat → PkgSig) (g₁ : Graph) (acc : IAcc) (n : Inst) : IAcc where
  nodes := acc.nodes ++ innerNodes S g₁ (renInst acc.ren n) acc.nodes.length
  ren := acc.ren ++ [innerRen g₁ (renInst acc.ren n) acc.nodes.length]

theorem inlineNode_ne (S : Nat → PkgSig) {k0 : Nat} (g₁ : Graph) (acc : IAcc) {n : Inst}
    (h : n.pkg ≠ k0) : inlineNode S k0 g₁ acc n = stepNe acc n := by
  unfold inlineNode
  rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
  rfl

theorem inlineNode_eq (S : Nat → PkgSig) {k0 : Nat} (g₁ : Graph) (acc : IAcc) {n : Inst}
    (h : n.pkg = k0) : inlineNode S k0 g₁ acc n = stepEq S g₁ acc n := by
  unfold inlineNode
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  rfl

/-! ## `RenOk` -/

theorem renOk_nil (S S' : Nat → PkgSig) (g₂ : Graph) : RenOk S S' g₂ {} 0 :=
  ⟨rfl, fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩

theorem getElem?_append_of_some {α : Type} {l : List α} {t : Nat} {a : α} (h : l[t]? = some a)
    (l' : List α) : (l ++ l')[t]? = some a := by
  have ht : t < l.length := (List.getElem?_eq_some_iff.1 h).1
  rw [List.getElem?_append_left ht, h]

/-- The earlier exports keep their renaming when the accumulator grows. -/
theorem renOk_old {S S' : Nat → PkgSig} {g₂ : Graph} {acc : IAcc} {j : Nat}
    (hr : RenOk S S' g₂ acc j) (Δ : List Inst) (f : String → Src) :
    ∀ j' n q, g₂.nodes[j']? = some n → j' < j → q ∈ names (S' n.pkg).exports →
      ∃ t q' m, renSrc (acc.ren ++ [f]) (.out j' q) = .out t q' ∧ (acc.nodes ++ Δ)[t]? = some m ∧
        q' ∈ names (S m.pkg).exports ∧ (S m.pkg).exports.lookup q' = (S' n.pkg).exports.lookup q := by
  intro j' n q hn hj hq
  obtain ⟨t, q', m, hs, hm, hq', hl⟩ := hr.2 j' n q hn hj hq
  have hj' : j' < acc.ren.length := hr.1 ▸ hj
  exact ⟨t, q', m, by rw [renSrc_append_lt _ _ hj', hs], getElem?_append_of_some hm Δ, hq', hl⟩

theorem lt_or_eq_of_lt_succ' {a b : Nat} (h : a < b + 1) : a < b ∨ a = b := by omega

theorem renOk_step_ne {S S' : Nat → PkgSig} {g₂ : Graph} {acc : IAcc} {j : Nat} {n : Inst}
    (hr : RenOk S S' g₂ acc j) (hn : g₂.nodes[j]? = some n) (hS : S' n.pkg = S n.pkg) :
    RenOk S S' g₂ (stepNe acc n) (j + 1) := by
  refine ⟨by simp [stepNe, hr.1], fun j' n₀ q hn₀ hj hq => ?_⟩
  rcases lt_or_eq_of_lt_succ' hj with hj | hj
  · exact renOk_old hr _ _ j' n₀ q hn₀ hj hq
  · have hnn : n₀ = n := Option.some.inj (hn₀.symm.trans (hj ▸ hn))
    have hself : renSrc (stepNe acc n).ren (.out j' q) = .out acc.nodes.length q := by
      rw [hj, ← hr.1]
      exact renSrc_append_self _ _ q
    refine ⟨acc.nodes.length, q, renInst acc.ren n, hself, by simp [stepNe], ?_, ?_⟩
    · show q ∈ names (S n.pkg).exports
      rw [← hS, ← hnn]
      exact hq
    · show (S n.pkg).exports.lookup q = (S' n₀.pkg).exports.lookup q
      rw [hnn, hS]

theorem mem_of_lookup {β : Type} : ∀ {l : List (String × β)} {q : String} {b : β},
    l.lookup q = some b → (q, b) ∈ l
  | [], _, _, h => by simp at h
  | (k, v) :: l, q, b, h => by
    by_cases hq : q = k
    · have hb : v = b := by simpa [List.lookup, hq] using h
      rw [hq, hb]
      exact List.mem_cons_self
    · have hb : (q == k) = false := by simpa using hq
      have h' : l.lookup q = some b := by simpa [List.lookup, hb] using h
      exact List.mem_cons_of_mem _ (mem_of_lookup h')

theorem lookup_of_mem {β : Type} : ∀ {l : List (String × β)} {q : String},
    q ∈ l.map Prod.fst → ∃ b, l.lookup q = some b
  | [], _, h => by simp at h
  | (k, v) :: l, q, h => by
    by_cases hq : q = k
    · exact ⟨v, by simp [List.lookup, hq]⟩
    · have hb : (q == k) = false := by simpa using hq
      have h' : q ∈ l.map Prod.fst := by simpa [hq] using h
      obtain ⟨b, hb'⟩ := lookup_of_mem h'
      exact ⟨b, by simp [List.lookup, hb, hb']⟩

/-- The interface of the composition `g₁` as a package. -/
theorem exports_sigOf_toComp (P : Nat → Comp M) (g₁ : Graph) :
    (sigOf (g₁.toComp P)).exports =
      g₁.exports.map fun p => (p.1, g₁.tyOf (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k)) p.2) := by
  simp [sigOf, Graph.toComp, Graph.build, Graph.mkExports]

theorem names_exports_toComp (P : Nat → Comp M) (g₁ : Graph) :
    names (sigOf (g₁.toComp P)).exports = g₁.exports.map Prod.fst := by
  simp [exports_sigOf_toComp, names]

theorem innerNodes_get (S : Nat → PkgSig) (g₁ : Graph) (n' : Inst) (base : Nat) {i : Nat}
    {m : Inst} (hm : g₁.nodes[i]? = some m) :
    (innerNodes S g₁ n' base)[i]? = some ⟨m.pkg, (m.explicate S).args.map fun a =>
      (a.1, innerSrc n' base a.2)⟩ := by
  simp [innerNodes, Graph.explicate, hm]
  rfl

/-- An export of an instance of `k0` is renamed to the inlined instance of its source. -/
theorem innerRen_out (P : Nat → Comp M) {g₁ : Graph} (n' : Inst) (base : Nat)
    (wf₁ : g₁.WF fun k => sigOf (P k)) (out₁ : g₁.ExportsOut) {q : String}
    (hq : q ∈ names (sigOf (g₁.toComp P)).exports) :
    ∃ s i q' m, g₁.exports.lookup q = some s ∧ s = .out i q' ∧ g₁.nodes[i]? = some m ∧
      q' ∈ names (sigOf (P m.pkg)).exports ∧ innerRen g₁ n' base q = .out (base + i) q' := by
  obtain ⟨s, hs⟩ := lookup_of_mem (by rwa [names_exports_toComp] at hq)
  have hmem : (q, s) ∈ g₁.exports := mem_of_lookup hs
  obtain ⟨i, q', hiq⟩ := out₁ _ hmem
  have hres := wf₁.2 _ hmem
  have hiq' : s = .out i q' := hiq
  have hres' : g₁.Resolves (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k))
      g₁.nodes.length (.out i q') := hiq ▸ hres
  obtain ⟨m, hm, _, hq'⟩ := hres'
  exact ⟨s, i, q', m, hs, hiq', hm, hq', by simp [innerRen, hs, hiq', innerSrc]⟩

/-- The renaming of an export of the new instance of `k0`. -/
theorem renOk_new_k0 (P : Nat → Comp M) {k0 : Nat} {g₁ : Graph} {acc : IAcc}
    {n : Inst} (wf₁ : g₁.WF fun k => sigOf (P k)) (out₁ : g₁.ExportsOut)
    (hk : n.pkg = k0) {q : String} (hq : q ∈ names (sigOf (nestPkgs P k0 g₁ n.pkg)).exports) :
    ∃ t q' m, renSrc (stepEq (fun k => sigOf (P k)) g₁ acc n).ren (.out acc.ren.length q) =
        .out t q' ∧ (stepEq (fun k => sigOf (P k)) g₁ acc n).nodes[t]? = some m ∧
      q' ∈ names (sigOf (P m.pkg)).exports ∧
      (sigOf (P m.pkg)).exports.lookup q' = (sigOf (nestPkgs P k0 g₁ n.pkg)).exports.lookup q := by
  have hP : nestPkgs P k0 g₁ n.pkg = g₁.toComp P := by simp [nestPkgs, hk]
  have hq₁ : q ∈ names (sigOf (g₁.toComp P)).exports := hP ▸ hq
  obtain ⟨s, i, q', m, hs, hsi, hm, hq', hren⟩ :=
    innerRen_out P (renInst acc.ren n) acc.nodes.length wf₁ out₁ hq₁
  have hself : renSrc (stepEq (fun k => sigOf (P k)) g₁ acc n).ren (.out acc.ren.length q) =
      .out (acc.nodes.length + i) q' := (renSrc_append_self _ _ q).trans hren
  have hget := innerNodes_get (fun k => sigOf (P k)) g₁ (renInst acc.ren n) acc.nodes.length hm
  have hget' : (stepEq (fun k => sigOf (P k)) g₁ acc n).nodes[acc.nodes.length + i]? =
      some ⟨m.pkg, ((m.explicate fun k => sigOf (P k)).args.map fun a =>
        (a.1, innerSrc (renInst acc.ren n) acc.nodes.length a.2))⟩ := by
    rw [stepEq, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, hget]
  obtain ⟨t, ht⟩ := lookup_of_mem hq'
  have hl : (sigOf (P m.pkg)).exports.lookup q' = (sigOf (nestPkgs P k0 g₁ n.pkg)).exports.lookup q := by
    rw [hP, exports_sigOf_toComp, lookup_map_snd, hs, hsi, ht]
    simp [Graph.tyOf, hm, ht]
  exact ⟨acc.nodes.length + i, q', _, hself, hget', hq', hl⟩

theorem renOk_step_eq (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph} {acc : IAcc} {j : Nat}
    {n : Inst} (wf₁ : g₁.WF fun k => sigOf (P k)) (out₁ : g₁.ExportsOut)
    (hr : RenOk (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ acc j)
    (hn : g₂.nodes[j]? = some n) (hk : n.pkg = k0) :
    RenOk (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂
      (stepEq (fun k => sigOf (P k)) g₁ acc n) (j + 1) := by
  refine ⟨by simp [stepEq, hr.1], fun j' n₀ q hn₀ hj hq => ?_⟩
  rcases lt_or_eq_of_lt_succ' hj with hj | hj
  · exact renOk_old hr _ _ j' n₀ q hn₀ hj hq
  · have hnn : n₀ = n := Option.some.inj (hn₀.symm.trans (hj ▸ hn))
    have hj' : j' = acc.ren.length := hj.trans hr.1.symm
    rw [hj', hnn]
    exact renOk_new_k0 P wf₁ out₁ hk (hnn ▸ hq)

end Silmaril.Wasm.Wac.NestProof
