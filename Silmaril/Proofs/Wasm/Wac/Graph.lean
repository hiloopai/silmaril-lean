module

public import Silmaril.Wasm.Wac.Graph.Defs
public import Silmaril.Wasm.Component.Semantics.Thms

/-!
# WAC composition graphs: proofs

* explicit promotion: `src_explicate`, `build_explicate` (filling in the promoted
  arguments does not change the composition), `explicit_explicate`;
* deduplication: `nodup_dedup`, `mem_dedup`;
* promotion: `mem_iface_of_uses`, `resolve_promoted`;
* compositionality: `denU_build` (the meaning of the composition is `Graph.sem` of the
  meanings of the packages), `sem_mono`, `sem_congr`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component Silmaril.Games

/-! ## Lookup -/

theorem lookup_map_self {β : Type} (f : String → β) :
    ∀ (l : Iface) (q : String), q ∈ names l →
      (l.map fun p => (p.1, f p.1)).lookup q = some (f q)
  | [], _, h => by simp at h
  | p :: l, q, h => by
    by_cases hq : q = p.1
    · subst hq
      simp
    · have h' : q ∈ names l := by
        simp only [names, List.map_cons, List.mem_cons] at h
        exact h.resolve_left hq
      have hb : (q == p.1) = false := by simpa using hq
      simp only [List.map_cons, List.lookup, hb]
      exact lookup_map_self f l q h'

/-! ## Explicit promotion -/

theorem src_explicate (S : Nat → PkgSig) (n : Inst) {q : String}
    (hq : q ∈ names (S n.pkg).imports) : (n.explicate S).src q = n.src q := by
  show ((((S n.pkg).imports.map fun p => (p.1, n.src p.1)).lookup q).getD (.imp q)) = n.src q
  rw [lookup_map_self (fun x => n.src x) _ q hq]
  rfl

theorem explicit_explicate (S : Nat → PkgSig) (n : Inst) : (n.explicate S).Explicit S := by
  intro p hp
  have hq : p.1 ∈ names (S n.pkg).imports := List.mem_map_of_mem hp
  simp [Inst.explicate, lookup_map_self (fun x => n.src x) _ p.1 hq]

theorem uses_explicate (S : Nat → PkgSig) (n : Inst) : (n.explicate S).uses S = n.uses S := by
  unfold Inst.uses
  apply List.filterMap_congr
  intro p hp
  rw [src_explicate S n (List.mem_map_of_mem hp)]

theorem iface_explicate (S : Nat → PkgSig) (g : Graph) :
    (g.explicate S).iface S = g.iface S := by
  simp only [Graph.iface, Graph.explicate, Graph.exportUses, List.flatMap_map]
  congr 3
  exact List.flatMap_congr fun n _ => uses_explicate S n

theorem offset_explicate (S : Nat → PkgSig) (g : Graph) (k : Nat) :
    (g.explicate S).offset S k = g.offset S k := by
  simp [Graph.offset, Graph.explicate, List.map_take, Function.comp_def, Inst.explicate]

theorem resolve_explicate (S : Nat → PkgSig) (g : Graph) (I : Iface) (b : Nat) (s : Src) :
    (g.explicate S).resolve S I b s = g.resolve S I b s := by
  cases s with
  | imp x => rfl
  | out k q =>
    simp only [Graph.resolve, offset_explicate]
    simp only [Graph.explicate, List.getElem?_map]
    cases g.nodes[k]? <;> rfl

theorem argsOf_explicate (S : Nat → PkgSig) (g : Graph) (I : Iface) (k : Nat) (n : Inst) :
    (g.explicate S).argsOf S I k (n.explicate S) = g.argsOf S I k n := by
  unfold Graph.argsOf
  apply List.map_congr_left
  intro p hp
  rw [resolve_explicate, src_explicate S n (List.mem_map_of_mem hp)]

theorem mkNodes_explicate {M : Type} (S : Nat → PkgSig) (P : Nat → Comp M) (g : Graph)
    (I : Iface) : ∀ (k : Nat) (ns : List Inst),
      (g.explicate S).mkNodes S P I k (ns.map (Inst.explicate S)) = g.mkNodes S P I k ns
  | _, [] => rfl
  | k, n :: ns => by
    simp only [List.map_cons, Graph.mkNodes, argsOf_explicate, mkNodes_explicate S P g I (k + 1) ns]
    rfl

theorem tyOf_explicate (S : Nat → PkgSig) (g : Graph) (I : Iface) (s : Src) :
    (g.explicate S).tyOf S I s = g.tyOf S I s := by
  cases s with
  | imp x => rfl
  | out k q =>
    simp only [Graph.tyOf, Graph.explicate, List.getElem?_map]
    cases g.nodes[k]? <;> rfl

/-- **Explicit promotion does not change the composition.** -/
theorem build_explicate {M : Type} (S : Nat → PkgSig) (P : Nat → Comp M) (g : Graph) :
    (g.explicate S).build S P = g.build S P := by
  have hI := iface_explicate S g
  have hx : (g.explicate S).mkExports S (g.iface S) = g.mkExports S (g.iface S) := by
    simp only [Graph.mkExports, tyOf_explicate, resolve_explicate]
    simp [Graph.explicate]
  simp only [Graph.build, hI, hx]
  exact congrArg (fun ns => Comp.mk (g.iface S) ns _) (mkNodes_explicate S P g _ 0 g.nodes)

/-! ## Deduplication -/

theorem mem_dedup : ∀ (l : Iface) (x : String), x ∈ names (dedup l) ↔ x ∈ names l
  | [], _ => Iff.rfl
  | p :: l, x => by
    have ih := mem_dedup l x
    by_cases hx : x = p.1
    · simp [dedup, hx]
    · simp only [dedup, names, List.map_cons, List.mem_cons, hx, false_or] at ih ⊢
      constructor
      · intro h
        obtain ⟨r, hr, hr1⟩ := List.mem_map.1 h
        subst hr1
        exact ih.1 (List.mem_map_of_mem (f := Prod.fst) (List.mem_filter.1 hr).1)
      · intro h
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (ih.2 h)
        exact List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, by simpa using hx⟩, rfl⟩

theorem nodup_dedup : ∀ l : Iface, (names (dedup l)).Nodup
  | [] => List.nodup_nil
  | p :: l => by
    simp only [dedup, names, List.map_cons, List.nodup_cons]
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨r, hr, hr1⟩ := List.mem_map.1 h
      have := (List.mem_filter.1 hr).2
      simp [hr1] at this
    · exact (nodup_dedup l).sublist (List.Sublist.map _ List.filter_sublist)

/-- **The imports of a composition have pairwise distinct names** (duplicates merged). -/
theorem nodup_iface (S : Nat → PkgSig) (g : Graph) : (names (g.iface S)).Nodup :=
  nodup_dedup _

/-- Every import used by an instance is an import of the composition. -/
theorem mem_iface_of_uses (S : Nat → PkgSig) (g : Graph) {n : Inst} (hn : n ∈ g.nodes)
    {x : String} (hx : x ∈ names (n.uses S)) : x ∈ names (g.iface S) := by
  rw [Graph.iface, mem_dedup]
  have : x ∈ names (g.nodes.flatMap (Inst.uses S)) := by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    exact List.mem_map_of_mem (List.mem_flatMap.2 ⟨n, hn, hr⟩)
  simp only [names, List.map_append, List.mem_append] at this ⊢
  exact Or.inl (Or.inr this)

/-- Declared imports are imports of the composition. -/
theorem mem_iface_of_declared (S : Nat → PkgSig) (g : Graph) {x : String}
    (hx : x ∈ names g.imports) : x ∈ names (g.iface S) := by
  rw [Graph.iface, mem_dedup]
  simp only [names, List.map_append, List.mem_append] at hx ⊢
  exact Or.inl (Or.inl hx)

theorem mem_uses (S : Nat → PkgSig) (n : Inst) {p : String × FuncTy}
    (hp : p ∈ (S n.pkg).imports) {x : String} (hs : n.src p.1 = .imp x) :
    x ∈ names (n.uses S) := by
  refine List.mem_map.2 ⟨(x, p.2), List.mem_filterMap.2 ⟨p, hp, ?_⟩, rfl⟩
  simp [hs]

/-- **Promotion**: an import `q` of an instance without an argument `q` is wired to the
import `q` of the composition, the same for every instance. -/
theorem resolve_promoted (S : Nat → PkgSig) (g : Graph) {n : Inst} (hn : n ∈ g.nodes)
    {p : String × FuncTy} (hp : p ∈ (S n.pkg).imports) (ha : n.args.lookup p.1 = none)
    (b : Nat) :
    g.resolve S (g.iface S) b (n.src p.1) = .fwd ((names (g.iface S)).idxOf p.1) := by
  have hs : n.src p.1 = .imp p.1 := by simp [Inst.src, ha]
  have hm : p.1 ∈ names (g.iface S) := mem_iface_of_uses S g hn (mem_uses S n hp hs)
  simp [hs, Graph.resolve, hm]

/-! ## Compositionality -/

variable {M : Type} [CoreModule M]

theorem envAfter_mkNodes (S : Nat → PkgSig) (P : Nat → Comp M)
    (hw : ∀ k, (P k).exports.length = (S k).exports.length) (g : Graph) (I : Iface) :
    ∀ (k e : Nat) (ns : List Inst), envAfter e (g.mkNodes S P I k ns) = Graph.envFrom S e ns
  | _, _, [] => rfl
  | k, e, n :: ns => by
    simp only [Graph.mkNodes, envAfter, Graph.envFrom, Node.width, hw]
    exact envAfter_mkNodes S P hw g I (k + 1) _ ns

theorem denNodes_mkNodes (C : CoreSem M) (S : Nat → PkgSig) (P : Nat → Comp M)
    (hw : ∀ k, (P k).exports.length = (S k).exports.length) (g : Graph) (I : Iface)
    {X : Sig.{0}} : ∀ (k e : Nat) (ns : List Inst) (E : Strategy X sigU),
      denNodes C e (g.mkNodes S P I k ns) E = g.semNodes S I (fun j => (P j).denU C) k e ns E
  | _, _, [], _ => by simp only [Graph.mkNodes, denNodes, Graph.semNodes]
  | k, e, n :: ns, E => by
    simp only [Graph.mkNodes, denNodes, Graph.semNodes, Node.width, hw, Node.den]
    exact denNodes_mkNodes C S P hw g I (k + 1) _ ns _

/-- **Compositionality**: the meaning of a composition is `Graph.sem` of the meanings of
its packages. -/
theorem denU_build (C : CoreSem M) (S : Nat → PkgSig) (P : Nat → Comp M)
    (hw : ∀ k, (P k).exports.length = (S k).exports.length) (g : Graph) :
    (g.build S P).denU C = g.sem S (fun k => (P k).denU C) := by
  simp only [Graph.build, Comp.denU, Graph.sem, denNodes_mkNodes C S P hw,
    envAfter_mkNodes S P hw]

theorem semNodes_mono (S : Nat → PkgSig) (g : Graph) (I : Iface)
    {D D' : Nat → Strategy sigU sigU} (hD : ∀ k, D k ≤ D' k) {X : Sig.{0}} :
    ∀ (k e : Nat) (ns : List Inst) {E E' : Strategy X sigU}, E ≤ E' →
      g.semNodes S I D k e ns E ≤ g.semNodes S I D' k e ns E'
  | _, _, [], _, _, hE => hE
  | k, e, n :: ns, _, _, hE => by
    simp only [Graph.semNodes]
    exact semNodes_mono S g I hD (k + 1) _ ns
      (ext_mono e hE (Strategy.comp_mono le_rfl (hD n.pkg)))

/-- `Graph.sem` is monotone in the meanings of the packages. -/
theorem sem_mono (S : Nat → PkgSig) (g : Graph) {D D' : Nat → Strategy sigU sigU}
    (hD : ∀ k, D k ≤ D' k) : g.sem S D ≤ g.sem S D' := by
  unfold Graph.sem
  exact Strategy.comp_mono (semNodes_mono S g _ hD 0 _ g.nodes le_rfl) le_rfl

end Silmaril.Wasm.Wac
