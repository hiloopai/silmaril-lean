module

public import Silmaril.Wasm.Wac.Seq.Defs
public import Silmaril.Proofs.Wasm.Wac.Graph

/-!
# Sequential composition: proofs

* `plugSrc_seq`: plugging into a sequential composition is plugging twice;
* `explicate_mapSrc_explicate`: substituting in an explicit instance keeps it explicit;
* `seq_assoc`: **associativity** of `Graph.seq`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component

theorem seq_imports (S : Nat → PkgSig) (g₁ g₂ : Graph) : (g₁.seq S g₂).imports =
    g₁.imports ++ g₂.imports.filter fun p => (g₁.exports.lookup p.1).isNone := rfl

theorem seq_nodes (S : Nat → PkgSig) (g₁ g₂ : Graph) : (g₁.seq S g₂).nodes =
    g₁.nodes ++ (g₂.explicate S).nodes.map (Inst.mapSrc g₁.plugSrc) := rfl

theorem seq_exports (S : Nat → PkgSig) (g₁ g₂ : Graph) : (g₁.seq S g₂).exports =
    g₂.exports.map (fun a => (a.1, g₁.plugSrc a.2)) ++ g₁.exports := rfl

theorem lookup_map_snd {β γ : Type} (f : β → γ) :
    ∀ (l : List (String × β)) (x : String),
      (l.map fun a => (a.1, f a.2)).lookup x = (l.lookup x).map f
  | [], _ => rfl
  | (k, v) :: l, x => by
    by_cases hx : x = k
    · subst hx
      simp
    · have hb : (x == k) = false := by simpa using hx
      simp only [List.map_cons, List.lookup, hb]
      exact lookup_map_snd f l x

theorem length_nodes_explicate (S : Nat → PkgSig) (g : Graph) :
    (g.explicate S).nodes.length = g.nodes.length := by
  simp [Graph.explicate]

theorem length_nodes_seq (S : Nat → PkgSig) (g₁ g₂ : Graph) :
    (g₁.seq S g₂).nodes.length = g₁.nodes.length + g₂.nodes.length := by
  simp [Graph.seq, Graph.explicate]

/-- Plugging into a sequential composition is plugging twice. -/
theorem plugSrc_seq (S : Nat → PkgSig) (g₁ g₂ : Graph) (s : Src) :
    (g₁.seq S g₂).plugSrc s = g₁.plugSrc (g₂.plugSrc s) := by
  cases s with
  | out k q =>
    simp only [Graph.plugSrc, length_nodes_seq, Src.out.injEq, and_true]
    omega
  | imp x =>
    have hl : (g₁.seq S g₂).exports.lookup x =
        ((g₂.exports.lookup x).map g₁.plugSrc).or (g₁.exports.lookup x) := by
      simp only [Graph.seq, List.lookup_append, lookup_map_snd]
    simp only [Graph.plugSrc, hl]
    cases g₂.exports.lookup x <;> rfl

theorem mapSrc_mapSrc (f g : Src → Src) (n : Inst) :
    (n.mapSrc g).mapSrc f = n.mapSrc (f ∘ g) := by
  simp [Inst.mapSrc, Function.comp_def]

theorem src_of_args {n : Inst} {l : Iface} {h : String → Src}
    (ha : n.args = l.map fun p => (p.1, h p.1)) {q : String} (hq : q ∈ names l) :
    n.src q = h q := by
  unfold Inst.src
  rw [ha, lookup_map_self h l q hq]
  rfl

/-- Substituting in an explicit instance keeps it explicit. -/
theorem explicate_mapSrc_explicate (S : Nat → PkgSig) (f : Src → Src) (n : Inst) :
    ((n.explicate S).mapSrc f).explicate S = (n.explicate S).mapSrc f := by
  have hargs : ((n.explicate S).mapSrc f).args =
      (S n.pkg).imports.map fun p => (p.1, f (n.src p.1)) := by
    simp [Inst.mapSrc, Inst.explicate]
  have hpkg : ((n.explicate S).mapSrc f).pkg = n.pkg := rfl
  have hsrc : ∀ p ∈ (S n.pkg).imports,
      ((n.explicate S).mapSrc f).src p.1 = f (n.src p.1) := fun p hp =>
    src_of_args (h := fun x => f (n.src x)) hargs (List.mem_map_of_mem hp)
  show (⟨_, _⟩ : Inst) = _
  cases hn : (n.explicate S).mapSrc f with
  | mk pkg args =>
    rw [hn] at hargs hpkg hsrc
    simp only at hargs hpkg hsrc
    subst hpkg hargs
    simp only [Inst.mk.injEq, true_and]
    exact List.map_congr_left fun p hp => by rw [hsrc p hp]

theorem filter_seq (S : Nat → PkgSig) (g₁ g₂ : Graph) (l : Iface) :
    l.filter (fun p => ((g₁.seq S g₂).exports.lookup p.1).isNone) =
      (l.filter fun p => (g₂.exports.lookup p.1).isNone).filter
        fun p => (g₁.exports.lookup p.1).isNone := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro p _
  simp only [Graph.seq, List.lookup_append, lookup_map_snd]
  cases g₂.exports.lookup p.1 <;> cases g₁.exports.lookup p.1 <;> rfl

/-- **Associativity of sequential composition.** -/
theorem seq_assoc (S : Nat → PkgSig) (g₁ g₂ g₃ : Graph) :
    (g₁.seq S g₂).seq S g₃ = g₁.seq S (g₂.seq S g₃) := by
  have hp : (g₁.seq S g₂).plugSrc = g₁.plugSrc ∘ g₂.plugSrc := funext (plugSrc_seq S g₁ g₂)
  have himp : ((g₁.seq S g₂).seq S g₃).imports = (g₁.seq S (g₂.seq S g₃)).imports := by
    simp only [seq_imports, List.filter_append, List.append_assoc, filter_seq]
  have hnodes : ((g₁.seq S g₂).seq S g₃).nodes = (g₁.seq S (g₂.seq S g₃)).nodes := by
    simp only [seq_nodes, Graph.explicate, List.map_append, List.map_map, List.append_assoc, hp]
    congr 2
    exact List.map_congr_left fun n _ => by
      simp [Function.comp_def, explicate_mapSrc_explicate, mapSrc_mapSrc]
  have hexp : ((g₁.seq S g₂).seq S g₃).exports = (g₁.seq S (g₂.seq S g₃)).exports := by
    simp only [seq_exports, List.map_append, List.map_map, List.append_assoc, hp]
    rfl
  cases h : (g₁.seq S g₂).seq S g₃
  cases h' : g₁.seq S (g₂.seq S g₃)
  rw [h, h'] at himp hnodes hexp
  simp_all

end Silmaril.Wasm.Wac
