module

public import Silmaril.Wasm.Component.Algebra.SeqGraph.Defs
public import Silmaril.Wasm.Component.Algebra.Plug.Thms

/-!
# `wac plug` of arbitrary graphs: names and imports

List lemmas for `Algebra.task_seq_graph`:

* `mem_names_dedup`: merging duplicate imports keeps the set of names;
* `lookup_of_mem`: the first entry of a name is found by `List.lookup` and by `idxOf`;
* `plug_out`: under the hypotheses of `SeqGraphLaw`, every import of the socket is
  replaced by `Graph.plugSrc` with an export of an instance of the plug;
* `src_plug`: the arguments of a plugged instance are its sources, substituted;
* `iface_seq`: the plugged graph has the plug's imports.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Algebra.SeqGraphProof

open Silmaril.Wasm.Component Silmaril.Wasm.Wac

theorem mem_names_dedup (x : String) : ∀ l : Iface, x ∈ names (dedup l) ↔ x ∈ names l
  | [] => Iff.rfl
  | p :: l => by
    have ih := mem_names_dedup x l
    simp only [dedup, names, List.map_cons, List.mem_cons] at ih ⊢
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h
        have hr' := (List.mem_filter.1 hr).1
        exact Or.inr (ih.1 (List.mem_map_of_mem hr'))
    · rintro (h | h)
      · exact Or.inl h
      · by_cases hx : x = p.1
        · exact Or.inl hx
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (ih.2 h)
          refine Or.inr (List.mem_map_of_mem (List.mem_filter.2 ⟨hr, ?_⟩))
          simpa using hx

/-- The first entry of a name: `List.lookup` finds it, and it sits at the name's `idxOf`. -/
theorem lookup_of_mem {α : Type} (x : String) :
    ∀ l : List (String × α), x ∈ l.map Prod.fst →
      ∃ v, l.lookup x = some v ∧ (x, v) ∈ l ∧ l[(l.map Prod.fst).idxOf x]? = some (x, v)
  | [], h => absurd h List.not_mem_nil
  | (y, w) :: l, h => by
    by_cases hx : x = y
    · subst hx
      refine ⟨w, ?_, List.mem_cons_self, ?_⟩
      · simp only [List.lookup, beq_self_eq_true]
      · simp only [List.map_cons, List.idxOf_cons_self, List.getElem?_cons_zero]
    · have h' : x ∈ l.map Prod.fst := by simpa [hx] using h
      obtain ⟨v, h₁, h₂, h₃⟩ := lookup_of_mem x l h'
      have hb : (x == y) = false := by simpa using hx
      have hne : (y == x) = false := beq_false_of_ne fun h => hx h.symm
      refine ⟨v, ?_, List.mem_cons_of_mem _ h₂, ?_⟩
      · simp only [List.lookup, hb, h₁]
      · simp only [List.map_cons, List.idxOf_cons, hne]
        simpa using h₃

/-! ## Membership in the imports of a graph -/

theorem mem_iface_of_imports (S : Nat → PkgSig) (g : Graph) {p : String × FuncTy}
    (hp : p ∈ g.imports) : p.1 ∈ names (g.iface S) := by
  rw [Graph.iface, mem_names_dedup]
  exact List.mem_map_of_mem (List.mem_append_left _ (List.mem_append_left _ hp))

theorem mem_iface_of_src (S : Nat → PkgSig) (g : Graph) {n : Inst} (hn : n ∈ g.nodes)
    {p : String × FuncTy} (hp : p ∈ (S n.pkg).imports) {x : String} (hx : n.src p.1 = .imp x) :
    x ∈ names (g.iface S) := by
  have hu : (x, p.2) ∈ Inst.uses S n := by
    refine List.mem_filterMap.2 ⟨p, hp, ?_⟩
    simp only [hx]
  rw [Graph.iface, mem_names_dedup]
  have hm : (x, p.2) ∈ g.imports ++ g.nodes.flatMap (Inst.uses S) ++ g.exportUses :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨n, hn, hu⟩))
  exact List.mem_map_of_mem (f := Prod.fst) hm

theorem mem_iface_of_export (S : Nat → PkgSig) (g : Graph) {p : String × Src}
    (hp : p ∈ g.exports) {x : String} (hx : p.2 = .imp x) : x ∈ names (g.iface S) := by
  have hu : (x, anyTy) ∈ g.exportUses := by
    refine List.mem_filterMap.2 ⟨p, hp, ?_⟩
    simp only [hx]
  rw [Graph.iface, mem_names_dedup]
  exact List.mem_map_of_mem (f := Prod.fst) (List.mem_append_right _ hu)

/-! ## The substitution of the plug -/

/-- Every import of the socket is plugged by an export of an instance of the plug. -/
theorem plug_out {S : Nat → PkgSig} {g₁ g₂ : Graph} (ho : g₁.ExportsOut) (hc : Covers S g₁ g₂)
    (hw : g₁.WF S) {x : String} (hx : x ∈ names (g₂.iface S)) :
    ∃ t q, g₁.exports.lookup x = some (.out t q) ∧ t < g₁.nodes.length ∧
      g₁.exports[(g₁.exports.map Prod.fst).idxOf x]? = some (x, .out t q) := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  obtain ⟨v, h₁, h₂, h₃⟩ := lookup_of_mem p.1 g₁.exports (hc p hp)
  obtain ⟨t, q, hv⟩ := ho _ h₂
  simp only at hv
  subst hv
  obtain ⟨n, -, ht, -⟩ := hw.2 _ h₂
  exact ⟨t, q, h₁, ht, h₃⟩

theorem plugSrc_imp_out {S : Nat → PkgSig} {g₁ g₂ : Graph} (ho : g₁.ExportsOut)
    (hc : Covers S g₁ g₂) (hw : g₁.WF S) {x : String} (hx : x ∈ names (g₂.iface S)) :
    ∃ t q, g₁.plugSrc (.imp x) = .out t q ∧ t < g₁.nodes.length := by
  obtain ⟨t, q, h₁, ht, -⟩ := plug_out ho hc hw hx
  exact ⟨t, q, by simp only [Graph.plugSrc, h₁, Option.getD_some], ht⟩

theorem src_plug (S : Nat → PkgSig) (f : Src → Src) (n : Inst) {p : String × FuncTy}
    (hp : p ∈ (S n.pkg).imports) : (Inst.mapSrc f (Inst.explicate S n)).src p.1 = f (n.src p.1) := by
  have he : (Inst.mapSrc f (Inst.explicate S n)).args =
      (S n.pkg).imports.map fun p => (p.1, f (n.src p.1)) := by
    simp only [Inst.mapSrc, Inst.explicate, List.map_map]
    rfl
  have hl := lookup_map_key (S n.pkg).imports (fun y => f (n.src y)) (List.mem_map_of_mem hp)
  show ((Inst.mapSrc f (Inst.explicate S n)).args.lookup p.1).getD _ = _
  rw [he, hl, Option.getD_some]

/-! ## The imports of the plugged graph -/

theorem uses_plug_nil {S : Nat → PkgSig} {g₁ g₂ : Graph} (ho : g₁.ExportsOut)
    (hc : Covers S g₁ g₂) (hw : g₁.WF S) :
    ((g₂.explicate S).nodes.map (Inst.mapSrc g₁.plugSrc)).flatMap (Inst.uses S) = [] := by
  refine List.flatMap_eq_nil_iff.2 fun n' hn' => ?_
  simp only [Graph.explicate, List.map_map, List.mem_map, Function.comp_apply] at hn'
  obtain ⟨n, hn, rfl⟩ := hn'
  refine List.filterMap_eq_nil_iff.2 fun p hp => ?_
  have hp' : p ∈ (S n.pkg).imports := hp
  rw [src_plug S g₁.plugSrc n hp']
  cases hs : n.src p.1 with
  | imp x =>
    obtain ⟨t, q, he, -⟩ := plugSrc_imp_out ho hc hw (mem_iface_of_src S g₂ hn hp' hs)
    simp only [he]
  | out k q => rfl

theorem exportUses_seq_nil {S : Nat → PkgSig} {g₁ g₂ : Graph} (ho : g₁.ExportsOut)
    (hc : Covers S g₁ g₂) (hw : g₁.WF S) : (g₁.seq S g₂).exportUses = [] := by
  refine List.filterMap_eq_nil_iff.2 fun a ha => ?_
  rcases List.mem_append.1 ha with h | h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
    cases hs : p.2 with
    | imp x =>
      obtain ⟨t, q, he, -⟩ := plugSrc_imp_out ho hc hw (mem_iface_of_export S g₂ hp hs)
      simp only [he]
    | out k q => rfl
  · obtain ⟨k, q, hk⟩ := ho a h
    simp only [hk]

theorem exportUses_nil {g : Graph} (ho : g.ExportsOut) : g.exportUses = [] := by
  refine List.filterMap_eq_nil_iff.2 fun a ha => ?_
  obtain ⟨k, q, hk⟩ := ho a ha
  simp only [hk]

theorem imports_seq_filter {S : Nat → PkgSig} {g₁ g₂ : Graph} (hc : Covers S g₁ g₂) :
    g₂.imports.filter (fun p => (g₁.exports.lookup p.1).isNone) = [] := by
  refine List.filter_eq_nil_iff.2 fun p hp => ?_
  obtain ⟨p', hp', he⟩ := List.mem_map.1 (mem_iface_of_imports S g₂ hp)
  obtain ⟨v, h₁, -, -⟩ := lookup_of_mem p.1 g₁.exports (he ▸ hc p' hp')
  simp [h₁]

/-- **The plugged graph has the plug's imports.** -/
theorem iface_seq {S : Nat → PkgSig} {g₁ g₂ : Graph} (ho : g₁.ExportsOut)
    (hc : Covers S g₁ g₂) (hw : g₁.WF S) : (g₁.seq S g₂).iface S = g₁.iface S := by
  have h₁ := uses_plug_nil ho hc hw
  have h₂ := exportUses_seq_nil ho hc hw
  have h₃ := imports_seq_filter (g₂ := g₂) hc
  simp only [Graph.iface, h₂, exportUses_nil ho]
  simp only [Graph.seq, h₃, List.flatMap_append, h₁, List.append_nil]

end Silmaril.Wasm.Component.Algebra.SeqGraphProof
