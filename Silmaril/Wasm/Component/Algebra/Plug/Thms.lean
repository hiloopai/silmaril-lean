module

public import Silmaril.Wasm.Component.Algebra.Plug.Defs
public import Silmaril.Wasm.Component.Algebra.ParComm.Thms
public import Silmaril.Wasm.Wac.Graph.Thms

/-!
# Plugging by name agrees with positional plugging

`wac plug` (`Graph.seq` of a plug package `0` and a socket package `1`, `plugGraph`) wires
each import of the socket to the export of the plug **of the same name**; the algebra's
`seq c₁ c₂` wires import `j` of `c₂` to export `j` of `c₁`.

* **`plug_equiv_seq`**: if every import of the socket is exported by the plug (`PlugCovers`),
  the plug's imports have distinct names and the socket's exports have distinct names, then the
  socket's exports of `wac plug` (the first `k₂` exports: `Graph.seq` re-exports the plug's
  exports after them) are equivalent to `seq (P 0) (reimport (exportIface (P 0)) (byName …)
  (P 1))`: positional plugging after re-reading the socket's imports by name (`byName`, the
  index of the first export of that name, as `List.lookup` takes it). Equivalent for every `C`.
* **`plug_equiv_seq_of_names`**: when the socket's import names are exactly the plug's export
  names, in order and distinct, `byName` is the identity wiring and `wac plug` is `seq (P 0)
  (P 1)`.

So the algebra's laws for `seq` (associativity, units, congruence) apply to `wac plug` through
`reimport`; associativity of `Graph.seq` itself is `Wac.toComp_seq_assoc`.

How: `toComp_plugGraph` writes the composed component out (`plugGraph_iface`: its imports are
the plug's; `argsOf_plug`, `argsOf_socket`: the wiring of the two instances; `mkExports_plug`:
the socket's exports come first, forwarded in order); `fwds_comp_map_fwd` composes the wiring of
`seq` with that of `reimport`, and `implsH_append_comp_selectH_range` drops the plug's
re-exported functions.
-/

public section

namespace Silmaril.Wasm.Component.Algebra

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Wac

variable {M : Type}

/-! ## Lists -/

theorem lookup_map_key (l : Iface) (f : String → Src) {x : String} (hx : x ∈ names l) :
    (l.map fun p => (p.1, f p.1)).lookup x = some (f x) := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons p l ih =>
    by_cases h : x = p.1
    · subst h
      simp only [List.map_cons, List.lookup, beq_self_eq_true]
    · have hx' : x ∈ names l := by simpa [names, h] using hx
      have hb : (x == p.1) = false := by simpa using h
      simp only [List.map_cons, List.lookup, hb, ih hx']

theorem dedup_of_nodup : ∀ {l : Iface}, (names l).Nodup → dedup l = l
  | [], _ => rfl
  | p :: l, h => by
    have h' : p.1 ∉ names l ∧ (names l).Nodup := by simpa [names] using h
    have hf : l.filter (fun r => r.1 != p.1) = l := by
      refine List.filter_eq_self.2 fun r hr => ?_
      have hr' : r.1 ≠ p.1 := fun he => h'.1 (he ▸ List.mem_map_of_mem hr)
      simpa using hr'
    simp only [dedup, dedup_of_nodup h'.2, hf]

theorem map_idxOf_of_nodup {l : Iface} (h : (names l).Nodup) :
    l.map (fun p => (names l).idxOf p.1) = List.range l.length := by
  apply List.ext_getElem (by simp)
  intro j h₁ h₂
  have hl : j < l.length := by simpa using h₂
  have hj : j < (names l).length := by simpa [names] using hl
  have he : l[j].1 = (names l)[j] := by simp only [names, List.getElem_map]
  rw [List.getElem_map, List.getElem_range, he]
  exact List.Nodup.idxOf_getElem h j hj

theorem idxOf_lt_of_mem {E : Iface} {x : String} (hx : x ∈ names E) :
    (names E).idxOf x < E.length := by
  have := List.idxOf_lt_length_of_mem hx
  simpa [names] using this

/-! ## The graph of `wac plug` -/

theorem plugSrc_imp {E : Iface} {x : String} (hx : x ∈ names E) :
    (pkgGraph 0 E).plugSrc (.imp x) = .out 0 x := by
  simp only [Graph.plugSrc, pkgGraph, lookup_map_key E (fun x => Src.out 0 x) hx, Option.getD_some]

/-- The arguments of the socket instance in the plugged graph. -/
abbrev plugArgs (S : Nat → PkgSig) : List (String × Src) :=
  (S 1).imports.map fun p => (p.1, (pkgGraph 0 (S 0).exports).plugSrc (.imp p.1))

theorem plugGraph_nodes (S : Nat → PkgSig) :
    (plugGraph S).nodes = [⟨0, []⟩, ⟨1, plugArgs S⟩] := by
  simp only [plugGraph, Graph.seq, pkgGraph, Graph.explicate, Inst.explicate, Inst.mapSrc,
    Inst.src, List.map_cons, List.map_nil, List.map_map, List.cons_append, List.nil_append,
    List.lookup, Option.getD_none]
  rfl

theorem plugGraph_imports (S : Nat → PkgSig) : (plugGraph S).imports = [] := rfl

theorem plugGraph_exports (S : Nat → PkgSig) :
    (plugGraph S).exports = (S 1).exports.map (fun p => (p.1, Src.out 1 p.1)) ++
      (S 0).exports.map (fun p => (p.1, Src.out 0 p.1)) := by
  simp only [plugGraph, Graph.seq, pkgGraph, List.map_map, Graph.plugSrc, List.length_singleton]
  rfl

/-- Every import of the socket is served by the plug. -/
def PlugCovers (S : Nat → PkgSig) : Prop := ∀ p ∈ (S 1).imports, p.1 ∈ names (S 0).exports

theorem src_plugArgs {S : Nat → PkgSig} (hc : PlugCovers S) {p : String × FuncTy}
    (hp : p ∈ (S 1).imports) : Inst.src ⟨1, plugArgs S⟩ p.1 = .out 0 p.1 := by
  have hm : p.1 ∈ names (S 1).imports := List.mem_map_of_mem hp
  have hl := lookup_map_key (S 1).imports
    (fun x => (pkgGraph 0 (S 0).exports).plugSrc (.imp x)) hm
  simp only [Inst.src, hl, Option.getD_some, plugSrc_imp (hc p hp)]

theorem plugGraph_iface {S : Nat → PkgSig} (hc : PlugCovers S) (hn : (names (S 0).imports).Nodup) :
    (plugGraph S).iface S = (S 0).imports := by
  have h₀ : Inst.uses S ⟨0, []⟩ = (S 0).imports := by
    show (S 0).imports.filterMap (fun p => some (p.1, p.2)) = _
    simp
  have h₁ : Inst.uses S ⟨1, plugArgs S⟩ = [] := by
    refine List.filterMap_eq_nil_iff.2 fun p hp => ?_
    simp only [src_plugArgs hc hp]
  have h₂ : (plugGraph S).exportUses = [] := by
    refine List.filterMap_eq_nil_iff.2 fun p hp => ?_
    rw [plugGraph_exports] at hp
    rcases List.mem_append.1 hp with h | h <;>
    · obtain ⟨q, -, rfl⟩ := List.mem_map.1 h
      rfl
  simp only [Graph.iface, plugGraph_imports, plugGraph_nodes, List.flatMap_cons, List.flatMap_nil,
    h₀, h₁, h₂, List.append_nil, List.nil_append]
  exact dedup_of_nodup hn

theorem plugGraph_offset_zero (S : Nat → PkgSig) : (plugGraph S).offset S 0 = 0 := rfl

theorem plugGraph_offset_one (S : Nat → PkgSig) :
    (plugGraph S).offset S 1 = (S 0).exports.length := by
  simp only [Graph.offset, plugGraph_nodes, List.take_succ_cons, List.take_zero, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- The plug instance reads the imports of the composition in order. -/
theorem argsOf_plug (S : Nat → PkgSig) (hn : (names (S 0).imports).Nodup) :
    (plugGraph S).argsOf S (S 0).imports 0 ⟨0, []⟩ = fwds 0 (S 0).imports.length := by
  have he : ((S 0).imports.map fun p => (plugGraph S).resolve S (S 0).imports 0
      (Inst.src ⟨0, []⟩ p.1)) =
      ((S 0).imports.map fun p => (names (S 0).imports).idxOf p.1).map Impl.fwd := by
    rw [List.map_map]
    refine List.map_congr_left fun p hp => ?_
    have hm : p.1 ∈ names (S 0).imports := List.mem_map_of_mem hp
    simp only [Inst.src, List.lookup, Option.getD_none, Graph.resolve, hm, ↓reduceIte,
      Function.comp_apply]
  rw [Graph.argsOf, he, map_idxOf_of_nodup hn, fwds_zero]

/-- The socket instance reads the exports of the plug by name. -/
theorem argsOf_socket {S : Nat → PkgSig} (hc : PlugCovers S) :
    (plugGraph S).argsOf S (S 0).imports 1 ⟨1, plugArgs S⟩ =
      (byName (S 0).exports (S 1).imports).map fun r => Impl.fwd ((S 0).imports.length + r) := by
  rw [Graph.argsOf, byName, List.map_map]
  refine List.map_congr_left fun p hp => ?_
  have hn : (plugGraph S).nodes[0]? = some ⟨0, []⟩ := by rw [plugGraph_nodes]; rfl
  have hx : 0 < 1 ∧ p.1 ∈ names (S 0).exports := ⟨Nat.one_pos, hc p hp⟩
  simp only [src_plugArgs hc hp, Graph.resolve, hn, hx, and_self, ↓reduceIte,
    plugGraph_offset_zero, Nat.add_zero, Function.comp_apply]

/-- The composition exports the socket's exports first, in order. -/
theorem mkExports_plug (S : Nat → PkgSig) (hn : (names (S 1).exports).Nodup) :
    ((plugGraph S).mkExports S (S 0).imports).map Export.impl =
      fwds ((S 0).imports.length + (S 0).exports.length) (S 1).exports.length ++
        (S 0).exports.map fun p => (plugGraph S).resolve S (S 0).imports 2 (.out 0 p.1) := by
  have hn1 : (plugGraph S).nodes[1]? = some ⟨1, plugArgs S⟩ := by rw [plugGraph_nodes]; rfl
  have hl : (plugGraph S).nodes.length = 2 := by rw [plugGraph_nodes]; rfl
  have h₁ : ((S 1).exports.map fun p => (plugGraph S).resolve S (S 0).imports 2 (.out 1 p.1)) =
      fwds ((S 0).imports.length + (S 0).exports.length) (S 1).exports.length := by
    have hc : ((S 1).exports.map fun p => (plugGraph S).resolve S (S 0).imports 2 (.out 1 p.1)) =
        ((S 1).exports.map fun p => (names (S 1).exports).idxOf p.1).map
          fun j => Impl.fwd ((S 0).imports.length + (S 0).exports.length + j) := by
      rw [List.map_map]
      refine List.map_congr_left fun p hp => ?_
      have hx : 1 < 2 ∧ p.1 ∈ names (S 1).exports := ⟨Nat.one_lt_two, List.mem_map_of_mem hp⟩
      simp only [Graph.resolve, hn1, hx, and_self, ↓reduceIte, plugGraph_offset_one,
        Function.comp_apply]
    rw [hc, map_idxOf_of_nodup hn]
    rfl
  rw [Graph.mkExports, List.map_map, hl, plugGraph_exports, List.map_append, List.map_map,
    List.map_map]
  rw [← h₁]
  rfl

/-! ## Handler lemmas -/

theorem implsH_append_comp_selectH_range (e : Nat) (l₁ l₂ : List Impl) :
    (implsH e (l₁ ++ l₂)).comp (selectH (List.range l₁.length)) = implsH e l₁ := by
  funext q
  obtain ⟨i, a⟩ := q
  by_cases hi : i < l₁.length
  · have hr : (List.range l₁.length)[i]? = some i := List.getElem?_range hi
    simp only [Handler.comp, selectH, hr, Prog.interp_call, Prog.interp_pure, Prog.bind_pure,
      implsH, List.getElem?_append_left hi]
  · have hr : (List.range l₁.length)[i]? = none := List.getElem?_eq_none (by simpa using hi)
    have hl : l₁[i]? = none := List.getElem?_eq_none (by omega)
    simp only [Handler.comp, selectH, hr, Prog.interp_pure, implsH, hl]

/-- Wrapping with forwarding arguments below forwarding wiring forwards directly. -/
theorem fwds_comp_map_fwd (e b k : Nat) {ρ : List Nat} (hρ : ∀ r ∈ ρ, r < k) :
    (implsH e (fwds b k)).comp (implsH k (ρ.map Impl.fwd)) =
      implsH e (ρ.map fun r => Impl.fwd (b + r)) := by
  have h := implsH_comp_subst e (fwds b k) (ρ.map Impl.fwd)
  rw [length_fwds] at h
  rw [h, List.map_map]
  congr 1
  refine List.map_congr_left fun r hr => ?_
  have hf : (fwds b k)[r]? = some (Impl.fwd (b + r)) := by
    simp only [fwds, List.getElem?_map, List.getElem?_range (hρ r hr), Option.map_some]
  simp only [Function.comp_apply, Impl.subst, hf, List.nil_append]

/-! ## Agreement -/

variable [CoreModule M]

theorem denU_two_inst (C : CoreSem M) (I : Iface) (c₁ c₂ : Comp M) (a₁ a₂ : List Impl)
    (xs : List Export) :
    (Comp.mk I [.inst c₁ a₁, .inst c₂ a₂] xs).denU C =
      (ext (I.length + c₁.exports.length)
        (ext I.length (Strategy.ofHandler (maskH I.length))
          ((Strategy.ofHandler (implsH I.length a₁)).comp (c₁.denU C)))
        ((Strategy.ofHandler (implsH (I.length + c₁.exports.length) a₂)).comp (c₂.denU C))).comp
      (Strategy.ofHandler (exportsH (I.length + c₁.exports.length + c₂.exports.length) xs)) := by
  simp only [Comp.denU, denNodes, Node.den, Node.width, envAfter]

omit [CoreModule M] in
/-- The composed component of `wac plug`, written out. -/
theorem toComp_plugGraph (P : Nat → Comp M) (hc : PlugCovers fun k => sigOf (P k))
    (hn : (names (P 0).imports).Nodup) :
    (plugGraph fun k => sigOf (P k)).toComp P =
      Comp.mk (P 0).imports
        [.inst (P 0) (fwds 0 (P 0).imports.length),
         .inst (P 1) ((byName (exportIface (P 0)) (P 1).imports).map
          fun r => Impl.fwd ((P 0).imports.length + r))]
        ((plugGraph fun k => sigOf (P k)).mkExports (fun k => sigOf (P k)) (P 0).imports) := by
  have hi := plugGraph_iface hc hn
  have h₀ := argsOf_plug (fun k => sigOf (P k)) hn
  have h₁ := argsOf_socket hc
  simp only [Graph.toComp, Graph.build, hi, plugGraph_nodes, Graph.mkNodes]
  rw [h₀]
  exact congrArg (fun a => Comp.mk _ [_, .inst (P 1) a] _) h₁

/-- **Plugging by name is positional plugging after re-reading the socket's imports by name.**
If every import of the socket is exported by the plug (`PlugCovers`), the plug's imports have
distinct names and the socket's exports have distinct names, then the socket's exports of
`wac plug` (`Graph.seq` of the two packages, keeping the first `k₂` exports: `Graph.seq` also
re-exports the plug's exports after them) are the positional plug `seq` of the plug into the
socket whose imports are re-read by name (`reimport … (byName …)`). -/
theorem plug_equiv_seq (C : CoreSem M) (P : Nat → Comp M) (hc : PlugCovers fun k => sigOf (P k))
    (hn₀ : (names (P 0).imports).Nodup) (hn₁ : (names (exportIface (P 1))).Nodup) :
    CompEquiv C
      (select (List.range (P 1).exports.length) ((plugGraph fun k => sigOf (P k)).toComp P))
      (seq (P 0) (reimport (exportIface (P 0)) (byName (exportIface (P 0)) (P 1).imports) (P 1))) := by
  have hk₀ : (exportIface (P 0)).length = (P 0).exports.length := List.length_map _
  have hk₀' : (sigOf (P 0)).exports.length = (P 0).exports.length := List.length_map _
  have hk₂ : (sigOf (P 1)).exports.length = (P 1).exports.length := List.length_map _
  obtain ⟨rest, hxs⟩ : ∃ rest, ((plugGraph fun k => sigOf (P k)).mkExports (fun k => sigOf (P k))
      (P 0).imports).map Export.impl =
      fwds ((P 0).imports.length + (P 0).exports.length) (P 1).exports.length ++ rest := by
    have h := mkExports_plug (fun k => sigOf (P k)) hn₁
    rw [hk₀', hk₂] at h
    exact ⟨_, h⟩
  have hlen : (P 1).exports.length ≤
      ((plugGraph fun k => sigOf (P k)).toComp P).exports.length := by
    have h := congrArg List.length hxs
    rw [List.length_map, List.length_append, length_fwds] at h
    rw [toComp_plugGraph P hc hn₀, Comp.exports_mk, h]
    exact Nat.le_add_right _ _
  have hf : (List.range (P 1).exports.length).filter
      (· < ((plugGraph fun k => sigOf (P k)).toComp P).exports.length) =
      List.range (P 1).exports.length := by
    refine List.filter_eq_self.2 fun j hj => ?_
    have hj' : j < (P 1).exports.length := List.mem_range.1 hj
    rw [decide_eq_true_eq]
    omega
  have hρ : ∀ r ∈ byName (exportIface (P 0)) (P 1).imports, r < (exportIface (P 0)).length := by
    intro r hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    exact idxOf_lt_of_mem (hc p hp)
  have hW : (reimport (exportIface (P 0)) (byName (exportIface (P 0)) (P 1).imports)
      (P 1)).exports.length = (P 1).exports.length := (sizes_wrap _ _ _).2
  have hN : (Strategy.ofHandler (implsH ((P 0).imports.length + (P 0).exports.length)
      (fwds (P 0).imports.length (exportIface (P 0)).length))).comp
        ((reimport (exportIface (P 0)) (byName (exportIface (P 0)) (P 1).imports) (P 1)).denU C) =
      (Strategy.ofHandler (implsH ((P 0).imports.length + (P 0).exports.length)
        ((byName (exportIface (P 0)) (P 1).imports).map
          fun r => Impl.fwd ((P 0).imports.length + r)))).comp ((P 1).denU C) := by
    rw [denU_reimport, ← Strategy.comp_assoc, ← Strategy.ofHandler_comp,
      fwds_comp_map_fwd _ _ _ hρ]
  have hX : (implsH ((P 0).imports.length + (P 0).exports.length + (P 1).exports.length)
      (((plugGraph fun k => sigOf (P k)).mkExports (fun k => sigOf (P k))
        (P 0).imports).map Export.impl)).comp (selectH (List.range (P 1).exports.length)) =
      implsH ((P 0).imports.length + (P 0).exports.length + (P 1).exports.length)
        (fwds ((P 0).imports.length + (P 0).exports.length) (P 1).exports.length) := by
    have h := implsH_append_comp_selectH_range
      ((P 0).imports.length + (P 0).exports.length + (P 1).exports.length)
      (fwds ((P 0).imports.length + (P 0).exports.length) (P 1).exports.length) rest
    rw [length_fwds] at h
    rw [hxs, h]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show ((plugGraph fun k => sigOf (P k)).toComp P).imports.length = (P 0).imports.length
    rw [toComp_plugGraph P hc hn₀]
    rfl
  · show (keptExports _ _ _).length = (reexport _ _).length
    rw [length_keptExports, hf, List.length_range, length_reexport, hW]
  · rw [denU_select, hf, toComp_plugGraph P hc hn₀, denU_two_inst, Strategy.comp_assoc,
      exportsH, ← Strategy.ofHandler_comp, hX]
    show _ = (Comp.mk (P 0).imports [.inst (P 0) (fwds 0 (P 0).imports.length),
      .inst _ (fwds (P 0).imports.length (exportIface (P 0)).length)]
      (reexport ((P 0).imports.length + (P 0).exports.length) _)).denU C
    rw [denU_two_inst, hN, exportsH, map_impl_reexport, hW]

/-- **Plugging by name agrees with positional plugging**: when the socket imports exactly the
plug's exports, by name and in order (and the names involved are distinct), the socket's
exports of `wac plug` are `seq` of the plug into the socket. -/
theorem plug_equiv_seq_of_names (C : CoreSem M) (P : Nat → Comp M)
    (hnames : names (P 1).imports = names (exportIface (P 0)))
    (hn₀ : (names (P 0).imports).Nodup) (hne : (names (exportIface (P 0))).Nodup)
    (hn₁ : (names (exportIface (P 1))).Nodup) :
    CompEquiv C
      (select (List.range (P 1).exports.length) ((plugGraph fun k => sigOf (P k)).toComp P))
      (seq (P 0) (P 1)) := by
  have hc : PlugCovers fun k => sigOf (P k) := by
    intro p hp
    show p.1 ∈ names (exportIface (P 0))
    rw [← hnames]
    exact List.mem_map_of_mem hp
  have hb : byName (exportIface (P 0)) (P 1).imports = List.range (P 1).imports.length := by
    have hm : (P 1).imports.map (fun p => (names (exportIface (P 0))).idxOf p.1) =
        (P 1).imports.map (fun p => (names (P 1).imports).idxOf p.1) := by
      rw [hnames]
    rw [byName, hm, map_idxOf_of_nodup (hnames ▸ hne)]
  have hl : (exportIface (P 0)).length = (P 1).imports.length := by
    have h := congrArg List.length hnames
    simpa [names] using h.symm
  have hr : CompEquiv C (reimport (exportIface (P 0)) (byName (exportIface (P 0)) (P 1).imports)
      (P 1)) (P 1) := by
    refine ⟨⟨hl, (sizes_wrap _ _ _).2⟩, ?_⟩
    rw [denU_reimport, hb, hl, implsH_fwd, maskH_comp_denU]
  exact (plug_equiv_seq C P hc hn₀ hn₁).trans (seq_congr (CompEquiv.refl C (P 0)) hr)

end Silmaril.Wasm.Component.Algebra
