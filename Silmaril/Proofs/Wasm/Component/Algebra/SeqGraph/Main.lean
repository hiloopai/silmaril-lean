module

public import Silmaril.Proofs.Wasm.Component.Algebra.SeqGraph.Run
public import Silmaril.Wasm.Component.Passes.Flatten.Thms

/-!
# `wac plug` of arbitrary graphs is positional plugging

Both sides of `SeqGraphLaw` are flattened (`Passes.Flatten`: `flatten` keeps the meaning).
The plug's instances give the same run on both sides (`r₁`); the socket's instances give the
runs related by `gRun_sim`; and the exports kept on the left are the socket's exports, which
the right re-exports through `reimport` and `seq`. So the two flat components have the same
imports, the same nodes and the same export wiring (`flat_nodes`, `flat_exports`), and the
same meaning.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Algebra.SeqGraphProof

open Silmaril.Wasm.Component Silmaril.Wasm.Wac

variable {M : Type}

/-! ## Wiring lists -/

theorem getElem?_fwds {b k i : Nat} (h : i < k) : (fwds b k)[i]? = some (Impl.fwd (b + i)) := by
  simp [fwds, List.getElem?_range h]

theorem getElem?_reexport :
    ∀ (b : Nat) (xs : List Export) (j : Nat),
      (reexport b xs)[j]? = xs[j]?.map fun x => { x with impl := .fwd (b + j) }
  | _, [], _ => rfl
  | b, x :: xs, 0 => rfl
  | b, x :: xs, j + 1 => by
    rw [reexport, List.getElem?_cons_succ, getElem?_reexport (b + 1) xs j, List.getElem?_cons_succ]
    congr 2
    funext y
    congr 2
    omega

/-- The wiring of an instance whose arguments are forwarding, substituted. -/
theorem args_fwds (b k : Nat) (σ : List Impl) :
    ((List.range k).map fun i => ((fwds b k)[i]?.getD .trap).subst σ) =
      (List.range k).map fun i => (Impl.fwd (b + i)).subst σ := by
  refine List.map_congr_left fun i hi => ?_
  rw [getElem?_fwds (List.mem_range.1 hi), Option.getD_some]

theorem range_fwd_subst_id (n : Nat) :
    ((List.range n).map fun i => (Impl.fwd (0 + i)).subst ((List.range n).map Impl.fwd)) =
      (List.range n).map Impl.fwd := by
  refine List.map_congr_left fun i hi => ?_
  rw [Nat.zero_add]
  exact subst_fwd (by simp [List.getElem?_range (List.mem_range.1 hi)])

theorem subst_fwd_append_right {σ L : List Impl} {n : Nat} (h : σ.length = n) (j : Nat) :
    (Impl.fwd (n + j)).subst (σ ++ L) = (Impl.fwd j).subst L := by
  have h' : σ.length ≤ n + j := by omega
  have he : n + j - σ.length = j := by omega
  simp only [Impl.subst, List.getElem?_append_right h', he]

variable [CoreModule M]

/-- Two flat components with the same imports, nodes and export wiring mean the same. -/
theorem linked_denU_congr (C : CoreSem M) {l l' : Linked M}
    (hi : l.imports.length = l'.imports.length) (hn : l.nodes = l'.nodes)
    (hx : l.exports.map Export.impl = l'.exports.map Export.impl) : l.denU C = l'.denU C := by
  obtain ⟨I, ns, xs⟩ := l
  obtain ⟨I', ns', xs'⟩ := l'
  simp only at hi hn hx
  subst hn
  simp only [Linked.denU, exportsH, hi, hx]

theorem flatten_one (I : Iface) (c : Comp M) (args : List Impl) (xs : List Export) :
    (flatten (.mk I [.inst c args] xs)).nodes =
        (flattenNodes ((List.range c.imports.length).map fun i =>
          (args[i]?.getD .trap).subst ((List.range I.length).map Impl.fwd)) I.length c.nodes).2.2 ∧
      (flatten (.mk I [.inst c args] xs)).exports.map Export.impl =
        xs.map fun x => x.impl.subst ((List.range I.length).map Impl.fwd ++
          c.exports.map fun x => x.impl.subst (flattenNodes ((List.range c.imports.length).map
            fun i => (args[i]?.getD .trap).subst ((List.range I.length).map Impl.fwd))
            I.length c.nodes).1) := by
  simp only [flatten, flattenNodes_inst_run, flattenNodes, List.append_nil, List.map_map]
  exact ⟨trivial, rfl⟩

theorem flatten_two (I : Iface) (c d : Comp M) (a b : List Impl) (xs : List Export) :
    (flatten (.mk I [.inst c a, .inst d b] xs)).nodes =
        (flattenNodes ((List.range c.imports.length).map fun i =>
          (a[i]?.getD .trap).subst ((List.range I.length).map Impl.fwd)) I.length c.nodes).2.2 ++
        (flattenNodes ((List.range d.imports.length).map fun i =>
          (b[i]?.getD .trap).subst ((List.range I.length).map Impl.fwd ++
            c.exports.map fun x => x.impl.subst (flattenNodes ((List.range c.imports.length).map
              fun i => (a[i]?.getD .trap).subst ((List.range I.length).map Impl.fwd))
              I.length c.nodes).1))
          (flattenNodes ((List.range c.imports.length).map fun i =>
            (a[i]?.getD .trap).subst ((List.range I.length).map Impl.fwd)) I.length c.nodes).2.1
          d.nodes).2.2 ∧
      (flatten (.mk I [.inst c a, .inst d b] xs)).exports.map Export.impl =
        xs.map fun x => x.impl.subst (((List.range I.length).map Impl.fwd ++
          c.exports.map fun x => x.impl.subst (flattenNodes ((List.range c.imports.length).map
            fun i => (a[i]?.getD .trap).subst ((List.range I.length).map Impl.fwd))
            I.length c.nodes).1) ++
          d.exports.map fun x => x.impl.subst (flattenNodes ((List.range d.imports.length).map
            fun i => (b[i]?.getD .trap).subst ((List.range I.length).map Impl.fwd ++
              c.exports.map fun x => x.impl.subst (flattenNodes ((List.range c.imports.length).map
                fun i => (a[i]?.getD .trap).subst ((List.range I.length).map Impl.fwd))
                I.length c.nodes).1))
            (flattenNodes ((List.range c.imports.length).map fun i =>
              (a[i]?.getD .trap).subst ((List.range I.length).map Impl.fwd)) I.length c.nodes).2.1
            d.nodes).1) := by
  simp only [flatten, flattenNodes_inst_run, flattenNodes, List.append_nil, List.map_map]
  exact ⟨trivial, rfl⟩

/-- Flattening the one node of a component with a single nested instance. -/
theorem flattenNodes_single (σ : List Impl) (eB : Nat) (c : Comp M) (a : List Impl) :
    flattenNodes σ eB [.inst c a] =
      (σ ++ c.exports.map fun x => x.impl.subst (flattenNodes ((List.range c.imports.length).map
          fun i => (a[i]?.getD .trap).subst σ) eB c.nodes).1,
        (flattenNodes ((List.range c.imports.length).map fun i => (a[i]?.getD .trap).subst σ)
          eB c.nodes).2.1,
        (flattenNodes ((List.range c.imports.length).map fun i => (a[i]?.getD .trap).subst σ)
          eB c.nodes).2.2) := by
  simp only [flattenNodes_inst_run, flattenNodes, List.append_nil]

theorem map_subst_keptExports (b : Nat) (xs : List Export) (keep : List Nat) (σ : List Impl) :
    (keptExports b xs keep).map (fun x => x.impl.subst σ) =
      (keep.filter (· < xs.length)).map fun j => (Impl.fwd (b + j)).subst σ := by
  rw [show (fun x : Export => x.impl.subst σ) = Impl.subst σ ∘ Export.impl from rfl,
    ← List.map_map, map_impl_keptExports, List.map_map]
  rfl

theorem map_subst_reexport (b : Nat) (xs : List Export) (σ : List Impl) :
    (reexport b xs).map (fun x => x.impl.subst σ) = (fwds b xs.length).map (Impl.subst σ) := by
  rw [show (fun x : Export => x.impl.subst σ) = Impl.subst σ ∘ Export.impl from rfl,
    ← List.map_map, map_impl_reexport]

/-! ## The runs -/

/-- The run of the plug's instances (the same on both sides). -/
def run₁ (P : Nat → Comp M) (S : Nat → PkgSig) (g₁ : Graph) :
    (Src → Impl) × Nat × List (M × List Impl) :=
  gRun P (baseV (g₁.iface S)) (g₁.iface S).length 0 g₁.nodes

/-- The socket's instances as plugged by `Graph.seq`. -/
def plugged (S : Nat → PkgSig) (g₁ g₂ : Graph) : List Inst :=
  g₂.nodes.map fun n => Inst.mapSrc g₁.plugSrc (Inst.explicate S n)

/-- The run of the plugged instances. -/
def run₂ (P : Nat → Comp M) (S : Nat → PkgSig) (g₁ g₂ : Graph) :
    (Src → Impl) × Nat × List (M × List Impl) :=
  gRun P (run₁ P S g₁).1 (run₁ P S g₁).2.1 (0 + g₁.nodes.length) (plugged S g₁ g₂)

/-- The positional side's run of the socket's instances, from its wiring. -/
def wiredRun (I I₂ : Iface) (ns₁ ns₂ : List (Node M)) (xs₁ : List Export) (ρ : List Nat) :
    List Impl × Nat × List (M × List Impl) :=
  flattenNodes ((List.range I₂.length).map fun i => ((ρ.map Impl.fwd)[i]?.getD .trap).subst
      ((List.range xs₁.length).map fun i => (Impl.fwd (I.length + i)).subst
        ((List.range I.length).map Impl.fwd ++ xs₁.map fun x => x.impl.subst
          (flattenNodes ((List.range I.length).map Impl.fwd) I.length ns₁).1)))
    (flattenNodes ((List.range I.length).map Impl.fwd) I.length ns₁).2.1 ns₂

omit [CoreModule M] in
/-- Forwarding past a prefix of length `n` reads the rest of the wiring. -/
theorem range_fwd_subst_append {σ₀ L : List Impl} {n : Nat} (h : σ₀.length = n) {k : Nat}
    (hk : k ≤ L.length) :
    ((List.range k).map fun j => (Impl.fwd (n + j)).subst (σ₀ ++ L)) = L.take k := by
  apply List.ext_getElem (by simp [List.length_take]; omega)
  intro j h₁ _
  have hj : j < L.length := by simp at h₁; omega
  have hL : L[j]? = some L[j] := List.getElem?_eq_getElem hj
  rw [List.getElem_map, List.getElem_range, subst_fwd_append_right h, subst_fwd hL,
    List.getElem_take]

omit [CoreModule M] in
theorem fwds_subst_append {σ₀ L : List Impl} {n : Nat} (h : σ₀.length = n) {k : Nat}
    (hk : k ≤ L.length) : (fwds n k).map (Impl.subst (σ₀ ++ L)) = L.take k := by
  rw [fwds, List.map_map]
  exact range_fwd_subst_append h hk

theorem filter_range_lt {k m : Nat} (h : k ≤ m) : (List.range k).filter (· < m) = List.range k :=
  List.filter_eq_self.2 fun j hj => by
    have := List.mem_range.1 hj
    simp only [decide_eq_true_eq]
    omega

/-- Flattening a selection of the exports of a component. -/
theorem flatten_select (I : Iface) (ns : List (Node M)) (xs : List Export) (keep : List Nat) :
    (flatten (select keep (.mk I ns xs))).nodes =
        (flattenNodes ((List.range I.length).map Impl.fwd) I.length ns).2.2 ∧
      (flatten (select keep (.mk I ns xs))).exports.map Export.impl =
        (keep.filter (· < xs.length)).map fun j => (Impl.fwd (I.length + j)).subst
          ((List.range I.length).map Impl.fwd ++ xs.map fun x => x.impl.subst
            (flattenNodes ((List.range I.length).map Impl.fwd) I.length ns).1) := by
  have h := flatten_one I (Comp.mk I ns xs) (fwds 0 I.length) (keptExports I.length xs keep)
  simp only [Comp.imports_mk, Comp.nodes_mk, Comp.exports_mk, args_fwds, range_fwd_subst_id,
    map_subst_keptExports] at h
  exact h

/-- Flattening the positional plug of a component into a wrapped component. -/
theorem flatten_seq_wrap (I I₂ E : Iface) (ns₁ ns₂ : List (Node M)) (xs₁ xs₂ : List Export)
    (hE : E.length = xs₁.length) (ρ : List Nat) :
    (flatten (seq (.mk I ns₁ xs₁) (wrap E (ρ.map Impl.fwd) (.mk I₂ ns₂ xs₂)))).nodes =
        (flattenNodes ((List.range I.length).map Impl.fwd) I.length ns₁).2.2 ++
          (wiredRun I I₂ ns₁ ns₂ xs₁ ρ).2.2 ∧
      (flatten (seq (.mk I ns₁ xs₁) (wrap E (ρ.map Impl.fwd) (.mk I₂ ns₂ xs₂)))).exports.map
        Export.impl = xs₂.map fun x => x.impl.subst (wiredRun I I₂ ns₁ ns₂ xs₁ ρ).1 := by
  have h := flatten_two I (Comp.mk I ns₁ xs₁) (wrap E (ρ.map Impl.fwd) (.mk I₂ ns₂ xs₂))
    (fwds 0 I.length) (fwds I.length E.length) (reexport (I.length + xs₁.length)
      (reexport E.length xs₂))
  simp only [wrap, Comp.imports_mk, Comp.nodes_mk, Comp.exports_mk, args_fwds, range_fwd_subst_id,
    flattenNodes_single, hE, map_subst_reexport, length_reexport] at h
  simp only [seq, wrap, Comp.imports_mk, Comp.exports_mk, hE]
  refine ⟨h.1, ?_⟩
  rw [h.2, fwds_subst_append (by simp) (by simp [length_fwds]),
    fwds_subst_append (by simp) (by simp), List.take_of_length_le (by simp),
    List.take_of_length_le (by simp)]
  rfl

omit [CoreModule M] in
theorem toComp_seq (P : Nat → Comp M) (g₁ g₂ : Graph)
    (hI : (g₁.seq (fun k => sigOf (P k)) g₂).iface (fun k => sigOf (P k)) =
      g₁.iface fun k => sigOf (P k)) :
    (g₁.seq (fun k => sigOf (P k)) g₂).toComp P =
      .mk (g₁.iface fun k => sigOf (P k))
        ((g₁.seq (fun k => sigOf (P k)) g₂).mkNodes (fun k => sigOf (P k)) P
          (g₁.iface fun k => sigOf (P k)) 0 (g₁.seq (fun k => sigOf (P k)) g₂).nodes)
        ((g₁.seq (fun k => sigOf (P k)) g₂).mkExports (fun k => sigOf (P k))
          (g₁.iface fun k => sigOf (P k))) := by
  unfold Graph.toComp Graph.build
  rw [hI]

omit [CoreModule M] in
theorem seq_nodes (S : Nat → PkgSig) (g₁ g₂ : Graph) :
    (g₁.seq S g₂).nodes = g₁.nodes ++ plugged S g₁ g₂ := by
  simp only [Graph.seq, Graph.explicate, plugged, List.map_map]
  rfl

/-- The run of the plugged graph's instances is the plug's run, then the plugged run. -/
theorem run_seq (P : Nat → Comp M) (g₁ g₂ : Graph) :
    (flattenNodes ((List.range (g₁.iface fun k => sigOf (P k)).length).map Impl.fwd)
        (g₁.iface fun k => sigOf (P k)).length
        ((g₁.seq (fun k => sigOf (P k)) g₂).mkNodes (fun k => sigOf (P k)) P
          (g₁.iface fun k => sigOf (P k)) 0 (g₁.seq (fun k => sigOf (P k)) g₂).nodes)).2.2 =
        (run₁ P (fun k => sigOf (P k)) g₁).2.2 ++ (run₂ P (fun k => sigOf (P k)) g₁ g₂).2.2 ∧
      ∀ s, ((g₁.seq (fun k => sigOf (P k)) g₂).resolve (fun k => sigOf (P k))
        (g₁.iface fun k => sigOf (P k)) (0 + (g₁.seq (fun k => sigOf (P k)) g₂).nodes.length) s).subst
        (flattenNodes ((List.range (g₁.iface fun k => sigOf (P k)).length).map Impl.fwd)
          (g₁.iface fun k => sigOf (P k)).length
          ((g₁.seq (fun k => sigOf (P k)) g₂).mkNodes (fun k => sigOf (P k)) P
            (g₁.iface fun k => sigOf (P k)) 0 (g₁.seq (fun k => sigOf (P k)) g₂).nodes)).1 =
        (run₂ P (fun k => sigOf (P k)) g₁ g₂).1 s := by
  have hA := flatten_mkNodes_run P (g₁.seq (fun k => sigOf (P k)) g₂)
    (g₁.iface fun k => sigOf (P k)) _ 0 _ (g₁.iface fun k => sigOf (P k)).length
    (baseV (g₁.iface fun k => sigOf (P k))) List.drop_zero
    (by simp [offset_zero_run]) (resolve_zero_subst_run _ _ _)
  have hR := gRun_append_run P g₁.nodes (plugged (fun k => sigOf (P k)) g₁ g₂)
    (baseV (g₁.iface fun k => sigOf (P k))) (g₁.iface fun k => sigOf (P k)).length 0
  rw [← seq_nodes] at hR
  exact ⟨by rw [hA.2.1, hR]; rfl, fun s => by rw [hA.2.2, hR]; rfl⟩

/-- The kept exports of the plugged graph are the socket's, substituted. -/
theorem take_seq_exports (S : Nat → PkgSig) (g₁ g₂ : Graph) (I : Iface) (σ : List Impl) :
    (((g₁.seq S g₂).mkExports S I).map fun x => x.impl.subst σ).take g₂.exports.length =
      g₂.exports.map fun e => ((g₁.seq S g₂).resolve S I (g₁.seq S g₂).nodes.length
        (g₁.plugSrc e.2)).subst σ := by
  have he : (g₁.seq S g₂).exports = g₂.exports.map (fun a => (a.1, g₁.plugSrc a.2)) ++ g₁.exports :=
    rfl
  have ht : (g₁.seq S g₂).exports.take g₂.exports.length =
      g₂.exports.map (fun a => (a.1, g₁.plugSrc a.2)) := by
    rw [he, List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  rw [Graph.mkExports, List.map_map, ← List.map_take, ht, List.map_map]
  rfl

/-- **The left side, flattened.** -/
theorem flat_lhs (P : Nat → Comp M) (g₁ g₂ : Graph)
    (hI : (g₁.seq (fun k => sigOf (P k)) g₂).iface (fun k => sigOf (P k)) =
      g₁.iface fun k => sigOf (P k)) :
    (flatten (select (List.range g₂.exports.length)
        ((g₁.seq (fun k => sigOf (P k)) g₂).toComp P))).imports = g₁.iface (fun k => sigOf (P k)) ∧
      (flatten (select (List.range g₂.exports.length)
        ((g₁.seq (fun k => sigOf (P k)) g₂).toComp P))).nodes =
        (run₁ P (fun k => sigOf (P k)) g₁).2.2 ++ (run₂ P (fun k => sigOf (P k)) g₁ g₂).2.2 ∧
      (flatten (select (List.range g₂.exports.length)
        ((g₁.seq (fun k => sigOf (P k)) g₂).toComp P))).exports.map Export.impl =
        g₂.exports.map fun e => (run₂ P (fun k => sigOf (P k)) g₁ g₂).1 (g₁.plugSrc e.2) := by
  rw [toComp_seq P g₁ g₂ hI]
  obtain ⟨hN, hX⟩ := flatten_select (M := M) _ _ _ (List.range g₂.exports.length)
  obtain ⟨hR₁, hR₂⟩ := run_seq P g₁ g₂
  have hk : g₂.exports.length ≤ ((g₁.seq (fun k => sigOf (P k)) g₂).mkExports
      (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k))).length := by
    simp [Graph.mkExports, Graph.seq]
  refine ⟨rfl, hN.trans hR₁, ?_⟩
  rw [hX, filter_range_lt hk, range_fwd_subst_append (by simp) (by simpa using hk),
    take_seq_exports]
  refine List.map_congr_left fun e _ => ?_
  rw [← hR₂, Nat.zero_add]

/-- The positional side's wiring after the plug's instance: its imports, then its exports. -/
def σ₁ (P : Nat → Comp M) (S : Nat → PkgSig) (g₁ : Graph) : List Impl :=
  (List.range (g₁.iface S).length).map Impl.fwd ++ g₁.exports.map fun p => (run₁ P S g₁).1 p.2

/-- The socket's imports, read by name among the plug's exports. -/
def ρ₁ (S : Nat → PkgSig) (g₁ g₂ : Graph) : List Nat :=
  (g₂.iface S).map fun p => (g₁.exports.map Prod.fst).idxOf p.1

/-- The wiring of the plug's exports, seen from the `reimport` wrapper. -/
def σW (P : Nat → Comp M) (S : Nat → PkgSig) (g₁ : Graph) : List Impl :=
  (List.range g₁.exports.length).map fun i => (Impl.fwd ((g₁.iface S).length + i)).subst (σ₁ P S g₁)

/-- The wiring of the socket's imports on the positional side. -/
def σ₂ (P : Nat → Comp M) (S : Nat → PkgSig) (g₁ g₂ : Graph) : List Impl :=
  (List.range (g₂.iface S).length).map fun i =>
    (((ρ₁ S g₁ g₂).map Impl.fwd)[i]?.getD .trap).subst (σW P S g₁)

/-- The valuation of the socket's references on the positional side. -/
def V₂ (P : Nat → Comp M) (S : Nat → PkgSig) (g₁ g₂ : Graph) (s : Src) : Impl :=
  (g₂.resolve S (g₂.iface S) 0 s).subst (σ₂ P S g₁ g₂)

/-- The run of the socket's instances on the positional side. -/
def run₂' (P : Nat → Comp M) (S : Nat → PkgSig) (g₁ g₂ : Graph) :
    (Src → Impl) × Nat × List (M × List Impl) :=
  gRun P (V₂ P S g₁ g₂) (run₁ P S g₁).2.1 0 g₂.nodes

omit [CoreModule M] in
theorem toComp_imports (P : Nat → Comp M) (g : Graph) :
    (g.toComp P).imports = g.iface fun k => sigOf (P k) := rfl

omit [CoreModule M] in
theorem toComp_nodes (P : Nat → Comp M) (g : Graph) :
    (g.toComp P).nodes = g.mkNodes (fun k => sigOf (P k)) P (g.iface fun k => sigOf (P k)) 0 g.nodes :=
  rfl

omit [CoreModule M] in
theorem toComp_exports (P : Nat → Comp M) (g : Graph) :
    (g.toComp P).exports = g.mkExports (fun k => sigOf (P k)) (g.iface fun k => sigOf (P k)) := rfl

omit [CoreModule M] in
theorem length_exportIface_toComp (P : Nat → Comp M) (g : Graph) :
    (exportIface (g.toComp P)).length = g.exports.length := by
  simp [exportIface, toComp_exports, Graph.mkExports]

omit [CoreModule M] in
theorem byName_toComp (P : Nat → Comp M) (g₁ g₂ : Graph) :
    byName (exportIface (g₁.toComp P)) (g₂.toComp P).imports = ρ₁ (fun k => sigOf (P k)) g₁ g₂ := by
  have h : names (exportIface (g₁.toComp P)) = g₁.exports.map Prod.fst := by
    simp only [exportIface, Graph.toComp, Graph.build, Comp.exports_mk, Graph.mkExports, names,
      List.map_map]
    rfl
  rw [byName, h]
  rfl

/-- The plug's flattened exports, on the positional side. -/
theorem plug_exports (P : Nat → Comp M) (g₁ : Graph) :
    ((g₁.mkExports (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k))).map fun x =>
      x.impl.subst (flattenNodes ((List.range (g₁.iface fun k => sigOf (P k)).length).map Impl.fwd)
        (g₁.iface fun k => sigOf (P k)).length
        (g₁.mkNodes (fun k => sigOf (P k)) P (g₁.iface fun k => sigOf (P k)) 0 g₁.nodes)).1) =
      g₁.exports.map fun p => (run₁ P (fun k => sigOf (P k)) g₁).1 p.2 := by
  have hA := flatten_mkNodes_run P g₁ (g₁.iface fun k => sigOf (P k)) _ 0 _
    (g₁.iface fun k => sigOf (P k)).length (baseV (g₁.iface fun k => sigOf (P k))) List.drop_zero
    (by simp [offset_zero_run]) (resolve_zero_subst_run _ _ _)
  rw [Graph.mkExports, List.map_map]
  refine List.map_congr_left fun p _ => ?_
  simp only [run₁, Function.comp_apply]
  rw [← hA.2.2, Nat.zero_add]

/-- The plug's run, on the positional side. -/
theorem plug_run (P : Nat → Comp M) (g₁ : Graph) :
    flattenNodes ((List.range (g₁.iface fun k => sigOf (P k)).length).map Impl.fwd)
        (g₁.iface fun k => sigOf (P k)).length
        (g₁.mkNodes (fun k => sigOf (P k)) P (g₁.iface fun k => sigOf (P k)) 0 g₁.nodes) =
      ((flattenNodes ((List.range (g₁.iface fun k => sigOf (P k)).length).map Impl.fwd)
        (g₁.iface fun k => sigOf (P k)).length
        (g₁.mkNodes (fun k => sigOf (P k)) P (g₁.iface fun k => sigOf (P k)) 0 g₁.nodes)).1,
        (run₁ P (fun k => sigOf (P k)) g₁).2.1, (run₁ P (fun k => sigOf (P k)) g₁).2.2) := by
  have hA := flatten_mkNodes_run P g₁ (g₁.iface fun k => sigOf (P k)) _ 0 _
    (g₁.iface fun k => sigOf (P k)).length (baseV (g₁.iface fun k => sigOf (P k))) List.drop_zero
    (by simp [offset_zero_run]) (resolve_zero_subst_run _ _ _)
  simp only [run₁]
  rw [← hA.1, ← hA.2.1]

/-- The positional side's run of the socket, for the compositions of the two graphs. -/
theorem wiredRun_toComp (P : Nat → Comp M) (g₁ g₂ : Graph) :
    wiredRun (g₁.iface fun k => sigOf (P k)) (g₂.iface fun k => sigOf (P k))
        (g₁.mkNodes (fun k => sigOf (P k)) P (g₁.iface fun k => sigOf (P k)) 0 g₁.nodes)
        (g₂.mkNodes (fun k => sigOf (P k)) P (g₂.iface fun k => sigOf (P k)) 0 g₂.nodes)
        (g₁.mkExports (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k)))
        (ρ₁ (fun k => sigOf (P k)) g₁ g₂) =
      flattenNodes (σ₂ P (fun k => sigOf (P k)) g₁ g₂) (run₁ P (fun k => sigOf (P k)) g₁).2.1
        (g₂.mkNodes (fun k => sigOf (P k)) P (g₂.iface fun k => sigOf (P k)) 0 g₂.nodes) := by
  have hl : (g₁.mkExports (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k))).length =
      g₁.exports.length := by simp [Graph.mkExports]
  rw [wiredRun, plug_exports, plug_run, hl]
  rfl

/-- **The right side, flattened.** -/
theorem flat_rhs (P : Nat → Comp M) (g₁ g₂ : Graph) :
    (flatten (seq (g₁.toComp P) (reimport (exportIface (g₁.toComp P))
        (byName (exportIface (g₁.toComp P)) (g₂.toComp P).imports) (g₂.toComp P)))).imports =
        g₁.iface (fun k => sigOf (P k)) ∧
      (flatten (seq (g₁.toComp P) (reimport (exportIface (g₁.toComp P))
        (byName (exportIface (g₁.toComp P)) (g₂.toComp P).imports) (g₂.toComp P)))).nodes =
        (run₁ P (fun k => sigOf (P k)) g₁).2.2 ++ (run₂' P (fun k => sigOf (P k)) g₁ g₂).2.2 ∧
      (flatten (seq (g₁.toComp P) (reimport (exportIface (g₁.toComp P))
        (byName (exportIface (g₁.toComp P)) (g₂.toComp P).imports) (g₂.toComp P)))).exports.map
          Export.impl = g₂.exports.map fun e => (run₂' P (fun k => sigOf (P k)) g₁ g₂).1 e.2 := by
  rw [byName_toComp]
  have hE : (exportIface (g₁.toComp P)).length =
      (g₁.mkExports (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k))).length := by
    simp [length_exportIface_toComp, Graph.mkExports]
  obtain ⟨hN, hX⟩ := flatten_seq_wrap (M := M) _ _ (exportIface (g₁.toComp P)) _
    (g₂.mkNodes (fun k => sigOf (P k)) P (g₂.iface fun k => sigOf (P k)) 0 g₂.nodes) _
    (g₂.mkExports (fun k => sigOf (P k)) (g₂.iface fun k => sigOf (P k))) hE
    (ρ₁ (fun k => sigOf (P k)) g₁ g₂)
  have hA₂ := flatten_mkNodes_run P g₂ (g₂.iface fun k => sigOf (P k)) _ 0
    (σ₂ P (fun k => sigOf (P k)) g₁ g₂) (run₁ P (fun k => sigOf (P k)) g₁).2.1
    (V₂ P (fun k => sigOf (P k)) g₁ g₂) List.drop_zero
    (by simp [σ₂, offset_zero_run]) (fun _ => rfl)
  rw [wiredRun_toComp, plug_run] at hN
  rw [wiredRun_toComp] at hX
  refine ⟨rfl, hN.trans (by rw [hA₂.2.1]; rfl), hX.trans ?_⟩
  rw [Graph.mkExports, List.map_map]
  refine List.map_congr_left fun e _ => ?_
  rw [Function.comp_apply, ← Nat.zero_add g₂.nodes.length]
  exact hA₂.2.2 e.2

end Silmaril.Wasm.Component.Algebra.SeqGraphProof
