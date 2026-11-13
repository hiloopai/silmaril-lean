module

public import Silmaril.Proofs.Wasm.Wac.Nest.Iface

/-!
# Nesting = inlining: the imports along the whole inlining

* `names_uses_inner`, `tyCons_uses_inner`: the nodes inlined for an instance of `k0` use
  the imports that instance uses, at the same types;
* `usesInv_fold`: the invariant `UsesInv` along the inlining;
* `lookup_iface_inline`, `sortIface_iface_inline`: the imports of the inlined graph and of
  `g₂` have the same lookups, and the same sorted form.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.NestProof

open Silmaril.Wasm.Component

variable {M : Type}

/-- A reference of `g₁`'s import `x` inside the nested instance is an import exactly when
the instance's argument `x` is. -/
theorem src_renInst_imp_iff (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph}
    (ok : NestOk P k0 g₁ g₂) {j : Nat} {n : Inst} {acc : IAcc} (hn : g₂.nodes[j]? = some n)
    (hP : nestPkgs P k0 g₁ n.pkg = g₁.toComp P)
    (hr : RenOk (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ acc j)
    {x : String} (hx : x ∈ names (g₁.iface fun k => sigOf (P k))) (y : String) :
    (renInst acc.ren n).src x = .imp y ↔ n.src x = .imp y := by
  rw [renInst, src_ren]
  exact renSrc_imp_iff hr (resolves_k0 P ok.wf₂ hn hP hx) y

theorem mem_imports_k0 (P : Nat → Comp M) {k0 : Nat} {g₁ : Graph} {n : Inst}
    (hP : nestPkgs P k0 g₁ n.pkg = g₁.toComp P) {q : String × FuncTy} :
    q ∈ (sigOf (nestPkgs P k0 g₁ n.pkg)).imports ↔ q ∈ g₁.iface fun k => sigOf (P k) := by
  rw [hP]
  rfl

/-- An entry used by an inlined node comes from an instance of `g₁`. -/
theorem mem_flatMap_inner (S : Nat → PkgSig) (g₁ : Graph) (n' : Inst) (base : Nat)
    {r : String × FuncTy} (h : r ∈ (innerNodes S g₁ n' base).flatMap (Inst.uses S)) :
    ∃ m ∈ g₁.nodes, ∃ p ∈ (S m.pkg).imports, ∃ x, m.src p.1 = .imp x ∧ n'.src x = .imp r.1 ∧
      p.2 = r.2 := by
  obtain ⟨m', hm', hrm⟩ := List.mem_flatMap.1 h
  rw [innerNodes_eq] at hm'
  obtain ⟨m, hm, hmm⟩ := List.mem_map.1 hm'
  exact ⟨m, hm, (mem_uses_innerInst S n' base m r).1 (hmm ▸ hrm)⟩

theorem names_uses_inner_mp (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph} (ok : NestOk P k0 g₁ g₂)
    {j : Nat} {n : Inst} {acc : IAcc} (hn : g₂.nodes[j]? = some n)
    (hP : nestPkgs P k0 g₁ n.pkg = g₁.toComp P)
    (hr : RenOk (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ acc j) (y : String)
    (h : y ∈ names ((innerNodes (fun k => sigOf (P k)) g₁ (renInst acc.ren n) acc.nodes.length).flatMap
        (Inst.uses fun k => sigOf (P k)))) :
    y ∈ names (n.uses fun k => sigOf (nestPkgs P k0 g₁ k)) := by
  obtain ⟨r, hr', hry⟩ := List.mem_map.1 h
  obtain ⟨m, hm, p, hp, x, hx, hy, _⟩ := mem_flatMap_inner _ g₁ _ _ hr'
  have hxI : x ∈ names (g₁.iface fun k => sigOf (P k)) :=
    mem_iface_of_uses _ g₁ hm (mem_uses _ m hp hx)
  obtain ⟨q, hq, hqx⟩ := List.mem_map.1 hxI
  have hs : n.src q.1 = .imp r.1 :=
    (src_renInst_imp_iff P ok hn hP hr (hqx ▸ hxI) r.1).1 (hqx ▸ hy)
  have hu : (r.1, q.2) ∈ n.uses fun k => sigOf (nestPkgs P k0 g₁ k) :=
    (mem_uses_iff _ n _).2 ⟨q, (mem_imports_k0 P hP).2 hq, hs, rfl⟩
  exact List.mem_map.2 ⟨_, hu, hry⟩

theorem names_uses_inner_mpr (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph} (ok : NestOk P k0 g₁ g₂)
    {j : Nat} {n : Inst} {acc : IAcc} (hn : g₂.nodes[j]? = some n)
    (hP : nestPkgs P k0 g₁ n.pkg = g₁.toComp P)
    (hr : RenOk (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ acc j) (y : String)
    (h : y ∈ names (n.uses fun k => sigOf (nestPkgs P k0 g₁ k))) :
    y ∈ names ((innerNodes (fun k => sigOf (P k)) g₁ (renInst acc.ren n) acc.nodes.length).flatMap
        (Inst.uses fun k => sigOf (P k))) := by
  obtain ⟨r, hr', hry⟩ := List.mem_map.1 h
  obtain ⟨p, hp, hs, _⟩ := (mem_uses_iff _ n r).1 hr'
  have hpI : p ∈ g₁.iface fun k => sigOf (P k) := (mem_imports_k0 P hP).1 hp
  have hpn : p.1 ∈ names g₁.imports := ok.declared ▸ List.mem_map_of_mem hpI
  obtain ⟨m, hm, q, hq, hmq⟩ := ok.used p.1 hpn
  have hy : (renInst acc.ren n).src p.1 = .imp r.1 :=
    (src_renInst_imp_iff P ok hn hP hr (List.mem_map_of_mem hpI) r.1).2 hs
  have hin : (r.1, q.2) ∈ (innerInst (fun k => sigOf (P k)) (renInst acc.ren n)
      acc.nodes.length m).uses fun k => sigOf (P k) :=
    (mem_uses_innerInst _ _ _ m _).2 ⟨q, hq, p.1, hmq, hy, rfl⟩
  have hmem : innerInst (fun k => sigOf (P k)) (renInst acc.ren n) acc.nodes.length m ∈
      innerNodes (fun k => sigOf (P k)) g₁ (renInst acc.ren n) acc.nodes.length := by
    rw [innerNodes_eq]
    exact List.mem_map_of_mem hm
  exact List.mem_map.2 ⟨_, List.mem_flatMap.2 ⟨_, hmem, hin⟩, hry⟩

/-- **The inlined nodes of an instance of `k0` use the names it uses.** -/
theorem names_uses_inner (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph} (ok : NestOk P k0 g₁ g₂)
    {j : Nat} {n : Inst} {acc : IAcc} (hn : g₂.nodes[j]? = some n)
    (hP : nestPkgs P k0 g₁ n.pkg = g₁.toComp P)
    (hr : RenOk (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ acc j) (y : String) :
    y ∈ names ((innerNodes (fun k => sigOf (P k)) g₁ (renInst acc.ren n) acc.nodes.length).flatMap
        (Inst.uses fun k => sigOf (P k))) ↔
      y ∈ names (n.uses fun k => sigOf (nestPkgs P k0 g₁ k)) :=
  ⟨names_uses_inner_mp P ok hn hP hr y, names_uses_inner_mpr P ok hn hP hr y⟩

/-- **The inlined nodes of an instance of `k0` use imports at the types of `g₂`.** -/
theorem tyCons_uses_inner (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph} (ok : NestOk P k0 g₁ g₂)
    {j : Nat} {n : Inst} {acc : IAcc} (hn : g₂.nodes[j]? = some n)
    (hP : nestPkgs P k0 g₁ n.pkg = g₁.toComp P)
    (hr : RenOk (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ acc j) :
    TyCons (lookupIn (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k)))
      ((innerNodes (fun k => sigOf (P k)) g₁ (renInst acc.ren n) acc.nodes.length).flatMap
        (Inst.uses fun k => sigOf (P k))) := by
  intro r hr'
  obtain ⟨m, hm, p, hp, x, hx, hy, ht⟩ := mem_flatMap_inner _ g₁ _ _ hr'
  have h1 : (g₁.iface fun k => sigOf (P k)).lookup x = some p.2 := ok.typed₁ m hm p hp x hx
  have hxI : x ∈ names (g₁.iface fun k => sigOf (P k)) :=
    mem_iface_of_uses _ g₁ hm (mem_uses _ m hp hx)
  obtain ⟨q, hq, hqx⟩ := List.mem_map.1 hxI
  have h2 : (g₁.iface fun k => sigOf (P k)).lookup q.1 = some q.2 :=
    (mem_iff_lookup (nodup_iface _ g₁) q).1 hq
  have h3 : q.2 = p.2 := Option.some.inj (h2.symm.trans (hqx ▸ h1))
  have hs : n.src q.1 = .imp r.1 :=
    (src_renInst_imp_iff P ok hn hP hr (hqx ▸ hxI) r.1).1 (hqx ▸ hy)
  have h4 := ok.typed₂ n (List.mem_of_getElem? hn) q ((mem_imports_k0 P hP).2 hq) r.1 hs
  show List.lookup r.1 _ = _
  rw [h4, h3, ht]

theorem tyCons_uses₂ (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph} (ok : NestOk P k0 g₁ g₂)
    {n : Inst} (hn : n ∈ g₂.nodes) :
    TyCons (lookupIn (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k)))
      (n.uses fun k => sigOf (nestPkgs P k0 g₁ k)) := by
  intro r hr
  obtain ⟨p, hp, hs, ht⟩ := (mem_uses_iff _ n r).1 hr
  rw [← ht]
  exact ok.typed₂ n hn p hp r.1 hs

/-! ## Along the inlining -/

theorem usesInv_step {S S' : Nat → PkgSig} {g₂ : Graph} {T : String → Option FuncTy}
    {acc acc' : IAcc} {j : Nat} {n : Inst} (hu : UsesInv S S' g₂ T acc j)
    (hn : g₂.nodes[j]? = some n) (Δ : List Inst) (hacc : acc'.nodes = acc.nodes ++ Δ)
    (hr' : RenOk S S' g₂ acc' (j + 1)) (hT : TyCons T (Δ.flatMap (Inst.uses S)))
    (hN : ∀ y, y ∈ names (Δ.flatMap (Inst.uses S)) ↔ y ∈ names (n.uses S')) :
    UsesInv S S' g₂ T acc' (j + 1) := by
  have htake : g₂.nodes.take (j + 1) = g₂.nodes.take j ++ [n] := by
    rw [List.take_add_one, hn]
    rfl
  refine ⟨hr', ?_, fun y => ?_⟩
  · rw [hacc, List.flatMap_append]
    exact tyCons_append hu.2.1 hT
  · rw [hacc, htake, List.flatMap_append, List.flatMap_append, List.flatMap_singleton]
    simp only [List.map_append, List.mem_append]
    exact or_congr (hu.2.2 y) (hN y)

/-- One instance of `g₂` keeps `UsesInv`. -/
theorem usesInv_inlineNode (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph} (ok : NestOk P k0 g₁ g₂)
    {j : Nat} {n : Inst} {acc : IAcc} (hn : g₂.nodes[j]? = some n)
    (hu : UsesInv (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂
      (lookupIn (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k))) acc j) :
    UsesInv (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂
      (lookupIn (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k)))
      (inlineNode (fun k => sigOf (P k)) k0 g₁ acc n) (j + 1) := by
  by_cases hk : n.pkg = k0
  · have hP : nestPkgs P k0 g₁ n.pkg = g₁.toComp P := ite_eq_left_of_eq_true _ _ (eq_true hk)
    rw [inlineNode_eq _ g₁ acc hk]
    exact usesInv_step hu hn _ rfl (renOk_step_eq P ok.wf₁ ok.out₁ hu.1 hn hk)
      (tyCons_uses_inner P ok hn hP hu.1) (names_uses_inner P ok hn hP hu.1)
  · have hP : nestPkgs P k0 g₁ n.pkg = P n.pkg := ite_eq_right_of_eq_false _ _ (eq_false hk)
    have hU : (renInst acc.ren n).uses (fun k => sigOf (P k)) =
        n.uses fun k => sigOf (nestPkgs P k0 g₁ k) :=
      uses_renInst hu.1 (congrArg sigOf hP).symm fun p hp => ok.wf₂.1 j n hn p hp
    have hT := tyCons_uses₂ P ok (List.mem_of_getElem? hn)
    rw [inlineNode_ne _ g₁ acc hk]
    refine usesInv_step hu hn [renInst acc.ren n] rfl
      (renOk_step_ne hu.1 hn (congrArg sigOf hP)) ?_ ?_
    · rw [List.flatMap_singleton, hU]
      exact hT
    · intro y
      rw [List.flatMap_singleton, hU]

theorem usesInv_fold (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph} (ok : NestOk P k0 g₁ g₂) :
    ∀ (ns : List Inst) (j : Nat) (acc : IAcc), g₂.nodes.drop j = ns →
      UsesInv (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂
        (lookupIn (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k))) acc j →
      UsesInv (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂
        (lookupIn (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k)))
        (ns.foldl (inlineNode (fun k => sigOf (P k)) k0 g₁) acc) (j + ns.length)
  | [], j, acc, _, hu => hu
  | n :: ns, j, acc, hd, hu => by
    have h := usesInv_fold P ok ns (j + 1) _ (drop_succ_of_drop hd)
      (usesInv_inlineNode P ok (getElem?_of_drop hd) hu)
    have hj : j + 1 + ns.length = j + (n :: ns).length := by simp; omega
    rw [List.foldl_cons, ← hj]
    exact h

/-! ## The imports -/

theorem exportUses_nil {g : Graph} (h : g.ExportsOut) : g.exportUses = [] := by
  unfold Graph.exportUses
  rw [List.filterMap_eq_nil_iff]
  intro p hp
  obtain ⟨k, q, hk⟩ := h p hp
  rw [hk]

/-- The inlining of the whole of `g₂`. -/
def inlineAcc (S : Nat → PkgSig) (k0 : Nat) (g₁ g₂ : Graph) : IAcc :=
  g₂.nodes.foldl (inlineNode S k0 g₁) {}

theorem usesInv_inline (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph} (ok : NestOk P k0 g₁ g₂) :
    UsesInv (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂
      (lookupIn (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k)))
      (inlineAcc (fun k => sigOf (P k)) k0 g₁ g₂) g₂.nodes.length := by
  have h := usesInv_fold P ok g₂.nodes 0 {} rfl
    ⟨renOk_nil _ _ g₂, fun _ hp => absurd hp List.not_mem_nil, fun _ => by simp⟩
  rw [Nat.zero_add] at h
  exact h

/-- The exports of the inlined graph are exports of instances. -/
theorem exportsOut_inline (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph} (ok : NestOk P k0 g₁ g₂) :
    (Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).ExportsOut := by
  intro p hp
  obtain ⟨p₀, hp₀, hpp⟩ := List.mem_map.1 hp
  obtain ⟨j, q, hj⟩ := ok.out₂ p₀ hp₀
  have hres := ok.wf₂.2 p₀ hp₀
  rw [hj] at hres
  obtain ⟨n, hn, hjl, hq⟩ := hres
  obtain ⟨t, q', _, hren, _⟩ := (usesInv_inline P ok).1.2 j n q hn hjl hq
  refine ⟨t, q', ?_⟩
  rw [← hpp]
  show renSrc (inlineAcc (fun k => sigOf (P k)) k0 g₁ g₂).ren p₀.2 = _
  rw [hj, hren]

/-- **The imports of the inlined graph have the lookups of those of `g₂`.** -/
theorem lookup_iface_inline (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph}
    (ok : NestOk P k0 g₁ g₂) (x : String) :
    ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).iface fun k => sigOf (P k)).lookup x =
      (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k)).lookup x := by
  have hu := usesInv_inline P ok
  have hB : ((inlineAcc (fun k => sigOf (P k)) k0 g₁ g₂).nodes.flatMap
      (Inst.uses fun k => sigOf (P k))).lookup x =
      (g₂.nodes.flatMap (Inst.uses fun k => sigOf (nestPkgs P k0 g₁ k))).lookup x := by
    have hT₂ : TyCons (lookupIn (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k)))
        (g₂.nodes.flatMap (Inst.uses fun k => sigOf (nestPkgs P k0 g₁ k))) := fun r hr => by
      obtain ⟨n, hn, hrn⟩ := List.mem_flatMap.1 hr
      exact tyCons_uses₂ P ok hn r hrn
    refine lookup_eq_of_tyCons hu.2.1 hT₂ (fun y => ?_) x
    rw [hu.2.2 y, List.take_length]
  have hE := exportUses_nil (exportsOut_inline P ok)
  have hE₂ := exportUses_nil ok.out₂
  show (dedup (g₂.imports ++ (inlineAcc (fun k => sigOf (P k)) k0 g₁ g₂).nodes.flatMap
      (Inst.uses fun k => sigOf (P k)) ++ (Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).exportUses)).lookup x =
    (dedup (g₂.imports ++ g₂.nodes.flatMap (Inst.uses fun k => sigOf (nestPkgs P k0 g₁ k)) ++
      g₂.exportUses)).lookup x
  rw [lookup_dedup, lookup_dedup, hE, hE₂, List.append_nil, List.append_nil, List.lookup_append,
    List.lookup_append, hB]

/-- **The sorted imports of the inlined graph are those of `g₂`.** -/
theorem sortIface_iface_inline (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph}
    (ok : NestOk P k0 g₁ g₂) :
    sortIface (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k)) =
      sortIface ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).iface fun k => sigOf (P k)) :=
  sortIface_eq_of_lookup (nodup_iface _ g₂) (nodup_iface _ _)
    fun x => (lookup_iface_inline P ok x).symm

end Silmaril.Wasm.Wac.NestProof
