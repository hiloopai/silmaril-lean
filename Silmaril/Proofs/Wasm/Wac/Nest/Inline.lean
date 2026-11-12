module

public import Silmaril.Proofs.Wasm.Wac.Nest.Outer

/-!
# Nesting = inlining: the instances of the nested composition, and the whole run

* `step_eq`: an instance of the nested composition `k0`, whose nodes are flattened by
  `flatten_mkNodes`, and its inlined nodes (`sim_inner`) keep `SimV`;
* `sim_outer`: the runs over `g₂` (packages `nestPkgs P k0 g₁`) and over the inlined graph
  (packages `P`) produce the same flat nodes, and their final valuations are related by
  the final renaming.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.NestProof

open Silmaril.Wasm.Component

variable {M : Type}

/-- The references of an instance of the nested composition resolve in `g₂`. -/
theorem resolves_k0 (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph}
    (wf₂ : g₂.WF fun k => sigOf (nestPkgs P k0 g₁ k)) {j : Nat} {n : Inst}
    (hn : g₂.nodes[j]? = some n) (hP : nestPkgs P k0 g₁ n.pkg = g₁.toComp P) {x : String}
    (hx : x ∈ names (g₁.iface fun k => sigOf (P k))) :
    g₂.Resolves (fun k => sigOf (nestPkgs P k0 g₁ k)) (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k))
      j (n.src x) := by
  obtain ⟨p, hp, hpx⟩ := List.mem_map.1 hx
  have hp' : p ∈ (sigOf (nestPkgs P k0 g₁ n.pkg)).imports := by
    rw [hP]
    exact hp
  exact hpx ▸ wf₂.1 j n hn p hp'

/-- The new export of an instance of the nested composition. -/
theorem simV_new_k0 (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph} (ok : NestRunOk P k0 g₁ g₂)
    {n : Inst} {acc : IAcc} {V : Src → Impl} (hk : n.pkg = k0) (τ : List Impl) (Uf : Src → Impl)
    (hexp : ∀ s, g₁.Resolves (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k))
        g₁.nodes.length s →
      (g₁.resolve (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k)) g₁.nodes.length s).subst τ =
        Uf (innerSrc (renInst acc.ren n) acc.nodes.length s))
    {q : String} (hq : q ∈ names (sigOf (nestPkgs P k0 g₁ n.pkg)).exports) :
    extV V acc.ren.length (g₁.mkExports (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k))) τ
        (.out acc.ren.length q) =
      Uf (renSrc (stepEq (fun k => sigOf (P k)) g₁ acc n).ren (.out acc.ren.length q)) := by
  have hP : nestPkgs P k0 g₁ n.pkg = g₁.toComp P := ite_eq_left_of_eq_true _ _ (eq_true hk)
  have hq₁ : q ∈ g₁.exports.map Prod.fst := by
    rw [← names_exports_toComp P g₁, ← hP]
    exact hq
  obtain ⟨s, hs₁⟩ := lookup_of_mem hq₁
  have hq' : q ∈ (g₁.mkExports (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k))).map
      Export.name := by
    rw [names_mkExports]
    exact hq₁
  have hres₁ : g₁.Resolves (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k))
      g₁.nodes.length s := ok.wf₁.2 _ (mem_of_lookup hs₁)
  have hren : renSrc (stepEq (fun k => sigOf (P k)) g₁ acc n).ren (.out acc.ren.length q) =
      innerSrc (renInst acc.ren n) acc.nodes.length s :=
    (renSrc_append_self _ _ q).trans (by simp [innerRen, hs₁])
  rw [hren, extV_self _ _ hq', expImpl_mkExports _ g₁ _ hs₁]
  exact hexp s hres₁

/-- The extension at an instance of the nested composition keeps `SimV`, given the
relation of the inner run's final valuation `Uf`. -/
theorem simV_eq_ext (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph} (ok : NestRunOk P k0 g₁ g₂)
    {j : Nat} {n : Inst} {acc : IAcc} {V U : Src → Impl} (hn : g₂.nodes[j]? = some n)
    (hk : n.pkg = k0)
    (hs : SimV (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ j acc V U)
    (τ : List Impl) (Uf : Src → Impl)
    (hUi : ∀ x, Uf (.imp x) = U (.imp x))
    (hUf : ∀ t q, t < acc.nodes.length → Uf (.out t q) = U (.out t q))
    (hexp : ∀ s, g₁.Resolves (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k))
        g₁.nodes.length s →
      (g₁.resolve (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k)) g₁.nodes.length s).subst τ =
        Uf (innerSrc (renInst acc.ren n) acc.nodes.length s)) :
    SimV (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ (j + 1)
      (stepEq (fun k => sigOf (P k)) g₁ acc n)
      (extV V j (g₁.mkExports (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k))) τ) Uf := by
  refine ⟨renOk_step_eq P ok.wf₁ ok.out₁ hs.1 hn hk, fun x => (hs.2.1 x).trans (hUi x).symm, ?_⟩
  intro j' n₀ q hn₀ hj hq
  rcases lt_or_eq_of_lt_succ' hj with hj | hj
  · exact simV_old hs _ (fun j' q h => extV_ne V (Nat.ne_of_lt h) _ _ q) hUf j' n₀ q hn₀ hj hq
  · have hnn : n₀ = n := Option.some.inj (hn₀.symm.trans (hj ▸ hn))
    have hj' : j' = acc.ren.length := hj.trans hs.1.1.symm
    rw [hj', show j = acc.ren.length from hs.1.1.symm]
    exact simV_new_k0 P ok hk τ Uf hexp (hnn ▸ hq)

/-- The first flat substitution of the nested instance represents the references of `g₁`
by their renamed sources. -/
theorem rel_k0 (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph}
    (wf₂ : g₂.WF fun k => sigOf (nestPkgs P k0 g₁ k)) {j : Nat} {n : Inst} {acc : IAcc}
    {V U : Src → Impl} (hn : g₂.nodes[j]? = some n) (hP : nestPkgs P k0 g₁ n.pkg = g₁.toComp P)
    (hs : SimV (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ j acc V U) :
    ∀ s, g₁.Resolves (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k)) 0 s →
      (g₁.resolve (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k)) 0 s).subst
          ((g₁.iface fun k => sigOf (P k)).map fun p => V (n.src p.1)) =
        U (innerSrc (renInst acc.ren n) acc.nodes.length s)
  | .imp x, hx => by
    rw [subst_imp_map _ g₁ 0 (fun y => V (n.src y)) hx]
    show V (n.src x) = U ((renInst acc.ren n).src x)
    rw [renInst, src_ren]
    exact simV_rel hs _ (resolves_k0 P wf₂ hn hP hx)
  | .out _ _, ⟨_, _, h, _⟩ => absurd h (Nat.not_lt_zero _)

variable [CoreModule M]

/-- **One instance of the nested composition.** -/
theorem step_eq (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph} (ok : NestRunOk P k0 g₁ g₂)
    {j : Nat} {n : Inst} {acc : IAcc} {V U : Src → Impl} (eB : Nat)
    (hn : g₂.nodes[j]? = some n) (hk : n.pkg = k0)
    (hs : SimV (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ j acc V U) :
    (gRun (nestPkgs P k0 g₁) V eB j [n]).2.1 = (gRun P U eB acc.nodes.length
        (innerNodes (fun k => sigOf (P k)) g₁ (renInst acc.ren n) acc.nodes.length)).2.1 ∧
      (gRun (nestPkgs P k0 g₁) V eB j [n]).2.2 = (gRun P U eB acc.nodes.length
        (innerNodes (fun k => sigOf (P k)) g₁ (renInst acc.ren n) acc.nodes.length)).2.2 ∧
      SimV (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ (j + 1)
        (stepEq (fun k => sigOf (P k)) g₁ acc n) (gRun (nestPkgs P k0 g₁) V eB j [n]).1
        (gRun P U eB acc.nodes.length
          (innerNodes (fun k => sigOf (P k)) g₁ (renInst acc.ren n) acc.nodes.length)).1 := by
  have hP : nestPkgs P k0 g₁ n.pkg = g₁.toComp P := ite_eq_left_of_eq_true _ _ (eq_true hk)
  have hA := flatten_mkNodes P g₁ (g₁.iface fun k => sigOf (P k)) g₁.nodes 0
    ((g₁.iface fun k => sigOf (P k)).map fun p => V (n.src p.1)) eB
    (fun s => (g₁.resolve (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k)) 0 s).subst
      ((g₁.iface fun k => sigOf (P k)).map fun p => V (n.src p.1)))
    (List.drop_zero) (by simp [offset_zero]) (fun _ => rfl)
  have hb : ∀ x ∈ names (g₁.iface fun k => sigOf (P k)), ∀ t q,
      (renInst acc.ren n).src x = .out t q → t < acc.nodes.length :=
    fun x hx t q h => renSrc_out_lt hs.1 (resolves_k0 P ok.wf₂ hn hP hx)
      ((src_ren acc.ren n x).symm.trans h)
  have hC := sim_inner P g₁ (renInst acc.ren n) acc.nodes.length ok.wf₁ hb g₁.nodes 0 _ U eB
    (List.drop_zero) (rel_k0 P ok.wf₂ hn hP hs)
  have hexp : ∀ s, g₁.Resolves (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k))
      g₁.nodes.length s →
      (g₁.resolve (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k)) g₁.nodes.length s).subst
        (flattenNodes ((g₁.iface fun k => sigOf (P k)).map fun p => V (n.src p.1)) eB
          (g₁.mkNodes (fun k => sigOf (P k)) P (g₁.iface fun k => sigOf (P k)) 0 g₁.nodes)).1 =
      (gRun P U eB acc.nodes.length (g₁.nodes.map
        (innerInst (fun k => sigOf (P k)) (renInst acc.ren n) acc.nodes.length))).1
        (innerSrc (renInst acc.ren n) acc.nodes.length s) := fun s hs' => by
    rw [← Nat.zero_add g₁.nodes.length] at hs' ⊢
    exact (hA.2.2 s).trans (hC.2.2 s hs')
  rw [gRun_one, hP, innerNodes_eq]
  exact ⟨hA.1.trans hC.1, hA.2.1.trans hC.2.1, simV_eq_ext P ok hn hk hs _ _
    (fun x => gRun_stable P _ U eB _ (.imp x) fun _ _ h => Src.noConfusion h)
    (fun t q ht => gRun_stable P _ U eB _ (.out t q) fun _ _ h => (Src.out.inj h).1 ▸ ht)
    hexp⟩

/-- One instance of `g₂`, of either kind. -/
theorem step_all (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph} (ok : NestRunOk P k0 g₁ g₂)
    {j : Nat} {n : Inst} {acc : IAcc} {V U : Src → Impl} (eB : Nat)
    (hn : g₂.nodes[j]? = some n)
    (hs : SimV (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ j acc V U) :
    ∃ Δ, (inlineNode (fun k => sigOf (P k)) k0 g₁ acc n).nodes = acc.nodes ++ Δ ∧
      (gRun (nestPkgs P k0 g₁) V eB j [n]).2.1 = (gRun P U eB acc.nodes.length Δ).2.1 ∧
      (gRun (nestPkgs P k0 g₁) V eB j [n]).2.2 = (gRun P U eB acc.nodes.length Δ).2.2 ∧
      SimV (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ (j + 1)
        (inlineNode (fun k => sigOf (P k)) k0 g₁ acc n) (gRun (nestPkgs P k0 g₁) V eB j [n]).1
        (gRun P U eB acc.nodes.length Δ).1 := by
  by_cases hk : n.pkg = k0
  · rw [inlineNode_eq _ g₁ acc hk]
    exact ⟨_, rfl, step_eq P ok eB hn hk hs⟩
  · rw [inlineNode_ne _ g₁ acc hk]
    exact ⟨_, rfl, step_ne P ok.wf₂ eB hn hk hs⟩

theorem gRun_append' (P : Nat → Comp M) (l₁ l₂ : List Inst) (V : Src → Impl) (eB k : Nat) :
    gRun P V eB k (l₁ ++ l₂) =
      ((gRun P (gRun P V eB k l₁).1 (gRun P V eB k l₁).2.1 (k + l₁.length) l₂).1,
        (gRun P (gRun P V eB k l₁).1 (gRun P V eB k l₁).2.1 (k + l₁.length) l₂).2.1,
        (gRun P V eB k l₁).2.2 ++
          (gRun P (gRun P V eB k l₁).1 (gRun P V eB k l₁).2.1 (k + l₁.length) l₂).2.2) :=
  gRun_append P l₁ l₂ V eB k

/-- **The outer simulation.** -/
theorem sim_outer (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph} (ok : NestRunOk P k0 g₁ g₂) :
    ∀ (ns : List Inst) (j : Nat) (acc : IAcc) (V U : Src → Impl) (eB : Nat),
      g₂.nodes.drop j = ns →
      SimV (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ j acc V U →
      ∃ R, (ns.foldl (inlineNode (fun k => sigOf (P k)) k0 g₁) acc).nodes = acc.nodes ++ R ∧
        (gRun (nestPkgs P k0 g₁) V eB j ns).2.1 = (gRun P U eB acc.nodes.length R).2.1 ∧
        (gRun (nestPkgs P k0 g₁) V eB j ns).2.2 = (gRun P U eB acc.nodes.length R).2.2 ∧
        SimV (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ (j + ns.length)
          (ns.foldl (inlineNode (fun k => sigOf (P k)) k0 g₁) acc)
          (gRun (nestPkgs P k0 g₁) V eB j ns).1 (gRun P U eB acc.nodes.length R).1
  | [], j, acc, V, U, eB, _, hs => ⟨[], by simp, rfl, rfl, hs⟩
  | n :: ns, j, acc, V, U, eB, hd, hs => by
    obtain ⟨Δ, hΔ, h1, h2, hs₁⟩ := step_all P ok eB (getElem?_of_drop hd) hs
    obtain ⟨R', hR', i1, i2, hs₂⟩ := sim_outer P ok ns (j + 1) _ _ _
      (gRun (nestPkgs P k0 g₁) V eB j [n]).2.1 (drop_succ_of_drop hd) hs₁
    have hlen : (inlineNode (fun k => sigOf (P k)) k0 g₁ acc n).nodes.length =
        acc.nodes.length + Δ.length := by
      rw [hΔ, List.length_append]
    have hN := gRun_append' (nestPkgs P k0 g₁) [n] ns V eB j
    have hI := gRun_append' P Δ R' U eB acc.nodes.length
    have hj : j + (n :: ns).length = j + 1 + ns.length := by simp; omega
    refine ⟨Δ ++ R', by rw [List.foldl_cons, hR', hΔ, List.append_assoc], ?_, ?_, ?_⟩
    · show (gRun (nestPkgs P k0 g₁) V eB j ([n] ++ ns)).2.1 = _
      rw [hN, hI, List.length_singleton, ← h1, ← hlen]
      exact i1
    · show (gRun (nestPkgs P k0 g₁) V eB j ([n] ++ ns)).2.2 = _
      rw [hN, hI, List.length_singleton, ← h1, ← hlen, h2, i2]
    · show SimV _ _ g₂ (j + (n :: ns).length) _ (gRun (nestPkgs P k0 g₁) V eB j ([n] ++ ns)).1 _
      rw [hN, hI, List.length_singleton, ← h1, ← hlen, hj, List.foldl_cons]
      exact hs₂

end Silmaril.Wasm.Wac.NestProof
