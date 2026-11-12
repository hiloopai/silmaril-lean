module

public import Silmaril.Proofs.Wasm.Wac.Nest.Run
public import Silmaril.Proofs.Wasm.Wac.Nest.Ren

/-!
# Nesting = inlining: the simulation between the two runs

* `sim_inner`: the run over the instances of `g₁` inside the nested instance (over the
  valuation `W` of `g₁`'s references) and the run over the inlined instances (over the
  valuation `U` of the inlined graph) agree, under `W s = U (innerSrc n' base s)`;
* `step_ne`, `step_eq`: one instance of `g₂` and its inlined nodes keep `SimV`;
* `sim_outer`: the runs over `g₂` (packages `nestPkgs P k0 g₁`) and over the inlined
  graph (packages `P`) agree.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.NestProof

open Silmaril.Wasm.Component

variable {M : Type}

theorem extV_keep (V : Src → Impl) {k : Nat} (xs : List Export) (σ : List Impl) {s : Src}
    (h : ∀ t q, s = .out t q → t ≠ k) : extV V k xs σ s = V s := by
  cases s with
  | imp x => rfl
  | out t q => exact extV_ne V (h t q rfl) xs σ q

/-- The inlined instance of an instance `m` of `g₁`. -/
def innerInst (S : Nat → PkgSig) (n' : Inst) (base : Nat) (m : Inst) : Inst :=
  ⟨m.pkg, (m.explicate S).args.map fun a => (a.1, innerSrc n' base a.2)⟩

@[simp] theorem innerInst_pkg (S : Nat → PkgSig) (n' : Inst) (base : Nat) (m : Inst) :
    (innerInst S n' base m).pkg = m.pkg := rfl

theorem innerNodes_eq (S : Nat → PkgSig) (g₁ : Graph) (n' : Inst) (base : Nat) :
    innerNodes S g₁ n' base = g₁.nodes.map (innerInst S n' base) := by
  simp only [innerNodes, Graph.explicate, List.map_map]
  rfl

/-- The relation of `sim_inner` survives an instance. -/
theorem rel_inner_step (P : Nat → Comp M) {g₁ : Graph} {n' : Inst} {base i : Nat} {m : Inst}
    {W U : Src → Impl} (τ : List Impl) (hm : g₁.nodes[i]? = some m)
    (hb : ∀ x ∈ names (g₁.iface fun k => sigOf (P k)), ∀ t q, n'.src x = .out t q → t < base)
    (hr : ∀ s, g₁.Resolves (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k)) i s →
      W s = U (innerSrc n' base s)) :
    ∀ s, g₁.Resolves (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k)) (i + 1) s →
      extV W i (P m.pkg).exports τ s = extV U (base + i) (P m.pkg).exports τ (innerSrc n' base s)
  | .imp x, hx => by
    have hkeep : extV U (base + i) (P m.pkg).exports τ (n'.src x) = U (n'.src x) :=
      extV_keep U _ τ fun t q h => Nat.ne_of_lt (Nat.lt_of_lt_of_le (hb x hx t q h) (by omega))
    show W (.imp x) = extV U (base + i) (P m.pkg).exports τ (n'.src x)
    rw [hkeep]
    exact hr (.imp x) hx
  | .out j q, ⟨n, hn, hj, hq⟩ => by
    rcases lt_or_eq_of_lt_succ' hj with hj | hj
    · show extV W i _ τ (.out j q) = extV U (base + i) _ τ (.out (base + j) q)
      rw [extV_ne W (Nat.ne_of_lt hj), extV_ne U (by omega)]
      exact hr (.out j q) ⟨n, hn, hj, hq⟩
    · have hnm : n = m := Option.some.inj (hn.symm.trans (hj ▸ hm))
      have hq' : q ∈ (P m.pkg).exports.map Export.name := by
        rw [← names_sigOf, ← hnm]
        exact hq
      show extV W i _ τ (.out j q) = extV U (base + i) _ τ (.out (base + j) q)
      rw [hj, extV_self _ _ hq', extV_self _ _ hq']

variable [CoreModule M]

theorem gRun_cons (P : Nat → Comp M) (V : Src → Impl) (eB k : Nat) (n : Inst) (ns : List Inst) :
    gRun P V eB k (n :: ns) =
      ((gRun P (extV V k (P n.pkg).exports
          (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).1)
          (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).2.1
          (k + 1) ns).1,
        (gRun P (extV V k (P n.pkg).exports
          (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).1)
          (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).2.1
          (k + 1) ns).2.1,
        (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).2.2 ++
          (gRun P (extV V k (P n.pkg).exports
            (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).1)
            (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).2.1
            (k + 1) ns).2.2) := rfl

/-- Two runs whose first instances have the same package and the same flat imports. -/
theorem gRun_cons_congr (P : Nat → Comp M) {V U : Src → Impl} (eB : Nat) (k' : Nat)
    {n n' : Inst} (hp : n'.pkg = n.pkg)
    (hσ : ((P n.pkg).imports.map fun p => V (n.src p.1)) =
      (P n.pkg).imports.map fun p => U (n'.src p.1)) (ns' : List Inst) :
    gRun P U eB k' (n' :: ns') =
      ((gRun P (extV U k' (P n.pkg).exports
          (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).1)
          (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).2.1
          (k' + 1) ns').1,
        (gRun P (extV U k' (P n.pkg).exports
          (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).1)
          (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).2.1
          (k' + 1) ns').2.1,
        (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).2.2 ++
          (gRun P (extV U k' (P n.pkg).exports
            (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).1)
            (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).2.1
            (k' + 1) ns').2.2) := by
  rw [gRun_cons, hp, ← hσ]

/-- **The inner simulation**: the instances of `g₁`, run inside the nested instance and
inlined. -/
theorem sim_inner (P : Nat → Comp M) (g₁ : Graph) (n' : Inst) (base : Nat)
    (wf₁ : g₁.WF fun k => sigOf (P k))
    (hb : ∀ x ∈ names (g₁.iface fun k => sigOf (P k)), ∀ t q, n'.src x = .out t q → t < base) :
    ∀ (ms : List Inst) (i : Nat) (W U : Src → Impl) (eB : Nat), g₁.nodes.drop i = ms →
      (∀ s, g₁.Resolves (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k)) i s →
        W s = U (innerSrc n' base s)) →
      (gRun P W eB i ms).2.1 =
          (gRun P U eB (base + i) (ms.map (innerInst (fun k => sigOf (P k)) n' base))).2.1 ∧
        (gRun P W eB i ms).2.2 =
          (gRun P U eB (base + i) (ms.map (innerInst (fun k => sigOf (P k)) n' base))).2.2 ∧
        ∀ s, g₁.Resolves (fun k => sigOf (P k)) (g₁.iface fun k => sigOf (P k)) (i + ms.length) s →
          (gRun P W eB i ms).1 s =
            (gRun P U eB (base + i) (ms.map (innerInst (fun k => sigOf (P k)) n' base))).1
              (innerSrc n' base s)
  | [], i, W, U, eB, _, hr => ⟨rfl, rfl, fun s h => hr s (by simpa using h)⟩
  | m :: ms, i, W, U, eB, hd, hr => by
    have hm : g₁.nodes[i]? = some m := getElem?_of_drop hd
    have hσ : ((P m.pkg).imports.map fun p => W (m.src p.1)) =
        (P m.pkg).imports.map fun p => U ((innerInst (fun k => sigOf (P k)) n' base m).src p.1) :=
      List.map_congr_left fun p hp => by
        rw [innerInst, src_inner (fun k => sigOf (P k)) n' base m (List.mem_map_of_mem hp)]
        exact hr _ (wf₁.1 i m hm p hp)
    have hU := gRun_cons_congr P eB (base + i) (innerInst_pkg _ n' base m) hσ
      (ms.map (innerInst (fun k => sigOf (P k)) n' base))
    have ih := sim_inner P g₁ n' base wf₁ hb ms (i + 1) _ _
      (flattenNodes ((P m.pkg).imports.map fun p => W (m.src p.1)) eB (P m.pkg).nodes).2.1
      (drop_succ_of_drop hd)
      (rel_inner_step P (flattenNodes ((P m.pkg).imports.map fun p => W (m.src p.1)) eB
        (P m.pkg).nodes).1 hm hb hr)
    have hbi : base + i + 1 = base + (i + 1) := by omega
    have hl : i + (m :: ms).length = i + 1 + ms.length := by simp; omega
    rw [List.map_cons, hU, gRun_cons, hbi, hl]
    exact ⟨ih.1, by rw [ih.2.1], ih.2.2⟩

end Silmaril.Wasm.Wac.NestProof
