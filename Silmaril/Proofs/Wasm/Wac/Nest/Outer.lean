module

public import Silmaril.Proofs.Wasm.Wac.Nest.Sim

/-!
# Nesting = inlining: the outer simulation

* `step_ne`, `step_eq`: an instance of `g₂` (of another package, or of the nested
  composition `k0`) and its nodes in the inlined graph keep `SimV`;
* `sim_outer`: the runs over `g₂` (packages `nestPkgs P k0 g₁`) and over the inlined graph
  (packages `P`) produce the same flat nodes, and their final valuations are related by
  the final renaming.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.NestProof

open Silmaril.Wasm.Component

variable {M : Type}

theorem simV_rel {S S' : Nat → PkgSig} {g₂ : Graph} {j : Nat} {acc : IAcc} {V U : Src → Impl}
    (hs : SimV S S' g₂ j acc V U) {I : Iface} :
    ∀ s, g₂.Resolves S' I j s → V s = U (renSrc acc.ren s)
  | .imp x, _ => hs.2.1 x
  | .out j' q, ⟨n, hn, hj, hq⟩ => hs.2.2 j' n q hn hj hq

theorem renSrc_out_lt {S S' : Nat → PkgSig} {g₂ : Graph} {acc : IAcc} {j : Nat}
    (hr : RenOk S S' g₂ acc j) {I : Iface} :
    ∀ {s : Src} {t : Nat} {q : String}, g₂.Resolves S' I j s → renSrc acc.ren s = .out t q →
      t < acc.nodes.length
  | .imp _, _, _, _, h => Src.noConfusion h
  | .out j' q₀, t, q, ⟨n, hn, hj, hq⟩, h => by
    obtain ⟨t', q', m, h', hm, _, _⟩ := hr.2 j' n q₀ hn hj hq
    have ht : t' = t := (Src.out.inj (h'.symm.trans h)).1
    exact ht ▸ (List.getElem?_eq_some_iff.1 hm).1

/-- The exports of earlier instances keep their relation when both runs go on. -/
theorem simV_old {S S' : Nat → PkgSig} {g₂ : Graph} {j : Nat} {acc : IAcc} {V U : Src → Impl}
    (hs : SimV S S' g₂ j acc V U) {V' U' : Src → Impl} (f : String → Src)
    (hV : ∀ j' q, j' < j → V' (.out j' q) = V (.out j' q))
    (hU : ∀ t q, t < acc.nodes.length → U' (.out t q) = U (.out t q)) :
    ∀ j' n q, g₂.nodes[j']? = some n → j' < j → q ∈ names (S' n.pkg).exports →
      V' (.out j' q) = U' (renSrc (acc.ren ++ [f]) (.out j' q)) := by
  intro j' n q hn hj hq
  obtain ⟨t, q', m, hren, hm, _, _⟩ := hs.1.2 j' n q hn hj hq
  have hj' : j' < acc.ren.length := hs.1.1 ▸ hj
  have ht : t < acc.nodes.length := (List.getElem?_eq_some_iff.1 hm).1
  rw [renSrc_append_lt _ _ hj', hren, hU t q' ht, hV j' q hj, hs.2.2 j' n q hn hj hq, hren]

theorem names_mkExports (S : Nat → PkgSig) (g : Graph) (I : Iface) :
    (g.mkExports S I).map Silmaril.Wasm.Component.Export.name = g.exports.map Prod.fst := by
  simp [Graph.mkExports]

theorem getElem_idxOf_map {β γ : Type} (F : β → γ) : ∀ (l : List (String × β)) (q : String),
    q ∈ l.map Prod.fst → (l.map fun p => F p.2)[(l.map Prod.fst).idxOf q]? = (l.lookup q).map F
  | [], _, h => by simp at h
  | (k, v) :: l, q, h => by
    by_cases hq : q = k
    · have hb : (q == k) = true := beq_iff_eq.2 hq
      have hb' : (k == q) = true := beq_iff_eq.2 hq.symm
      simp only [List.map_cons, List.idxOf_cons, hb', ↓reduceIte, List.lookup, hb,
        List.getElem?_cons_zero, Option.map_some]
    · have hb : (q == k) = false := beq_eq_false_iff_ne.2 hq
      have hb' : (k == q) = false := beq_eq_false_iff_ne.2 (Ne.symm hq)
      have h' : q ∈ l.map Prod.fst := by simpa [hq] using h
      simp only [List.map_cons, List.idxOf_cons, hb', List.lookup, hb, Bool.false_eq_true,
        ↓reduceIte, List.getElem?_cons_succ]
      exact getElem_idxOf_map F l q h'

/-- The export `q` of a composition, as a package. -/
theorem expImpl_mkExports (S : Nat → PkgSig) (g : Graph) (I : Iface) {q : String} {s : Src}
    (h : g.exports.lookup q = some s) (τ : List Impl) :
    expImpl (g.mkExports S I) τ q = (g.resolve S I g.nodes.length s).subst τ := by
  have hq : q ∈ g.exports.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) (mem_of_lookup h)
  have hl := getElem_idxOf_map (fun s => (g.resolve S I g.nodes.length s).subst τ) g.exports q hq
  simp only [expImpl, Graph.mkExports, List.map_map, Function.comp_def]
  rw [hl, h]
  rfl

theorem subst_imp_map (S : Nat → PkgSig) (g : Graph) {I : Iface} (b : Nat) (h : String → Impl)
    {x : String} (hx : x ∈ names I) :
    (g.resolve S I b (.imp x)).subst (I.map fun p => h p.1) = h x := by
  have hl : (names I).idxOf x < I.length := by simpa [names] using idxOf_lt hx
  have hget : (I.map fun p => h p.1)[(names I).idxOf x]? = some (h x) := by
    have h1 : (names I).idxOf x < (names I).length := by simpa [names] using hl
    have he : I[(names I).idxOf x].1 = x := by
      rw [← List.getElem_map Prod.fst]
      exact List.getElem_idxOf h1
    simp [hl, he]
  simp only [Graph.resolve, hx, ↓reduceIte]
  exact subst_fwd_of_get hget

/-- The extension at an instance of another package keeps `SimV`. -/
theorem simV_ne_ext (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph} {j : Nat} {n : Inst}
    {acc : IAcc} {V U : Src → Impl}
    (hs : SimV (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ j acc V U)
    (hn : g₂.nodes[j]? = some n) (hP : nestPkgs P k0 g₁ n.pkg = P n.pkg) (τ : List Impl) :
    SimV (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ (j + 1) (stepNe acc n)
      (extV V j (P n.pkg).exports τ) (extV U acc.nodes.length (P n.pkg).exports τ) := by
  refine ⟨renOk_step_ne hs.1 hn (congrArg sigOf hP), fun x => hs.2.1 x, ?_⟩
  intro j' n₀ q hn₀ hj hq
  rcases lt_or_eq_of_lt_succ' hj with hj | hj
  · exact simV_old hs _ (fun j' q h => extV_ne V (Nat.ne_of_lt h) _ _ q)
      (fun t q h => extV_ne U (Nat.ne_of_lt h) _ _ q) j' n₀ q hn₀ hj hq
  · have hnn : n₀ = n := Option.some.inj (hn₀.symm.trans (hj ▸ hn))
    have hq' : q ∈ (P n.pkg).exports.map Silmaril.Wasm.Component.Export.name := by
      rw [← names_sigOf, ← hP, ← hnn]
      exact hq
    have hself : renSrc (stepNe acc n).ren (.out j' q) = .out acc.nodes.length q := by
      rw [hj, ← hs.1.1]
      exact renSrc_append_self _ _ q
    rw [hself, hj, extV_self _ _ hq', extV_self _ _ hq']

variable [CoreModule M]

theorem gRun_one (P : Nat → Comp M) (V : Src → Impl) (eB k : Nat) (n : Inst) :
    gRun P V eB k [n] =
      (extV V k (P n.pkg).exports
          (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).1,
        (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).2.1,
        (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).2.2) := by
  simp [gRun]

/-- **One instance of another package.** -/
theorem step_ne (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph}
    (wf₂ : g₂.WF fun k => sigOf (nestPkgs P k0 g₁ k)) {j : Nat} {n : Inst} {acc : IAcc}
    {V U : Src → Impl} (eB : Nat) (hn : g₂.nodes[j]? = some n) (hk : n.pkg ≠ k0)
    (hs : SimV (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ j acc V U) :
    (gRun (nestPkgs P k0 g₁) V eB j [n]).2.1 = (gRun P U eB acc.nodes.length [renInst acc.ren n]).2.1 ∧
      (gRun (nestPkgs P k0 g₁) V eB j [n]).2.2 =
        (gRun P U eB acc.nodes.length [renInst acc.ren n]).2.2 ∧
      SimV (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ (j + 1) (stepNe acc n)
        (gRun (nestPkgs P k0 g₁) V eB j [n]).1 (gRun P U eB acc.nodes.length [renInst acc.ren n]).1 := by
  have hP : nestPkgs P k0 g₁ n.pkg = P n.pkg := ite_eq_right_of_eq_false _ _ (eq_false hk)
  have hσ : ((P n.pkg).imports.map fun p => V (n.src p.1)) =
      (P n.pkg).imports.map fun p => U ((renInst acc.ren n).src p.1) :=
    List.map_congr_left fun p hp => by
      have hp' : p ∈ (sigOf (nestPkgs P k0 g₁ n.pkg)).imports := by rw [hP]; exact hp
      rw [renInst, src_ren]
      exact simV_rel hs _ (wf₂.1 j n hn p hp')
  have hR := gRun_cons_congr P eB acc.nodes.length (n := n) (n' := renInst acc.ren n) rfl hσ []
  rw [gRun_one, hP, hR]
  exact ⟨rfl, by simp [gRun], simV_ne_ext P hs hn hP _⟩

end Silmaril.Wasm.Wac.NestProof
