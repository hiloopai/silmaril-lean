module

public import Silmaril.Proofs.Wasm.Component.Algebra.SeqGraph.Iface
public import Silmaril.Wasm.Wac.NestRun.Thms

/-!
# `wac plug` of arbitrary graphs: the two runs

The socket's instances are flattened twice: inside the nested component `g₂.toComp P` (the
positional side, valuation `V`), and as the plugged instances of `g₁.seq S g₂` (valuation
`U`, instance indices shifted by the plug's `m` instances). `gRun_sim` shows that the two
runs produce the same flat nodes, related by `Inv`: imports of the socket are, on the
positional side, what `Graph.plugSrc` sends them to on the plugged side, and the export `q`
of instance `j` is the export `q` of instance `j + m`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Algebra.SeqGraphProof

open Silmaril.Wasm.Component Silmaril.Wasm.Wac

variable {M : Type} [CoreModule M]

theorem subst_fwd {σ : List Impl} {r : Nat} {im : Impl} (h : σ[r]? = some im) :
    (Impl.fwd r).subst σ = im := by
  simp [Impl.subst, h]

/-- The relation between the valuations of the two runs. -/
def Inv (D : List String) (m : Nat) (f : Src → Src) (V U : Src → Impl) : Prop :=
  (∀ x ∈ D, V (.imp x) = U (f (.imp x))) ∧ ∀ j q, V (.out j q) = U (.out (j + m) q)

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

omit [CoreModule M] in
/-- Extending both valuations at corresponding instances keeps them related. -/
theorem inv_extV {D : List String} {m : Nat} {f : Src → Src}
    (hD : ∀ x ∈ D, ∃ t q, f (.imp x) = .out t q ∧ t < m) {V U : Src → Impl}
    (hI : Inv D m f V U) (j : Nat) (xs : List Export) (σ : List Impl) :
    Inv D m f (extV V j xs σ) (extV U (j + m) xs σ) := by
  refine ⟨fun x hx => ?_, fun j' q => ?_⟩
  · obtain ⟨t, q, he, ht⟩ := hD x hx
    have hne : ¬(t = j + m ∧ q ∈ xs.map Export.name) := fun h => by omega
    show V (.imp x) = _
    rw [hI.1 x hx, he]
    simp only [extV, hne, ↓reduceIte]
  · by_cases hj : j' = j
    · subst hj
      simp only [extV, true_and]
      by_cases hq : q ∈ xs.map Export.name
      · simp only [hq, ↓reduceIte]
      · simp only [hq, ↓reduceIte]
        exact hI.2 j' q
    · have hne : ¬(j' = j ∧ q ∈ xs.map Export.name) := fun h => hj h.1
      have hne' : ¬(j' + m = j + m ∧ q ∈ xs.map Export.name) := fun h => hj (by omega)
      simp only [extV, hne, hne', ↓reduceIte]
      exact hI.2 j' q

omit [CoreModule M] in
/-- The arguments of a plugged instance have, on the plugged side, the values of the
original instance's arguments on the positional side. -/
theorem args_sim (P : Nat → Comp M) (f : Src → Src) {D : List String} {m : Nat}
    (hf : ∀ j q, f (.out j q) = .out (j + m) q) {V U : Src → Impl} (hI : Inv D m f V U)
    (n : Inst) (hs : ∀ p ∈ (P n.pkg).imports, ∀ x, n.src p.1 = .imp x → x ∈ D) :
    ((P n.pkg).imports.map fun p =>
        U ((Inst.mapSrc f (Inst.explicate (fun k => sigOf (P k)) n)).src p.1)) =
      (P n.pkg).imports.map fun p => V (n.src p.1) := by
  refine List.map_congr_left fun p hp => ?_
  have hp' : p ∈ (sigOf (P n.pkg)).imports := hp
  rw [src_plug (fun k => sigOf (P k)) f n hp']
  cases h : n.src p.1 with
  | imp x => exact (hI.1 x (hs p hp x h)).symm
  | out k q => rw [hf]; exact (hI.2 k q).symm

/-- **The two runs of the socket's instances agree.** -/
theorem gRun_sim (P : Nat → Comp M) (f : Src → Src) {D : List String} {m : Nat}
    (hf : ∀ j q, f (.out j q) = .out (j + m) q)
    (hD : ∀ x ∈ D, ∃ t q, f (.imp x) = .out t q ∧ t < m) :
    ∀ (ns : List Inst) (j : Nat) (V U : Src → Impl) (eB : Nat),
      (∀ n ∈ ns, ∀ p ∈ (P n.pkg).imports, ∀ x, n.src p.1 = .imp x → x ∈ D) →
      Inv D m f V U →
      (gRun P V eB j ns).2 = (gRun P U eB (j + m)
          (ns.map fun n => Inst.mapSrc f (Inst.explicate (fun k => sigOf (P k)) n))).2 ∧
      Inv D m f (gRun P V eB j ns).1 (gRun P U eB (j + m)
          (ns.map fun n => Inst.mapSrc f (Inst.explicate (fun k => sigOf (P k)) n))).1
  | [], _, _, _, _, _, hI => ⟨rfl, hI⟩
  | n :: ns, j, V, U, eB, hs, hI => by
    have ha := args_sim P f hf hI n (hs n List.mem_cons_self)
    have hI' := inv_extV hD hI j (P n.pkg).exports
      (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).1
    have ih := gRun_sim P f hf hD ns (j + 1) _ _
      (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).2.1
      (fun n' hn' => hs n' (List.mem_cons_of_mem _ hn')) hI'
    have hk : j + 1 + m = j + m + 1 := by omega
    rw [hk] at ih
    rw [List.map_cons, gRun_cons, gRun_cons]
    have hpkg : (Inst.mapSrc f (Inst.explicate (fun k => sigOf (P k)) n)).pkg = n.pkg := rfl
    rw [hpkg, ha]
    exact ⟨by rw [ih.1], ih.2⟩

/-- A run leaves the valuation unchanged at instances after its last one. -/
theorem gRun_above (P : Nat → Comp M) :
    ∀ (ns : List Inst) (V : Src → Impl) (eB k t : Nat) (q : String), k + ns.length ≤ t →
      (gRun P V eB k ns).1 (.out t q) = V (.out t q)
  | [], _, _, _, _, _, _ => rfl
  | n :: ns, V, eB, k, t, q, h => by
    have h' : k + 1 + ns.length ≤ t := by simp at h; omega
    rw [gRun_cons]
    simp only
    rw [gRun_above P ns _ _ (k + 1) t q h']
    have hne : ¬(t = k ∧ q ∈ (P n.pkg).exports.map Export.name) := fun h₂ => by
      simp at h; omega
    simp only [extV, hne, ↓reduceIte]

end Silmaril.Wasm.Component.Algebra.SeqGraphProof
