module

public import Silmaril.Wasm.Wac.NestRun.Defs
public import Silmaril.Proofs.Wasm.Wac.Graph

/-!
# Flattening a composition graph is a run over valuations

* `flatten_buildWith`: flattening `Graph.buildWith` is `gRun` from `baseV`, with the
  exports read off the final valuation;
* `gRun_append`, `gRun_stable`: runs compose, and leave the valuation unchanged below
  their first instance.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.NestProof

open Silmaril.Wasm.Component

variable {M : Type}

/-! ## Substitution -/

theorem subst_fwd_of_get {σ : List Impl} {r : Nat} {im : Impl} (h : σ[r]? = some im) :
    (Impl.fwd r).subst σ = im := by
  simp [Impl.subst, h]

theorem subst_append_of_scoped {e : Nat} {im : Impl} (h : im.Scoped e) {σ : List Impl}
    (hσ : e ≤ σ.length) (E : List Impl) : im.subst (σ ++ E) = im.subst σ := by
  unfold Impl.subst
  unfold Impl.Scoped at h
  split
  · next r hr =>
    rw [hr] at h
    rw [List.getElem?_append_left (by omega)]
  · rfl

/-! ## Offsets -/

theorem offset_zero (S : Nat → PkgSig) (g : Graph) : g.offset S 0 = 0 := by
  simp [Graph.offset]

theorem offset_succ (S : Nat → PkgSig) (g : Graph) {j : Nat} {n : Inst}
    (h : g.nodes[j]? = some n) : g.offset S (j + 1) = g.offset S j + (S n.pkg).exports.length := by
  simp [Graph.offset, List.take_add_one, h]

theorem offset_le_succ (S : Nat → PkgSig) (g : Graph) (j : Nat) :
    g.offset S j ≤ g.offset S (j + 1) := by
  simp only [Graph.offset, List.take_add_one, List.map_append, List.sum_append]
  omega

theorem offset_mono (S : Nat → PkgSig) (g : Graph) {a b : Nat} (h : a ≤ b) :
    g.offset S a ≤ g.offset S b := by
  induction b with
  | zero => rw [Nat.le_zero.1 h]
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · exact Nat.le_trans (ih (Nat.le_of_lt_succ h')) (offset_le_succ S g b)
    · rw [h']

theorem idxOf_lt {l : List String} {q : String} (h : q ∈ l) : l.idxOf q < l.length :=
  List.idxOf_lt_length_iff.2 h

theorem resolve_imp_scoped (S : Nat → PkgSig) (g : Graph) (I : Iface) (b : Nat) (x : String) :
    (g.resolve S I b (.imp x)).Scoped (I.length + g.offset S b) := by
  simp only [Graph.resolve]
  split
  · next hx =>
    have h : (names I).idxOf x < I.length := by simpa [names] using idxOf_lt hx
    exact show (names I).idxOf x < I.length + g.offset S b by omega
  · trivial

theorem resolve_out_scoped (S : Nat → PkgSig) (g : Graph) (I : Iface) (b j : Nat) (q : String) :
    (g.resolve S I b (.out j q)).Scoped (I.length + g.offset S b) := by
  simp only [Graph.resolve]
  split
  · next n hn =>
    split
    · next hq =>
      have h1 : g.offset S (j + 1) = g.offset S j + (S n.pkg).exports.length :=
        offset_succ S g hn
      have h2 : g.offset S (j + 1) ≤ g.offset S b := offset_mono S g hq.1
      have h3 : (names (S n.pkg).exports).idxOf q < (S n.pkg).exports.length := by
        simpa [names] using idxOf_lt hq.2
      exact show I.length + g.offset S j + (names (S n.pkg).exports).idxOf q <
        I.length + g.offset S b by omega
    · trivial
  · trivial

/-- A reference resolved below `b` calls a function below `|I| + offset b`. -/
theorem resolve_scoped (S : Nat → PkgSig) (g : Graph) (I : Iface) (b : Nat) :
    ∀ s : Src, (g.resolve S I b s).Scoped (I.length + g.offset S b)
  | .imp x => resolve_imp_scoped S g I b x
  | .out j q => resolve_out_scoped S g I b j q

theorem resolve_imp_bound (S : Nat → PkgSig) (g : Graph) (I : Iface) (b b' : Nat) (x : String) :
    g.resolve S I b (.imp x) = g.resolve S I b' (.imp x) := rfl

theorem resolve_succ_ne (S : Nat → PkgSig) (g : Graph) (I : Iface) {j k : Nat} (h : j ≠ k)
    (q : String) : g.resolve S I (k + 1) (.out j q) = g.resolve S I k (.out j q) := by
  have hiff : (j < k + 1) ↔ j < k := by omega
  simp only [Graph.resolve, hiff]

theorem resolve_self (S : Nat → PkgSig) (g : Graph) (I : Iface) (k : Nat) (q : String) :
    g.resolve S I k (.out k q) = .trap := by
  simp only [Graph.resolve, Nat.lt_irrefl, false_and, ↓reduceIte]
  split <;> rfl

/-! ## Extending valuations -/

theorem extV_imp (V : Src → Impl) (k : Nat) (xs : List Export) (σ : List Impl) (x : String) :
    extV V k xs σ (.imp x) = V (.imp x) := rfl

theorem extV_ne (V : Src → Impl) {j k : Nat} (h : j ≠ k) (xs : List Export) (σ : List Impl)
    (q : String) : extV V k xs σ (.out j q) = V (.out j q) := by
  simp [extV, h]

theorem extV_self (V : Src → Impl) (k : Nat) {xs : List Export} {q : String}
    (h : q ∈ xs.map Export.name) (σ : List Impl) : extV V k xs σ (.out k q) = expImpl xs σ q := by
  simp [extV, h]

theorem extV_not_mem (V : Src → Impl) (k : Nat) {xs : List Export} {q : String}
    (h : q ∉ xs.map Export.name) (σ : List Impl) : extV V k xs σ (.out k q) = V (.out k q) := by
  simp [extV, h]

theorem names_sigOf (c : Comp M) : names (sigOf c).exports = c.exports.map Export.name := by
  simp [sigOf, names]

/-- The export `q` of the flat environment extended by the exports `xs`. -/
theorem subst_append_export {σ : List Impl} {xs : List Export} {q : String}
    (h : q ∈ xs.map Export.name) (τ : List Impl) :
    (Impl.fwd (σ.length + (xs.map Export.name).idxOf q)).subst
      (σ ++ xs.map fun x => x.impl.subst τ) = expImpl xs τ q := by
  have hl : (xs.map Export.name).idxOf q < xs.length := by simpa using idxOf_lt h
  have hg : (σ ++ xs.map fun x => x.impl.subst τ)[σ.length + (xs.map Export.name).idxOf q]? =
      some ((xs.map fun x => x.impl.subst τ)[(xs.map Export.name).idxOf q]'(by simpa using hl)) := by
    rw [List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    exact List.getElem?_eq_getElem _
  rw [subst_fwd_of_get hg, expImpl, List.getElem?_eq_getElem (by simpa using hl), Option.getD_some]

/-- The representation of a valuation by a flat substitution survives an instance. -/
theorem rep_step (P : Nat → Comp M) (g : Graph) (I : Iface) {k : Nat} {n : Inst}
    {σ τ : List Impl} {V : Src → Impl} (hn : g.nodes[k]? = some n)
    (hlen : σ.length = I.length + g.offset (fun k => sigOf (P k)) k)
    (hV : ∀ s, (g.resolve (fun k => sigOf (P k)) I k s).subst σ = V s) :
    ∀ s, (g.resolve (fun k => sigOf (P k)) I (k + 1) s).subst
        (σ ++ (P n.pkg).exports.map fun x => x.impl.subst τ) = extV V k (P n.pkg).exports τ s
  | .imp x => by
    rw [extV_imp, ← hV, resolve_imp_bound _ g I (k + 1) k]
    exact subst_append_of_scoped (resolve_scoped _ g I k _) (by omega) _
  | .out j q => by
    by_cases hj : j = k
    · rw [hj]
      by_cases hq : q ∈ (P n.pkg).exports.map Export.name
      · have hr : g.resolve (fun k => sigOf (P k)) I (k + 1) (.out k q) =
            .fwd (σ.length + ((P n.pkg).exports.map Export.name).idxOf q) := by
          simp [Graph.resolve, hn, hlen, names_sigOf, hq, Nat.add_assoc]
        rw [hr, subst_append_export hq, extV_self _ _ hq]
      · have hr : g.resolve (fun k => sigOf (P k)) I (k + 1) (.out k q) = .trap := by
          simp [Graph.resolve, hn, names_sigOf, hq]
        rw [hr, extV_not_mem _ _ hq, ← hV, resolve_self]
        rfl
    · rw [extV_ne _ hj, ← hV, resolve_succ_ne _ g I hj]
      exact subst_append_of_scoped (resolve_scoped _ g I k _) (by omega) _

/-! ## Flattening -/

theorem range_map_args {α : Type} (I : List α) (f : α → Impl) (σ : List Impl) :
    ((List.range I.length).map fun i => ((I.map f)[i]?.getD .trap).subst σ) =
      I.map fun p => (f p).subst σ := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have hi : i < I.length := by simpa using h2
  simp [hi]

theorem getElem?_of_drop {l : List Inst} {k : Nat} {n : Inst} {ns : List Inst}
    (h : l.drop k = n :: ns) : l[k]? = some n := by
  rw [← List.head?_drop, h]
  rfl

theorem drop_succ_of_drop {l : List Inst} {k : Nat} {n : Inst} {ns : List Inst}
    (h : l.drop k = n :: ns) : l.drop (k + 1) = ns := by
  rw [← List.drop_drop, h]
  rfl

/-- One instance of `flatten_mkNodes`: the flat imports of the instance agree. -/
theorem argsOf_subst (P : Nat → Comp M) (g : Graph) (I : Iface) {k : Nat} {n : Inst}
    {σ : List Impl} {V : Src → Impl}
    (hV : ∀ s, (g.resolve (fun k => sigOf (P k)) I k s).subst σ = V s) :
    ((List.range (P n.pkg).imports.length).map fun i =>
        ((g.argsOf (fun k => sigOf (P k)) I k n)[i]?.getD .trap).subst σ) =
      (P n.pkg).imports.map fun p => V (n.src p.1) := by
  rw [show g.argsOf (fun k => sigOf (P k)) I k n =
      (P n.pkg).imports.map fun p => g.resolve (fun k => sigOf (P k)) I k (n.src p.1) from rfl,
    range_map_args]
  exact List.map_congr_left fun p _ => hV _

variable [CoreModule M]

theorem flattenNodes_inst (σ : List Impl) (eB : Nat) (c : Comp M) (args : List Impl)
    (ns : List (Node M)) :
    flattenNodes σ eB (.inst c args :: ns) =
      let rc := flattenNodes ((List.range c.imports.length).map fun i =>
        (args[i]?.getD .trap).subst σ) eB c.nodes
      let r := flattenNodes (σ ++ c.exports.map fun x => x.impl.subst rc.1) rc.2.1 ns
      (r.1, r.2.1, rc.2.2 ++ r.2.2) := by
  cases c
  rw [flattenNodes]
  rfl

/-- **Flattening the instances of a graph is a run over valuations.** -/
theorem flatten_mkNodes (P : Nat → Comp M) (g : Graph) (I : Iface) :
    ∀ (ns : List Inst) (k : Nat) (σ : List Impl) (eB : Nat) (V : Src → Impl),
      g.nodes.drop k = ns → σ.length = I.length + g.offset (fun k => sigOf (P k)) k →
      (∀ s, (g.resolve (fun k => sigOf (P k)) I k s).subst σ = V s) →
      (flattenNodes σ eB (g.mkNodes (fun k => sigOf (P k)) P I k ns)).2.1 =
          (gRun P V eB k ns).2.1 ∧
        (flattenNodes σ eB (g.mkNodes (fun k => sigOf (P k)) P I k ns)).2.2 =
          (gRun P V eB k ns).2.2 ∧
        ∀ s, (g.resolve (fun k => sigOf (P k)) I (k + ns.length) s).subst
          (flattenNodes σ eB (g.mkNodes (fun k => sigOf (P k)) P I k ns)).1 = (gRun P V eB k ns).1 s
  | [], k, σ, eB, V, _, _, hV => by
    simp only [Graph.mkNodes, flattenNodes, gRun, List.length_nil, Nat.add_zero]
    exact ⟨trivial, trivial, hV⟩
  | n :: ns, k, σ, eB, V, hd, hlen, hV => by
    have hn : g.nodes[k]? = some n := getElem?_of_drop hd
    have hargs := argsOf_subst P g I (n := n) hV
    have hlen' : (σ ++ (P n.pkg).exports.map fun x => x.impl.subst
        (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).1).length =
        I.length + g.offset (fun k => sigOf (P k)) (k + 1) := by
      simp [offset_succ _ g hn, hlen, sigOf, Nat.add_assoc]
    have ih := flatten_mkNodes P g I ns (k + 1) _
      (flattenNodes ((P n.pkg).imports.map fun p => V (n.src p.1)) eB (P n.pkg).nodes).2.1 _
      (drop_succ_of_drop hd) hlen'
      (rep_step P g I hn hlen hV)
    have hk : k + (n :: ns).length = k + 1 + ns.length := by simp; omega
    simp only [Graph.mkNodes, flattenNodes_inst, hargs, gRun, hk]
    exact ⟨ih.1, by rw [ih.2.1], ih.2.2⟩

theorem resolve_zero_subst (S : Nat → PkgSig) (g : Graph) (I : Iface) (s : Src) :
    (g.resolve S I 0 s).subst ((List.range I.length).map Impl.fwd) = baseV I s := by
  cases s with
  | imp x =>
    by_cases hx : x ∈ names I
    · have hl : (names I).idxOf x < I.length := by simpa [names] using idxOf_lt hx
      simp only [Graph.resolve, baseV, hx, ↓reduceIte]
      exact subst_fwd_of_get (by simp [hl])
    · simp only [Graph.resolve, baseV, hx, ↓reduceIte]
      rfl
  | out j q =>
    simp only [Graph.resolve, Nat.not_lt_zero, false_and, ↓reduceIte, baseV]
    split <;> rfl

/-- **Flattening a composition** is the run of its instances from `baseV`. -/
theorem flatten_buildWith (P : Nat → Comp M) (g : Graph) (I : Iface) :
    flatten (g.buildWith (fun k => sigOf (P k)) P I) =
      ⟨I, (gRun P (baseV I) I.length 0 g.nodes).2.2,
        g.exports.map fun p => ⟨p.1, g.tyOf (fun k => sigOf (P k)) I p.2,
          (gRun P (baseV I) I.length 0 g.nodes).1 p.2⟩⟩ := by
  have hA := flatten_mkNodes P g I g.nodes 0 ((List.range I.length).map Impl.fwd) I.length
    (baseV I) (by simp) (by simp [offset_zero]) (resolve_zero_subst _ g I)
  have hx : ∀ p ∈ g.exports, (g.resolve (fun k => sigOf (P k)) I g.nodes.length p.2).subst
      (flattenNodes ((List.range I.length).map Impl.fwd) I.length
        (g.mkNodes (fun k => sigOf (P k)) P I 0 g.nodes)).1 =
      (gRun P (baseV I) I.length 0 g.nodes).1 p.2 := fun p _ => by
    simpa using hA.2.2 p.2
  simp only [Graph.buildWith, flatten, Graph.mkExports, List.map_map]
  rw [hA.2.1]
  congr 1
  exact List.map_congr_left fun p hp => by simp [hx p hp]

/-! ## Runs -/

theorem gRun_append (P : Nat → Comp M) :
    ∀ (l₁ l₂ : List Inst) (V : Src → Impl) (eB k : Nat),
      gRun P V eB k (l₁ ++ l₂) =
        let r₁ := gRun P V eB k l₁
        let r₂ := gRun P r₁.1 r₁.2.1 (k + l₁.length) l₂
        (r₂.1, r₂.2.1, r₁.2.2 ++ r₂.2.2)
  | [], l₂, V, eB, k => by simp [gRun]
  | n :: l₁, l₂, V, eB, k => by
    have ih := gRun_append P l₁ l₂
    have hk : k + 1 + l₁.length = k + (n :: l₁).length := by simp; omega
    simp only [List.cons_append, gRun, ih, hk, List.append_assoc]

/-- A run leaves the valuation unchanged at the imports and below its first instance. -/
theorem gRun_stable (P : Nat → Comp M) :
    ∀ (ns : List Inst) (V : Src → Impl) (eB k : Nat) (s : Src),
      (∀ t q, s = .out t q → t < k) → (gRun P V eB k ns).1 s = V s
  | [], _, _, _, _, _ => rfl
  | n :: ns, V, eB, k, s, hs => by
    have h' : ∀ t q, s = .out t q → t < k + 1 := fun t q h => Nat.lt_succ_of_lt (hs t q h)
    rw [show (gRun P V eB k (n :: ns)).1 = (gRun P _ _ (k + 1) ns).1 from rfl,
      gRun_stable P ns _ _ (k + 1) s h']
    cases s with
    | imp x => rfl
    | out t q => exact extV_ne V (Nat.ne_of_lt (hs t q rfl)) _ _ q

end Silmaril.Wasm.Wac.NestProof
