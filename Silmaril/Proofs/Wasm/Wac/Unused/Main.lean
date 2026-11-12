module

public import Silmaril.Wasm.Wac.Unused.Defs
public import Silmaril.Wasm.Wac.NestRun.Thms
public import Silmaril.Wasm.Component.Passes.Flatten.Thms

/-!
# Unused imports: the run over a smaller import list

* `gRun_agree`: two valuations that agree at the instances' exports and at the imports in `U`
  give runs with the same flat nodes, when the instances only refer to imports in `U`;
* `flatten_buildWith_sub`: a composition built over the imports `I` flattens to the
  specialisation, by `importPerm I J`, of the same composition built over `J ⊆ I`, when the
  graph refers only to imports in `J` and `I`, `J` give them the same types.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.UnusedProof

open Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

/-- Two valuations agree at every instance export and at the imports `U`. -/
def AgreeOn (U : List String) (V V' : Src → Impl) : Prop :=
  (∀ j q, V (.out j q) = V' (.out j q)) ∧ ∀ x ∈ U, V (.imp x) = V' (.imp x)

theorem agree_src {U : List String} {V V' : Src → Impl} (h : AgreeOn U V V') {s : Src}
    (hs : ∀ x, s = .imp x → x ∈ U) : V s = V' s := by
  cases s with
  | imp x => exact h.2 x (hs x rfl)
  | out j q => exact h.1 j q

theorem agree_extV {U : List String} {V V' : Src → Impl} (h : AgreeOn U V V') (k : Nat)
    (xs : List Silmaril.Wasm.Component.Export) (σ : List Impl) : AgreeOn U (extV V k xs σ) (extV V' k xs σ) := by
  refine ⟨fun j q => ?_, fun x hx => h.2 x hx⟩
  simp only [extV]
  split
  · rfl
  · exact h.1 j q

theorem gRun_agree (P : Nat → Comp M) (U : List String) :
    ∀ (ns : List Inst) (V V' : Src → Impl) (eB k : Nat), AgreeOn U V V' →
      (∀ n ∈ ns, ∀ p ∈ (P n.pkg).imports, ∀ x, n.src p.1 = .imp x → x ∈ U) →
      AgreeOn U (gRun P V eB k ns).1 (gRun P V' eB k ns).1 ∧
        (gRun P V eB k ns).2 = (gRun P V' eB k ns).2
  | [], _, _, _, _, h, _ => ⟨h, rfl⟩
  | n :: ns, V, V', eB, k, h, hn => by
    have hi : ((P n.pkg).imports.map fun p => V (n.src p.1)) =
        (P n.pkg).imports.map fun p => V' (n.src p.1) :=
      List.map_congr_left fun p hp => agree_src h (hn n List.mem_cons_self p hp)
    simp only [gRun]
    rw [hi]
    have ih := gRun_agree P U ns
      (extV V k (P n.pkg).exports
        (flattenNodes ((P n.pkg).imports.map fun p => V' (n.src p.1)) eB (P n.pkg).nodes).1)
      (extV V' k (P n.pkg).exports
        (flattenNodes ((P n.pkg).imports.map fun p => V' (n.src p.1)) eB (P n.pkg).nodes).1)
      (flattenNodes ((P n.pkg).imports.map fun p => V' (n.src p.1)) eB (P n.pkg).nodes).2.1
      (k + 1) (agree_extV h _ _ _) (fun m hm => hn m (List.mem_cons_of_mem _ hm))
    exact ⟨ih.1, by rw [ih.2]⟩

theorem fwd_subst_get {σ : List Impl} {r : Nat} {im : Impl} (h : σ[r]? = some im) :
    (Impl.fwd r).subst σ = im := by
  simp [Impl.subst, h]

theorem mem_names_iff_lookup : ∀ (I : Iface) (x : String), x ∈ names I ↔ I.lookup x ≠ none
  | [], x => by simp
  | (y, t) :: I, x => by
    by_cases h : x = y
    · subst h
      simp [List.lookup]
    · have hb : (x == y) = false := beq_eq_false_iff_ne.2 h
      simp only [names, List.map_cons, List.mem_cons, h, false_or, List.lookup, hb]
      exact mem_names_iff_lookup I x

theorem mem_names_of_lookup {I J : Iface} {x : String} (hx : x ∈ names J)
    (hl : I.lookup x = J.lookup x) : x ∈ names I := by
  rw [mem_names_iff_lookup, hl]
  exact (mem_names_iff_lookup J x).1 hx

theorem length_importPerm (I J : Iface) : (importPerm I J).length = J.length := by
  simp [importPerm]

/-- The renumbering only forwards to imports of `I`. -/
theorem scoped_importPerm {I J : Iface} (hl : ∀ x ∈ names J, I.lookup x = J.lookup x) :
    ScopedList I.length (importPerm I J) := by
  intro im him
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 him
  have h : (names I).idxOf x < (names I).length :=
    List.idxOf_lt_length_of_mem (mem_names_of_lookup hx (hl x hx))
  simpa [Impl.Scoped, names] using h

/-- The start of the run over `J`, renumbered into `I`, agrees with the start over `I`. -/
theorem agree_start (S : Nat → PkgSig) (g : Graph) {I J : Iface}
    (hl : ∀ x ∈ names J, I.lookup x = J.lookup x) :
    AgreeOn (names J) (baseV I) fun s => (g.resolve S J 0 s).subst (importPerm I J) := by
  refine ⟨fun j q => ?_, fun x hx => ?_⟩
  · simp only [Graph.resolve, Nat.not_lt_zero, false_and, ↓reduceIte, baseV]
    split <;> rfl
  · have hxI := mem_names_of_lookup hx (hl x hx)
    have hj : (names J).idxOf x < (names J).length := List.idxOf_lt_length_of_mem hx
    have hget : (importPerm I J)[(names J).idxOf x]? = some (.fwd ((names I).idxOf x)) := by
      simp only [importPerm, List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some,
        List.getElem_idxOf hj]
    simp only [baseV, Graph.resolve, hxI, hx, ↓reduceIte]
    exact (fwd_subst_get hget).symm

theorem tyOf_sub (S : Nat → PkgSig) (g : Graph) {I J : Iface}
    (hl : ∀ x ∈ names J, I.lookup x = J.lookup x) {s : Src} (hs : ∀ x, s = .imp x → x ∈ names J) :
    g.tyOf S J s = g.tyOf S I s := by
  cases s with
  | imp x => simp [Graph.tyOf, hl x (hs x rfl)]
  | out j q => rfl

/-- **A composition over more imports than it refers to is a specialisation** of the
composition over the imports it refers to. -/
theorem flatten_buildWith_sub (P : Nat → Comp M) (g : Graph) {I J : Iface}
    (hl : ∀ x ∈ names J, I.lookup x = J.lookup x) (hr : g.RefsIn (fun k => sigOf (P k)) (names J)) :
    flatten (g.buildWith (fun k => sigOf (P k)) P I) =
      specialise I (importPerm I J) (g.buildWith (fun k => sigOf (P k)) P J) := by
  have hA := flatten_mkNodes_run P g I g.nodes 0 ((List.range I.length).map Impl.fwd) I.length
    (baseV I) (by simp) (by simp [offset_zero_run]) (resolve_zero_subst_run _ g I)
  have hB := flatten_mkNodes_run P g J g.nodes 0 (importPerm I J) I.length
    (fun s => (g.resolve (fun k => sigOf (P k)) J 0 s).subst (importPerm I J)) (by simp)
    (by simp [length_importPerm, offset_zero_run]) (fun _ => rfl)
  have hR := gRun_agree P (names J) g.nodes (baseV I)
    (fun s => (g.resolve (fun k => sigOf (P k)) J 0 s).subst (importPerm I J)) I.length 0
    (agree_start _ g hl)
    (fun n hn p hp x hx => hr.1 n hn p (by simpa [sigOf] using hp) x hx)
  simp only [Graph.buildWith, flatten, specialise, Graph.mkExports, List.map_map]
  rw [hA.2.1, hB.2.1, hR.2]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  have hs : ∀ x, p.2 = .imp x → x ∈ names J := hr.2 p hp
  have e₁ := hA.2.2 p.2
  have e₂ := hB.2.2 p.2
  simp only [Nat.zero_add] at e₁ e₂
  simp only [Function.comp_apply, e₁, e₂, agree_src hR.1 hs, tyOf_sub _ g hl hs]

end Silmaril.Wasm.Wac.UnusedProof
