module

public import Silmaril.Wasm.Wac.NestOrder.Defs
public import Silmaril.Proofs.Wasm.Wac.Nest.Main

/-!
# Nesting = inlining with first-occurrence import order: the renumbering

* `flatten_buildWith_perm`: a composition built over the imports `I` flattens to the
  specialisation, by `importPerm I J`, of the same composition built over the imports
  `J`, when `I` and `J` have the same lookups;
* `flatten_nest_inline_perm`: the flat nested composition (`Graph.toComp`, first
  occurrence order) is the inlined one (`Graph.toComp`) specialised by the renumbering
  of its imports.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.NestProof

open Silmaril.Wasm.Component

variable {M : Type}

theorem mem_names_iff_lookup : ∀ (I : Iface) (x : String), x ∈ names I ↔ I.lookup x ≠ none
  | [], x => by simp
  | (y, t) :: I, x => by
    by_cases h : x = y
    · subst h
      simp [List.lookup]
    · have hb : (x == y) = false := beq_eq_false_iff_ne.2 h
      simp only [names, List.map_cons, List.mem_cons, h, false_or, List.lookup, hb]
      exact mem_names_iff_lookup I x

theorem mem_names_of_lookup {I J : Iface} (hl : ∀ x, I.lookup x = J.lookup x) {x : String} :
    x ∈ names I ↔ x ∈ names J := by
  rw [mem_names_iff_lookup, mem_names_iff_lookup, hl]

theorem length_importPerm (I J : Iface) : (importPerm I J).length = J.length := by
  simp [importPerm]

theorem importPerm_get {I J : Iface} {x : String} (hx : x ∈ names J) :
    (importPerm I J)[(names J).idxOf x]? = some (.fwd ((names I).idxOf x)) := by
  have hl : (names J).idxOf x < (names J).length := List.idxOf_lt_length_of_mem hx
  simp only [importPerm, List.getElem?_map, List.getElem?_eq_getElem hl, Option.map_some,
    List.getElem_idxOf hl]

/-- The renumbering only forwards to imports of `I`. -/
theorem scoped_importPerm {I J : Iface} (hl : ∀ x, I.lookup x = J.lookup x) :
    ScopedList I.length (importPerm I J) := by
  intro im him
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 him
  have hxI : x ∈ names I := (mem_names_of_lookup hl).2 hx
  have h : (names I).idxOf x < (names I).length := List.idxOf_lt_length_of_mem hxI
  simpa [Impl.Scoped, names] using h

/-- Under the renumbering, a reference resolved over `J` is the base valuation over
`I`. -/
theorem resolve_zero_perm (S : Nat → PkgSig) (g : Graph) {I J : Iface}
    (hl : ∀ x, I.lookup x = J.lookup x) (s : Src) :
    (g.resolve S J 0 s).subst (importPerm I J) = baseV I s := by
  cases s with
  | imp x =>
    by_cases hx : x ∈ names J
    · have hxI : x ∈ names I := (mem_names_of_lookup hl).2 hx
      simp only [Graph.resolve, baseV, hx, hxI, ↓reduceIte]
      exact subst_fwd_of_get (importPerm_get hx)
    · have hxI : x ∉ names I := fun h => hx ((mem_names_of_lookup hl).1 h)
      simp only [Graph.resolve, baseV, hx, hxI, ↓reduceIte]
      rfl
  | out j q =>
    simp only [Graph.resolve, Nat.not_lt_zero, false_and, ↓reduceIte, baseV]
    split <;> rfl

theorem tyOf_perm (S : Nat → PkgSig) (g : Graph) {I J : Iface}
    (hl : ∀ x, I.lookup x = J.lookup x) (s : Src) : g.tyOf S J s = g.tyOf S I s := by
  cases s with
  | imp x => simp [Graph.tyOf, hl]
  | out j q => rfl

variable [CoreModule M]

/-- **Changing the order of the imports is a specialisation.** -/
theorem flatten_buildWith_perm (P : Nat → Comp M) (g : Graph) {I J : Iface}
    (hl : ∀ x, I.lookup x = J.lookup x) :
    flatten (g.buildWith (fun k => sigOf (P k)) P I) =
      specialise I (importPerm I J) (g.buildWith (fun k => sigOf (P k)) P J) := by
  have hA := flatten_mkNodes P g J g.nodes 0 (importPerm I J) I.length (baseV I) (by simp)
    (by simp [length_importPerm, offset_zero]) (resolve_zero_perm _ g hl)
  have hx : ∀ p ∈ g.exports, (g.resolve (fun k => sigOf (P k)) J g.nodes.length p.2).subst
      (flattenNodes (importPerm I J) I.length
        (g.mkNodes (fun k => sigOf (P k)) P J 0 g.nodes)).1 =
      (gRun P (baseV I) I.length 0 g.nodes).1 p.2 := fun p _ => by
    simpa using hA.2.2 p.2
  rw [flatten_buildWith]
  simp only [Graph.buildWith, specialise, Graph.mkExports, List.map_map]
  rw [hA.2.1]
  congr 1
  exact List.map_congr_left fun p hp => by simp [hx p hp, tyOf_perm _ g hl]

/-- **Nesting = inlining, first-occurrence import order**: the flat nested composition
is the inlined composition with its imports renumbered. -/
theorem flatten_nest_inline_perm (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph}
    (ok : NestOk P k0 g₁ g₂) :
    flatten (g₂.toComp (nestPkgs P k0 g₁)) =
      specialise (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k))
        (importPerm (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k))
          ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).iface fun k => sigOf (P k)))
        ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).toComp P) := by
  have hl : ∀ x, (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k)).lookup x =
      ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).iface fun k => sigOf (P k)).lookup x :=
    fun x => (lookup_iface_inline P ok x).symm
  show flatten (g₂.buildWith _ _ _) = specialise _ _ ((Graph.inline _ k0 g₁ g₂).buildWith _ _ _)
  rw [flatten_nest_inline_with P ok, flatten_buildWith_perm P _ hl]

end Silmaril.Wasm.Wac.NestProof
