module

public import Silmaril.Wasm.Component.BinaryP3.WorldSub.Defs

/-!
# `World.targets` is sound for Component Model subtyping

**PROVED**

* `CSub.trans`, `CSub.refl`: `CSub` is a preorder;
* `sub_sound`: `World.sub a b = true → CSub a b`;
* `provides_sound`: `World.provides h n = true → Provides h n`;
* **`targets_sound`**: if `World.targets c W = true`, the closed types `resolveAst c` and
  `resolveWorld W` exist and the component's is a Component Model subtype of the world's:
  `CSub (resolveAst c) (resolveWorld W)`;
* `sub_incomplete`: `World.sub` misses depth subtyping (a concrete pair related by `CSub` that
  `sub` rejects), so `targets` is sound, not complete.

**The claim, narrowed.** `targets` relates the closed types that `resolveAst` and
`resolveWorld` compute; those resolutions are not themselves checked against a reference
type checker here (their approximations are listed in `Silmaril.Wasm.Component.BinaryP3.World`).
What is proved is that the comparison `targets` makes on them is Component Model subtyping.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryP3.World

theorem mem_of_lookup : ∀ {l : Table} {n : String} {t : CType}, l.lookup n = some t → (n, t) ∈ l
  | [], _, _, h => by simp at h
  | (m, u) :: l, n, t, h => by
    by_cases hm : n = m
    · subst hm
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · have hb : (n == m) = false := by simpa using hm
      simp only [List.lookup, hb] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem isSome_some_iff {o : Option CType} : o.isSome = true ↔ ∃ t, o = some t :=
  Option.isSome_iff_exists

/-- Both directions of transitivity through a derivation, proved together (component imports are
contravariant). -/
theorem CSub.both {a b : CType} (h : CSub a b) :
    (∀ c, CSub b c → CSub a c) ∧ (∀ z, CSub z a → CSub z b) := by
  induction h with
  | refl a => exact ⟨fun _ h => h, fun _ h => h⟩
  | @inst as bs hs hsub ih =>
    show (∀ c, CSub (.inst bs) c → CSub (.inst as) c) ∧ (∀ z, CSub z (.inst as) → CSub z (.inst bs))
    refine ⟨fun c hc => ?_, fun z hz => ?_⟩
    · cases hc with
      | refl => exact .inst hs hsub
      | inst hs2 hsub2 =>
        refine .inst (fun n tc hn => ?_) (fun n tc ta hn hla => ?_)
        · obtain ⟨tb, hb⟩ := isSome_some_iff.1 (hs2 n tc hn)
          exact hs n tb (mem_of_lookup hb)
        · obtain ⟨tb, hb⟩ := isSome_some_iff.1 (hs2 n tc hn)
          exact (ih n tb ta (mem_of_lookup hb) hla).1 tc (hsub2 n tc tb hn hb)
    · cases hz with
      | refl => exact .inst hs hsub
      | inst hs2 hsub2 =>
        refine .inst (fun n tb hn => ?_) (fun n tb tz hn hlz => ?_)
        · obtain ⟨ta, ha⟩ := isSome_some_iff.1 (hs n tb hn)
          exact hs2 n ta (mem_of_lookup ha)
        · obtain ⟨ta, ha⟩ := isSome_some_iff.1 (hs n tb hn)
          exact (ih n tb ta hn ha).2 tz (hsub2 n ta tz (mem_of_lookup ha) hlz)
  | @comp ai ae bi be hi hisub he hesub ihi ihe =>
    show (∀ c, CSub (.comp bi be) c → CSub (.comp ai ae) c) ∧
      (∀ z, CSub z (.comp ai ae) → CSub z (.comp bi be))
    refine ⟨fun c hc => ?_, fun z hz => ?_⟩
    · show CSub (.comp ai ae) c
      cases hc with
      | refl => exact .comp hi hisub he hesub
      | @comp _ _ ci ce hi2 hisub2 he2 hesub2 =>
        show CSub (.comp ai ae) (.comp ci ce)
        refine .comp (fun n ta hn => ?_) (fun n ta tc hn hlc => ?_) (fun n tc hn => ?_)
          (fun n tc ta hn hla => ?_)
        · obtain ⟨tb, hb⟩ := isSome_some_iff.1 (hi n ta hn)
          exact hi2 n tb (mem_of_lookup hb)
        · obtain ⟨tb, hb⟩ := isSome_some_iff.1 (hi n ta hn)
          exact (ihi n ta tb hn hb).2 tc (hisub2 n tb tc (mem_of_lookup hb) hlc)
        · obtain ⟨tb, hb⟩ := isSome_some_iff.1 (he2 n tc hn)
          exact he n tb (mem_of_lookup hb)
        · obtain ⟨tb, hb⟩ := isSome_some_iff.1 (he2 n tc hn)
          exact (ihe n tb ta (mem_of_lookup hb) hla).1 tc (hesub2 n tc tb hn hb)
    · show CSub z (.comp bi be)
      cases hz with
      | refl => exact .comp hi hisub he hesub
      | @comp zi ze _ _ hi2 hisub2 he2 hesub2 =>
        show CSub (.comp zi ze) (.comp bi be)
        refine .comp (fun n tz hn => ?_) (fun n tz tb hn hlb => ?_) (fun n tb hn => ?_)
          (fun n tb tz hn hlz => ?_)
        · obtain ⟨ta, ha⟩ := isSome_some_iff.1 (hi2 n tz hn)
          exact hi n ta (mem_of_lookup ha)
        · obtain ⟨ta, ha⟩ := isSome_some_iff.1 (hi2 n tz hn)
          exact (ihi n ta tb (mem_of_lookup ha) hlb).1 tz (hisub2 n tz ta hn ha)
        · obtain ⟨ta, ha⟩ := isSome_some_iff.1 (he n tb hn)
          exact he2 n ta (mem_of_lookup ha)
        · obtain ⟨ta, ha⟩ := isSome_some_iff.1 (he n tb hn)
          exact (ihe n tb ta hn ha).2 tz (hesub2 n ta tz (mem_of_lookup ha) hlz)

/-- **`CSub` is transitive.** -/
theorem CSub.trans {a b c : CType} (h1 : CSub a b) (h2 : CSub b c) : CSub a c :=
  h1.both.1 c h2

/-- **`World.sub` is sound for Component Model subtyping.** -/
theorem sub_sound {a b : CType} (h : sub a b = true) : CSub a b := by
  unfold sub at h
  split at h
  · rename_i as bs
    rw [List.all_eq_true] at h
    have hl : ∀ n tb, (n, tb) ∈ bs.toList → as.toList.lookup n = some tb := fun n tb hn => by
      simpa using h (n, tb) hn
    refine .inst (fun n tb hn => by rw [hl n tb hn]; rfl) (fun n tb ta hn ha => ?_)
    rw [hl n tb hn, Option.some.injEq] at ha
    subst ha
    exact .refl _
  · exact (of_decide_eq_true h) ▸ .refl _

/-- **`World.provides` is sound.** -/
theorem provides_sound {h need : Table} (hp : provides h need = true) : Provides h need := by
  intro n t hn
  unfold provides at hp
  rw [List.all_eq_true] at hp
  have := hp (n, t) hn
  simp only at this
  split at this
  · rename_i t' ht
    exact ⟨t', ht, sub_sound this⟩
  · exact absurd this Bool.false_ne_true

theorem csub_comp_of {ai ae bi be : CFields} (hi : Provides bi.toList ai.toList)
    (he : Provides ae.toList be.toList) : CSub (.comp ai ae) (.comp bi be) := by
  refine .comp (fun n ta hn => ?_) (fun n ta tb hn hb => ?_) (fun n tb hn => ?_)
    (fun n tb ta hn ha => ?_)
  · obtain ⟨t', ht, -⟩ := hi n ta hn
    rw [ht]; rfl
  · obtain ⟨t', ht, hs⟩ := hi n ta hn
    rw [ht, Option.some.injEq] at hb
    exact hb ▸ hs
  · obtain ⟨t', ht, -⟩ := he n tb hn
    rw [ht]; rfl
  · obtain ⟨t', ht, hs⟩ := he n tb hn
    rw [ht, Option.some.injEq] at ha
    exact ha ▸ hs

/-- **`World.targets` is sound**: the component's closed type is a Component Model subtype of
the world's. -/
theorem targets_sound {c : Ast} {W : Silmaril.Wasm.Wit.Project.WorldType} (h : targets c W = true) :
    ∃ tc tw, resolveAst c = some tc ∧ resolveWorld W = some tw ∧ CSub tc tw := by
  unfold targets at h
  split at h
  · rename_i ci ce wi we hc hw
    rw [Bool.and_eq_true] at h
    exact ⟨_, _, hc, hw, csub_comp_of (provides_sound h.1) (provides_sound h.2)⟩
  · exact absurd h Bool.false_ne_true

/-- An instance type with the named exports. -/
def instOf (l : Table) : CType := .inst (CFields.ofList l)

theorem toList_ofList : ∀ l : Table, (CFields.ofList l).toList = l
  | [] => rfl
  | (n, t) :: l => by simp only [CFields.ofList, CFields.toList, toList_ofList l]

/-- Instance subtyping from lookups. -/
theorem csub_instOf {as bs : Table}
    (h : ∀ p ∈ bs, ∃ ta, as.lookup p.1 = some ta ∧ CSub ta p.2) : CSub (instOf as) (instOf bs) := by
  refine .inst (fun n tb hn => ?_) (fun n tb ta hn ha => ?_)
  · have hn' : (n, tb) ∈ bs := by rwa [toList_ofList] at hn
    obtain ⟨ta, hta, -⟩ := h (n, tb) hn'
    show ((CFields.ofList as).toList.lookup n).isSome = true
    rw [toList_ofList, hta]; rfl
  · have hn' : (n, tb) ∈ bs := by rwa [toList_ofList] at hn
    have ha' : as.lookup n = some ta := by rwa [toList_ofList] at ha
    obtain ⟨ta', hta, hs⟩ := h (n, tb) hn'
    have e : ta = ta' := Option.some.inj (ha'.symm.trans hta)
    exact e ▸ hs

/-- **`World.sub` is incomplete**: it has no depth subtyping. An instance exporting `a`, an
instance with `x` and `y`, is a subtype of one exporting `a` with `x` only, which `sub`
rejects. -/
theorem sub_incomplete :
    ∃ a b : CType, CSub a b ∧ sub a b = false := by
  have hin : CSub (instOf [("x", .coreModule), ("y", .coreModule)]) (instOf [("x", .coreModule)]) :=
    csub_instOf fun p hp => by obtain rfl := List.mem_singleton.1 hp; exact ⟨.coreModule, rfl, .refl _⟩
  have hout : CSub (instOf [("a", instOf [("x", .coreModule), ("y", .coreModule)])])
      (instOf [("a", instOf [("x", .coreModule)])]) :=
    csub_instOf fun p hp => by obtain rfl := List.mem_singleton.1 hp; exact ⟨_, rfl, hin⟩
  exact ⟨_, _, hout, by decide⟩

end Silmaril.Wasm.Component.BinaryP3.World

end
