module

public import Silmaril.Proofs.Wasm.Wit.Elab.Iface
public import Silmaril.Proofs.Wasm.Wit.Elab.Sound
public import Silmaril.Wasm.Wit.Text.Thms
public import Silmaril.Wasm.Wit.Binary.Thms

/-!
# Elaboration: names of a valid universe survive the binary encoding

* `Version.str` spells a version as the text printer does (`Version.str_toList`),
  so it is injective on valid versions (`Version.str_inj`, from `parseVer_verChars`);
  `pkgName` and `ifaceName` are injective on valid names;
* `ifaceName_validB`: the binary name of an interface of a valid package passes
  `IfaceName.validB` (identifiers contain none of `: / @`);
* `resolve_has`, `has_iface_valid`, `has_world_valid`: what a path of a valid
  universe resolves to has a valid package name and a valid identifier.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Elab

open Silmaril.Wasm.Component.Wat (natChars digitChar)
open Silmaril.Wasm.Wit.Text (verChars joinOn verOk_of_valid parseVer_verChars)

theorem digitsAux_eq : ∀ (f n : Nat) (acc : List Char), n < f → digitsAux f n acc = natChars n ++ acc
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, n, acc, h => by
    unfold digitsAux
    rw [natChars]
    by_cases hn : n < 10
    · have h0 : n / 10 = 0 := Nat.div_eq_of_lt hn
      have hm : n % 10 = n := Nat.mod_eq_of_lt hn
      simp [h0, hn, hm, digitChar]
    · have h0 : n / 10 ≠ 0 := by omega
      have hlt : n / 10 < f := by omega
      simp only [h0, ite_false, hn, digitsAux_eq f (n / 10) _ hlt, List.append_assoc, List.singleton_append,
        digitChar]

theorem natStr_toList (n : Nat) : (natStr n).toList = natChars n := by
  simp [natStr, digitsAux_eq (n + 1) n [] (Nat.lt_succ_self n)]

theorem joinWith_toList : ∀ l : List String, (joinWith "." l).toList = joinOn '.' (l.map String.toList)
  | [] => rfl
  | [s] => by simp [joinWith, joinOn]
  | s :: t :: rest => by
    have ih := joinWith_toList (t :: rest)
    simp only [joinWith] at ih ⊢
    simp [String.toList_append, ih, joinOn]

/-- `Version.str` is the text printer's spelling. -/
theorem Version.str_toList (v : Version) : v.str.toList = verChars v := by
  unfold Version.str verChars
  simp only [String.toList_append, natStr_toList, List.append_assoc]
  by_cases hp : v.pre = [] <;> by_cases hb : v.build = [] <;>
    simp [hp, hb, joinWith_toList]

/-- **`Version.str` is injective on valid versions.** -/
theorem Version.str_inj {v w : Version} (hv : v.Valid) (hw : w.Valid) (h : v.str = w.str) : v = w := by
  have h1 := parseVer_verChars v (verOk_of_valid hv)
  have h2 := parseVer_verChars w (verOk_of_valid hw)
  rw [← Version.str_toList, h, Version.str_toList] at h1
  rw [h1] at h2
  exact Option.some.inj h2

theorem pkgName_inj {p q : PackageName} (hp : p.Valid) (hq : q.Valid) (h : pkgName p = pkgName q) : p = q := by
  obtain ⟨ns, n, v⟩ := p
  obtain ⟨ns', n', v'⟩ := q
  simp only [pkgName, Binary.PackageName.mk.injEq] at h
  obtain ⟨rfl, rfl, hv⟩ := h
  cases v with
  | none => cases v' with
    | none => rfl
    | some _ => cases hv
  | some a => cases v' with
    | none => cases hv
    | some b =>
      have hab : a.str = b.str := Option.some.inj hv
      rw [Version.str_inj (hp.2.2 a rfl) (hq.2.2 b rfl) hab]

theorem ifaceName_inj {i j : ItemId} (hi : i.pkg.Valid) (hj : j.pkg.Valid) (h : ifaceName i = ifaceName j) :
    i = j := by
  obtain ⟨p, n⟩ := i
  obtain ⟨q, m⟩ := j
  simp only [ifaceName, Binary.IfaceName.mk.injEq] at h
  have hpq : p = q := pkgName_inj hi hj h.1
  rw [hpq, h.2]

/-- Interface names of valid ids pass the binary check. -/
theorem ifaceName_validB {i : ItemId} (hp : i.pkg.Valid) (hn : ValidId i.name) :
    IfaceName.validB (ifaceName i) = true := by
  have h1 := plain_of_validId hp.1
  have h2 := plain_of_validId hp.2.1
  have h3 := plain_of_validId hn
  have a := not_mem_of_plain h1 plainChar_colon
  have b := not_mem_of_plain h2 plainChar_slash
  have c := not_mem_of_plain h3 plainChar_at
  simp only [IfaceName.validB, ifaceName, pkgName, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simpa using ‹_›

theorem ifaceName_valid {i : ItemId} (hp : i.pkg.Valid) (hn : ValidId i.name) : (ifaceName i).Valid :=
  IfaceName.validB_sound (ifaceName_validB hp hn)

/-- The ids of distinct valid interfaces differ. -/
theorem ifaceName_id_inj {i j : ItemId} (hip : i.pkg.Valid) (hin : ValidId i.name) (hjp : j.pkg.Valid)
    (hjn : ValidId j.name) (h : (ifaceName i).id = (ifaceName j).id) : i = j := by
  have hc : (ifaceName i).idChars = (ifaceName j).idChars := by
    have := congrArg String.toList h
    simpa [Binary.IfaceName.id] using this
  have h1 := Binary.parseIfaceName_id (ifaceName_valid hip hin)
  have h2 := Binary.parseIfaceName_id (ifaceName_valid hjp hjn)
  rw [hc, h2] at h1
  exact ifaceName_inj hip hjp (Option.some.inj h1).symm

/-! ## What paths resolve to -/

theorem resolve_has {U : Universe} {k : Kind} {p : PackageName} {path : UsePath} {j : ItemId}
    (h : resolve U k p path = some j) : U.has k j = true := by
  cases resolve_sound h <;> assumption

theorem pkg?_mem {U : Universe} {p : PackageName} {P : Package} (h : U.pkg? p = some P) :
    P ∈ U ∧ P.name = p := by
  unfold Universe.pkg? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem pkgIface?_mem {P : Package} {n : Name} {I : Interface} (h : P.iface? n = some I) :
    PackageItem.iface I ∈ P.items ∧ I.name = n := by
  unfold Package.iface? at h
  obtain ⟨it, hit, hs⟩ := List.exists_of_findSome?_eq_some h
  cases it with
  | iface J =>
    by_cases hJ : J.name = n
    · simp only [hJ, ite_true, Option.some.injEq] at hs
      subst hs
      exact ⟨hit, hJ⟩
    · simp [hJ] at hs
  | world _ => simp at hs
  | use _ => simp at hs

theorem pkgWorld?_mem {P : Package} {n : Name} {W : World} (h : P.world? n = some W) :
    PackageItem.world W ∈ P.items ∧ W.name = n := by
  unfold Package.world? at h
  obtain ⟨it, hit, hs⟩ := List.exists_of_findSome?_eq_some h
  cases it with
  | world J =>
    by_cases hJ : J.name = n
    · simp only [hJ, ite_true, Option.some.injEq] at hs
      subst hs
      exact ⟨hit, hJ⟩
    · simp [hJ] at hs
  | iface _ => simp at hs
  | use _ => simp at hs

/-- The interface with a given id is an interface of a package of the universe. -/
theorem Universe.iface?_mem {U : Universe} {i : ItemId} {I : Interface} (h : U.iface? i = some I) :
    ∃ P ∈ U, P.name = i.pkg ∧ PackageItem.iface I ∈ P.items ∧ I.name = i.name := by
  unfold Universe.iface? at h
  cases hP : U.pkg? i.pkg with
  | none => rw [hP] at h; cases h
  | some P =>
    rw [hP] at h
    obtain ⟨hm, hn⟩ := pkg?_mem hP
    obtain ⟨hI, hIn⟩ := pkgIface?_mem h
    exact ⟨P, hm, hn, hI, hIn⟩

/-- The world with a given id is a world of a package of the universe. -/
theorem Universe.world?_mem {U : Universe} {i : ItemId} {W : World} (h : U.world? i = some W) :
    ∃ P ∈ U, P.name = i.pkg ∧ PackageItem.world W ∈ P.items ∧ W.name = i.name := by
  unfold Universe.world? at h
  cases hP : U.pkg? i.pkg with
  | none => rw [hP] at h; cases h
  | some P =>
    rw [hP] at h
    obtain ⟨hm, hn⟩ := pkg?_mem hP
    obtain ⟨hW, hWn⟩ := pkgWorld?_mem h
    exact ⟨P, hm, hn, hW, hWn⟩

/-- An interface of a valid universe has a valid package name and identifier. -/
theorem iface_valid {L : Leaves} {U : Universe} (hv : ValidWith L U) {i : ItemId} {I : Interface}
    (h : U.iface? i = some I) : i.pkg.Valid ∧ ValidId i.name := by
  obtain ⟨P, hP, hn, hI, hIn⟩ := Universe.iface?_mem h
  have hpk := hv.2 P hP
  have hok : InterfaceOk L P.name I := hpk.2.2 _ hI
  exact ⟨hn ▸ hpk.1, hIn ▸ hok.1⟩

/-- A world of a valid universe has a valid package name and identifier. -/
theorem world_valid {L : Leaves} {U : Universe} (hv : ValidWith L U) {i : ItemId} {W : World}
    (h : U.world? i = some W) : i.pkg.Valid ∧ ValidId i.name := by
  obtain ⟨P, hP, hn, hW, hWn⟩ := Universe.world?_mem h
  have hpk := hv.2 P hP
  have hok : WorldOk L P.name W := hpk.2.2 _ hW
  exact ⟨hn ▸ hpk.1, hWn ▸ hok.1⟩

theorem has_valid {L : Leaves} {U : Universe} (hv : ValidWith L U) {k : Kind} {j : ItemId}
    (h : U.has k j = true) : j.pkg.Valid ∧ ValidId j.name := by
  cases k with
  | iface =>
    obtain ⟨I, hI⟩ := Option.isSome_iff_exists.mp h
    exact iface_valid hv hI
  | world =>
    obtain ⟨W, hW⟩ := Option.isSome_iff_exists.mp h
    exact world_valid hv hW

/-- What a path of a valid universe resolves to has valid names. -/
theorem resolve_valid {L : Leaves} {U : Universe} (hv : ValidWith L U) {k : Kind} {p : PackageName}
    {path : UsePath} {j : ItemId} (h : resolve U k p path = some j) : j.pkg.Valid ∧ ValidId j.name :=
  has_valid hv (resolve_has h)

/-- A path that resolves elaborates to the resolved interface. -/
theorem resolve_getD {U : Universe} {k : Kind} {p : PackageName} {path : UsePath} {j : ItemId}
    (h : ResolvesTo U k p path j) (d : ItemId) : (resolve U k p path).getD d = j := by
  rw [resolve_complete h]; rfl

end Silmaril.Wasm.Wit.Elab
