module

public import Silmaril.Wasm.Tools.Component.Semver.Defs
public import Silmaril.Wasm.Wac.TargetsT.Thms

/-!
# Theorems of `semver-check` and `targets --semver-compatible`

* `semverCheck_ok`: `semver-check` succeeds exactly when the two worlds of the package exist and
  the previous world's component kind, versions erased, is a WIT subtype (`Wac.Sub`) of the new
  world's.
* `targetsSemver_sub`: a positive verdict of `targets --semver-compatible` is WIT subtyping of
  the canonical views.
* `semverCheck_of_sub`: the converse of `semverCheck_ok`.
* `lastOfEach_names_nodup`: the merged view has one item per name.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Semver

open Silmaril.Wasm.Wac (Kind Externs Sub)

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- **`semver-check` succeeds on subtyping**, versions erased. -/
theorem semverCheck_ok {pb : ByteArray} {prev new : String}
    (h : semverCheck pb prev new = .ok ()) :
    ∃ q pi pe ni ne, (Wac.Bridge.decodePkg pb).map Prod.fst = .ok q ∧
      Wac.TargetsT.worldOf q.defs (some prev) = .ok (pi, pe) ∧
      Wac.TargetsT.worldOf q.defs (some new) = .ok (ni, ne) ∧
      Sub (.comp none (Wac.TargetsT.promoteEx (eraseVersions pi))
          (Wac.TargetsT.promoteEx (eraseVersions pe)))
        (.comp none (Wac.TargetsT.promoteEx (eraseVersions ni))
          (Wac.TargetsT.promoteEx (eraseVersions ne))) := by
  unfold semverCheck at h
  obtain ⟨⟨q, x⟩, hq, h⟩ := bind_ok h
  obtain ⟨⟨pi, pe⟩, hp, h⟩ := bind_ok h
  obtain ⟨⟨ni, ne⟩, hn, h⟩ := bind_ok h
  have hf : semverFits pi pe ni ne = true := by
    dsimp only at h
    split at h
    · assumption
    · cases h
  refine ⟨q, pi, pe, ni, ne, ?_, hp, hn, (Wac.TargetsT.fitsB_iff _ _ _ _).mp hf⟩
  rw [hq]; rfl

/-- Conversely, subtyping of the two worlds' kinds is success. -/
theorem semverCheck_of_sub {pb : ByteArray} {prev new : String} {q x pi pe ni ne}
    (hq : Wac.Bridge.decodePkg pb = .ok (q, x))
    (hp : Wac.TargetsT.worldOf q.defs (some prev) = .ok (pi, pe))
    (hn : Wac.TargetsT.worldOf q.defs (some new) = .ok (ni, ne))
    (hs : Sub (.comp none (Wac.TargetsT.promoteEx (eraseVersions pi))
          (Wac.TargetsT.promoteEx (eraseVersions pe)))
        (.comp none (Wac.TargetsT.promoteEx (eraseVersions ni))
          (Wac.TargetsT.promoteEx (eraseVersions ne)))) :
    semverCheck pb prev new = .ok () := by
  have hf : semverFits pi pe ni ne = true := (Wac.TargetsT.fitsB_iff _ _ _ _).mpr hs
  unfold semverCheck
  rw [hq]
  change (Wac.TargetsT.worldOf q.defs (some prev) >>= _) = _
  rw [hp]
  change (Wac.TargetsT.worldOf q.defs (some new) >>= _) = _
  rw [hn]
  change (if semverFits pi pe ni ne = true then _ else _) = _
  simp only [hf, ite_true]
  rfl

/-- A positive verdict of `targets --semver-compatible` is subtyping of the canonical views. -/
theorem targetsSemver_sub {comp pb : ByteArray} {w : String} {mis : List String}
    (h : targetsSemver comp pb w = .ok (true, mis)) :
    ∃ p q wi we, (Wac.TypeOf.decodeAny comp).map Prod.fst = .ok p ∧
      (Wac.Bridge.decodePkg pb).map Prod.fst = .ok q ∧
      Wac.TargetsT.worldOf q.defs (some w) = .ok (wi, we) ∧
      Sub (.comp none (canonical p.imports) (canonical p.exports))
        (.comp none (Wac.TargetsT.promoteEx (canonical wi)) (Wac.TargetsT.promoteEx (canonical we))) := by
  unfold targetsSemver at h
  obtain ⟨⟨p, x⟩, hp, h⟩ := bind_ok h
  obtain ⟨⟨q, y⟩, hq, h⟩ := bind_ok h
  obtain ⟨⟨wi, we⟩, hw, h⟩ := bind_ok h
  have hf : Wac.TargetsT.fitsB (canonical p.imports) (canonical p.exports) (canonical wi)
      (canonical we) = true := (Prod.mk.inj (Except.ok.inj h)).1
  refine ⟨p, q, wi, we, ?_, ?_, hw, (Wac.TargetsT.fitsB_iff _ _ _ _).mp hf⟩
  · rw [hp]; rfl
  · rw [hq]; rfl

theorem lastOfEach_step_nodup (acc : Externs) (hn : (acc.map (·.1)).Nodup) (x : String × Kind) :
    ((if acc.any (·.1 == x.1) then acc else acc ++ [x]).map (·.1)).Nodup := by
  split
  · exact hn
  · rename_i ha
    rw [List.map_append, List.map_singleton]
    refine List.nodup_append.mpr ⟨hn, List.nodup_singleton _, ?_⟩
    intro a hamem b hb hab
    rw [List.mem_singleton.mp hb] at hab
    subst hab
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hamem
    exact ha (List.any_eq_true.mpr ⟨y, hy, by simp [hyx]⟩)

theorem foldl_last_nodup : ∀ (es acc : Externs), (acc.map (·.1)).Nodup →
    ((es.foldl (fun acc (x : String × Kind) =>
      if acc.any (·.1 == x.1) then acc else acc ++ [x]) acc).map (·.1)).Nodup
  | [], _, h => h
  | x :: xs, acc, h => by
    rw [List.foldl_cons]
    exact foldl_last_nodup xs _ (lastOfEach_step_nodup acc h x)

/-- The merged view has one item per name. -/
theorem lastOfEach_names_nodup (es : Externs) : ((lastOfEach es).map (·.1)).Nodup := by
  unfold lastOfEach
  rw [List.map_reverse, List.nodup_reverse]
  exact foldl_last_nodup es.reverse [] List.nodup_nil

end Silmaril.Wasm.Tools.Component.Semver
