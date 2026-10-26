module

public import Silmaril.Process.LPS.Uapi

/-!
# LPS in Lean: the pathname helpers of `Sys/Fs/Namei.v`

The pathname predicates that `openat`, `faccessat` and `unlinkat` share (LPS
`Sys/Fs/Namei.v:32-200`, upstream commit `f1006fe8`): `..`, the separator, the implied
directory of the flat file system (`fs_under`), trailing-separator stripping and the private
`/tmp` names. They are pure functions on byte strings; `unlinkat_spec` itself is in
`Sys/FsMeta/Namei`. (The fs-io and fs-meta lanes each translated these helpers; the
integration keeps the fs-meta text, which also has `slash_byte` and the `dir_prefixb`/`fs_under`
lemmas, here.)
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Fs (Path FileSystem)

/-- LPS `Sys/Fs/Namei.v:32` `dotdot_path`: `".."`, typed `LAST_DOTDOT` by `link_path_walk`. -/
def dotdotPath : Path := [46, 46]

/-- LPS `Sys/Fs/Namei.v:34` `slash_byte`: `'/'`. -/
def slashByte : Byte := 47

/-- LPS `Sys/Fs/Namei.v:42` `slash_byte_is_path_slash_byte`. -/
theorem slashByte_eq_fs : slashByte = Fs.slashByte := rfl

/-- LPS `Sys/Fs/Namei.v:46` `path_has_slash`. -/
def pathHasSlash (p : Path) : Bool := p.any (· == slashByte)

/-- LPS `Sys/Fs/Namei.v:51` `drop_leading_slashes`. -/
def dropLeadingSlashes : Path → Path
  | [] => []
  | b :: r => if b == slashByte then dropLeadingSlashes r else b :: r

/-- LPS `Sys/Fs/Namei.v:65` `path_strip_trailing_slashes`: trailing separators change neither
which component is last nor its type (for `unlinkat`'s `path_parentat` route only; a lookup
through `lookup_last` treats them differently). -/
def pathStripTrailingSlashes (p : Path) : Path := (dropLeadingSlashes p.reverse).reverse

/-- LPS `Sys/Fs/Namei.v:72` `path_trailing_slash`: the byte `do_unlinkat` tests at
`last.name[last.len]` is not NUL. -/
def pathTrailingSlash (p : Path) : Bool :=
  !((pathStripTrailingSlashes p).length == p.length)

/-- LPS `Sys/Fs/Namei.v:79` `dir_prefixb p q`: `q` is `p ++ "/" ++ _`, i.e. `q` lives under
the directory `p`. -/
def dirPrefixb : Path → Path → Bool
  | [], [] => false
  | [], c :: _ => c == slashByte
  | _ :: _, [] => false
  | a :: p, b :: q => a == b && dirPrefixb p q

/-- LPS `Sys/Fs/Namei.v:89` `fs_under`: some key lives under `p`, so `p` is an implied
directory the flat map cannot hold. -/
def fsUnder : FileSystem → Path → Bool
  | [], _ => false
  | (q, _) :: r, p => dirPrefixb p q || fsUnder r p

/-- LPS `Sys/Fs/Namei.v:99` `dir_prefixb_app`. -/
theorem dirPrefixb_app : ∀ (p q : Path), dirPrefixb p q = true → ∃ r, q = p ++ slashByte :: r
  | [], [], h => by simp [dirPrefixb] at h
  | [], c :: q, h => by
    simp only [dirPrefixb, beq_iff_eq] at h
    exact ⟨q, by simp [h]⟩
  | _ :: _, [], h => by simp [dirPrefixb] at h
  | a :: p, b :: q, h => by
    simp only [dirPrefixb, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨r, rfl⟩ := dirPrefixb_app p q h
    exact ⟨r, rfl⟩

/-- LPS `Sys/Fs/Namei.v:113` `fs_under_false_of_keys`. -/
theorem fsUnder_false_of_keys (fs : FileSystem) (p : Path)
    (h : ∀ qd ∈ fs, dirPrefixb p qd.1 = false) : fsUnder fs p = false := by
  induction fs with
  | nil => rfl
  | cons qd fs ih =>
    obtain ⟨q, d⟩ := qd
    simp only [fsUnder, Bool.or_eq_false_iff]
    exact ⟨h (q, d) (by simp), ih fun x hx => h x (by simp [hx])⟩

/-- LPS `Sys/Fs/Namei.v:123` `path_strip_prefix`. -/
def pathStripPrefix : Path → Path → Option Path
  | [], p => some p
  | _ :: _, [] => none
  | a :: pre, b :: p => if a == b then pathStripPrefix pre p else none

/-- LPS `Sys/Fs/Namei.v:131` `path_strip_prefix_app`. -/
theorem pathStripPrefix_app : ∀ (pre p n : Path), pathStripPrefix pre p = some n → p = pre ++ n
  | [], p, n, h => by
    simp only [pathStripPrefix, Option.some.injEq] at h
    simp [h]
  | _ :: _, [], n, h => by simp [pathStripPrefix] at h
  | a :: pre, b :: p, n, h => by
    simp only [pathStripPrefix] at h
    split at h
    · rename_i hab
      have : a = b := by simpa using hab
      subst this
      simp [pathStripPrefix_app pre p n h]
    · simp at h

/-- LPS `Sys/Fs/Namei.v:171` `tmp_name`: the one pathname shape under `/tmp` the model
answers for, `"/tmp/<name>"` with exactly one further component (not `.`, not `..`, no
separator, not empty). -/
def tmpName (p : Path) : Option Path :=
  match pathStripPrefix tmpPrefix p with
  | none => none
  | some n =>
    if Fs.pathEqb n [] then none
    else if pathHasSlash n then none
    else if Fs.pathEqb n dotPath then none
    else if Fs.pathEqb n dotdotPath then none
    else some n

/-- LPS `Sys/Fs/Namei.v:186` `tmp_name_key`: the gate and the seeding (`fs_seed_tmp`) agree on
the key. -/
theorem tmpName_key (p n : Path) (h : tmpName p = some n) : p = tmpKey n := by
  unfold tmpName at h
  split at h
  · simp at h
  · rename_i n' hs
    have hp := pathStripPrefix_app _ _ _ hs
    split at h
    · simp at h
    split at h
    · simp at h
    split at h
    · simp at h
    split at h
    · simp at h
    cases h
    exact hp

end Silmaril.Process.LPS
