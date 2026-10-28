module

public import Silmaril.Process.LPS.Basic

/-!
# LPS in Lean: the flat file system

Translation of LPS `Fs.v` (upstream commit `f1006fe8`). The file system is a sorted
association list from paths (byte strings) to contents: no directory tree, no symbolic links,
no permissions. It is observed only at exit (`ExitEv code fs`).
-/

@[expose] public section

namespace Silmaril.Process.LPS.Fs

/-- LPS `Fs.v:49` `path`. -/
abbrev Path := List Byte

/-- LPS `Fs.v:51` `path_eqb`. -/
def pathEqb (p q : Path) : Bool := p == q

/-- LPS `Fs.v:76` `path_ltb`: lexicographic order on unsigned bytes. -/
def pathLtb : Path → Path → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: p, b :: q => decide (a.toNat < b.toNat) || (a == b && pathLtb p q)

/-- LPS `Fs.v:86` `Fs`. -/
abbrev FileSystem := List (Path × List Byte)

/-- LPS `Fs.v:88` `fs_lookup`. -/
def lookup : FileSystem → Path → Option (List Byte)
  | [], _ => none
  | (q, data) :: r, p => if pathEqb p q then some data else lookup r p

/-- LPS `Fs.v:95` `fs_set`: insert or replace, keeping the list sorted. -/
def set : FileSystem → Path → List Byte → FileSystem
  | [], p, data => [(p, data)]
  | (q, d) :: r, p, data =>
    if pathLtb p q then (p, data) :: (q, d) :: r
    else if pathEqb p q then (p, data) :: r
    else (q, d) :: set r p data

/-- LPS `Fs.v:132` `fs_remove`. -/
def remove : FileSystem → Path → FileSystem
  | [], _ => []
  | (q, d) :: r, p => if pathEqb p q then r else (q, d) :: remove r p

/-- LPS `Fs.v:139` `fs_sorted`. -/
def sorted : FileSystem → Bool
  | [] => true
  | [_] => true
  | (p, _) :: (q, d) :: r => pathLtb p q && sorted ((q, d) :: r)

/-- LPS `Fs.v:283` `valid_fs`: sorted, and no key contains NUL. -/
def ValidFs (fs : FileSystem) : Prop := sorted fs = true ∧ ∀ pf ∈ fs, (0 : Byte) ∉ pf.1

/-- LPS `Fs.v:297` `path_slash_byte`. -/
def slashByte : Byte := 47

/-- LPS `Fs.v:313` `key_is_relative`. -/
def KeyIsRelative : Path → Prop
  | [] => True
  | b :: _ => b ≠ slashByte

/-- LPS `Fs.v:333` `fs_keys_relative`. -/
def KeysRelative (fs : FileSystem) : Prop := ∀ pf ∈ fs, KeyIsRelative pf.1

/-- LPS `Fs.v:368` `file_from`: the contents from offset `off` on. -/
def fileFrom : List Byte → Int → List Byte
  | [], _ => []
  | data@(_ :: tl), off => if off ≤ 0 then data else fileFrom tl (off - 1)

/-- LPS `Fs.v:402` `file_read`. -/
def fileRead (data : List Byte) (off count : Word) : List Byte :=
  let rest := fileFrom data (uns off)
  rest.take (wordToNatBounded count rest.length)

/-- LPS `Fs.v:427` `file_write`: write at `off`, zero-filling a gap. -/
def fileWrite (data : List Byte) (off : Word) (bs : List Byte) : List Byte :=
  match bs with
  | [] => data
  | _ :: _ =>
    let padded := data ++ List.replicate (wordToNat off - data.length) 0
    padded.take (wordToNat off) ++ bs ++ padded.drop (wordToNat off + bs.length)

/-- LPS `Fs.v:466` `file_truncate`. -/
def fileTruncate (data : List Byte) (len : Word) : List Byte :=
  data.take (wordToNat len) ++ List.replicate (wordToNat len - data.length) 0

end Silmaril.Process.LPS.Fs
