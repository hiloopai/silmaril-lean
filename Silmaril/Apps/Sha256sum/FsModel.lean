module

public import Silmaril.Apps.Sha256sum.Basic

/-! # A concrete file-system oracle (test support, not part of the specification)

`sha256sum` takes the file system as an oracle `Bytes → ReadResult`. This file gives the
concrete oracle that the differential corpus uses (`fs_read` in the research note's
`refmodel.py`): a finite map from relative paths to nodes, with Linux path resolution for
the cases the corpus exercises (`ENAMETOOLONG` for a component over 255 bytes, `ENOTDIR`
through a file, `ENOENT`/`ELOOP` through a missing or looping component, a trailing `/`,
and `.`/`..` as directories). It is used by the `sha256sum_spec` executable only; nothing
in the specification or its theorems depends on it.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum

inductive Node where
  /-- A readable regular file. -/
  | file (data : Bytes)
  /-- Exists; `open` fails with `EACCES`. -/
  | noperm
  /-- A directory: `open` succeeds, the first `read` fails with `EISDIR`. -/
  | dir
  /-- A symlink loop. -/
  | loop
  /-- A dangling symlink. -/
  | dangling
  /-- `open` succeeds; reads give `pre`, then fail with `EIO`. -/
  | eio (pre : Bytes)
  deriving DecidableEq, Repr

abbrev Tree := List (Bytes × Node)

def Tree.find (t : Tree) (p : Bytes) : Option Node := (t.find? (·.1 == p)).map (·.2)

def joinSlash : List Bytes → Bytes
  | [] => []
  | [c] => c
  | c :: cs => c ++ [47] ++ joinSlash cs

def isDotName (p : Bytes) : Bool := p = [] || p = [46] || p = [46, 46]

/-- Strip trailing `/`. -/
def rstripSlash (p : Bytes) : Bytes := (p.reverse.dropWhile (· == 47)).reverse

def endsWith (p s : Bytes) : Bool := s.isSuffixOf p

def Tree.read (t : Tree) (path : Bytes) : ReadResult :=
  if path = [] then .openErr .ENOENT else
  let comps := splitOn 47 path
  if comps.any (·.length > 255) then .openErr .ENAMETOOLONG else
  let prefixCheck : Option ReadResult :=
    ((List.range comps.length).drop 1).findSome? fun k =>
      let pre := joinSlash (comps.take k)
      if isDotName pre then none
      else match t.find pre with
        | some (.file _) | some .noperm | some (.eio _) => some (.openErr .ENOTDIR)
        | some .loop => some (.openErr .ELOOP)
        | none | some .dangling => some (.openErr .ENOENT)
        | some .dir => none
  match prefixCheck with
  | some r => r
  | none =>
    let key := if endsWith path [47] && !(rstripSlash path).isEmpty then rstripSlash path else path
    if key = [46] || key = [46, 46] || key = [47] || endsWith key [47, 46] || endsWith key [47, 46, 46]
    then .readErr .EISDIR []
    else match t.find key with
      | none => .openErr .ENOENT
      | some (.file d) => .ok d
      | some .noperm => .openErr .EACCES
      | some .dir => .readErr .EISDIR []
      | some .loop => .openErr .ELOOP
      | some .dangling => .openErr .ENOENT
      | some (.eio pre) => .readErr .EIO pre

end Silmaril.Apps.Sha256sum
