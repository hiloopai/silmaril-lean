module

public import Silmaril.Elf.Link.Dyn.Elf.Defs
public import Silmaril.Project.Shapes.Elf.Defs
public meta import Lean.Elab.Term

/-!
# Included files as pages

`include_bytes` holds a file as 4 KiB chunk literals (`IncludeBytes.decode 4096 len cs`).
`pages c len cs` reads that list as the sparse view (`Chunk`s, `Dyn.Elf`) whose chunks are
exactly the literals, at their offsets. `Thms.pages_of` proves once, for every chunk list,
that each page is part of the file the chunks denote (`ChunksOf`). A reading program can then
run on the pages (`sparseRead`) instead of on the 2 MB file as one number (`blobRead`),
and `run_sparse` transfers its result. Every kernel read then touches one 4 KiB literal, not
the whole file. (Measured on glibc's `libc.so.6`: one ld.so lookup on the whole number took
3.7 GB, and 200 took 10.5 GB.)

`chunks_of% n` elaborates to the chunk-literal list of the `include_bytes` constant `n`, so
that a proof module can name it without the bytes appearing in any source file.
-/

@[expose] public section

namespace Silmaril.Elf.Link.DynElf

/-- The pages of a chunk list: chunk `k` at offset `c * k`, of length `min c (len - c * k)`;
the list stops after the chunk that reaches `len`. -/
def pages (c : Nat) : Nat → List Nat → List Chunk
  | _, [] => []
  | len, x :: cs =>
    ⟨0, min c len, x⟩ ::
      (if len ≤ c then [] else (pages c (len - c) cs).map fun ch => { ch with off := ch.off + c })

/-- The pages of a chunk list from offset `off`, built in one pass (what a kernel evaluates;
`pages c len cs = pagesFrom c 0 len cs` in content). -/
def pagesFrom (c : Nat) (off : Nat) : Nat → List Nat → List Chunk
  | _, [] => []
  | len, x :: cs => ⟨off, min c len, x⟩ :: (if len ≤ c then [] else pagesFrom c (off + c) (len - c) cs)

/-- **The page reader**: a read inside page `o / c` of `pg` is answered by that page alone
(one list index and one shift of a page literal); a read that runs past the end of the page
is answered by that page and the next one; anything else fails. -/
def pageRead (c : Nat) (pg : List Chunk) (o w : Nat) : Option Nat :=
  match pg[o / c]? with
  | some ch =>
    match ch.read o w with
    | some v => some v
    | none =>
      let a := ch.off + ch.len - o
      if 0 < a ∧ a < w then
        match ch.read o a, pg[o / c + 1]? with
        | some lo, some ch' => (ch'.read (o + a) (w - a)).map fun hi => lo + 2 ^ (8 * a) * hi
        | _, _ => none
      else none
  | none => none

end Silmaril.Elf.Link.DynElf

open Lean Elab Term Meta in
/-- `chunks_of% n`: the chunk literals of the `include_bytes` constant `n`
(`n := ⟨IncludeBytes.decode c len cs⟩` elaborates to `cs`). -/
elab "chunks_of% " n:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo n
  let some v := (← getConstInfo name).value? (allowOpaque := true)
    | throwError "chunks_of%: {name} has no value"
  match v.getAppFnArgs with
  | (``Silmaril.Formats.Bytes.mk, #[d]) =>
    match d.getAppFnArgs with
    | (``Silmaril.IncludeBytes.decode, #[_, _, cs]) => return cs
    | _ => throwError "chunks_of%: {name} is not `⟨include_bytes …⟩`"
  | _ => throwError "chunks_of%: {name} is not `⟨include_bytes …⟩`"

open Lean Elab Term Meta in
/-- `bytes_of% n off len`: the `len` bytes at offset `off` of the `include_bytes` constant `n`,
as a `List (BitVec 8)` literal computed at elaboration from its chunk literals. The bytes enter
the elaborated term (and the `.olean`), never a source file. -/
elab "bytes_of% " n:ident off:num len:num : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo n
  let some v := (← getConstInfo name).value? (allowOpaque := true)
    | throwError "bytes_of%: {name} has no value"
  let some cs := (match v.getAppFnArgs with
    | (``Silmaril.Formats.Bytes.mk, #[d]) =>
      match d.getAppFnArgs with
      | (``Silmaril.IncludeBytes.decode, #[c, _, cs]) => some (c, cs)
      | _ => none
    | _ => none) | throwError "bytes_of%: {name} is not `⟨include_bytes …⟩`"
  let some chunk := (← instantiateMVars cs.1).rawNatLit? <|> cs.1.nat?
    | throwError "bytes_of%: chunk size is not a literal"
  let some (_, elems) := cs.2.listLit? | throwError "bytes_of%: chunks are not a list literal"
  let vals ← elems.mapM fun e => match e.rawNatLit? <|> e.nat? with
    | some k => pure k
    | none => throwError "bytes_of%: a chunk is not a literal"
  let o := off.getNat; let l := len.getNat
  let byte (i : Nat) : Nat := (vals.getD (i / chunk) 0 >>> (8 * (i % chunk))) % 256
  let ty := mkApp (mkConst ``BitVec) (mkNatLit 8)
  mkListLit ty ((List.range l).map fun i =>
    mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 8) (mkNatLit (byte (o + i))))
