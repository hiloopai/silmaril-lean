module

public import Silmaril.Elf.Link.Dyn.Streams.Extra

/-! # `sha256sum`'s import table

`shaContracts` (`Streams.Defs`), B's `strcspn`/`fputs_unlocked` (`Streams.Extra`) and
`clearerr_unlocked` (standard input's tail in `digest_file`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Streams

open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Imports
open Silmaril.X86.RelIsa (Res)

/-- **The import table of `sha256sum`'s happy path.** -/
def shaTable (E : Env) (R : ShaRep) (W : World) : List (Name × (PState → Res PState → Prop)) :=
  shaContracts E R W ++ [(nm "strcspn", strcspnStep E W), (nm "fputs_unlocked", fputsStep E W),
    (nm "clearerr_unlocked", clearerrStep E W)]

end Silmaril.Elf.Link.Dyn.Streams
