module

public import Silmaril.Elf.Ast.Defs
public import Silmaril.Elf.Parse.Defs
public import Silmaril.Elf.Lookup.Defs
public import Silmaril.Elf.Index.Defs
public import Silmaril.Elf.Facts.Defs
public import Silmaril.Elf.Shapes.Defs

/-! # The ELF verification API (`Silmaril.Elf`)

One namespace for what a proof needs to know about an ELF64 file: import this module.

| layer | module | main names |
|---|---|---|
| bytes | `Silmaril.Elf.Link.DynElf` (reused) | `Rd`, `blobRead`, `Chunk`, `sparseRead`, `run_sparse`, `pageRead` |
| AST | `Silmaril.Elf.Ast` | `File`, `Section`, `Body`, `Span`, `Kind`, `File.kind` |
| parse | `Silmaril.Elf.Parse` | `read`, `parse`, `Parses`, `format` |
| semantics | `Silmaril.Elf.Lookup` | `Ref`, `Ver`, `Def`, `Sel`, `File.lookupDef`, `File.select`, `File.relocs`, `DynConsistent` |
| index | `Silmaril.Elf.Index` | `Index`, `Index.build`, `Index.lookup` |
| facts | `Silmaril.Elf.Facts` | `KindIs`, `SymbolAt`, `Lookup`, `Needed`, `Relocs`, `Placement`, `CodeAt`, `Binds` |
| shapes | `Silmaril.Elf.Shapes` | `silmaril.shapes.elf.{parses,index,kind,symbol,lookup,needed,relocs,placement,code_at,binds}` |
| bridges | `Silmaril.Elf.Bridge` (import separately) | `Task.*` relating `DynElf`, `ElfBind`, `Dyn.Loader`, silmaril readers |
| loading models | `Silmaril.Elf.Link.{ElfBind,Dyn.Loader,Dyn.Image}` (import separately) | `ElfBind.{Bound,CodeAt,Placement,RoLoaded}`, `Dyn.ExeLoaded` (ld.so's effect, a specified relation) |
| equivalences | `Silmaril.Elf.BindEq` (import separately) | `codeAt_iff`, `placement_iff`, `directCall_of_binds` |
| executables | `Silmaril.Elf.Exe` (import separately) | `NoTextRelD`, `roLoaded_of_exeLoaded`, `ExeFacts` |
| CLI executables | `Silmaril.Elf.CliExe` (import separately) | `silmaril.shapes.elf.cli_exe` over `Silmaril.Cli.Institution` |

-/
