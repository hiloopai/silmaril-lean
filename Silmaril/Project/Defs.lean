module

public import Silmaril.Project.Core.Defs
public import Silmaril.Project.Core.Thms
public import Silmaril.Project.Registry.Defs
public import Silmaril.Project.Registry.Dag.Defs
public import Silmaril.Project.Registry.Predicate.Defs
public import Silmaril.Project.Registry.Artifacts.Defs
public import Silmaril.Project.Registry.Value.Defs
public import Silmaril.Project.Registry.Room.Defs
public import Silmaril.Project.Registry.Load.Defs
public import Silmaril.Project.Registry.Attr.Defs

/-!
# Silmaril projects

The header of the `Project` region, and the module a project imports (the guide is
`docs/projects/silmaril-projects.md`):

* the definitions (`Silmaril.Project.Core.Defs`: `ArtifactType`, `blob`, `Format` and its laws,
  `Equivalent`, `Holds`, `Value`), the lemmas about values and the tactic `silmaril_decide`
  (`Silmaril.Project.Core.Thms`);
* the registry (`Silmaril.Project.Registry.Defs`: the `silmaril` command, the table of kind
  handlers, `#silmaril`, `#silmaril_dump`) with every layer's handlers and sugar forms
  (`Silmaril.Project.Registry.{Dag,Predicate,Artifacts,Value,Room}.Defs`), records files
  (`silmaril load`, `Silmaril.Project.Registry.Load.Defs`) and the attribute forms
  (`@[problem "N" (k := v)]`, `@[conjecture]`, `@[value]`, `Silmaril.Project.Registry.Attr.Defs`);
* the built-in artifact type `blob` and the identity format `bytes`, registered below.

The format adapters over silmaril's parsers are `Silmaril.Project.Formats.Defs`, the standard
shapes `Silmaril.Project.Shapes.Format.Defs` (formats and values),
`Silmaril.Project.Shapes.Elf.Defs` (ELF executables) and `Silmaril.Project.Shapes.X86.Defs`
(x86-64 functions). A project registers its own
artifacts with `silmaril artifacts "silmaril/artifacts.toml"` in one of its modules; this
header reads no file.
-/

namespace Silmaril.Project

silmaril artifact_type blob := Silmaril.Project.blob
  (doc := "Bytes, identified by a raw-codec BLAKE3 CIDv1 (bafkr4i…)")

silmaril format bytes := Silmaril.Project.bytes (doc := "The identity format: a blob as its bytes")
silmaril format_law bytes roundtrip := Silmaril.Project.bytes_roundtrip

end Silmaril.Project
