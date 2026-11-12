module

public import Silmaril.Compiler.C.Sem.Triangle.Defs
public import Silmaril.Cerberus.Ail.Codec.Defs
@[expose] public section

/-!
# ccomp's front end with its C library

`ccompMir` (`Triangle.lean`) links a program's own unit only, so every program that calls
`abort` or `exit` fails to link. ccomp's real link (`Silmaril.Compile.C.Main`, `run.link`)
compiles `tools/ccomp/runtime/libc.c` first, as the weak unit `u0`, then the program as `u1`.
`ccompMirRt` is that pipeline, as a function: the C library is its typed Ail, embedded.

`runtime/libc.ail` is the typed-Ail document ccomp's link produces for `libc.c` (the
preprocessor flags of `Silmaril.Compile.C.Main.preprocess` with no user flags, then
`--ail-from-oracle`), generated from the repository root with cc 13.3.0 and the Cerberus oracle:

```
rt=cerberus-runtime   # the Cerberus runtime directory
cc -std=c11 -E -CC -Werror -Wno-builtin-macro-redefined -nostdinc -undef -D__cerb__ \
  -I$rt/libc/include -I$rt/libc/include/posix -include $rt/libc/include/builtins.h \
  tools/ccomp/runtime/libc.c > libc.i
cerb-oracle --level tail --output libc.ail libc.i
```

(`libc.ail` was generated from the revision of `libc.c` with sha256 `285f7c74…9828497`; the
`libc.c` in this repository may be later. The runtime directory in the source locations of
`libc.ail` is written `cerberus-runtime`, without the generating machine's prefix.)
-/

namespace Silmaril.Compile.C.Sem

/-- The typed Ail of ccomp's C library (`tools/ccomp/runtime/libc.c`), as a document. -/
def ccompLibcDoc : String := include_str "runtime/libc.ail"

/-- The typed Ail of ccomp's C library. -/
def ccompLibc : Option Silmaril.Cerberus.Ail.TypedProgram :=
  match Silmaril.Cerberus.Ail.Codec.readTailDocument ccompLibcDoc with
  | .ok (.document _ _ prog) => some prog
  | _ => none

/-- ccomp's Mir units of a single typed-Ail translation unit linked with ccomp's C library:
the runtime unit, then the definitions reachable from `main` of the library (weak, `u0`) and
the program (`u1`) (the `link` path of `Silmaril.Compile.C.Main`). -/
def ccompMirRt (p : Silmaril.Cerberus.Ail.TypedProgram) : Option (Array Mir.Unit) :=
  match ccompLibc with
  | none => none
  | some libc =>
    match Silmaril.Compile.Forks.Csem.C.compileReachableUnits
        #[{ tag := "u0", prog := libc, weak := true }, { tag := "u1", prog := p }] ["main"] with
    | .ok units =>
      match (units.flatMap (·.funcs)).find? (·.name == "main") with
      | some main => some (#[Target.unit main.params.length main.results] ++ units)
      | none => none
    | .error _ => none

end Silmaril.Compile.C.Sem
