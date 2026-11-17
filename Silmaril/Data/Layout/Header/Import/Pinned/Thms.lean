module

public import Silmaril.Data.Layout.Header.Import.Pinned.Defs
public import Silmaril.Data.Layout.Header.Import.Pinned.Arith.Thms
public import Silmaril.Data.Layout.Header.Import.Pinned.Probe.Thms
public import Silmaril.Data.Layout.Header.Import.Pinned.ZlibSolo.Thms
public import Silmaril.Data.Layout.Header.Import.Pinned.ZlibHosted.Thms
public import Silmaril.Data.Layout.Header.Import.Pinned.GlibcString.Thms
public import Silmaril.Data.Layout.Header.Import.Pinned.GlibcMath.Thms
public import Silmaril.Data.Layout.Header.Import.Pinned.GlibcStdlib.Thms
public import Silmaril.Data.Layout.Header.Zlib.Defs

/-!
# The pinned clang imports: the cross-check with the subset reader

PROVED (standard axioms). Each artifact's JSON is parsed in the kernel once, by
`import_<name>` (`Pinned.<Name>.Thms`, one module each, so they check in parallel); the
theorems here rewrite with it and compute (`decide +kernel`) on the literal entries:

* `arith_routes_agree`: for `arith.h` with `rt.h`, the subset reader and the clang import give
  **the same `Header`**: the same six typedefs and the same twenty prototypes, in order
  (`Header.read` on the text equals `Imported.header` of the pinned JSON);
* `zlibSolo_routes_agree`: under `-DZ_SOLO`, the eleven functions of the checksum API that the
  subset reader reads from the pinned excerpt have the same `CProto` in the clang import of the
  real `zlib.h` and `zconf.h`;
* `zlibHosted_routes`: hosted, nine agree and **two disagree**: `adler32_z` and `crc32_z`. Their
  `z_size_t` is `size_t`, which the subset reader takes as its built-in `.int .size .unsigned`
  and clang as `unsigned long` (`.int .long .unsigned`, from stddef.h). The two `CProto`s lower
  to the same System V prototype (`Machine.Abi.Conformance.Import.Thms`);
* `probe_reads`: the probe header's kinds, conventions (`ms_abi`, `sysv_abi`, `regcall`),
  attributes, asm label and tag definitions as the import reads them;
* `glibcMath_reads`: glibc's `math.h` (libm) as pinned (default feature set): 623 retained
  entries, all imported; `glibcMath_implicit_duplicates`: each of the 177 implicit builtin
  entries duplicates an explicit declaration of the same name; the 438 explicit names are
  distinct.
* `glibcStdlib_reads`: glibc's `stdlib.h` (with `alloca.h`) as pinned: 130 retained entries,
  all imported; 102 explicit function entries, 101 names (`reallocarray` twice); 9 entries
  whose prototype the import cannot represent, listed; the 19 implicit builtin entries
  duplicate explicit declarations.
* `glibcString_reads`: glibc's `string.h`: 66 entries, 26 of them clang's implicit builtin
  declarations, and `strerror_r`'s asm label `__xpg_strerror_r` (glibc's `__REDIRECT_NTH`);
* `provenance_reads`: the provenance records of the artifacts, as read from their `.prov`.

The coverage of each header per route is in `Machine.Abi.Conformance.Import.Thms`.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Import.Pinned

set_option maxRecDepth 100000 in
theorem arith_routes_agree :
    arith.error = none ∧ arith.entries.length = 26 ∧ arith.conflicts = [] ∧
    (read arithFiles "arith.h").toOption = some arith.header := by
  rw [import_arith]; decide +kernel

set_option maxRecDepth 100000 in
theorem zlibSolo_routes_agree :
    zlibSolo.error = none ∧ zlibSolo.entries.length = 72 ∧ zlibSolo.conflicts = [] ∧
    compareRead Zlib.soloFiles "zlib.h" zlibSolo = some { agree := Zlib.checksumApi } := by
  rw [import_zlibSolo]; decide +kernel

set_option maxRecDepth 100000 in
theorem zlibHosted_routes :
    zlibHosted.error = none ∧ zlibHosted.entries.length = 108 ∧ zlibHosted.conflicts = [] ∧
    compareRead Zlib.hostedFiles "zlib.h" zlibHosted = some
      { agree := ["zlibVersion", "zlibCompileFlags", "adler32", "crc32", "crc32_combine_op",
          "adler32_combine", "crc32_combine", "crc32_combine_gen", "get_crc_table"]
        disagree := [("adler32_z", Zlib.sizedProto .size, Zlib.sizedProto .long),
          ("crc32_z", Zlib.sizedProto .size, Zlib.sizedProto .long)] } := by
  rw [import_zlibHosted]; decide +kernel

set_option maxRecDepth 100000 in
theorem probe_reads :
    probe.error = none ∧
    probe.entries.map (·.kind) = [.typedef, .struct, .typedef, .struct, .union, .enum, .typedef,
      .typedef, .variable, .variable] ++ List.replicate 21 .function ∧
    probe.entries.filterMap (fun e => match e.body with
      | .tag d => some (e.name, d) | _ => none) =
      [("pair", true), ("fwd", false), ("u", true), ("color", true)] ∧
    probe.functions.map (fun (e, f) => (e.name, f.cc, f.attrs, f.asmLabel)) =
      [("plain", .c, [], none), ("knr", .c, [], none), ("vf", .c, [.format], none),
       ("die", .c, [.noreturn], none), ("die2", .c, [.noreturn], none),
       ("nn", .c, [.nonnull], none), ("old", .c, [.deprecated], none),
       ("hidden", .c, [.visibility "hidden"], none),
       ("renamed", .c, [.asmLabel], some "renamed_v2"), ("win", .msAbi, [], none),
       ("sysv", .sysvAbi, [], none), ("rc", .regcall, [], none), ("by_value", .c, [], none),
       ("fp", .c, [], none), ("flag", .c, [], none), ("sort", .c, [], none),
       ("arr", .c, [], none), ("mk", .c, [], none), ("paint", .c, [], none),
       ("inl", .c, [], none), ("plain", .c, [], none)] := by
  rw [import_probe]; decide +kernel

set_option maxRecDepth 100000 in
theorem glibcString_reads :
    glibcString.error = none ∧ glibcString.entries.length = 66 ∧
    (glibcString.entries.filter (·.implicit)).length = 26 ∧
    (glibcString.fn? "strerror_r").map (fun (_, f) => (f.symbol, f.asmLabel)) =
      some ("__xpg_strerror_r", some "__xpg_strerror_r") := by
  rw [import_glibcString]; decide +kernel

set_option maxRecDepth 100000 in
/-- glibc's `math.h` (libm), **as pinned**: clang 18.1.8, `x86_64-unknown-linux-gnu`,
`-std=gnu11` with no feature macro (glibc's default feature set). The artifact keeps the
top-level declarations of `math.h`, `bits/mathcalls.h`, `bits/mathcalls-helper-functions.h` and
`bits/floatn-common.h`; **every retained entry is imported**: no entry whose body the import
cannot read, and no function whose prototype it cannot represent; no asm renames: 623 entries, 615 functions (177 of them clang's implicit builtin declarations, see
`glibcMath_implicit_duplicates`). `sin` is `double (double)`, `sinf` `float (float)` and `sinl`
`long double (long double)`.

This is not the whole `math.h` API. What the file filter drops of the translation unit (no
function declaration; 64 declarations of `bits/types.h` and 5 implicit typedefs) and the 488
public names declared only under `-D_GNU_SOURCE` (the `_FloatN`/`_FloatNx` functions,
`canonicalize*`, the narrowing `f32add`/`daddl` family, `exp10`, …) are in the recipe's report
`examples/headers/clang/glibc-math.scope`, which `recipe.sh --check` regenerates and compares
byte for byte: a recipe-level check of clang's output, not a theorem. -/
theorem glibcMath_reads :
    glibcMath.error = none ∧ glibcMath.entries.length = 623 ∧
    (glibcMath.entries.filter (·.kind == .function)).length = 615 ∧
    (glibcMath.entries.filter (·.implicit)).length = 177 ∧
    (glibcMath.entries.filter (fun e => match e.body with
      | .unsupported _ => true | _ => false)).length = 0 ∧
    (glibcMath.entries.filter (fun e => match e.body with
      | .function f => (match f.proto with | .unsupported _ => true | _ => false)
      | _ => false)).length = 0 ∧
    (glibcMath.entries.filter (fun e => match e.body with
      | .function f => f.asmLabel.isSome | _ => false)).length = 0 ∧
    (glibcMath.fn? "sin").map (fun (_, f) => f.proto) =
      some (.ok ⟨.float .double, [.float .double], false⟩) ∧
    (glibcMath.fn? "sinf").map (fun (_, f) => f.proto) =
      some (.ok ⟨.float .float, [.float .float], false⟩) ∧
    (glibcMath.fn? "sinl").map (fun (_, f) => f.proto) =
      some (.ok ⟨.float .longDouble, [.float .longDouble], false⟩) := by
  rw [import_glibcMath]; decide +kernel

set_option maxRecDepth 100000 in
/-- **Where the 177 implicit `math.h` entries come from.** Clang adds an implicit declaration
for a library builtin (`acos`, `cos`, …) where the header first declares it; every implicit
entry of the pinned import has an explicit (non-implicit) entry of the same name, and the 438
explicit function entries have distinct names. So an ABI classification that treats implicit
entries as internal (`Conformance.Import.status`) classifies no public name as internal: the
explicit declaration of the same name is classified on its own. -/
theorem glibcMath_implicit_duplicates :
    (glibcMath.entries.filter (·.implicit)).all (fun e =>
      glibcMath.entries.any (fun e' => !e'.implicit && e'.kind == .function && e'.name == e.name)) ∧
    ((glibcMath.entries.filter (fun e => !e.implicit && e.kind == .function)).map
      (·.name)).length = 438 ∧
    ((glibcMath.entries.filter (fun e => !e.implicit && e.kind == .function)).map
      (·.name)).Nodup := by
  rw [import_glibcMath]; decide +kernel

set_option maxRecDepth 100000 in
/-- glibc's `stdlib.h` **as pinned** (clang 18.1.8, `x86_64-unknown-linux-gnu`, `-std=gnu11`, default
feature set), with `alloca.h`, which it includes by default. Every retained entry is imported
(none whose body the import cannot read): 130 entries, 121 functions, 19 of them clang's
implicit builtin declarations, each the duplicate of an explicit declaration of the same name.
The 102 explicit function entries have 101 distinct names: `reallocarray` is declared twice
(lines 576 and 582). **9 of them keep their entry but not a prototype**: the import cannot
represent it (`Fn.proto = .unsupported`), for an unresolved typedef (`size_t`, `int32_t`,
`__uint32_t`, `wchar_t`) or a function-pointer parameter (`CProto` has none), listed exactly. No
asm renames. What the file filter drops (8 function declarations: internal inline helpers of
`bits/byteswap.h` and `bits/uintn-identity.h`, and `sys/select.h`'s `select`/`pselect`) and the 37
names only under `-D_GNU_SOURCE` are in `examples/headers/clang/glibc-stdlib.scope` (checked
byte for byte, not a theorem). -/
theorem glibcStdlib_reads :
    glibcStdlib.error = none ∧ glibcStdlib.entries.length = 130 ∧
    (glibcStdlib.entries.filter (·.kind == .function)).length = 121 ∧
    (glibcStdlib.entries.filter (·.implicit)).length = 19 ∧
    (glibcStdlib.entries.filter (fun e => match e.body with
      | .unsupported _ => true | _ => false)).length = 0 ∧
    (glibcStdlib.entries.filter (fun e => match e.body with
      | .function f => f.asmLabel.isSome | _ => false)).length = 0 ∧
    (glibcStdlib.entries.filter (·.implicit)).all (fun e =>
      glibcStdlib.entries.any (fun e' => !e'.implicit && e'.kind == .function && e'.name == e.name)) ∧
    (glibcStdlib.entries.filter (fun e => !e.implicit && e.kind == .function)).length = 102 ∧
    ((glibcStdlib.entries.filter (fun e => !e.implicit && e.kind == .function)).map
      (·.name)).eraseDups.length = 101 ∧
    (glibcStdlib.entries.filter (fun e => !e.implicit && e.name == "reallocarray")).length = 2 ∧
    glibcStdlib.entries.filterMap (fun e => match e.body with
      | .function f => (match f.proto with | .unsupported w => some (e.name, w) | _ => none)
      | _ => none) =
      [("__ctype_get_mb_cur_max", "result: unknown type name size_t"),
       ("random_r", "parameter 2: unknown type name int32_t"),
       ("arc4random", "result: unknown type name __uint32_t"),
       ("atexit", "parameter 1: function or function-pointer type: outside CProto"),
       ("at_quick_exit", "parameter 1: function or function-pointer type: outside CProto"),
       ("on_exit", "parameter 1: function or function-pointer type: outside CProto"),
       ("bsearch", "parameter 5: typedef __compar_fn_t: function or function-pointer type: outside CProto"),
       ("qsort", "parameter 4: typedef __compar_fn_t: function or function-pointer type: outside CProto"),
       ("mbtowc", "parameter 1: unknown type name wchar_t")] := by
  rw [import_glibcStdlib]; decide +kernel

set_option maxRecDepth 100000 in
theorem provenance_reads :
    (Provenance.parse arithProv).image =
      "silkeh/clang@sha256:3914c93a02e866795aafc80737488e515b96390eff3d2787cf8c5095997baea9" ∧
    (Provenance.parse arithProv).target = "x86_64-unknown-linux-gnu" ∧
    (Provenance.parse arithProv).std = "gnu11" ∧
    (Provenance.parse arithProv).includes = ["../common"] ∧
    (Provenance.parse arithProv).inputs.map (·.1) = ["arith.h", "../common/rt.h"] ∧
    (Provenance.parse zlibSoloProv).defines = ["Z_SOLO"] ∧
    (Provenance.parse zlibSoloProv).source = some
      "zlib-1.3.1.tar.gz 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23 \
      https://github.com/madler/zlib/releases/download/v1.3.1/zlib-1.3.1.tar.gz" ∧
    (Provenance.parse zlibHostedProv).defines = [] := by
  decide +kernel

end Silmaril.Data.Layout.Header.Import.Pinned

end
