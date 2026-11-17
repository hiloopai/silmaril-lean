module

public import Silmaril.Data.Layout.Header.Import.Pinned.Defs
public import Silmaril.Data.Layout.Header.Import.Pinned.Arith.Thms
public import Silmaril.Data.Layout.Header.Import.Pinned.Probe.Thms
public import Silmaril.Data.Layout.Header.Import.Pinned.ZlibSolo.Thms
public import Silmaril.Data.Layout.Header.Import.Pinned.ZlibHosted.Thms
public import Silmaril.Data.Layout.Header.Import.Pinned.GlibcString.Thms
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
