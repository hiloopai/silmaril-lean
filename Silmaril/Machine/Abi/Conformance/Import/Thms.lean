module

public import Silmaril.Machine.Abi.Conformance.Import.Defs
public import Silmaril.Machine.Abi.Conformance.LeafArith.Defs
public import Silmaril.Data.Layout.Header.Import.Pinned.Thms
import Silmaril.Proofs.Machine.Abi.Conformance.Import

/-!
# Coverage and `Declares` from the clang import: theorems

PROVED (standard axioms; the per-header facts rewrite with `Pinned.import_<name>` and run
`decide +kernel` on the literal entries, never on the JSON):

* `declares_iff_of_header`, `declares_iff_of_all`: when the subset reader's header is the
  import's (or the two agree on a list of names, and `A` lowers alike with the two routes' tag
  definitions, as `sysvInt`, which reads none, does) and the conventions are `sysvInt`'s, the
  two routes give the same `Declares`;
* `arith_declares_iff`: for `arith.h`, `Declares sysvInt LeafArith.hdr` (the subset reader) and
  `DeclaresImport sysvInt sysvCcs Pinned.arith` (clang) are the same relation, for every name and
  prototype;
* `zlibSolo_declares_iff`, `zlibHosted_declares_iff`: the same for the checksum API, on the
  names where the two routes agree (all eleven under `-DZ_SOLO`; nine hosted);
* `zlibHosted_disagreement_lowers_alike`: the hosted disagreement (`z_size_t` = `size_t` as
  `.size` or as `unsigned long`) lowers to the same System V prototype, `uint64 (uint64,
  pointer, uint64)`;
* `arith_coverage`: the twenty functions are claimable, none unsupported, and the conformance
  example's `LeafArith.coverage` (checked by the subset route, `Coverage.check`) is also a
  checked coverage of the import;
* `zlibSolo_coverage`, `zlibHosted_coverage`, `probe_coverage`, `glibcString_coverage`: each
  header's claimable functions and its unsupported ones with the reasons.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance

open Silmaril.Data.Layout.Header.Import
open Silmaril.Data.Layout.Header.Import.Pinned

variable {A : AbiDef} {hdr : HeaderSrc} {ccs : List CallConv} {imp : Imported} {f : String}
  {p : A.V.Proto}

theorem declares_iff_of_header
    (h : (Silmaril.Data.Layout.Header.read hdr.files hdr.root).toOption = some imp.header)
    (hcc : ccsOk ccs imp = true) :
    Declares A hdr f p ↔ DeclaresImport A ccs imp f p :=
  Silmaril.Proofs.Machine.Abi.Conformance.Import.declares_iff_of_header h hcc

theorem declares_iff_of_all {fs : List String}
    (h : fs.all (fun f => hdr.proto? f == imp.proto? f &&
      (imp.fn? f).any (fun x => ccs.contains x.2.cc)) = true)
    (he : ∀ cp, A.lower hdr.env cp = A.lower imp.header.env cp) :
    ∀ f ∈ fs, ∀ p : A.V.Proto, Declares A hdr f p ↔ DeclaresImport A ccs imp f p :=
  Silmaril.Proofs.Machine.Abi.Conformance.Import.declares_iff_of_all h he

set_option maxRecDepth 100000 in
theorem arith_coverage :
    claimable sysvInt sysvCcs arith = ["sc3", "rt_write", "rt_read", "rt_puts", "rt_put_hex",
      "rt_check", "rt_failures", "rt_finish", "memcpy", "memset", "memmove", "memcmp", "strlen",
      "popcount32", "gcd_u32", "clamp_i32", "isqrt_u32", "sat_add_u32", "bswap32_manual",
      "ilog2_u32"] ∧
    unsupportedFns sysvInt sysvCcs arith = [] ∧ ccsOk sysvCcs arith = true ∧
    checkCoverage sysvInt sysvCcs arith LeafArith.coverage = true ∧
    Coverage.check sysvInt LeafArith.hdr LeafArith.coverage = true := by
  rw [import_arith]; decide +kernel

theorem arith_declares_iff (f : String) (p : sysvInt.V.Proto) :
    Declares sysvInt LeafArith.hdr f p ↔ DeclaresImport sysvInt sysvCcs arith f p :=
  declares_iff_of_header arith_routes_agree.2.2.2 arith_coverage.2.2.1

set_option maxRecDepth 100000 in
theorem zlibSolo_declares_iff :
    ∀ f ∈ Silmaril.Data.Layout.Header.Zlib.checksumApi, ∀ p : sysvInt.V.Proto,
      Declares sysvInt Silmaril.Data.Layout.Header.Zlib.solo f p ↔
        DeclaresImport sysvInt sysvCcs zlibSolo f p :=
  declares_iff_of_all (by rw [import_zlibSolo]; decide +kernel) (fun _ => rfl)

set_option maxRecDepth 100000 in
theorem zlibHosted_declares_iff :
    ∀ f ∈ ["zlibVersion", "zlibCompileFlags", "adler32", "crc32", "crc32_combine_op",
        "adler32_combine", "crc32_combine", "crc32_combine_gen", "get_crc_table"],
      ∀ p : sysvInt.V.Proto,
      Declares sysvInt Silmaril.Data.Layout.Header.Zlib.hosted f p ↔
        DeclaresImport sysvInt sysvCcs zlibHosted f p :=
  declares_iff_of_all (by rw [import_zlibHosted]; decide +kernel) (fun _ => rfl)

theorem zlibHosted_disagreement_lowers_alike :
    (sysvInt.lower [] (Silmaril.Data.Layout.Header.Zlib.sizedProto .size)).toOption.map
        (·.signature) = some ⟨[.uint64, .pointer, .uint64], some .uint64⟩ ∧
    (sysvInt.lower [] (Silmaril.Data.Layout.Header.Zlib.sizedProto .long)).toOption.map
        (·.signature) = some ⟨[.uint64, .pointer, .uint64], some .uint64⟩ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem zlibSolo_coverage :
    (claimable sysvInt sysvCcs zlibSolo).length = 47 ∧
    Silmaril.Data.Layout.Header.Zlib.checksumApi.all
      (claimable sysvInt sysvCcs zlibSolo).contains = true ∧
    unsupportedFns sysvInt sysvCcs zlibSolo =
      [("inflateBack", "parameter 2: typedef in_func: function or function-pointer type: \
        outside CProto")] ∧
    (interface sysvInt sysvCcs zlibSolo).length = 48 := by
  rw [import_zlibSolo]; decide +kernel

set_option maxRecDepth 100000 in
theorem zlibHosted_coverage :
    (claimable sysvInt sysvCcs zlibHosted).length = 79 ∧
    Silmaril.Data.Layout.Header.Zlib.checksumApi.all
      (claimable sysvInt sysvCcs zlibHosted).contains = true ∧
    unsupportedFns sysvInt sysvCcs zlibHosted =
      [("inflateBack", "parameter 2: typedef in_func: function or function-pointer type: \
        outside CProto"),
       ("gzprintf", "variadic: the %al count and va_list are outside the INTEGER fragment")] ∧
    (interface sysvInt sysvCcs zlibHosted).length = 81 := by
  rw [import_zlibHosted]; decide +kernel

set_option maxRecDepth 100000 in
theorem probe_coverage :
    claimable sysvInt sysvCcs probe =
      ["plain", "die", "die2", "nn", "old", "hidden", "sysv", "arr", "mk"] ∧
    unsupportedFns sysvInt sysvCcs probe =
      [("knr", "no prototype (K&R f()): outside CProto"),
       ("vf", "variadic: the %al count and va_list are outside the INTEGER fragment"),
       ("renamed", "asm label: the symbol is renamed_v2, and a row binds the C name"),
       ("win", "calling convention ms_abi"),
       ("rc", "calling convention regcall"),
       ("by_value", "struct pair by value: aggregates are outside the INTEGER fragment"),
       ("fp", "floating type: SSE/x87 classes are outside the INTEGER fragment"),
       ("flag", "result: _Bool: outside the INTEGER fragment (4- and 8-byte integers and \
        pointers)"),
       ("sort", "parameter 3: typedef cmp_fn: function or function-pointer type: outside CProto"),
       ("paint", "enum color: enumerations are outside the INTEGER fragment")] ∧
    (table sysvInt sysvCcs probe).filter (fun x => x.2 matches .internal _) =
      [("inl", .internal "static: internal linkage")] := by
  rw [import_probe]; decide +kernel

set_option maxRecDepth 100000 in
theorem glibcString_coverage :
    (claimable sysvInt sysvCcs glibcString).length = 39 ∧
    unsupportedFns sysvInt sysvCcs glibcString =
      [("strerror_r", "asm label: the symbol is __xpg_strerror_r, and a row binds the C name")] ∧
    ((table sysvInt sysvCcs glibcString).filter (fun x => x.2 matches .internal _)).length =
      26 := by
  rw [import_glibcString]; decide +kernel

end Silmaril.Machine.Abi.Conformance

end
