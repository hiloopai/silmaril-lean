module

public import Silmaril.Elf.Abi.ZlibMatrix.Api.Defs
public import Silmaril.Elf.Abi.ZlibLibz.Thms
public import Silmaril.Machine.Abi.Conformance.Zlib.Api.Thms
import Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi

/-! # The 11-declaration zlib.h checksum excerpt in Ubuntu's `libz.so.1.3`: theorems

PROVED (standard axioms), proofs in `Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi`: for each of the
seven functions, `*_code` (`CodeOf` through a structural model of ld.so's versioned lookup), `*_untouched` (8-byte
relocation types only, none on the code or the read-only data), `*_declared` (`Declares` in the
hosted header); `coverage_check`, `coverage_complete` (nothing excluded); `*_of` (each row from
its task) and `header_complete_of`: **complete header satisfaction from the eleven tasks**.

OPEN: the eleven conformance tasks (`ZlibLibz.Task.*`, `Task.*` here). -/

@[expose] public section

namespace Silmaril.Elf.Abi.ZlibMatrix.Api

open Silmaril.Elf
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Zlib.Api
open Silmaril.Machine.Abi.Conformance.ZlibApi
open Silmaril.Elf.Abi.ZlibLibz (hdr)
open Silmaril.Elf.Staged.Pinned.ZlibLibz (F)

theorem crc32Combine_code : CodeOf F (.dynsym (some zlib122)) "crc32_combine" crc32CombineCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.crc32Combine_code
theorem crc32Combine_untouched : Untouched F crc32CombineCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.crc32Combine_untouched
theorem crc32Combine_declared : Declares sysvInt hdr "crc32_combine" combineProto := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.crc32Combine_declared
theorem crc32Combine_of (h : Task.crc32Combine) : silmaril.elf.abi.zlib_libz.crc32_combine := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.crc32Combine_of h
theorem adler32Combine_code : CodeOf F (.dynsym (some zlib122)) "adler32_combine" adler32CombineCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.adler32Combine_code
theorem adler32Combine_untouched : Untouched F adler32CombineCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.adler32Combine_untouched
theorem adler32Combine_declared : Declares sysvInt hdr "adler32_combine" combineProto := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.adler32Combine_declared
theorem adler32Combine_of (h : Task.adler32Combine) : silmaril.elf.abi.zlib_libz.adler32_combine := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.adler32Combine_of h
theorem crc32CombineGen_code : CodeOf F (.dynsym (some zlib1212)) "crc32_combine_gen" crc32CombineGenCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.crc32CombineGen_code
theorem crc32CombineGen_untouched : Untouched F crc32CombineGenCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.crc32CombineGen_untouched
theorem crc32CombineGen_declared : Declares sysvInt hdr "crc32_combine_gen" genProto := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.crc32CombineGen_declared
theorem crc32CombineGen_of (h : Task.crc32CombineGen) : silmaril.elf.abi.zlib_libz.crc32_combine_gen := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.crc32CombineGen_of h
theorem crc32CombineOp_code : CodeOf F (.dynsym (some zlib1212)) "crc32_combine_op" crc32CombineOpCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.crc32CombineOp_code
theorem crc32CombineOp_untouched : Untouched F crc32CombineOpCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.crc32CombineOp_untouched
theorem crc32CombineOp_declared : Declares sysvInt hdr "crc32_combine_op" opProto := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.crc32CombineOp_declared
theorem crc32CombineOp_of (h : Task.crc32CombineOp) : silmaril.elf.abi.zlib_libz.crc32_combine_op := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.crc32CombineOp_of h
theorem getCrcTable_code : CodeOf F (.dynsym none) "get_crc_table" getCrcTableCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.getCrcTable_code
theorem getCrcTable_untouched : Untouched F getCrcTableCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.getCrcTable_untouched
theorem getCrcTable_declared : Declares sysvInt hdr "get_crc_table" ptrProto := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.getCrcTable_declared
theorem getCrcTable_of (h : Task.getCrcTable) : silmaril.elf.abi.zlib_libz.get_crc_table := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.getCrcTable_of h
theorem zlibVersion_code : CodeOf F (.dynsym none) "zlibVersion" zlibVersionCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.zlibVersion_code
theorem zlibVersion_untouched : Untouched F zlibVersionCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.zlibVersion_untouched
theorem zlibVersion_declared : Declares sysvInt hdr "zlibVersion" ptrProto := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.zlibVersion_declared
theorem zlibVersion_of (h : Task.zlibVersion) : silmaril.elf.abi.zlib_libz.zlib_version := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.zlibVersion_of h
theorem zlibCompileFlags_code : CodeOf F (.dynsym (some zlib1202)) "zlibCompileFlags" zlibCompileFlagsCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.zlibCompileFlags_code
theorem zlibCompileFlags_untouched : Untouched F zlibCompileFlagsCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.zlibCompileFlags_untouched
theorem zlibCompileFlags_declared : Declares sysvInt hdr "zlibCompileFlags" flagsProto := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.zlibCompileFlags_declared
theorem zlibCompileFlags_of (h : Task.zlibCompileFlags) : silmaril.elf.abi.zlib_libz.zlib_compile_flags := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.zlibCompileFlags_of h
theorem coverage_check : coverage.check sysvInt hdr = true := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.coverage_check
theorem coverage_complete : coverage.complete = true ∧ coverage.available = true := Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.coverage_complete

/-- **`libz.so.1.3` satisfies all 11 declarations of the zlib.h checksum excerpt**, given the
eleven open tasks (`crc32_combine_op`'s on its domain: operators with nonzero low 32 bits). -/
theorem header_complete_of (h0 : Silmaril.Elf.Abi.ZlibLibz.Task.crc32z) (h1 : Silmaril.Elf.Abi.ZlibLibz.Task.crc32) (h2 : Silmaril.Elf.Abi.ZlibLibz.Task.adler32z) (h3 : Silmaril.Elf.Abi.ZlibLibz.Task.adler32)
    (g0 : Task.crc32Combine) (g1 : Task.adler32Combine) (g2 : Task.crc32CombineGen) (g3 : Task.crc32CombineOp) (g4 : Task.getCrcTable) (g5 : Task.zlibVersion) (g6 : Task.zlibCompileFlags) :
    silmaril.elf.abi.zlib_libz.zlib_h_complete :=
  Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi.header_complete_of h0 h1 h2 h3 g0 g1 g2 g3 g4 g5 g6

end Silmaril.Elf.Abi.ZlibMatrix.Api

end

silmaril group silmaril.abi.zlib_libz_api
  (title := "ABI conformance: the 11-declaration zlib.h checksum excerpt in Ubuntu's libz.so.1.3 (complete header satisfaction, open)")
  (children := [silmaril.elf.abi.zlib_libz.crc32_combine, silmaril.elf.abi.zlib_libz.adler32_combine, silmaril.elf.abi.zlib_libz.crc32_combine_gen, silmaril.elf.abi.zlib_libz.crc32_combine_op, silmaril.elf.abi.zlib_libz.get_crc_table, silmaril.elf.abi.zlib_libz.zlib_version, silmaril.elf.abi.zlib_libz.zlib_compile_flags,
    silmaril.elf.abi.zlib_libz.zlib_h_complete])
