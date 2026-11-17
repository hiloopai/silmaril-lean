module
public import Silmaril.Elf.Corpus.OpenSslQuicCount.Defs
import Silmaril.Proofs.Elf.Corpus.OpenSslQuicCount
@[expose] public section
namespace Silmaril.Elf.Corpus.OpenSslQuicCount
theorem elaborates : Silmaril.Project.Shapes.C.ElaboratesTo ail "ossl_quic_num_ciphers" sourceFn :=
  Silmaril.Proofs.Elf.Corpus.OpenSslQuicCount.elaborates
open Silmaril.Elf.Staged.Corpus.Openssl.X8664.LibsslSo3 in
theorem code_at : Silmaril.Elf.CodeAt F 0x6e010 code :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
open Silmaril.Elf.Staged.Corpus.Openssl.X8664.LibsslSo3 in
theorem symbol_identity :
    s27_1949.name = ("ossl_quic_num_ciphers".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s27_1949.raw.value = 0x6e010 ∧ s27_1949.raw.size = 3 ∧ s27_1949.kind = 2 := by
  decide +kernel
end Silmaril.Elf.Corpus.OpenSslQuicCount
