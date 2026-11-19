module
public import Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Equivalence.Defs
public import Silmaril.Elf.Staged.CorpusVariants.Darkhttpd.N117.Default.X8664.Og.Unstripped.DarkhttpdBinary.Thms
@[expose] public section
namespace Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Equivalence
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.CorpusVariants.Darkhttpd.N117.Default.X8664.Og.Unstripped.DarkhttpdBinary in
theorem actual_right_code : Silmaril.Elf.CodeAt F 10262 rightCode :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
    (by decide +kernel) (by decide +kernel)
open Silmaril.Elf.Staged.CorpusVariants.Darkhttpd.N117.Default.X8664.Og.Unstripped.DarkhttpdBinary in
theorem actual_right_symbol :
    s29_13.name = ("needs_logencoding".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s29_13.raw.value = 10262 ∧ s29_13.raw.size = 21 ∧ s29_13.kind = 2 := by decide +kernel
end Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Equivalence
