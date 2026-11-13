module

public import Silmaril.Machine.Link.FnSpec.Defs
public import Silmaril.Proofs.Machine.Link.FnSpec.Logic
public import Silmaril.Proofs.Machine.Link.FnSpec.Unit
public import Silmaril.Proofs.Machine.Link.FnSpec.Load
public import Silmaril.Proofs.Machine.Link.FnSpec.Step
public import Silmaril.Proofs.Machine.Link.FnSpec.CallSite
public import Silmaril.Proofs.Machine.Link.FnSpec.Data

/-! # The `FnSpec` logic for `link_compose`: theorems (header)

PROVED (standard axioms; the proofs are in `Silmaril.Proofs.Machine.Link.FnSpec.*`, namespace
`Silmaril.Proofs.Machine.Link.FnSpec`):

**The logic** (`Logic`):
* `logic : Contract.Logic FnSpec`, with `Safe` (`Silmaril.Machine.Link.FnSpec.Safe`), the laws
  `safe_zero`, `safe_mono`, `safe_frame` and `safe_sub` (`Sub := FnSpec.Sub`).
* `SafeN`: `safeN_mono`, `safeN_le`, `safeN_post`, `safeN_of_run`, `safeN_of_reaches`,
  `safeN_prefix`, `safeN_bind`.
* `STriple`: `zero`, `mono`, `le`, `frame`, `conseq`, `of_triple`, `triple_seq`,
  `seq_triple`, `progress_seq` (with `Progress`, `progress_of_rsp`), `sexists_pre`,
  `spure_pre`.
* Code regions: `code_congr`, `code_split_byte`, `code_split`.

**Unit contracts** (`Unit`):
* `tu_sat_of_code`: a relocation-free unit whose exports are `unverified` or have
  position-independent `FnSpec.Sat` proofs (`ExportCode`) satisfies `TU.Sat logic` for every
  relocator. `safe_of_sat`, `safe_unverified`, `image_mem`, `exportCode_contains`.

**Call sites** (`Step`, `CallSite`):
* `aluI8_step`: the `op $imm8,%r64` triple. `code_triple`: instruction triples inside a code
  region. `scall_rule`: the step-indexed call rule (a call to a `Safe n` import is one
  instruction at index `n + 1`).

**Loaded executables** (`Load`, S-validate-compose):
* `validated_compose`: from `Validated objs exe W` (the linker's `validate_sound`, or
  `Exe.run_validated` for the executable linker), prepared objects equal to the units'
  objects, `TU.Sat`, `AbiCompatible` and `ImportsClosed`, every export at its linked address
  is `logic.Safe n` in the linked image and `SafeN n` on every machine that holds the
  executable's loader image. (F3) removed the hypothesis that every allocated section
  is executable: `Code` covers the executable sections only (`ContainsX`, `Dom`), and the
  data sections are in the frame.
* `linkSection_meta`, `link_meta`, `containsF_loaded`, `contains_loaded`, `ContainsX.contains`,
  `code_onBytes`, `sep_onBytes`.

**Data sections** (`Data`, F3; REVIEW M14):
* `data_section_ro`, `data_section_rw`: in a validated link, every non-executable section
  `s` is `bytesPtRO s.address (expected s) ∗ ⊤` (its data then its zero fill, so `.bss` is
  covered; `bytesPt …` if writable) in the frame
  `offBytes (Dom out) (toFrag m)` of every machine that holds the loader image with its
  permissions (`ImageLoaded`, `ImagePerms`); this is the frame `validated_compose` hands to an
  export's precondition. `data_loaded` (the whole `DataPt out`), `containsM_loaded`,
  `expected_length`, `not_dom_of_data`,
  `region_split_byte`, `region_split`, `pairwise_ne`.

Assumed / modelled (not proved): the open x86 machine (`Silmaril.X86.Ext`/`Ext8` semantics),
`ImageLoaded` as the meaning of "the executable is loaded", and the readers and linker that
`Validated` mentions (see `Silmaril.Machine.Link.Validate.Thms`). `Safe` is partial correctness:
it does not claim termination. `Code` asks for execute permission on the bytes of executable
sections only; read-only and writable sections are owned through the frame (`DataPt`,
`bytesPtRO`, `bytesPt`); see `Silmaril.Machine.Link.FnSpec.Defs`.
-/
