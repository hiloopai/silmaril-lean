module

public import Silmaril.X86.MemoryModel.Litmus.Corpus.Defs

/-!
# The x86 litmus corpus: decided facts about the generated data

PROVED by kernel `decide` on the generated data:

* `all_length`: the corpus has 68 tests; `names_nodup`: their names are distinct;
* `tso_decodes`: on every x86-TSO-covered test, every instruction's assembled bytes are
  exactly one instruction of the `Atomic9` listing decoder (`Insn.decodes`), so those bytes are
  inside the atomic machine (`Atomic9`);
* `events_match`: on every test, every instruction's recorded events (`Insn.events`, the
  events the tool's checker reads it as, computed from the tool's IR) are exactly the
  `MemEvent.atomic9Accesses` events of its decoded bytes; `tso_has_events`: on every
  x86-TSO-covered test every instruction records its events. So a changed byte (a dropped
  `lock` prefix, an `mfence` turned into an `lfence`, another address or width) breaks a proof;
* `movnti_not_decoded`, `stosb_not_decoded`: `movnti` and `rep stosb` (used only by XL-only
  tests) are **not** decoded by `Atomic9` today; the decoder must be extended
  before those tests can run on the byte machines;
* `coverage_tso_iff`, `xl_eq_tso`, `sc_allowed_tso_allowed`: the recorded verdicts are well
  formed: a TSO verdict is recorded exactly on covered tests, XL's verdict equals TSO's there,
  and no recorded SC-allowed witness is TSO-forbidden.

These are facts about the data, not about any memory model: the verdicts themselves are
recorded (herd7 output, paper tables) or computed by the tool's checker, and are tested only.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Litmus.Corpus

open Silmaril.X86.MemoryModel.Litmus

theorem all_length : all.length = 68 := by decide

set_option maxRecDepth 100000 in
theorem names_nodup : (all.map Test.name).Nodup := by decide

set_option maxRecDepth 100000 in
theorem tso_decodes : ∀ t ∈ all, t.coverage = .tso → t.decodes = true := by decide

set_option maxRecDepth 100000 in
theorem events_match : ∀ t ∈ all, t.eventsMatch = true := by decide

set_option maxRecDepth 100000 in
theorem tso_has_events : ∀ t ∈ all, t.coverage = .tso → t.hasEvents = true := by decide

theorem movnti_not_decoded : «MP+movnti».decodes = false := by decide

theorem stosb_not_decoded : «MP+stosb».decodes = false := by decide

set_option maxRecDepth 100000 in
theorem coverage_tso_iff : ∀ t ∈ all, t.coverage = .tso ↔ t.tso.isSome = true := by decide

set_option maxRecDepth 100000 in
theorem xl_eq_tso : ∀ t ∈ all, ∀ v, t.tso = some v → t.xl = v := by decide

set_option maxRecDepth 100000 in
theorem sc_allowed_tso_allowed :
    ∀ t ∈ all, t.sc = some .allowed → t.tso = some .allowed := by decide

end Silmaril.X86.MemoryModel.Litmus.Corpus
