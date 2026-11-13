module

public import Silmaril.Compiler.C.Sem.CoreX86.Defs
@[expose] public section

/-!
# Approved Core → x86 target statements

This file is frozen
after its statements-only commit. The backend and source-bridge premises are explicit;
these statements do not assert soundness of ccomp or core-comp. Ordinary API lemmas
live in `Silmaril.Compile.C.Sem.CoreX86`.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.Category Silmaril.Compile.C.Sem
open Silmaril.Compile.C.Sem.CoreX86 CategoryTheory

/-- Exact validity criterion: the ordinary contract plus a source witness if exhaustion occurs. -/
def core_x86_valid_iff : Prop :=
  ∀ (M : X86Model) (p : Core.lang.Prog) (a : M.Artifact),
    Valid (c_CoreX86 M) p a ↔
      M.lang.beh a ⊆ allows M (Core.beh p) ∧
      ((∃ x ∈ M.lang.beh a, M.process x = none) → (Core.beh p).Nonempty)

/-- On accepted programs with a behaviour, the soundness statement is exactly `Valid`. -/
def core_compile_sound_iff_valid : Prop :=
  ∀ (M : X86Model) (Document : Type) (elaborate : Document → Core.lang.Prog)
    (compile : Document → Option M.Artifact),
    (∀ doc a, compile doc = some a → (Core.beh (elaborate doc)).Nonempty) →
    (SoundSpec M elaborate compile ↔
      ∀ doc a, compile doc = some a → Valid (c_CoreX86 M) (elaborate doc) a)

end Silmaril.Compile.Targets
