module

public import Silmaril.Libc.AllocLoad.Defs
public import Silmaril.Libc.AllocElf.Thms

/-!
# Allocator rows at the concrete loading model: reducts

PROVED (standard axioms), names in `Silmaril.Libc.AllocLoad`:

* `Row.reduct`, `Row.full_mfcr`, `Row.mfcr_mfc`, `Row.mfc_mf`: a row at a signature gives the
  rows below it;
* `Row.posixSafe`: a row at an environment satisfying the import hypothesis;
* `Env.ok_unbound`: the import hypothesis holds of an environment that binds nothing (so it is
  satisfiable; such an environment starts only a file without strong imports).
-/

@[expose] public section

namespace Silmaril.Libc.AllocLoad

open Silmaril.Libc.AllocSig (Sig)
open Silmaril.Libc.AllocElf (Syms PosixSafe)
open Silmaril.X86.Link (Blob)

theorem Row.reduct {s s' : Sig} {F : Blob} {S : Syms} (hle : s ≤ s') (h : Row s' F S) :
    Row s F S := fun E hE => AllocElf.PosixSafe.reduct hle (h E hE)

theorem Row.full_mfcr {F : Blob} {S : Syms} (h : Row .full F S) : Row .mfcr F S :=
  Row.reduct (by decide) h

theorem Row.mfcr_mfc {F : Blob} {S : Syms} (h : Row .mfcr F S) : Row .mfc F S :=
  Row.reduct (by decide) h

theorem Row.mfc_mf {F : Blob} {S : Syms} (h : Row .mfc F S) : Row .mf F S :=
  Row.reduct (by decide) h

theorem Row.posixSafe {s : Sig} {F : Blob} {S : Syms} (h : Row s F S) (E : Env) (hE : E.Ok) :
    PosixSafe (model E) s F S := h E hE

theorem Env.ok_unbound (ifn : Silmaril.X86.Word → Option Silmaril.X86.Word)
    (call : Silmaril.X86.Word → Option Impl) (tpoff : Silmaril.X86.Word) (errno : Nat) :
    Env.Ok ⟨fun _ => none, ifn, call, tpoff, errno⟩ := by
  intro r w C h; cases h

end Silmaril.Libc.AllocLoad
