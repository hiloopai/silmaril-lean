module

public import Silmaril.Libc.FileIo.Defs
public import Silmaril.Libc.Stdio.Printf.Thms
public import Silmaril.Libc.Stdio.Scanf.Thms
import Silmaril.Proofs.Libc.FileIo.Mono

/-!
# Stream and file I/O: theorems (header)

PROVED (standard axioms; proofs in `Silmaril.Proofs.Libc.FileIo.Mono`):

* **The order of the parameters**: `PText.mono`, `PUse.mono`, `SUse.mono`, and
  **`fileTable_le`**: a higher format tier and a dialect that fixes more give a stronger
  contract for every function (a weaker precondition, a stronger postcondition), so
  **`fileC_le`**: `fileC F t D ≤ fileC F t' D'`; in particular every contract refines the POSIX
  one at the same tier (`fileC_iso_le`), and `Dialect.glibc` refines `Dialect.iso`.
-/

@[expose] public section

namespace Silmaril.Libc.FileIo

open Silmaril.Libc.Contracts (Api FnSpec Contract Sig)
open Silmaril.X86 (Byte)
open Silmaril.Libc.Stdio.Printf (Tier PArg PtrLe)

theorem Dialect.Le.ptr {D D' : Dialect} (h : D.Le D') : PtrLe D.ptr D'.ptr :=
  Proofs.Libc.FileIo.Dialect.Le.ptr h

theorem Dialect.Le.msg {D D' : Dialect} (h : D.Le D') {e : Nat} {m : List Byte}
    (hm : Msg D' e m) : Msg D e m :=
  Proofs.Libc.FileIo.Dialect.Le.msg h hm

theorem Dialect.Le.refl (D : Dialect) : D.Le D := ⟨fun _ h => h, fun _ h => h⟩

/-- ISO C fixes nothing. -/
theorem Dialect.iso_le (D : Dialect) : Dialect.iso.Le D :=
  ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩

theorem PText.mono {D D' : Dialect} (h : D.Le D') {fmt : List Byte} {as : List PArg}
    {out : List Byte} (ho : PText D fmt as out) : PText D' fmt as out :=
  Proofs.Libc.FileIo.PText.mono h ho

theorem PUse.mono {t t' : Tier} {D D' : Dialect} (ht : t.le t') (h : D.Le D') {fmt : List Byte}
    {as : List PArg} (hu : PUse t D fmt as) : PUse t' D' fmt as :=
  Proofs.Libc.FileIo.PUse.mono ht h hu

theorem SUse.mono {t t' : Tier} (ht : t.le t') {fmt : List Byte} (hu : SUse t fmt) :
    SUse t' fmt :=
  Proofs.Libc.FileIo.SUse.mono ht hu

/-- **A higher tier and a dialect that fixes more give a stronger contract**, function by
function. -/
theorem fileTable_le {t t' : Tier} {D D' : Dialect} (ht : t.le t') (hD : D.Le D') (f : FFn) :
    FnLe (fileTable t D f) (fileTable t' D' f) :=
  Proofs.Libc.FileIo.fileTable_le ht hD f

/-- **The contracts are ordered by tier and dialect.** -/
theorem fileC_le (F : Set FFn) {t t' : Tier} {D D' : Dialect} (ht : t.le t') (hD : D.Le D') :
    (fileC F t D).Le (fileC F t' D') :=
  ⟨fun _ h => h, fun f _ g a h => (fileTable_le ht hD f).1 g a h,
    fun f _ g a r g' hp hq => (fileTable_le ht hD f).2 g a r g' hp hq⟩

/-- Every dialect's contract refines the POSIX one. -/
theorem fileC_iso_le (F : Set FFn) (t : Tier) (D : Dialect) :
    (fileC F t Dialect.iso).Le (fileC F t D) :=
  fileC_le F (Silmaril.Libc.Stdio.Printf.Tier.le_refl t) (Dialect.iso_le D)

end Silmaril.Libc.FileIo
