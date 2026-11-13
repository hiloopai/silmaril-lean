module

public import Silmaril.Libc.FileIo.Defs
public import Silmaril.Libc.Stdio.Printf.Thms
public import Silmaril.Libc.Stdio.Scanf.Thms

/-!
# Proofs: a higher tier and a dialect that fixes more give stronger stream contracts

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Proofs.Libc.FileIo

open Silmaril.Libc.Contracts (Api FnSpec)
open Silmaril.Libc.Stdio.Printf (Tier PArg)
open Silmaril.Libc.FileIo
open Silmaril.X86 (Byte)
open Silmaril.Libc.Stdio.Printf (PtrLe)

open Silmaril.Libc.Stdio.Printf (PtrLe)

theorem Dialect.Le.ptr {D D' : Dialect} (h : D.Le D') : PtrLe D.ptr D'.ptr := h.1

theorem Dialect.Le.msg {D D' : Dialect} (h : D.Le D') {e : Nat} {m : List Byte}
    (hm : Msg D' e m) : Msg D e m := fun f hf => hm f (h.2 f hf)

theorem PText.mono {D D' : Dialect} (h : D.Le D') {fmt : List Byte} {as : List PArg}
    {out : List Byte} (ho : PText D fmt as out) : PText D' fmt as out :=
  let ⟨is, h1, h2⟩ := ho
  ⟨is, h1, Silmaril.Libc.Stdio.Printf.render_mono (Dialect.Le.ptr h) h2⟩

theorem PUse.mono {t t' : Tier} {D D' : Dialect} (ht : t.le t') (h : D.Le D') {fmt : List Byte}
    {as : List PArg} (hu : PUse t D fmt as) : PUse t' D' fmt as :=
  let ⟨out, h1, h2⟩ := hu
  ⟨out, h1.mono ht (Dialect.Le.ptr h), h2⟩

theorem SUse.mono {t t' : Tier} (ht : t.le t') {fmt : List Byte} (hu : SUse t fmt) :
    SUse t' fmt :=
  let ⟨is, h1, h2⟩ := hu
  ⟨is, h1, h2.mono ht⟩

theorem fileTable_le {t t' : Tier} {D D' : Dialect} (ht : t.le t') (hD : D.Le D') (f : FFn) :
    FnLe (fileTable t D f) (fileTable t' D' f) := by
  cases f
  case printf | fprintf | warnx | dprintf =>
    exact ⟨fun _ _ h => ⟨h.1, PUse.mono ht hD h.2⟩,
      fun _ _ _ _ _ hq out ho => hq out (PText.mono hD ho)⟩
  case sprintf | snprintf | asprintf =>
    exact ⟨fun _ _ h => PUse.mono ht hD h, fun _ _ _ _ _ hq out ho => hq out (PText.mono hD ho)⟩
  case perror =>
    refine ⟨fun _ _ h => h, fun _ _ _ _ _ hq => ?_⟩
    obtain ⟨m, r, hm, hp⟩ := hq
    exact ⟨m, r, Dialect.Le.msg hD hm, hp⟩
  case warn =>
    refine ⟨fun _ _ h => ⟨h.1, PUse.mono ht hD h.2⟩, fun _ _ _ _ _ hq out ho => ?_⟩
    obtain ⟨m, r, hm, hp⟩ := hq out (PText.mono hD ho)
    exact ⟨m, r, Dialect.Le.msg hD hm, hp⟩
  case error =>
    refine ⟨fun _ _ h => ⟨h.1, h.2.1, PUse.mono ht hD h.2.2⟩,
      fun _ _ _ _ _ hq => ⟨hq.1, fun out ho => ?_⟩⟩
    obtain ⟨m, w1, r1, r, hm, hf, hp⟩ := hq.2 out (PText.mono hD ho)
    exact ⟨m, w1, r1, r, fun he => Dialect.Le.msg hD (hm he), hf, hp⟩
  case err | errx =>
    exact ⟨fun _ _ h => ⟨h.1, PUse.mono ht hD h.2⟩, fun _ _ _ _ _ hq => hq⟩
  case scanf | fscanf | sscanf =>
    exact ⟨fun _ _ h => ⟨h.1, SUse.mono ht h.2.1, h.2.2⟩, fun _ _ _ _ _ hq => hq⟩
  all_goals exact ⟨fun _ _ h => h, fun _ _ _ _ _ h => h⟩

end Silmaril.Proofs.Libc.FileIo
