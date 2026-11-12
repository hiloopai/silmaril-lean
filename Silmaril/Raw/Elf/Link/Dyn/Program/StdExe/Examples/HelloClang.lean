-- variant-of: glibc.hello.clang | style: stdexe-at-main | see-also: Silmaril.Raw.Elf.Link.Dyn.Hello.ClangRun, Silmaril.Raw.Elf.Link.Dyn.Program.StdExe.Examples.HelloGcc
module

public import Silmaril.Elf.Link.Dyn.Program.StdExe.Thms
public import Silmaril.Elf.Link.Dyn.Program.StdExe.Bins.HelloClang
public import Silmaril.Raw.Elf.Link.Dyn.Program.Examples.Hello

/-! # Hello, world (`clang -O2`) as a standard executable

`hello-clang` (generated `Bin`, `StdExe.Bins.HelloClang`: clang's `.plt` stub `jmp *slot(%rip)`,
no `endbr64`) against the specification of `hello-gcc` (`helloSpec`), under eager binding (the
loader relation of `Program.Verified`; `hello-clang` allows lazy binding, which is
`Task.helloClangLazy`). -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program.Examples

open Silmaril.Elf.Link.Dyn Silmaril.Elf.Link.Dyn.Program

/-- `hello-clang` as a standard executable. -/
def helloClangStd : StdExe where
  bin := helloClang
  sha256 := "ecad1a19e6e63e4828e9386a9c831dc6beb635c6858dc42d2c248e6397eaa713"
  cc := .clang
  spec := helloSpec

theorem helloClangStd_ok : helloClangStd.ok = true := by decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Every (eagerly bound) run of `hello-clang` writes `hello, world` and exits 0.** -/
theorem helloClangStd_verified : helloClangStd.Verified := by
  at_main helloClangStd_ok
  mblock
  mname u0 hu0
  -- the frame after `push rax`: one saved word
  have K : Frm helloClang (world helloClang S w b lb gate (!w.stdoutFull) args fs) b lb t
      [((t.m.core.read .rsp - 8#64).toNat, Silmaril.Machine.LittleEndian.encodeWords [t.m.core.read .rax])]
      (guardKL fs guard) u0.m.memory := by
    rw [hu0]; mstores K
  have O : Streams.StdoutIs S.E u0.m.memory (outSt 1) := by rw [hu0]; mstdout hstdout
  mcallN u
  · mregs; exact ⟨_, Frm.str F X (by mfind) (by mnat) (by mnat) rfl⟩
  · mregs; exact ⟨_, file_push O.1 (by mnat), O.2⟩
  rintro v ⟨hlib, hout, hoth, happ⟩
  obtain ⟨st, hst, -, -, -, hap⟩ := happ _ (by mregs; exact Frm.str F X (by mfind) (by mnat) (by mnat) rfl) _
    (by mregs; exact ⟨file_push O.1 (by mnat), O.2⟩)
  mghost hout
  mret hlib
  mblock
  all_goals try exact ⟨_, by mslot⟩
  main_returns
  · refine ⟨st, hst, ?_⟩
    rcases hap with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; mregs; simp [outSt, helloSpec, Streams.ofSpec]; rfl
    · simp only [world0] at h1; rw [hrel] at h1; cases h1
  · mregs; simp [helloSpec, Streams.ofSpec]; mfind
  · simp [Silmaril.Elf.Link.Dyn.Proc.low32, helloSpec]

/-- **Open (`Task`): `hello-clang` under lazy binding.** `helloClang` has no `DF_BIND_NOW`, so
`ld.so` binds `puts` lazily by default: the GOT slot `0x4000` first holds the `.plt` entry's
`push`, and the first call goes through `PLT0` to the resolver (`GOT[2]`, at `0x3ff8`), which
stores the import's address and jumps to it (`Proc.World.lazy`). `helloClangStd_verified` is
the eager case (`ExeLoaded … false`, as under `LD_BIND_NOW`). The `Small` adder proofs did the lazy
case directly (`Small.AdderClangLazyMain`). Neither proved nor refuted. -/
def Task.helloClangLazy : Prop :=
  ∀ w, Tier.reliable w → ∀ (Fc Fl : Silmaril.X86.Link.Blob), ChunksOf Fc libc.chunks →
  ChunksOf Fl ld.chunks → ∀ (S : Std), S.E.fs = w.fs →
  ∀ (b lb ldb res gate rsv : Silmaril.X86.Word) (ifn : Silmaril.X86.Word → Option Silmaril.X86.Word)
    (args : Nat → Prop) (s : Proc.PState),
    Dyn.ExeLoaded [helloClang.file, Fc, Fl] [b, lb, ldb] ifn true res s.m.memory →
    Silmaril.X86.Ext.loadN s.m.memory (b + 0x3ff8#64) 8 = some rsv →
    Placed helloClang b lb gate →
    let W := { world helloClang S w b lb gate (!w.stdoutFull) args s.m.core.fsBase with
      lazy := some (rsv, [(0x4000, lb + BitVec.ofNat 64 0x87cc0)]) }
    AtStart helloClang W w b s → Proc.MustQ W (Observed (helloSpec w)) s

end Silmaril.Elf.Link.Dyn.Program.Examples
