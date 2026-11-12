module

public import Silmaril.Elf.Link.Dyn.Program.StdExe.Defs
public import Silmaril.Elf.Link.Dyn.Program.Cli.Thms
public import Silmaril.Raw.Elf.Link.Dyn.Program.Call

/-! # Standard executables: the specialization lemmas, the opaque view, outlining

* `StdExe.verified_iff`, `StdExe.verified`: `StdExe.Verified` is `Program.Verified` and is
  proved by `Program.verified` from the one check and `main`'s obligation;
* `StdExe.Verified.sat`, `.sat_lift`, `.sat_liftAll`: the CLI reading (`x86Model_sat`);
* `GlibcView.entry`, `GlibcView.store`, `GlibcView.call`: the glibc-opaque view at `main`'s
  entry, across stores into `main`'s frame and across library calls;
* outlining: `putc_inline_appended` (the fast path of an inline `putc (c, stdout)` has the effect
  of the call `__overflow (stdout, c)`), `puts_as_printf` (`puts (s)` has the effect of
  `printf ("s\n")`, the call gcc and clang compile it to). -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Ext (loadN)
open Silmaril.Process (Memory)
open Silmaril.Elf.Link.Dyn.Proc (PState Keeps)
open Silmaril.Elf.Link.Dyn.Streams (StdoutIs Appended Env)
open Silmaril.Cli.Institution (Level Sen)

namespace StdExe

/-- **`main`'s obligation**: `Program.MainProof`. -/
def Main (E : StdExe) : Prop := MainProof E.bin E.spec E.tier E.L E.env

/-- **`StdExe.Verified` is `Program.Verified`**. -/
theorem verified_iff (E : StdExe) :
    E.Verified ↔ Program.Verified E.bin E.glibc.libc E.glibc.ld E.spec E.tier E.L E.env := Iff.rfl

/-- `StdExe.Main` is `Program.MainProof`. -/
theorem main_iff (E : StdExe) : E.Main ↔ MainProof E.bin E.spec E.tier E.L E.env := Iff.rfl

theorem bin_ok {E : StdExe} (h : E.ok = true) : E.bin.ok E.glibc.libc E.glibc.ld = true := by
  simp only [StdExe.ok, Bool.and_eq_true] at h; exact h.1

/-- The checked facts of the executable. -/
theorem facts {E : StdExe} (h : E.ok = true) : E.bin.Facts E.glibc.libc E.glibc.ld :=
  Bin.facts (bin_ok h)

/-- **A standard executable is verified** once its check holds and its `main` meets its
obligation (the tier's reliability is found for the standard tiers). -/
theorem verified {E : StdExe} (h : E.ok = true) (hmain : E.Main)
    (hrel : ∀ w, E.tier w → Tier.reliable w := by
      first | exact fun _ h => h | exact fun _ h => h.1 | exact fun _ h => h.1.1) :
    E.Verified :=
  Program.verified (bin_ok h) E.glibc.ok.1 E.glibc.ok.2 hrel hmain

/-- **The CLI reading**: a verified standard executable is a model of its CLI specification. -/
theorem Verified.sat {E : StdExe} (h : E.Verified) (conv : PathConv := .cwd) :
    (E.model conv).Sat (E.cli conv) :=
  x86Model_sat conv h

/-- Through a level: the `lv` reduct satisfies `φ` when the CLI specification refines its lift. -/
theorem Verified.sat_lift {E : StdExe} (h : E.Verified) {conv : PathConv} {lv : Level}
    {φ : Sen lv.sig} (hφ : E.cli conv ≤ Level.lift φ) : (lv.reduct (E.model conv)).Sat φ :=
  x86Model_sat_lift conv h hφ

/-- Uniformly in the extension: the model satisfies the `liftAll` of `φ`. -/
theorem Verified.sat_liftAll {E : StdExe} (h : E.Verified) {conv : PathConv} {lv : Level}
    {φ : Sen lv.sig} (hφ : E.cli conv ≤ Level.liftAll φ) : (E.model conv).Sat (Level.liftAll φ) :=
  (h.sat conv).mono hφ

end StdExe

/-! ## `main`'s entry -/

/-- **`main`'s entry**, from the hypotheses of `MainOk` in the program's world (`at_main`). -/
theorem Entry.of {B : Bin} {S : Std} {w : World} {b lb gate : Word} {args : Nat → Prop}
    {fs argv : Word} {L : LibTable} {t : PState}
    (hal : (t.m.core.read .rsp).toNat % 16 = 8)
    (hroom : Proc.StackRoom (world B S w b lb gate (!w.stdoutFull) args fs L) t.m.memory
      (t.m.core.read .rsp))
    (hx : ExtraX B b lb t.m.core.fsBase t.m.memory ∧
      ArgvAt (world B S w b lb gate (!w.stdoutFull) args fs L) w argv t.m.memory ∧
      t.m.core.fsBase = fs ∧ GuardAt fs t.m.memory ∧ MainRO B b t.m.memory)
    (hat : (world B S w b lb gate (!w.stdoutFull) args fs L).atMain t)
    (hpre : t.g.inp = stdinBytes w ∧ t.g.out = [] ∧ t.g.err = [] ∧ t.g.jobs = [.exitRax] ∧
      t.g.allocs = 0 ∧ t.g.heap = 0 ∧ t.g.files = 0)
    (hrdi : t.m.core.read .rdi = ((BitVec.ofNat 64 w.argv.length).setWidth 32).setWidth 64)
    (hrsi : t.m.core.read .rsi = argv) :
    Entry B S w (world B S w b lb gate (!w.stdoutFull) args fs L) b lb fs argv t :=
  ⟨hrdi, hrsi, hx.2.1, hat.stdin, hat.stdout, hat.stderr, hat.vars, hpre.1, hpre.2.1, hpre.2.2.1,
    hpre.2.2.2.1, hpre.2.2.2.2, hx.2.2.1, hx.2.2.2.1, hroom, hal, hat.lo, hat.errno⟩

/-- A stream across a store into memory above the library's bound (the stack frame). -/
theorem file_store {E : Streams.Env} {m : Memory} {f : Word} {st : Streams.St} (h : E.S.file m f st)
    {a v : Word} {k : Nat} (ha : E.S.lo ≤ a.toNat) : E.S.file (Proc.storeMem m a k v) f st :=
  (E.S.local_ m _ f st (fun x hx => Proc.storeMem_keeps (P := fun x => x < E.S.lo)
    (fun y hy => by omega) x (E.S.foot_lo m _ st x h hx)) h).1

/-- `je` after `cmp x, y`: taken iff `x = y`. -/
theorem cond_e_cmp {n : Nat} (x y : BitVec n) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.AluOp.flagsN .cmp x y) .e = some (x == y) := by
  simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.subFlagsN,
    Silmaril.X86.Ext.isZeroN]
  constructor
  · intro h; have := congrArg (· + y) h; simpa using this
  · intro h; subst h; simp

/-! ## The glibc-opaque view -/

/-- The view at `main`'s entry. -/
theorem GlibcView.entry {B : Bin} {S : Std} {w : World} {W : Proc.World} {b lb fs argv : Word}
    {t : PState} (h : Entry B S w W b lb fs argv t) : GlibcView S (t.m.core.read .rsp) t.m.memory :=
  ⟨⟨_, h.stdin⟩, ⟨_, h.stdout⟩, ⟨_, h.stderr⟩, h.lo, h.errno⟩

/-- **`main`'s own stores keep the view**: any change of memory at or above the library's bound
`lo` (the stack frame, the image's data) leaves the library's state as it was. -/
theorem GlibcView.store {S : Std} {sp : Word} {m m' : Memory} (h : GlibcView S sp m)
    (hk : ∀ a, a < S.E.S.lo → m'.bytes.get? a = m.bytes.get? a ∧ ∀ acc, m'.permits acc a = m.permits acc a) :
    GlibcView S sp m' := by
  obtain ⟨⟨s1, h1⟩, ⟨s2, h2, h2'⟩, ⟨s3, h3⟩, hlo, he⟩ := h
  exact ⟨⟨s1, file_keep_lo hk h1⟩, ⟨s2, file_keep_lo hk h2, h2'⟩, ⟨s3, file_keep_lo hk h3⟩, hlo, he⟩

/-- **A library call keeps the view**: the streams the call does not name keep their states
(`OthersKept`, every contract of `lib`), and those it names it leaves as streams (`hnamed`). -/
theorem GlibcView.call {S : Std} {sp : Word} {s t : PState} {fs : List Word}
    (h : GlibcView S sp s.m.memory) (hk : Streams.OthersKept S.E s t fs)
    (hnamed : ∀ f ∈ fs, ∃ st, S.E.S.file t.m.memory f st)
    (hstdout : S.E.stdoutF ∈ fs → ∃ st, StdoutIs S.E t.m.memory st) : GlibcView S sp t.m.memory := by
  obtain ⟨⟨s1, h1⟩, ⟨s2, h2, h2'⟩, ⟨s3, h3⟩, hlo, he⟩ := h
  have keep : ∀ f st, S.E.S.file s.m.memory f st → ∃ st', S.E.S.file t.m.memory f st' := fun f st hf => by
    by_cases hm : f ∈ fs
    · exact hnamed f hm
    · exact ⟨st, hk f st hm hf⟩
  refine ⟨keep _ _ h1, ?_, keep _ _ h3, hlo, he⟩
  by_cases hm : S.E.stdoutF ∈ fs
  · exact hstdout hm
  · exact ⟨s2, hk _ _ hm h2, h2'⟩

/-! ## Outlining: code the compilers inline, read as the library's calls -/

/-- **The inline `putc (c, stdout)`** (`<stdio.h>`'s `__putc_unlocked_body`, as gcc and clang
inline it): when `_IO_write_ptr < _IO_write_end`, the program stores `c` at `_IO_write_ptr` and
advances it. Its effect on the library's state is **that of the call `__overflow (stdout, c)`**
taken otherwise (`Streams.overflowStep`'s `Appended … [c]`), for every state of `stdout`: the
two paths of the inlined code are one library step. -/
theorem putc_inline_appended {E : Env} {W : Proc.World} {s t : PState} {p e : Word} {c : Byte}
    (hp : loadN s.m.memory (E.stdoutF + 0x28#64) 8 = some p)
    (he : loadN s.m.memory (E.stdoutF + 0x30#64) 8 = some e) (hlt : p.toNat < e.toNat)
    (hk : Keeps (fun a => E.S.foot s.m.memory E.stdoutF a ∧ a ≠ p.toNat ∧
        ¬ ((E.stdoutF + 0x28#64).toNat ≤ a ∧ a < (E.stdoutF + 0x28#64).toNat + 8)) s.m.memory t.m.memory)
    (hreg : t.m.memory.regions = s.m.memory.regions)
    (hc : loadN t.m.memory p 1 = some (c.setWidth 64))
    (hp' : loadN t.m.memory (E.stdoutF + 0x28#64) 8 = some (p + 1#64)) (hg : t.g = s.g) :
    Appended E W s t [c] := by
  intro st hst
  obtain ⟨-, -, -, h⟩ := E.S.putc s.m.memory E.stdoutF st p e c hst.1 hp he hlt
  exact ⟨{ st with buf := st.buf ++ [c] }, ⟨h t.m.memory hk hreg hc hp', hst.2⟩, rfl, rfl, rfl,
    Or.inl ⟨by rw [hg, List.append_assoc], rfl⟩⟩

/-- What `printf (fmt)` does for a format `fmt` without conversions: it appends `fmt` to
`stdout` and changes nothing else of the library's state (`putsStep`'s post with the format). -/
def PrintfLitPost (S : Std) (W : Proc.World) (fmt : List Byte) (s t : PState) : Prop :=
  Streams.LibRet S.E W (fun _ => False) s t ∧ OutOnly s t ∧
    Streams.OthersKept S.E s t [S.E.stdoutF] ∧ Appended S.E W s t fmt

/-- **`printf ("s\n")` compiled to `puts ("s")`** (gcc and clang rewrite a `printf` of a
literal ending in a newline, without conversions, to `puts`): the binary's call of `puts` has
the effect the C source's `printf` has. -/
theorem puts_as_printf {S : Std} {W : Proc.World} {s t : PState} {str : List Byte}
    (h : Streams.LibRet S.E W (fun _ => False) s t ∧ OutOnly s t ∧
      Streams.OthersKept S.E s t [S.E.stdoutF] ∧
      ∀ str, Proc.CStr s.m.memory (s.m.core.read .rdi) str → Appended S.E W s t (str ++ [10]))
    (hs : Proc.CStr s.m.memory (s.m.core.read .rdi) str) : PrintfLitPost S W (str ++ [10]) s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2 str hs⟩

end Silmaril.Elf.Link.Dyn.Program
