module

public import Silmaril.Raw.Elf.Link.Dyn.Hello.GccRun
public import Silmaril.X86.BinInstitution.Defs

/-! # hello-gcc as a sentence of the binary institution (`Sen.proc`)

Bridge from `hello_gcc` to the process sentences of the binary institution
(`Silmaril.X86.BinInstitution.ProcSen`). Two shapes differ and are adapted here:

* **The machine depends on the load.** `proc W` is indexed by the world `W` (image base, the
  bound library entry points, the callback gate), which the load outcome fixes; `ProcSen.Sat`
  fixes one machine `C` before quantifying over loads. Adapter: the world becomes part of the
  state (`DState`), constant along runs (`dproc`), set by `Starts`.
* **The libc contracts are inside the machine**, not `Imports`: the sentence has
  `imports := []`, so `withImports C r []` is `C` (with liveness, here trivial).

`hello_gcc_sen`: for every glibc pair agreeing with the chunks, the sentence "every process of
hello-gcc ends with status 0 having written `hello, world\n` (a prefix if writes may fail)" is
satisfied by `dproc`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Hello.Sen

open Silmaril.X86 (Word Byte)
open Silmaril.X86.RelIsa (Res Must)
open Silmaril.X86.Link (Blob)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Glibc
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.X86.BinInstitution

/-- A process state together with the world of its load. -/
structure DState where
  W : World
  s : PState

/-- `proc W`, with `W` carried in the state. -/
def dproc : Silmaril.X86.RelIsa DState where
  core d := d.s.m.core
  mem d := d.s.m.memory
  upd d c m := ⟨d.W, ⟨⟨c, m⟩, d.s.g⟩⟩
  core_upd _ _ _ := rfl
  mem_upd _ _ _ := rfl
  upd_self _ := rfl
  live _ := True
  step d o := match o with
    | .ok t => t.W = d.W ∧ (proc d.W).step d.s (.ok t.s)
    | .stop => (proc d.W).step d.s .stop
  live_step _ _ := trivial

theorem must_dproc {W : World} {Q : PState → Prop} {s : PState} (h : MustQ W Q s) :
    Must dproc (fun _ => True) (fun d => d.W = W ∧ Q d.s) ⟨W, s⟩ := by
  induction h with
  | done hq => exact .done ⟨rfl, hq⟩
  | step _ hstop _ ih =>
    refine .step trivial hstop ?_
    rintro ⟨W', t⟩ ⟨rfl, ht⟩
    exact ih t ht

theorem must_withImports_nil {r : DynLoad} {Q : DState → Prop} {d : DState}
    (h : Must dproc (fun _ => True) Q d) : Must (withImports dproc r []) (fun _ => True) Q d := by
  induction h with
  | done hq => exact .done hq
  | step _ hstop _ ih =>
    refine .step trivial (fun h' => hstop h'.1) ?_
    intro t ht
    exact ih t ht.1

def libcName : String := "libc.so.6"
def ldName : String := "ld-linux-x86-64.so.2"

/-- **Process creation for hello-gcc** (trusted, as in `hello_gcc`): the libraries agree with
the pinned chunks, the load puts the three objects at bases `b`, `lb`, `ldb`, the state's world
is hello-gcc's at those bases, and the state is what the loader relation and the kernel give. -/
def startsGcc (rel : Bool) : ProcLoader DState where
  Starts exe libs _ r d := ∃ Fc Fl b lb ldb res gate argc, ∃ ifn : Word → Option Word, ∃ lazy : Bool,
    libs = [(libcName, Fc), (ldName, Fl)] ∧ ChunksOf Fc libcChunks ∧ ChunksOf Fl ldChunks ∧
    r.base "" = some b ∧ r.base libcName = some lb ∧ r.base ldName = some ldb ∧
    d.W = gccWorld b lb gate rel ∧ GccEnv b lb gate ∧
    ExeLoaded [exe, Fc, Fl] [b, lb, ldb] ifn lazy res d.s.m.memory ∧
    GccStartState (gccWorld b lb gate rel) b d.s argc

def obsD : ProcObs DState := ⟨fun d => d.s.g.done⟩

def helloPost (rel : Bool) (e : Nat) (out : List Byte) : Prop :=
  e = 0 ∧ out <+: helloNL ∧ (rel = true → out = helloNL)

/-- **The sentence.** -/
def helloGccSen (rel : Bool) (Fc Fl : Blob) (env : ProcEnv) : ProcSen DState where
  loader := startsGcc rel
  obs := obsD
  exe := gccFile
  libs := [(libcName, Fc), (ldName, Fl)]
  env := env
  imports := []
  post := helloPost rel

/-- **hello-gcc satisfies its process sentence.** -/
theorem hello_gcc_sen (rel : Bool) (Fc Fl : Blob) (env : ProcEnv) :
    (helloGccSen rel Fc Fl env).Sat dproc := by
  rintro r ⟨W, s⟩ ⟨Fc', Fl', b, lb, ldb, res, gate, argc, ifn, lazy, hlibs, hc, hl, -, -, -, hW, E,
    hload, hs⟩ - -
  simp only [helloGccSen, List.cons.injEq, Prod.mk.injEq, and_true, true_and] at hlibs
  obtain ⟨rfl, rfl⟩ := hlibs
  simp only at hW hload hs
  subst hW
  refine must_withImports_nil (Must.mono (fun _ h => h) (fun d hd => ?_) (must_dproc
    (hello_gcc hc hl E hload hs)))
  obtain ⟨-, w, hw, hp, hr⟩ := hd
  exact ⟨0, w, hw, rfl, hp, hr⟩

end Silmaril.Elf.Link.Dyn.Hello.Sen
