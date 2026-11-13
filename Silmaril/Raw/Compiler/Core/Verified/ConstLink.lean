module

public import Silmaril.Compiler.Core.Verified.Backend.Defs

/-! # The link of a program whose `main` returns a constant

`link w` is the whole linked program of a C `main` that returns the 64-bit word `w`:
one Lir function, `__ccomp_start`, that loads `w` into a register and returns it. The
control block symbol is at `Spec.ctlAddr` and the initial image is empty, so the
linear memory below the argument block starts as zeros: crt0 finds an empty output
buffer (control words 3 and 6 are 0) and exits with `w mod 256`.

`link_beh` is its Lir behaviour on every initial memory: it returns `[w]` with the
memory unchanged (two steps). `link_sound` composes it with the backend bridge
`artifactOf_sound`: every observation of the artifact of `link w` is exhaustion or
`exit (w mod 256) []`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ConstLink

open Silmaril.Machine
open Spec Backend

/-- `__ccomp_start(argc, argv)`: ignore the arguments, `r0 := w; ret r0`. -/
def startFunc (w : Lir.Word) : Lir.Func Mir.Reg :=
  { params := [.reg 1, .reg 2], entry := 0, blocks := [⟨[.op (.const 0 w)], .ret [.reg 0]⟩] }

/-- The linked program of a `main` returning `w`. -/
def link (w : Lir.Word) : Mir.Linked where
  prog := ⟨[startFunc w]⟩
  funcs := (∅ : Std.HashMap Mir.Symbol Nat).insert Silmaril.Compile.Forks.CoreComp.Target.startSymbol 0
  data := (∅ : Std.HashMap Mir.Symbol Nat).insert Silmaril.Compile.Forks.CoreComp.Target.ctlSymbol ctlAddr
  dataBase := Silmaril.Compile.Forks.CoreComp.Target.dataBase
  dataEnd := Silmaril.Compile.Forks.CoreComp.Target.dataBase
  image := .empty

theorem link_funcs (w : Lir.Word) : (link w).funcs[Silmaril.Compile.Forks.CoreComp.Target.startSymbol]? = some 0 := by
  simp [link]

/-- The Lir run of `__ccomp_start` returns `[w]` and leaves the memory unchanged. -/
theorem link_returns (w argc argv : Lir.Word) (mem : Lir.Memory) :
    ∃ s, (link w).prog.start 0 [argc, argv] mem = some s ∧
      Lir.Behaves (link w).prog s (.returned [w] mem) := by
  let fr := (Lir.Frame.empty.set 1 argc).set 2 argv
  refine ⟨⟨⟨0, 0, 0⟩, fr, [], mem⟩, rfl, ?_⟩
  refine ⟨⟨⟨0, 0, 1⟩, fr.set 0 w, [], mem⟩, Relation.ReflTransGen.single ?_, ?_⟩
  · rfl
  · rfl

/-- Every Lir behaviour of `__ccomp_start` is the return of `[w]` with the initial
memory. -/
theorem link_beh {w argc argv : Lir.Word} {mem : Lir.Memory} {s : Lir.State Mir.Reg}
    (hs : (link w).prog.start 0 [argc, argv] mem = some s) {b : Lir.Behavior}
    (hb : Lir.Behaves (link w).prog s b) : b = .returned [w] mem := by
  obtain ⟨s', hs', hr⟩ := link_returns w argc argv mem
  rw [hs] at hs'
  cases hs'
  exact Lir.Behaves.unique hb hr

/-- An empty image leaves every byte below the argument block zero. -/
theorem lmem_bytes_empty {a : Artifact} (h : a.image = .empty) (args : List String)
    (i : Nat) (hi : i < a.argBase) : (a.lmem args).bytes i = 0 := by
  simp [Artifact.lmem, h, ByteArray.size_empty, show ¬ a.argBase ≤ i from by omega]

theorem leNat_zeros (n : Nat) : leNat (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, leNat, ih]; rfl

theorem memWord_zero {lm : Lir.Memory} (addr : Nat)
    (h : ∀ i : Fin 8, lm.bytes (addr + i) = 0) :
    memWord lm addr = 0 := by
  have : (List.ofFn fun i : Fin 8 => lm.bytes (addr + i)) = List.replicate 8 0 := by
    simp [h]
  simp only [memWord, this, leNat_zeros]

/-- A zero output length and address mean the output is empty. -/
theorem stdoutOf_zero {lm : Lir.Memory} (h : memWord lm (ctlAddr + 24) = 0)
    (haddr : memWord lm (ctlAddr + 48) = 0)
    {out : List UInt8} (ho : StdoutOf lm out) : out = [] :=
  ho [] (by simp [memStdout?, h, haddr])

/-- The backend reserves its fixed argument area and preserves the link's image. -/
theorem artifact_layout {l : Mir.Linked} {a : Artifact} (h : artifactOf l = .ok a) :
    a.argBase = Silmaril.Compile.Forks.CoreComp.Target.argBase ∧ a.argSize = Silmaril.Compile.Forks.CoreComp.Target.argSize ∧ a.image = l.image := by
  unfold artifactOf at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- **The constant link is correct.** Every observation of the loaded artifact of
`link w` is exhaustion or the exit with status `w mod 256` and no output. -/
theorem link_sound {w : Lir.Word} {a : Artifact} (h : artifactOf (link w) = .ok a)
    {S : X86.Backend.Space} {exit : X86.Word} {E0 : Nat} (hl : Loaded a S exit E0)
    {saved : X86.Reg → X86.Word} {init : X86.State} {args : List String} {o : Obs}
    (hb : MachineBeh a S exit E0 saved init args o) :
    o = .exhausted ∨ o = .exit (w.toNat % 256) [] := by
  obtain ⟨hbase, _, himg⟩ := artifact_layout h
  have hzero (addr : Nat) (hi : addr + 8 ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase) :
      memWord (a.lmem args) addr = 0 := by
    apply memWord_zero
    intro i
    apply lmem_bytes_empty (by simpa [link] using himg)
    rw [hbase]
    have := i.isLt
    omega
  have hlen := hzero (ctlAddr + 24) (by decide)
  have haddr := hzero (ctlAddr + 48) (by decide)
  obtain ⟨start, s, hstart, hs, ho⟩ := artifactOf_sound h hl hb
  rw [link_funcs] at hstart
  cases hstart
  rcases ho with ho | hstuck | ⟨b, hb, hobs⟩
  · exact .inl ho
  · cases link_beh hs hstuck
  · right
    cases link_beh hs hb
    obtain ⟨k, out, rfl, hk, hout⟩ := hobs
    rw [hk w rfl, stdoutOf_zero hlen haddr hout]

end Silmaril.Compile.Core.Verified.ConstLink
