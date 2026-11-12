module

public import Silmaril.Raw.Elf.Link.Dyn.Crt.Basic

/-! # The C runtime: its image facts from the loader relation

`Layout.imageOk`: one closed Boolean per executable (checked by `decide +kernel` on the file
and its slot table): every runtime function, `main` and the read-only slice are plain bytes of
their `PT_LOAD` (no relocation covers them), `completed.0` is a zero byte of the writable
segment outside `PT_GNU_RELRO`, and the GOT slots hold the bindings. `crtMem_of_loaded`: from
the loader relation `ExeLoaded`, the runtime's image facts `CrtMem` hold at every base. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Crt

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn.Proc

/-- A plain slice of a `PT_LOAD`, readable with `acc`. -/
def plainIn (f : Blob) (i : Elf.DynInfo) (ph : Elf.Phdr) (D : List (Nat × Val)) (acc : Access)
    (v : Nat) (l : List Byte) : Bool :=
  i.phs.contains ph && ph.kind == 1 && decide (ph.vaddr ≤ v) &&
    decide (v + l.length ≤ ph.vaddr + ph.memsz) && decide (0 < l.length) &&
    flagAllows ph acc && plainOk f ph D v l

/-- A GOT slot of a readable `PT_LOAD`, holding `val`. -/
def slotIn (i : Elf.DynInfo) (ph : Elf.Phdr) (D : List (Nat × Val)) (s : Nat) (val : Val) : Bool :=
  i.phs.contains ph && ph.kind == 1 && decide (ph.vaddr ≤ s) && decide (s + 8 ≤ ph.vaddr + ph.memsz) &&
    decide (ph.flags / 4 % 2 = 1) && slotOk D s val

/-- **The per-binary image check.** `lsmOff`, `cxaOff`: the offsets of `__libc_start_main` and
`__cxa_finalize` in `libc.so.6` (object 1). -/
def Layout.imageOk (L : Layout) (f : Blob) (i : Elf.DynInfo) (tx ro rw : Elf.Phdr)
    (D : List (Nat × Val)) (lsmOff cxaOff : Nat) : Bool :=
  plainIn f i tx D .execute L.init L.cInit && plainIn f i tx D .execute L.start L.cStart &&
  plainIn f i tx D .execute L.dereg L.cDereg && plainIn f i tx D .execute L.reg L.cReg &&
  plainIn f i tx D .execute L.dtors L.cDtors && plainIn f i tx D .execute L.fdummy L.cFdummy &&
  plainIn f i tx D .execute L.fini L.cFini && plainIn f i tx D .execute L.plt L.cPlt &&
  plainIn f i tx D .execute L.main L.cMain && plainIn f i ro D .read L.ro L.cRo &&
  plainIn f i rw D .read L.cmpl [0] &&
  decide (rw.flags / 2 % 2 = 1) && !inRelro i L.cmpl &&
  slotIn i rw D L.gotLsm (.addr 1 lsmOff) && slotIn i rw D L.gotDereg (.abs 0) &&
  slotIn i rw D L.gotGmon (.abs 0) && slotIn i rw D L.gotReg (.abs 0) &&
  slotIn i rw D L.gotCxa (.addr 1 cxaOff) && slotIn i rw D L.dso (.addr 0 L.dso)

section
variable {f : Blob} {b : Word} {i : Elf.DynInfo} {bases : List Word} {ifn : Word → Option Word}
  {res : Word} {D : List (Nat × Val)} {T : List (Nat × Option Word)} {mem : Memory}

theorem plainIn_read (h : ImageOk ⟨f, b⟩ i T mem)
    (hT : D.mapM (fun e => (e.2.word bases ifn res).map fun w => (e.1, w)) = some T)
    {ph : Elf.Phdr} {acc : Access} {v : Nat} {l : List Byte} (hok : plainIn f i ph D acc v l = true) :
    mem.readWith acc (b + BitVec.ofNat 64 v).toNat l.length = some l := by
  simp only [plainIn, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem,
    and_assoc] at hok
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hok
  exact h.readPlain hT h1 h2 h3 h4 h5 h6 h7

theorem slotIn_load (h : ImageOk ⟨f, b⟩ i T mem)
    (hT : D.mapM (fun e => (e.2.word bases ifn res).map fun w => (e.1, w)) = some T)
    {ph : Elf.Phdr} {s : Nat} {val : Val} {w : Word} (hok : slotIn i ph D s val = true)
    (hval : val.word bases ifn res = some (some w)) : loadN mem (b + BitVec.ofNat 64 s) 8 = some w := by
  simp only [slotIn, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem,
    and_assoc] at hok
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hok
  exact h.loadSlot hT h1 h2 h3 h4 h5 h6 hval
end

/-- **The runtime's image facts from the loader relation**, at every base. -/
theorem crtMem_of_loaded {L : Layout} {f Fc Fl : Blob} {i : Elf.DynInfo}
    {tx ro rw : Elf.Phdr} {D : List (Nat × Val)} {lsmOff cxaOff : Nat}
    (hi : finfo f = some i) {lz : Bool} (hD : slots [f, Fc, Fl] lz f i = some D)
    (hok : L.imageOk f i tx ro rw D lsmOff cxaOff = true)
    {b lb ldb res : Word} {ifn : Word → Option Word} {mem : Memory}
    (h : ExeLoaded [f, Fc, Fl] [b, lb, ldb] ifn lz res mem) :
    CrtMem L b (lb + BitVec.ofNat 64 lsmOff) (lb + BitVec.ofNat 64 cxaOff) 0#8 mem := by
  obtain ⟨f', b', i', D', T, hf, hb, hi', -, hD', hT, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb
  subst hf hb
  rw [hi, Option.some.injEq] at hi'
  subst hi'
  rw [hD, Option.some.injEq] at hD'
  subst hD'
  simp only [Layout.imageOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', and_assoc] at hok
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, w1, w2, s1, s2, s3, s4, s5, s6⟩ := hok
  have hdone := plainIn_read himg hT p11
  refine ⟨plainIn_read himg hT p1, plainIn_read himg hT p2, plainIn_read himg hT p3,
    plainIn_read himg hT p4, plainIn_read himg hT p5, plainIn_read himg hT p6,
    plainIn_read himg hT p7, plainIn_read himg hT p8, plainIn_read himg hT p9,
    plainIn_read himg hT p10,
    slotIn_load himg hT s1 (by simp [Val.word]), slotIn_load himg hT s2 (by simp [Val.word]),
    slotIn_load himg hT s3 (by simp [Val.word]), slotIn_load himg hT s4 (by simp [Val.word]),
    slotIn_load himg hT s5 (by simp [Val.word]), slotIn_load himg hT s6 (by simp [Val.word]),
    hdone, ?_⟩
  -- `completed.0` is writable
  simp only [plainIn, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem,
    and_assoc] at p11
  obtain ⟨h1, h2, h3, h4, -, -, -⟩ := p11
  obtain ⟨hw, -, -, hwr, -⟩ := himg.point h1 h2 h3 (by simp at h4; omega)
  rw [Memory.Permitted, Memory.checkSpan_iff]
  have hwrap := hw
  simp only at hwrap
  rw [addr_toNat hwrap]
  refine ⟨by simp only [Silmaril.Process.addressLimit]; omega,
    by simp only [Silmaril.Process.addressLimit]; omega, fun k hk => ?_⟩
  have : k = 0 := by omega
  subst this
  simp only [Nat.add_zero]
  rw [hwr, w1, w2]; rfl

end Silmaril.Elf.Link.Dyn.Crt
