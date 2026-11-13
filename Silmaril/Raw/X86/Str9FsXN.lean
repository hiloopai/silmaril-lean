module

public import Silmaril.X86.Str9FsXN.Defs
public import Silmaril.X86.Str9FsX.Thms
public import Silmaril.X86.Narrow9.Thms

/-!
# `Str9FsXN`: the conservative extension of `Str9FsX`, the listing laws, the machine

* `step_of_str9fsx`: **every `Str9FsX` step is a step** (the `Narrow9` forms are tried only
  where every decoder of `Str9FsX` rejects the fetch window), so `extendsStr9FsX :
  Str9FsX.isa.Extends isa` (identity lens on `XState`) and, by composition, `extendsSse9`,
  `extendsStr9Fs`, `extendsStr9`, `extendsOpen9`, `extendsOpen`.
* `step_of_fetch_narrow`, `step_of_listed_narrow`, `step_of_listed`: the listing laws (`isa`:
  `Str9FsX`'s integer instructions and the `Narrow9` forms); `step_of_listed_sse`: the SSE
  forms, lifted from `Str9FsX`.
-/

@[expose] public section

namespace Silmaril.X86.Str9FsXN

open Silmaril.X86 (State MState Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.Sse9 (XState XFile)
open Silmaril.Process (Memory)

/-! ## Conservative extension -/

/-- **Every `Str9FsX` step is a step.** -/
theorem step_of_str9fsx {x y : XState} (h : Str9FsX.step x = some y) : step x = some y := by
  unfold Str9FsX.step at h
  unfold step
  split at h
  · rename_i h8
    rw [h8]
    simp only
    split at h
    · rename_i i n h9; rw [h9]; exact h
    · cases h
    · rename_i h9
      rw [h9]
      simp only
      split at h
      · rename_i i n hs; rw [hs]; exact h
      · cases h
      · rename_i hs
        rw [hs]
        simp only
        split at h
        · rename_i i n hn; rw [hn]; exact h
        · cases h
        · rename_i hn
          rw [hn]
          simp only
          split at h
          · rename_i i n hsse; rw [hsse]; exact h
          · cases h
          · rename_i hsse
            rw [hsse]
            simp only
            split at h
            · rename_i n hst; rw [hst]; exact h
            · cases h
  · rename_i h8
    split
    · rename_i h8'; exact absurd h8' h8
    · exact h

/-! ## Listing laws -/

theorem decodeStosd_none_of_bad {w : List Byte} (h : stosdBad w = true) (more : List Byte) :
    Str9FsX.decodeStosd (w ++ more) = none := by
  match w, h with
  | b :: t, h =>
    simp only [stosdBad, bne_iff_ne, ne_eq] at h
    simp only [List.cons_append]
    unfold Str9FsX.decodeStosd
    split
    · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h
    · rfl

theorem decodeNarrowL_spec {w : List Byte} {i : Narrow9.New} {n : Nat}
    (h : decodeNarrowL w = some (i, n)) :
    Narrow9.decodeNew w = some (i, n) ∧ Silmaril.X86.Ext.decode w = none ∧
      Silmaril.X86.Open9.newBad w = true ∧ Silmaril.X86.Open9.rawNotEof w = true ∧
      Silmaril.X86.Str9.ext9Bad w = true ∧ Silmaril.X86.Str9Fs.strBad w = true ∧
      Str9FsX.atomicBad w = true ∧ Str9FsX.fsBad w = true ∧ Str9FsX.sseBad w = true ∧
      stosdBad w = true ∧ 0 < n ∧ n ≤ maxInstrLength := by
  unfold decodeNarrowL at h
  split at h
  · rename_i j k hj
    split at h
    · rename_i c
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hj, c⟩
    · cases h
  · cases h

/-- **The fetch form of the `Narrow9` law.** -/
theorem step_of_fetch_narrow {x : XState} {l : Nat} {w : List Byte} {i : Narrow9.New}
    {c : State} {mem : Memory}
    (fetched : x.m.memory.fetchBytes x.m.core.rip.toNat l = some w)
    (hdec : decodeNarrowL w = some (i, l))
    (hx : Narrow9.execNew i x.m.core x.m.memory (x.m.core.rip + BitVec.ofNat 64 l) = .ok c mem) :
    step x = some ⟨⟨c, mem⟩, x.xmm⟩ := by
  obtain ⟨hd, hnone, hbad, hne, hbad9, hstr, ha, hf, hs, hsd, -, h15⟩ := decodeNarrowL_spec hdec
  obtain ⟨more, hmore, hf8⟩ :=
    Silmaril.X86.Open9.fetch8_undecodable_of fetched h15 hnone hbad hne
  have hfn9 : Silmaril.X86.Ext9.fetchNew x.m.memory x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Ext9.fetchNew
    rw [hmore, Silmaril.X86.Str9.decodeNew_none_of_bad hbad9 more]
    rfl
  have hfs : Silmaril.X86.Str9.fetchStr x.m.memory x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9.fetchStr
    rw [hmore, Silmaril.X86.Str9Fs.decodeStr_none_of_strBad hstr more]
    rfl
  have hfn : Silmaril.X86.Str9Fs.fetchNew x.m.memory x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9Fs.fetchNew
    rw [hmore, Str9FsX.str9fsNew_none ha hf more]
    rfl
  have hss : Silmaril.X86.Sse9.fetchSse x.m.memory x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Sse9.fetchSse
    rw [hmore, Str9FsX.sse_none hs more]
    rfl
  have hst : Str9FsX.fetchStosd x.m.memory x.m.core.rip.toNat = none := by
    unfold Str9FsX.fetchStosd
    rw [hmore, decodeStosd_none_of_bad hsd more]
    rfl
  have hnw : Narrow9.fetchNew x.m.memory x.m.core.rip.toNat = some (some (i, l)) := by
    unfold Narrow9.fetchNew
    rw [hmore, Narrow9.decodeNew_append hd more]
    simp [Silmaril.Process.Memory.readWith_permitted fetched]
  simp only [step, hf8, hfn9, hfs, hfn, hss, hst, hnw, hx, Str9FsX.keep,
    Silmaril.X86.Open.ofResult, Option.map_some]

/-- **The `Narrow9` listing law.** -/
theorem step_of_listed_narrow {x : XState} {base : Word} {code : List Byte} {o l : Nat}
    {i : Narrow9.New} {c : State} {mem : Memory} (hl : Loaded x.m.memory base code)
    (hrip : x.m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decodeNarrowL ((code.drop o).take l) = some (i, l))
    (hx : Narrow9.execNew i x.m.core x.m.memory (x.m.core.rip + BitVec.ofNat 64 l) = .ok c mem) :
    step x = some ⟨⟨c, mem⟩, x.xmm⟩ := by
  have h1 : 0 < l := (decodeNarrowL_spec hdec).2.2.2.2.2.2.2.2.2.2.1
  have hA : x.m.core.rip.toNat = base.toNat + o := by rw [hrip]; exact hl.toNat_add (by omega)
  have fetched : x.m.memory.fetchBytes x.m.core.rip.toNat l = some ((code.drop o).take l) := by
    rw [hA]; exact hl.fetchBytes_sub (by omega) hfit
  exact step_of_fetch_narrow fetched hdec hx

/-- **The listing law of the integer instructions.** -/
theorem step_of_listed {x : XState} {base : Word} {code : List Byte} {o l : Nat} {i : Instr}
    {c : State} {mem : Memory} (hl : Loaded x.m.memory base code)
    (hrip : x.m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (i, l))
    (hx : exec i x.m.core x.m.memory l = .ok c mem) :
    step x = some ⟨⟨c, mem⟩, x.xmm⟩ := by
  unfold decode at hdec
  split at hdec
  · rename_i j n hj
    simp only [Option.some.injEq, Prod.mk.injEq] at hdec
    obtain ⟨rfl, rfl⟩ := hdec
    exact step_of_str9fsx (Str9FsX.step_of_listed hl hrip hfit hj hx)
  · cases hs : decodeNarrowL ((code.drop o).take l) with
    | none => rw [hs] at hdec; cases hdec
    | some p =>
      obtain ⟨j, n⟩ := p
      rw [hs] at hdec
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hdec
      obtain ⟨rfl, rfl⟩ := hdec
      exact step_of_listed_narrow hl hrip hfit hs hx

/-- **The SSE listing law** (`Str9FsX.step_of_listed_sse`, lifted). -/
theorem step_of_listed_sse {x : XState} {base : Word} {code : List Byte} {o l : Nat}
    {i : Silmaril.X86.Sse9.Instr} {c : State} {xs : XFile} {mem : Memory}
    (hl : Loaded x.m.memory base code) (hrip : x.m.core.rip = base + BitVec.ofNat 64 o)
    (hfit : o + l ≤ code.length) (hdec : Str9FsX.decodeSseL ((code.drop o).take l) = some (i, l))
    (hx : Silmaril.X86.Sse9.exec i x.m.core x.xmm x.m.memory (x.m.core.rip + BitVec.ofNat 64 l) =
      .ok c xs mem) :
    step x = some ⟨⟨c, mem⟩, xs⟩ :=
  step_of_str9fsx (Str9FsX.step_of_listed_sse hl hrip hfit hdec hx)

/-! ## The machine -/

/-- **`Str9FsXN` as a segment-VC instance** over its integer instructions (`Str9FsX`'s and the
`Narrow9` forms); the SSE forms have `step_of_listed_sse`. -/
@[reducible] def isa : Silmaril.X86.SegVC.Isa XState where
  Instr := Instr
  instDecEq := inferInstance
  decode := decode
  exec := exec
  core := fun x => x.m.core
  mem := fun x => x.m.memory
  upd := fun x c m => ⟨⟨c, m⟩, x.xmm⟩
  core_upd := fun _ _ _ => rfl
  mem_upd := fun _ _ _ => rfl
  upd_self := fun _ => rfl
  ok := fun _ _ => True
  live := fun _ => True
  step := step
  live_step := fun _ _ => trivial
  step_of := fun _ hl hrip hfit hdec hx _ => step_of_listed hl hrip hfit hdec hx

@[simp] theorem isa_step : isa.step = step := rfl

/-- **`Str9FsXN` extends `Str9FsX`** on the same states. -/
@[reducible] def extendsStr9FsX : Str9FsX.isa.Extends isa :=
  .ofStep (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ h => h) step_of_str9fsx

/-- `Str9FsXN` extends `Sse9`. -/
@[reducible] def extendsSse9 : Silmaril.X86.Sse9.isa.Extends isa :=
  Str9FsX.extendsSse9.trans extendsStr9FsX

/-- `Str9FsXN` extends `Str9Fs` (the XMM file is the frame). -/
@[reducible] def extendsStr9Fs : Silmaril.X86.Str9Fs.isa.Extends isa :=
  Str9FsX.extendsStr9Fs.trans extendsStr9FsX

/-- `Str9FsXN` extends `Str9`. -/
@[reducible] def extendsStr9 : Silmaril.X86.Str9.isa.Extends isa :=
  Str9FsX.extendsStr9.trans extendsStr9FsX

/-- `Str9FsXN` extends the open machine over `Ext9`. -/
@[reducible] def extendsOpen9 : Silmaril.X86.Open9.isa.Extends isa :=
  Str9FsX.extendsOpen9.trans extendsStr9FsX

/-- `Str9FsXN` extends the open machine over `Ext8`. -/
@[reducible] def extendsOpen : Silmaril.X86.Open.isa.Extends isa :=
  Str9FsX.extendsOpen.trans extendsStr9FsX

end Silmaril.X86.Str9FsXN
